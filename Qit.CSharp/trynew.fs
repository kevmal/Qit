namespace Qit.CSharp2


open Qit
open Microsoft.CodeAnalysis.CSharp

module Internal = 

    open Microsoft.CodeAnalysis.CSharp
    open Microsoft.CodeAnalysis.CSharp.Syntax
    open Microsoft.CodeAnalysis.CSharp
    open System
    open Microsoft.FSharp.Core.CompilerServices
    open System.Reflection
    open Microsoft.FSharp.Quotations
    open Microsoft.FSharp.Quotations.Patterns
    open Microsoft.CodeAnalysis

    let rec typeStr (t : Type) = 
        if t.IsGenericType then 
            let targs = t.GetGenericArguments() |> Array.map typeStr
            let name =
                let name = t.FullName
                let i = name.LastIndexOf "`"
                name.Substring(0,i)
            sprintf "%s<%s>" name (targs |> String.concat ", ")
        else
            t.FullName

    module Crap = 
        open UncheckedQuotations

        let simple expr = 
            expr 
            |> traverseQuotation
                (fun q ->
                    match q with 
                    | Application(Lambda(v,b),a) -> Expr.Let(v,a,b) |> Some
                    | _ -> None
                )
        let rewriteAss v expr = 
            let expr = simple expr
            let rec traverseQuotation f q = 
                match f q with 
                | None ->
                    match q with
                    | Sequential(e1,e2) -> Expr.Sequential(e1, traverseQuotation f e2)
                    | Let(v,e1,e2) -> Expr.Let(v,e1,traverseQuotation f e2)
                    | IfThenElse(c,e1,e2) -> Expr.IfThenElse(c,traverseQuotation f e1, traverseQuotation f e2)
                    | ShapeCombinationUnchecked(a, args) -> 
                        let nargs = args |> List.map (traverseQuotation f)
                        RebuildShapeCombinationUnchecked(a, nargs)
                    | ShapeLambdaUnchecked(v, body) -> Expr.Lambda(v, traverseQuotation f body)
                    | ShapeVarUnchecked(v) -> Expr.Var(v)
                | Some q -> q
            printfn "%A" expr
            let mutable changeFlag = false
            let newExpr = 
                expr 
                |> traverseQuotation
                    (fun q ->
                        match q with 
                        | Value _ 
                        | AddressOf _
                        | Call _
                        | Coerce _
                        | DefaultValue _
                        | FieldGet _
                        | PropertyGet _
                        | Var _
                        | TupleGet _ ->
                            printfn "%A" q
                            Some(Expr.VarSet(v,q))
                        | _ ->  
                            changeFlag <- true
                            None
                    )
            if changeFlag then 
                Some newExpr 
            else
                None

    open Crap
    let rec findVarByName name expr =
        match expr with
        | ExprShape.ShapeVar(v) when v.Name = name -> true
        | ExprShape.ShapeLambda(v, body) when v.Name = name -> true
        | ExprShape.ShapeCombination(a, args) -> args |> List.exists (findVarByName name)
        | ExprShape.ShapeLambda(v, body) -> findVarByName name body
        | ExprShape.ShapeVar(v) -> false
     
    module Regex = 
        open System.Text.RegularExpressions

        let isMatch (pattern : string) (input : string) = Regex.IsMatch(input, pattern)
        let isMatchIgnoreCase (pattern : string) (input : string) = Regex.IsMatch(input, pattern, RegexOptions.IgnoreCase)
        let groups (pattern : string) (input : string) = Regex.Match(input, pattern).Groups |> Seq.cast<Group> |> Seq.map (fun x -> x.Value) |> Seq.toArray
        let tryGroups (pattern : string) (input : string) = 
            let m = Regex.Match(input, pattern)
            if m.Success then
                m.Groups |> Seq.cast<Group> |> Seq.map (fun x -> x.Value) |> Seq.toArray |> Some
            else
                None
        let makePattern (pattern : string) = 
            let rx = Regex(pattern, RegexOptions.Compiled)
            fun input -> 
                let m = rx.Match(input)
                if m.Success then
                    m.Groups |> Seq.cast<Group> |> Seq.map (fun x -> x.Value) |> Seq.toArray |> Some
                else
                    None

    let (|Rx|_|) p x = Regex.tryGroups p x

    let rewriteVar (existingNames : string Set) (v : Var) expr = 
        expr 
        |> traverseQuotation
            (fun q ->
                match q with 
                | Let(v2,e1,e2) when v.Name = v2.Name && v <> v2 -> 
                    let name,n = 
                        match v.Name with 
                        | Rx @"(.*)__(\d+)" g -> g.[1],int g.[2] + 1
                        | _ -> v.Name,1
                    let mutable k = n
                    let mutable newName = (name + "__" + string k)
                    while existingNames.Contains newName || findVarByName newName e2 do 
                        k <- k + 1
                        newName <- (name + "__" + string k)
                    let newVar = Var(newName,v2.Type,v2.IsMutable)
                    Expr.Let(newVar,e1,e2.Substitute(fun v -> if v = v2 then Some (Expr.Var newVar) else None))
                    |> Some
                | _ -> None
            )

        
    let rewriteShadowing expr = 
        let rec expand vars expr = 
            let expanded = 
                match expr with
                | ExprShape.ShapeVar v -> Expr.Var v
                | ExprShape.ShapeLambda(v, expr) -> 
                  Expr.Lambda(v, expand vars expr)
                | ExprShape.ShapeCombination(o, exprs) ->
                  let fuck = List.map (expand vars) exprs
                  let e = ExprShape.RebuildShapeCombination(o, fuck)
                  e
            match expanded with
                | Patterns.Application(ExprShape.ShapeLambda(v, body), assign)
                | Patterns.Let(v, assign, body) -> 
                    if Set.contains v.Name vars then 
                        let name,n = 
                            match v.Name with 
                            | Rx @"(.*)__(\d+)" g -> g.[1],int g.[2] + 1
                            | _ -> v.Name,1
                        let mutable k = n
                        let mutable newName = (name + "__" + string k)
                        while vars.Contains newName || findVarByName newName body do 
                            k <- k + 1
                            newName <- (name + "__" + string k)
                        let newVar = Var(newName,v.Type,v.IsMutable)
                        Expr.Let(newVar,assign,body.Substitute(fun v2 -> if v = v2 then Some (Expr.Var newVar) else None))
                    else
                        Expr.Let(v,expand vars assign,expand (Set.add v.Name vars) body)
                | _ -> expanded
        expand Set.empty expr

    let parse (x : string) = CSharpSyntaxTree.ParseText(x).GetRoot().NormalizeWhitespace()

    let rec opMethod q = 
        match q with 
        | Lambda(_, expr) -> opMethod expr
        | Call(_, mi, _) ->  mi
        | _ -> failwith "opMethod invalid quote"

    let (|Op|_|) (op : Expr) q = 
        let m = opMethod op
        match q with 
        | Call(exprOption, methodInfo, exprList) -> 
            if exprList.Length = 2 then 
                if m.IsGenericMethod then 
                    if methodInfo.IsGenericMethod && methodInfo.GetGenericMethodDefinition() = m.GetGenericMethodDefinition() then 
                        Some(exprList.[0], exprList.[1])
                    else 
                        None
                elif m = methodInfo then 
                    Some(exprList.[0], exprList.[1])
                else 
                    None
            else
                None
        | _ -> None

    let (|Cl|_|) (op : Expr) q = 
        let m = opMethod op
        match q with 
        | Call(exprOption, methodInfo, exprList) -> 
            if m.IsGenericMethod then 
                if methodInfo.IsGenericMethod && methodInfo.GetGenericMethodDefinition() = m.GetGenericMethodDefinition() then 
                    Some(exprList)
                else 
                    None
            elif m = methodInfo then 
                Some(exprList)
            else 
                None
        | _ -> None



    let rec exs q = 
        (ex q).GetText().ToString()
    and ex q : SyntaxNode =
        printfn "22222222222222222222222222222222222222222222222222222222"
        printfn "%A" q
        printfn "22222222222222222222222222222222222222222222222222222222"
        match q with
        | AddressOf(expr) -> SyntaxFactory.PrefixUnaryExpression(SyntaxKind.AddressOfExpression, ex expr :?> _) :> _
        | AddressSet(expr1, expr2) ->  failwithf "AddressSet(%A, %A)" expr1 expr2
        | Application(Lambda(v,expr2), expr1) ->
            let e = Expr.Let(v,expr1,expr2)
            ex e
        | Op <@@ (>) @@> (a,b) -> sprintf "%s > %s" (exs a) (exs b) |> parse
        | Op <@@ (<) @@> (a,b) -> sprintf "%s < %s" (exs a) (exs b) |> parse
        | Op <@@ (=) @@> (a,b) -> sprintf "%s == %s" (exs a) (exs b) |> parse
        | Op <@@ (>=) @@> (a,b) -> sprintf "%s >= %s" (exs a) (exs b) |> parse
        | Op <@@ (<=) @@> (a,b) -> sprintf "%s <= %s" (exs a) (exs b) |> parse
        | Op <@@ (+) @@> (a,b) -> sprintf "%s + %s" (exs a) (exs b) |> parse
        | Op <@@ (-) @@> (a,b) -> sprintf "%s - %s" (exs a) (exs b) |> parse
        | Op <@@ (*) @@> (a,b) -> sprintf "%s * %s" (exs a) (exs b) |> parse
        | Op <@@ (/) @@> (a,b) -> sprintf "%s / %s" (exs a) (exs b) |> parse
        | Op <@@ Array.empty.[0] @@> (a,b) -> sprintf "%s[%s]" (exs a) (exs b) |> parse
        | Cl <@@ Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions.SetArray @@> (args) 
          & Call(None, methodInfo, exprList) -> 
            let v = Var("a", args.[2].Type)
            let expr = rewriteAss v args.[2]
            match expr with 
            | Some expr ->
                expr 
                |> traverseQuotation
                    (function 
                     | VarSet(v0,e) when v0 = v -> 
                        let exprList2 = [exprList.[0]; exprList.[1]; e]
                        Some(Expr.Call(methodInfo, exprList2))
                     | _ -> None)
                |> ex
            | None -> sprintf "%s[%s] = %s;" (exs args.[0]) (exs args.[1]) (exs args.[2]) |> parse
        | Call(exprOption, methodInfo, exprList) -> 
        //CSharpSyntaxTree.ParseText("System.TimeSpan.FromMinutes(23.0)").GetRoot()
            let o = 
                match exprOption with 
                | Some v -> sprintf "(%s)" ((ex v).GetText().ToString())
                | None -> methodInfo.DeclaringType |> typeStr
            let args = exprList |> List.map (exs) |> List.map (fun x -> sprintf "(%s)" x) |> String.concat ","
            if methodInfo.IsGenericMethod then
                let targs = methodInfo.GetGenericArguments() |> Array.map typeStr |> String.concat ","
                sprintf "%s.%s<%s>(%s)" o methodInfo.Name targs args
                |> parse
            else
                sprintf "%s.%s(%s)" o methodInfo.Name args
                |> parse
        | Coerce(expr, type1) -> sprintf "((%s)(%s))" (typeStr type1) (exs expr) |> parse
        | DefaultValue(type1) -> sprintf "(new %s())" (typeStr type1) |> parse
        | FieldGet(expr, fieldInfo) -> 
            match expr with
            | Some expr ->
                sprintf "(%s).%s" (exs expr) fieldInfo.Name |> parse
            | None ->
                sprintf "%s" fieldInfo.Name |> parse
        | FieldSet(exprOption, fieldInfo, expr) -> 
            match exprOption with
            | Some e ->
                sprintf "(%s).%s = %s" (exs e) fieldInfo.Name (exs expr) |> parse
            | None ->
                sprintf "%s = %s" fieldInfo.Name (exs expr) |> parse
        | ForIntegerRangeLoop(var1, expr1, expr2, expr3) -> 
            sprintf "for(int %s = %s; %s <= %s; %s++) { %s }" (var1.Name) (exs expr1) (var1.Name) (exs expr2) (var1.Name) (exs expr3) |> parse
        | IfThenElse(expr1, expr2, expr3) -> 
            match expr1 with
            | Sequential(e1, e2) -> 
                let iff = Expr.IfThenElse(e2,expr2,expr3)
                sprintf "%s; %s;" (exs e1) (exs iff) |> parse
            | _ -> sprintf "if(%s) {%s} else {%s}" (exs expr1) (exs expr2) (exs expr3) |> parse
        | Lambda(var1, expr) -> 
            sprintf "((%s %s) => {%s})" (typeStr var1.Type) var1.Name (exs expr) |> parse
        | LetRecursive(varExprList, expr) -> failwith "let rec"
        | Let(var, expr1, expr2) ->
            let x = 
                match rewriteAss var expr1 with 
                | Some x -> x
                | None -> expr1
            sprintf "%s %s; %s; %s;" (typeStr var.Type) var.Name (exs x) (exs expr2) |> parse
        | NewArray(type1, exprList) -> 
            sprintf "new[] {%s}" (exprList |> List.map exs |> String.concat  ",") |> parse
        | NewDelegate(type1, varList, expr) -> failwith "NewDelegate(type1, varList, expr)"
        | NewObject(constructorInfo, exprList) -> 
            sprintf "new %s(%s)" (typeStr constructorInfo.DeclaringType) (exprList |> Seq.map exs |> String.concat ", ") |> parse
        | NewRecord(type1, exprList) -> failwith "NewRecord(type1, exprList)"
        | NewTuple(exprList) -> failwith "NewTuple(exprList)"
        | NewUnionCase(unionCaseInfo, exprList) -> failwith "NewUnionCase(unionCaseInfo, exprList)"
        | PropertyGet(exprOption, propertyInfo, exprList) -> 
            if List.isEmpty exprList |> not then failwith "indexed property get"
            match exprOption with
            | Some expr ->
                sprintf "(%s).%s" (exs expr) propertyInfo.Name |> parse
            | None ->
                sprintf "%s" propertyInfo.Name |> parse
        | PropertySet(exprOption, propertyInfo, exprList, expr) -> 
            if List.isEmpty exprList |> not then failwith "indexed property set"
            match exprOption with
            | Some e ->
                sprintf "(%s).%s = %s" (exs e) propertyInfo.Name (exs expr) |> parse
            | None ->
                sprintf "%s = %s" propertyInfo.Name (exs expr) |> parse
        | QuoteTyped(expr) -> failwith "QuoteTyped(expr)"
        | QuoteRaw(expr) -> failwith "QuoteRaw(expr)"
        | Sequential(expr1, expr2) -> 
            sprintf "%s; %s;" (exs expr1) (exs expr2) |> parse
        | TryFinally(expr1, expr2) -> failwith "TryFinally(expr1, expr2)"
        | TryWith(expr1, var1, expr2, var2, expr3) -> failwith "TryWith(expr1, var1, expr2, var2, expr3)"
        | TupleGet(expr, int1) -> failwith "TupleGet(expr, int1)"
        | TypeTest(expr, type1) -> failwith "TypeTest(expr, type1)"
        | UnionCaseTest(expr, unionCaseInfo) -> failwith "UnionCaseTest(expr, unionCaseInfo)"
        //| ValueWithName(obj1, type1, name) when List.contains name vs -> name
        | Value(_, t) when t = typeof<unit> -> parse ""
        | Value(null, type1) -> parse "null"
        | Value(obj1, type1) -> obj1.ToString() |> parse
        | VarSet(var, expr)  as qq -> 
            printfn "hi"
            let qq2 = rewriteAss var expr
            //sprintf "%s = %s;" var.Name (exs expr) |> parse
            match qq2 with
            | None -> sprintf "%s = %s;" var.Name (exs expr) |> parse
            | Some qq2 -> 
                //printfn "%A <> %A" qq qq2
                qq2 |> ex
        | Var(var) -> sprintf "%s" var.Name  |> parse
        | WhileLoop(expr1, expr2) -> 
            sprintf "while(%s) {%s}" (exs expr1) (exs expr2) |> parse
        | x -> failwithf "End of matches %A" x


    let assemblies (q : Expr) = 
        let ra = ResizeArray()
        q
        |> traverseQuotation 
            (fun q ->
                match q with 
                | Patterns.Call(e,m,el) -> 
                    ra.Add m.DeclaringType.Assembly
                    None
                | _ -> None
            )
        |> ignore
        ra.ToArray() |> Array.distinct


    type C() = 
        inherit CSharpSyntaxRewriter()
        override x.VisitEmptyStatement(_) = null |> box |> unbox
    let csharp q = 
        use cw = new AdhocWorkspace()
        let format x  = Formatting.Formatter.Format(x,cw)
        let c = C().Visit(ex q |> format).NormalizeWhitespace().ToFullString() |> CSharpSyntaxTree.ParseText
        c, assemblies q

    (*
    let b = 
        exs <@@
                let a = 0


                a + 2
        @@>

    let a = 
        exs <@@ 
            let a = 12
            a + 2
        @@> |> CSharpSyntaxTree.ParseText

    let q = 
        <@
            let mutable bb = 0
            let b = 60
            let a = 
                if 23 = 23 then
                    let b = 23
                    bb <- 232
                    b + 2
                elif 23 = 42 then   
                    let v = 23 
                    let b = 66
                    v + b
                else
                    23 + b
            a + 23
        @>

    let q2 = 
        <@
            let f x = x + 1
            let a = 2 
            f a
        @>
    exs q |> CSharpSyntaxTree.ParseText
    csharp q 

    let b = q2 |> rewriteShadowing |> exs



    let poo = sprintf """
        namespace poo{
            public class shit{
                void OnBar()
                {
                    %s;
                }
            }
        }
            """ b|> CSharpSyntaxTree.ParseText









    assemblies <@@
                let a = 12
                a + 2
        @@>
    |> Seq.iter (fun x -> printfn "%A" x.Location)

    let asm = typeof<obj>.Assembly
    let mscorlib = Microsoft.CodeAnalysis.PortableExecutableReference.CreateFromFile(asm.Location);
    let fsharplib = Microsoft.CodeAnalysis.PortableExecutableReference.CreateFromFile(typeof<string list>.Assembly.Location);

    let compilation = 
        CSharpCompilation.Create("foo", [poo], [mscorlib; fsharplib])

    compilation.WithOptions(new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary)).Emit(@"sdajfiasdjfasfd.dll")

    poo.ToString()


    let cw = Microsoft.CodeAnalysis.MSBuild.MSBuildWorkspace.Create()

    compilation.GetSemanticModel(a,true)

    Formatting.Formatter.Format(poo.GetRoot(),cw).ToFullString()


    type C() = 
        inherit CSharpSyntaxRewriter()
        override x.VisitEmptyStatement(_) = null |> box |> unbox
    C().Visit(poo.GetRoot()).NormalizeWhitespace()


    poo.GetRoot().R .NormalizeWhitespace()
    *)

module Quote = 
    open Internal
    open Microsoft.FSharp.Quotations
    open Microsoft.CodeAnalysis
    let toCSharpString (q : Expr) = 
        (ex q).NormalizeWhitespace().ToFullString() 
    let toFormattedCSharpString (q : Expr) = 
        use cw = new AdhocWorkspace()
        let format x  = Formatting.Formatter.Format(x,cw)
        C().Visit(ex q |> format).NormalizeWhitespace().ToFullString()
        