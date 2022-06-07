#r "nuget:Microsoft.CodeAnalysis.CSharp"
#r "nuget:Microsoft.CodeAnalysis.Workspaces.Common"
#r "nuget:FSharp.Quotations.Evaluator"

#load @"..\Qit\ProvidedTypes.fs"
#load @"..\Qit\Library.fs"
#load @"..\Qit\Patterns.fs"


#load @"Library.fs"

open Qit
open Qit.UncheckedQuotations
open Qit.CSharp
open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Quotations.Patterns
open Microsoft.FSharp.Quotations.DerivedPatterns
open Qit.CSharp.Internal.Crap
open System


let tp (x : Type) = x.Name
    
let (|SpecificCall|_|) templateParameter = 
    match templateParameter with
    | (Lambdas(_, Call(_, minfo1, _)) | Call(_, minfo1, _)) ->
        let isg1 = minfo1.IsGenericMethod
        let gmd = 
            if minfo1.IsGenericMethodDefinition then 
                minfo1
            elif isg1 then 
                minfo1.GetGenericMethodDefinition() 
            else null
        (fun tm ->
           match tm with
           | Call(obj, minfo2, args) when (minfo1.MetadataToken = minfo2.MetadataToken &&
                    if isg1 then
                      minfo2.IsGenericMethod && gmd = minfo2.GetGenericMethodDefinition()
                    else
                      minfo1 = minfo2) ->
               Some(obj, (minfo2.GetGenericArguments() |> Array.toList), args)
           | _ -> None)
        | _ ->
             invalidArg "templateParameter" "The parameter is not a recognized method name"
let (|TypeOf|_|) = (|SpecificCall|_|) <@ typeof<obj> @>
let mutable ai = 0
let argName() = 
    ai <- ai + 1
    $"a_{ai}__"
type Binding = 
    {
        Var : Var
        Expr : Expr
    }
let vignore = Var("_",typeof<obj>)    
let doe e = {Var = vignore; Expr = e}
let nop = <@@ () @@>


let initmut<'a> : 'a = failwith "initmut"
type M = M with 
    static member f<'a>() = <@@ initmut<'a> @@>
let fmeth = typeof<M>.GetMethod("f")
let unchecked (t : Type) = fmeth.MakeGenericMethod(t).Invoke(null,[||]) :?> Expr
//<@ 1 + %%(unchecked typeof<int>) @>
let vr v expr = {Var = v; Expr = expr}
let do_ expr = {Var = Var("_",typeof<unit>); Expr = expr}
let cc x = List.concat x
let letb l body = 
    (l |> List.concat, body) 
    ||> List.foldBack   
        (fun e s -> 
            if LanguagePrimitives.PhysicalEquality e.Var vignore then 
                Expr.Sequential(e.Expr,s)
            else
                Expr.Let(e.Var,e.Expr,s))
let esq l = l |> List.reduce(fun a b -> Expr.Sequential(a,b))
let lambdas(vs : Var list list, b : Expr) = 
    let lambda vs e = 
        match vs with 
        | [v] -> Expr.Lambda(v,e)
        | vs -> 
            let tp = FSharp.Reflection.FSharpType.MakeTupleType(vs |> List.map(fun v -> v.Type) |> List.toArray)
            let v = Var("tupledArg",tp)
            let b = (vs |> List.indexed, e) ||> List.foldBack (fun (i,v) b -> Expr.Let(v,Expr.TupleGet(Expr.Var v,i),b))
            Expr.Lambda(v, b)
    (vs,b) ||> List.foldBack (fun e s -> lambda e s)
(*let (|RecLoop|) e = 
    match e with 
    | LetRecursive([f,Lambdas(vs,lamb)],b) ->
        let rec traverseQuotation q = 
            match q with
            | Let(v,e,b)  -> Expr.Let(v,e,traverseQuotation b)
            | Sequential(a,b) -> Expr.Sequential(a,traverseQuotation b)
            | IfThenElse(cond,t,f) -> Expr.IfThenElse(cond,traverseQuotation t, traverseQuotation f)
            | Application(Var ff,_) when ff = f  -> 
        traverseQuotation lamb


let (|LastExpr|) e = 
    let rec traverseQuotation q = 
        match q with
        | Let(v,e,b)  -> Expr.Let(v,e,traverseQuotation b)
        | Sequential(a,b) -> Expr.Sequential(a,traverseQuotation b)
        | IfThenElse(cond,t,f) -> Expr.IfThenElse(cond,traverseQuotation t, traverseQuotation f)
        | q -> q
    traverseQuotation e *)
let insertVarSet (v : Var) (e : Expr) = 
    let rec traverseQuotation q = 
        match q with
        | Let(v,e,b)  -> Expr.Let(v,e,traverseQuotation b)
        | Sequential(a,b) -> Expr.Sequential(a,traverseQuotation b)
        | IfThenElse(cond,t,f) -> Expr.IfThenElse(cond,traverseQuotation t, traverseQuotation f)
        | q -> Expr.VarSet(v,q)
    traverseQuotation e
    
let firstPass (e : Expr) = 
    let rec f canDef (scope : Var Set) (e : Expr) : (Binding list * Expr)  = 
        let ret l b = 
            if canDef then 
                [],letb l b
            else 
                cc l,b
        let (|NS|) x = f false scope x
        let (|NI|) x = f canDef scope x
        let (|S|) v x = f false (scope |> Set.add v) x
        match e with 
        | ForIntegerRangeLoop(loopVar, NS(e1,first), NS(e2,last), body) -> 
            let e3,body = f canDef (scope |> Set.add loopVar) body 
            ret [e1;e2;e3] (Expr.ForIntegerRangeLoop(loopVar, first, last, body))
        | NewArray(elementTy, elements) -> 
            let e,b = elements |> List.map (f false scope) |> List.unzip
            ret e (Expr.NewArray(elementTy, b))
        | WhileLoop(cond, NS(e2,body)) -> ret [e2] (Expr.WhileLoop(cond,body))
        | Var v -> [], e
        | Coerce (arg, ty) -> [],e
        | TypeOf(None, [t1], []) -> [],e
        | FieldSet(Some(NS(e,o)), field, NS(e1,v)) -> ret [e;e1] (Expr.FieldSet(o,field,v))
        | PropertySet(Some(NS(e,o)), field, [], NS(e1,v)) -> ret [e;e1] (Expr.PropertySet(o,field,v))
        | FieldGet (None, field) -> [],e
        | FieldGet (Some(NS(e,o)), field) -> ret [e] (Expr.FieldGet(o,field))
        | PropertyGet(None, meth, args) ->
            let e,b = args |> List.map (f false scope) |> List.unzip
            ret e (Expr.PropertyGet(meth,b))
        | PropertyGet(Some(NS(e0,o)), meth, args) ->
            let e,b = args |> List.map (f false scope) |> List.unzip
            let e = [e0;yield! e]
            ret e (Expr.PropertyGet(o,meth,b))
        | Call(None, meth, args) ->
            let e,b = args |> List.map (f false scope) |> List.unzip
            ret e (Expr.Call(meth,b))
        | Call(Some(NS(e0,o)), meth, args) ->
            let e,b = args |> List.map (f false scope) |> List.unzip
            let e = [e0;yield! e]
            ret e (Expr.Call(o,meth,b))
        | Applications(func,args) ->  
            let eb = args |> List.map (fun i -> i |> List.map (f false scope)) 
            let e = eb |> List.concat |> List.map fst
            let b = eb |> List.map (fun i -> i |> List.map snd)
            ret e (Expr.Applications(func, b))
        | DefaultValue (t) -> [],e
        | Value (v, _ty) -> [],e
        | Sequential(NI(e1,b1), NI(e2,b2)) -> ret [e1;e2] (Expr.Sequential(b1,b2))
        | IfThenElse(cond, ifTrue, ifFalse) -> 
            let et = e.Type
            if et = typeof<unit> then 
                let e1,cond = f canDef scope cond
                let e2,ifTrue = f canDef scope ifTrue
                let e3,ifFalse = f canDef scope ifFalse
                ret [e1;e2;e3] (Expr.IfThenElse(cond,ifTrue,ifFalse))
            else 
                let v = Var(argName(), et, true)
                let e1,cond = f false scope cond
                let e2,ifTrue = f canDef scope (Expr.VarSet(v,ifTrue))
                let e3,ifFalse = f canDef scope (Expr.VarSet(v,ifFalse))
                ret [e1;[vr v (unchecked et)];e2;e3] (Expr.Sequential(Expr.IfThenElse(cond,ifTrue,ifFalse), Expr.Var v))
        | TryWith(body, _filterVar, _filterBody, catchVar, catchBody) -> failwithf "%A" e
        | TryFinally(body, finallyBody) -> failwithf "%A" e
        | VarSet(v, ((Let _ | Sequential _ | IfThenElse _) as e)) -> 
            printfn "--- %A -----" v.Name
            printfn "%A" e
            printfn "-----"
            let e = insertVarSet v e
            printfn "%A" e
            f canDef scope e
        | VarSet(v, NS(e,b)) -> 
            ret [e; [doe(Expr.VarSet(v,b))]] nop
        | Let(v, Lambdas(vs,body), b) -> 
            let scope2 = vs |> List.concat |> Set.ofList |> Set.union scope
            let e00,b00 = f true scope2 body
            printfn "%A" b00
            if canDef then 
                let e1,b1 = f true scope b
                ret [e00;e1] (Expr.Let(v, lambdas(vs,b00), b1)) 
            else 
                let e0 = [{ Var = v; Expr = lambdas(vs,b00)}]
                let e1,b1 = f true scope b
                ret [e00;e0;e1] b1
        | Lambdas(vs, body) -> 
            let v = Var(argName(), e.Type)
            let e1,_ = f canDef scope (Expr.Let(v,e,<@@ () @@>))
            ret [e1] (Expr.Var v)
        | Let(v, e, b) -> 
            let v2 = 
                if v.IsMutable then 
                    v
                else 
                    Var(v.Name,v.Type, true)
            let e0,b0 = f false scope (Expr.VarSet(v2,e))
            let b = 
                if not v.IsMutable then 
                    b.Substitute(fun i -> if i = v then Some(Expr.Var(v2)) else None)
                else 
                    b
            let scope2 = scope |> Set.add v2
            let e1,b1 = f canDef scope2 b
            ret [
                    [vr v2 (unchecked v2.Type)]
                    e0
                    e1
                ] 
                (Expr.Sequential(b0,b1))
        | NewUnionCase(c,args) -> 
            let e,b = args |> List.map (f false scope) |> List.unzip
            ret e (Expr.NewUnionCase(c,b))
        | n -> failwithf "unknown expression '%A' in generated method" n
    f true Set.empty e 
    ||> List.foldBack   
        (fun e s -> 
            if LanguagePrimitives.PhysicalEquality e.Var vignore then 
                Expr.Sequential(e.Expr,s)
            else
                Expr.Let(e.Var,e.Expr,s))
    |> traverseQuotation
        (fun e -> 
            match e with 
            | Patterns.Sequential(e1,e2) when LanguagePrimitives.PhysicalEquality e1 nop -> 
                Some e2
            | Patterns.Sequential(e1,e2) when LanguagePrimitives.PhysicalEquality e2 nop -> 
                Some e1
            | _ -> None
        )

<@ 
    if (let a = 1 in a + 6) > 0 then 
        2
    else
        8
@>    
|> firstPass



<@ 
    [1;2;3]
    |> List.map (fun x -> x + 1)
    |> List.map (fun x -> x - 1)
@>    
|> firstPass