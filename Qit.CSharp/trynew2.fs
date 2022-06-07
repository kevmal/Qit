module Qit.CSharp3.Bleh

open System
open System.Reflection
open System.Runtime.CompilerServices
open FSharp.Quotations
open FSharp.Quotations.Patterns
open FSharp.Quotations.DerivedPatterns
open Qit

open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis
    
let parse (x : string) = CSharpSyntaxTree.ParseText(x).GetRoot().NormalizeWhitespace()
    
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

let languagePrimitivesType() = typedefof<list<_>>.Assembly.GetType("Microsoft.FSharp.Core.LanguagePrimitives")

let (|MakeDecimal|_|) = 
    let minfo1 = languagePrimitivesType().GetNestedType("IntrinsicFunctions").GetMethod("MakeDecimal")
    (fun tm ->
       match tm with
       | Call(None, minfo2, args) when (minfo1.MetadataToken = minfo2.MetadataToken && minfo1 = minfo2) -> Some(args)
       | _ -> None)

let (|NaN|_|) =
    let operatorsType = typedefof<list<_>>.Assembly.GetType("Microsoft.FSharp.Core.Operators")
    let minfo1 = operatorsType.GetProperty("NaN").GetGetMethod()
    (fun e -> 
        match e with
        | Call(None, minfo2, []) when (minfo1.MetadataToken = minfo2.MetadataToken && minfo1 = minfo2) -> Some()
        | _ -> None)
    
let (|NaNSingle|_|) =
    let operatorsType = typedefof<list<_>>.Assembly.GetType("Microsoft.FSharp.Core.Operators")
    let minfo1 = operatorsType.GetProperty("NaNSingle").GetGetMethod()
    (fun e -> 
        match e with
        | Call(None, minfo2, []) when (minfo1.MetadataToken = minfo2.MetadataToken && minfo1 = minfo2) -> Some()
        | _ -> None)
let (|Signed|Unsigned|) x = 
    if x = typeof<sbyte> || x = typeof<int> || x = typeof<int32> || x = typeof<int64> then 
        Signed 
    else 
        Unsigned
let (|TypeOf|_|) = (|SpecificCall|_|) <@ typeof<obj> @>
let (|LessThan|_|) = (|SpecificCall|_|) <@ (<) @>
let (|GreaterThan|_|) = (|SpecificCall|_|) <@ (>) @>
let (|LessThanOrEqual|_|) = (|SpecificCall|_|) <@ (<=) @>
let (|GreaterThanOrEqual|_|) = (|SpecificCall|_|) <@ (>=) @>
let (|Equals|_|) = (|SpecificCall|_|) <@ (=) @>
let (|NotEquals|_|) = (|SpecificCall|_|) <@ (<>) @>
let (|Multiply|_|) = (|SpecificCall|_|) <@ (*) @>
let (|Addition|_|) = (|SpecificCall|_|) <@ (+) @>
let (|Subtraction|_|) = (|SpecificCall|_|) <@ (-) @>
let (|UnaryNegation|_|) = (|SpecificCall|_|) <@ (~-) @>
let (|Division|_|) = (|SpecificCall|_|) <@ (/) @>
let (|UnaryPlus|_|) = (|SpecificCall|_|) <@ (~+) @>
let (|Modulus|_|) = (|SpecificCall|_|) <@ (%) @>
let (|LeftShift|_|) = (|SpecificCall|_|) <@ (<<<) @>
let (|RightShift|_|) = (|SpecificCall|_|) <@ (>>>) @>
let (|And|_|) = (|SpecificCall|_|) <@ (&&&) @>
let (|Or|_|) = (|SpecificCall|_|) <@ (|||) @>
let (|Xor|_|) = (|SpecificCall|_|) <@ (^^^) @>
let (|Not|_|) = (|SpecificCall|_|) <@ (~~~) @>
//let (|Compare|_|) = (|SpecificCall|_|) <@ compare @>
let (|Max|_|) = (|SpecificCall|_|) <@ max @>
let (|Min|_|) = (|SpecificCall|_|) <@ min @>
//let (|Hash|_|) = (|SpecificCall|_|) <@ hash @>
let (|CallString|_|) = (|SpecificCall|_|) <@ string @>
let (|CallByte|_|) = (|SpecificCall|_|) <@ byte @>
let (|CallSByte|_|) = (|SpecificCall|_|) <@ sbyte @>
let (|CallUInt16|_|) = (|SpecificCall|_|) <@ uint16 @>
let (|CallInt16|_|) = (|SpecificCall|_|) <@ int16 @>
let (|CallUInt32|_|) = (|SpecificCall|_|) <@ uint32 @>
let (|CallInt|_|) = (|SpecificCall|_|) <@ int @>
let (|CallInt32|_|) = (|SpecificCall|_|) <@ int32 @>
let (|CallUInt64|_|) = (|SpecificCall|_|) <@ uint64 @>
let (|CallInt64|_|) = (|SpecificCall|_|) <@ int64 @>
let (|CallSingle|_|) = (|SpecificCall|_|) <@ single @>
let (|CallFloat32|_|) = (|SpecificCall|_|) <@ float32 @>
let (|CallDouble|_|) = (|SpecificCall|_|) <@ double @>
let (|CallFloat|_|) = (|SpecificCall|_|) <@ float @>
let (|CallDecimal|_|) = (|SpecificCall|_|) <@ decimal @>
let (|CallChar|_|) = (|SpecificCall|_|) <@ char @>
let (|Ignore|_|) = (|SpecificCall|_|) <@ ignore @>
let (|GetArray|_|) = (|SpecificCall|_|) <@ LanguagePrimitives.IntrinsicFunctions.GetArray @>
let (|GetArray2D|_|) = (|SpecificCall|_|) <@ LanguagePrimitives.IntrinsicFunctions.GetArray2D @>
let (|GetArray3D|_|) = (|SpecificCall|_|) <@ LanguagePrimitives.IntrinsicFunctions.GetArray3D @>
let (|GetArray4D|_|) = (|SpecificCall|_|) <@ LanguagePrimitives.IntrinsicFunctions.GetArray4D @>
let (|Abs|_|) = (|SpecificCall|_|) <@ abs @>
let (|Acos|_|) = (|SpecificCall|_|) <@ acos @>
let (|Asin|_|) = (|SpecificCall|_|) <@ asin @>
let (|Atan|_|) = (|SpecificCall|_|) <@ atan @>
let (|Atan2|_|) = (|SpecificCall|_|) <@ atan2 @>
let (|Ceil|_|) = (|SpecificCall|_|) <@ ceil @>
let (|Exp|_|) = (|SpecificCall|_|) <@ exp @>
let (|Floor|_|) = (|SpecificCall|_|) <@ floor @>
let (|Truncate|_|) = (|SpecificCall|_|) <@ truncate @>
let (|Round|_|) = (|SpecificCall|_|) <@ round @>
let (|Sign|_|) = (|SpecificCall|_|) <@ sign @>
let (|Log|_|) = (|SpecificCall|_|) <@ log @>
let (|Log10|_|) = (|SpecificCall|_|) <@ log10 @>
let (|Sqrt|_|) = (|SpecificCall|_|) <@ sqrt @>
let (|Cos|_|) = (|SpecificCall|_|) <@ cos @>
let (|Cosh|_|) = (|SpecificCall|_|) <@ cosh @>
let (|Sin|_|) = (|SpecificCall|_|) <@ sin @>
let (|Sinh|_|) = (|SpecificCall|_|) <@ sinh @>
let (|Tan|_|) = (|SpecificCall|_|) <@ tan @>
let (|Tanh|_|) = (|SpecificCall|_|) <@ tanh @>
//let (|Range|_|) = (|SpecificCall|_|) <@ (..) @>
//let (|RangeStep|_|) = (|SpecificCall|_|) <@ (.. ..) @>
let (|Pow|_|) = (|SpecificCall|_|) <@ ( ** ) @>
//let (|Pown|_|) = (|SpecificCall|_|) <@ pown @>


let tp (x : Type) = x.Name

let mutable ai = 0
let argName() = 
    ai <- ai + 1
    $"a_{ai}__"
type Binding = 
    {
        Var : Var
        Expr : Expr
    }
let initmut<'a> : 'a = failwith "initmut"
type M = M with 
    static member f<'a>() = <@@ initmut<'a> @@>
let fmeth = typeof<M>.GetMethod("f")
let unchecked (t : Type) = fmeth.MakeGenericMethod(t).Invoke(null,[||]) :?> Expr
//<@ 1 + %%(unchecked typeof<int>) @>
let vr v expr = {Var = v; Expr = expr}
let do_ expr = {Var = Var("_",typeof<unit>); Expr = expr}
let cc x = List.concat x
let letb l body = (l |> List.concat, body) ||> List.foldBack (fun e s -> Expr.Let(e.Var,e.Expr,s))
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
                let e1,cond = f canDef scope cond
                let e2,ifTrue = f canDef scope (Expr.VarSet(v,ifTrue))
                let e3,ifFalse = f canDef scope (Expr.VarSet(v,ifFalse))
                ret [e1;[vr v (unchecked et)];e2;e3] (Expr.IfThenElse(cond,ifTrue,ifFalse))
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
            ret [e] (Expr.VarSet(v,b))
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
            
        | n -> failwithf "unknown expression '%A' in generated method" n
    f true Set.empty e 
    ||> List.foldBack (fun e s -> Expr.Let(e.Var,e.Expr,s))

let secondPass e = 
    let rec traverseQuotation (vs : Map<string,Var>) q = 
        match q with
        | Let(v,e,b) when vs.ContainsKey(v.Name) -> 
            let mutable i = 1
            while vs.ContainsKey($"{v.Name}__{i}") do 
                i <- i + 1
            let v2 = Var($"{v.Name}__{i}",v.Type,v.IsMutable)
            let b = b.Substitute(fun i -> if i = v then Some(Expr.Var v2) else None)
            let vs2 = vs |> Map.add v2.Name v2
            Expr.Let(v2,traverseQuotation vs e, traverseQuotation vs2 b)
        | Let(v,e,b) ->
            let vs2 = vs |> Map.add v.Name v
            Expr.Let(v,traverseQuotation vs e, traverseQuotation vs2 b)
        | ExprShape.ShapeCombination(a, args) -> 
            let nargs = args |> List.map (traverseQuotation vs)
            ExprShape.RebuildShapeCombination(a, nargs)
        | ExprShape.ShapeLambda(v, body)  -> 
            Expr.Lambda(v, traverseQuotation vs body)
        | ExprShape.ShapeVar(v) ->
            Expr.Var(v)
    traverseQuotation Map.empty e
    
type Conv = 
    {
        Lines : string list
    }
    override x.ToString() = 
        match x.Lines with
        | [] -> ""
        | [l] -> l
        | _ -> x.Lines |> String.concat "\r\n" 

let c x = {Lines = [x]}        
let l x = {Lines = x}
let indent l = l |> Seq.map (fun x -> "    " + x)
let convExpr (e : Expr) = 
    let rec f (e : Expr) = 
        match e with 
        | NewArray(elementTy, elements) -> failwithf "New array unhandled %A" e
        | WhileLoop(cond, body) -> 
            let b : Conv = f body
            [
                $"while ({f cond}){{"
                yield! indent b.Lines
                "}"
            ] |> l
        | ForIntegerRangeLoop(loopVar, first, last, body) -> 
            let b : Conv = f body
            //let last = <@ %%last + 1 @>
            [
                $"for(int {loopVar.Name} = {f first}; {loopVar.Name} <= {f last}; i++){{"
                yield! indent b.Lines
                "}"
            ] |> l
        | Var v -> v.Name |> c
        | Coerce (arg, ty) -> $"({tp ty}) {f arg}" |> c
        | TypeOf(None, [t1], []) -> $"typeof({tp t1})" |> c
        | NaN ->  "Double.NaN" |> c
        | NaNSingle -> "Single.NaN" |> c
        | MakeDecimal(args) -> $"{args[0]}m" |> c
        | LessThan(None, [t1], [a1; a2]) -> $"({f a1} < {f a2})" |>c
        | GreaterThan(None, [t1], [a1; a2]) -> $"({f a1} > {f a2})" |>c
        | LessThanOrEqual(None, [t1], [a1; a2]) -> $"({f a1} <= {f a2})" |>c
        | GreaterThanOrEqual(None, [t1], [a1; a2]) -> $"({f a1} >= {f a2})" |>c
        | Equals(None, [t1], [a1; a2]) ->  $"({f a1} == {f a2})" |>c
        | NotEquals(None, [t1], [a1; a2]) ->  $"({f a1} != {f a2})" |>c
        | Multiply(None, [t1; t2; _], [a1; a2]) -> $"({f a1} * {f a2})" |>c
        | Addition(None, [t1; t2; _], [a1; a2]) ->  $"({f a1} + {f a2})" |>c
        | Subtraction(None, [t1; t2; _], [a1; a2]) ->  $"({f a1} - {f a2})" |>c
        | UnaryNegation(None, [t1], [a1]) ->  $"(-{f a1})" |>c
        | Division(None, [t1; t2; _], [a1; a2]) -> $"({f a1} / {f a2})" |>c
        | UnaryPlus(None, [t1], [a1]) ->  $"(+{f a1})" |>c
        | Modulus(None, [t1; t2; _], [a1; a2]) ->  $"({f a1} %% {f a2})" |>c
        | LeftShift(None, [t1], [a1; a2]) ->  $"({a1} << {a2})" |>c
        | RightShift(None, [t1], [a1; a2]) -> $"({a1} >> {a2})" |>c
        | And(None, [t1], [a1; a2]) -> $"({f a1} & {f a2})" |>c
        | Or(None, [t1], [a1; a2]) ->  $"({f a1} | {f a2})" |>c
        | Xor(None, [t1], [a1; a2]) ->  $"({f a1} ^ {f a2})" |>c
        | Not(None, [t1], [a1]) -> $"(not {f a1})" |>c
        | Max(None, [t1], [a1; a2]) -> $"max({f a1}, {f a2})" |>c
        | Min(None, [t1], [a1; a2]) ->  $"min({f a1}, {f a2})" |>c
        | CallString(None, [t1], [a1]) -> $"str({a1})" |>c
        | CallByte(None, [t1], [a1]) -> failwithf "%A" e
        | CallSByte(None, [t1], [a1]) ->  failwithf "%A" e
        | CallUInt16(None, [t1], [a1]) ->  failwithf "%A" e
        | CallInt16(None, [t1], [a1]) ->  failwithf "%A" e
        | CallUInt32(None, [t1], [a1]) ->  failwithf "%A" e
        | CallInt(None, [t1], [a1])
        | CallInt32(None, [t1], [a1]) ->  $"int({f a1})" |>c
        | CallUInt64(None, [t1], [a1]) ->  failwithf "%A" e
        | CallInt64(None, [t1], [a1]) ->  $"int({f a1})" |>c
        | CallSingle(None, [t1], [a1])
        | CallFloat32(None, [t1], [a1]) ->  $"float({f a1})" |>c
        | CallDouble(None, [t1], [a1])
        | CallFloat(None, [t1], [a1]) ->  $"float({f a1})" |>c
        | CallDecimal(None, [t1], [a1]) -> failwithf "%A" e
        | CallChar(None, [t1], [a1]) ->  failwithf "%A" e
        | Ignore(None, [t1], [a1]) ->  "" |>c
        | GetArray(None, [ty], [arr; index]) -> $"{arr}[{f index}]" |>c
        | GetArray2D(None, _ty, arr::indices)
        | GetArray3D(None, _ty, arr::indices)
        | GetArray4D(None, _ty, arr::indices) -> failwithf "%A" e
        | Abs(None, [t1], [a1]) ->  $"Math.Abs({f a1})" |>c
        | Acos(None, [t1], [a1]) -> $"Math.Acos({f a1})" |>c
        | Asin(None, [t1], [a1]) -> $"Math.Asin({f a1})" |>c
        | Atan(None, [t1], [a1]) -> $"Math.Atan({f a1})" |>c
        | Atan2(None, [t1;t2], [a1; a2]) -> $"Math.Atan2({f a1},{f a2})" |>c
        | Ceil(None, [t1], [a1]) -> $"Math.Ceil({f a1})" |>c
        | Exp(None, [t1], [a1]) -> $"Math.Exp({f a1})" |>c
        | Floor(None, [t1], [a1]) -> $"Math.Floor({f a1})" |>c
        | Truncate(None, [t1], [a1]) -> $"Math.Truncate({f a1})" |>c
        | Round(None, [t1], [a1]) -> $"Math.Round({f a1})" |>c
        | Sign(None, [t1], [a1]) -> $"Math.Signum({f a1})" |>c
        | Log(None, [t1], [a1]) -> $"Math.Log({f a1})" |>c
        | Log10(None, [t1], [a1]) -> $"Math.Log10({f a1})" |>c
        | Sqrt(None, [t1; t2], [a1]) -> $"Math.Sqrt({f a1})" |>c
        | Cos(None, [t1], [a1]) -> $"Math.Cos({f a1})" |>c
        | Cosh(None, [t1], [a1]) -> $"Math.Cosh({f a1})" |>c
        | Sin(None, [t1], [a1]) -> $"Math.Sin({f a1})" |>c
        | Sinh(None, [t1], [a1]) -> $"Math.Sinh({f a1})" |>c
        | Tan(None, [t1], [a1]) -> $"Math.Tan({f a1})" |>c
        | Tanh(None, [t1], [a1]) -> $"Math.Tanh({f a1})" |>c
        | Pow(None, [t1; t2], [a1; a2]) -> $"Math.Pow({f a1}, {f a2})"|>c
        | FieldGet (None, field) when field.DeclaringType.IsEnum -> $"{field.DeclaringType.Name}.{field.Name}" |>c
        | FieldGet (Some o, field) -> $"{f o}.{field.Name}" |>c
        | FieldGet (None, field) -> failwithf "%A" e 
        | FieldSet (Some o, field, v) -> $"{f o}.{field.Name} = {f v}" |>c
        | FieldSet (None, field, v) -> failwithf "%A" e
        | PropertyGet(objOpt, meth, args) ->
            if objOpt.IsSome && meth.DeclaringType = typeof<string> then    
                match e with 
                | BindQuote <@ (Quote.withType "o" : string).Length@> _ -> $"{f objOpt.Value}.Length" |>c
                | _ -> failwithf "%A" e
            elif objOpt.IsSome && args.Length = 0 then 
                $"{f objOpt.Value}.{meth.Name}" |>c
            else 
                failwithf "%A" e 
        | Applications (Var v, args) -> 
            let sargs = args |> List.map (List.map f >> string) |> String.concat ", "
            $"{v.Name}({sargs})"|>c
        | Call (objOpt, meth, args) -> 
            if objOpt.IsSome then 
                let comma = ", "
                $"{f objOpt.Value}.{meth.Name}({args |> List.map f})" |>c
            else 
                failwithf "%A" e 
        | DefaultValue (t) -> failwithf "%A" e
        | Value (v, _ty) ->
            match v with
            | :? string as x -> $"'{x}'"
            | :? int8 as x -> string x
            | :? uint8 as x -> string x
            | :? int16 as x -> string x
            | :? uint16 as x -> string x
            | :? int32 as x -> string x
            | :? uint32 as x -> string x
            | :? int64 as x -> string x
            | :? uint64 as x -> string x
            | :? char as x ->  $"'{x}'"
            | :? bool as x -> if x then "True" else "False"
            | :? float32 as x -> string x
            | :? float as x -> string x
            //| :? Enum as x when x.GetType().GetEnumUnderlyingType() = typeof<int32> -> ilg.Emit(mk_ldc (unbox<int32> v))
            | :? Type as ty -> failwithf "Value of type %A" v
            | :? decimal as x -> string x
            //| :? DateTime as x -> $"`{x:O}`"
            //| :? DateTimeOffset as x -> $"`{x:O}`"
            | null -> "null"
            | _ -> failwithf "unknown constant '%A' of type '%O" e (v.GetType())
            |> c
        | TypeTest(e, tgtTy) -> failwithf "%A" e
        | Sequential(e1, e2) -> 
            [
                yield! (f e1).Lines
                yield! (f e2).Lines
            ] |> l
        | IfThenElse(cond, ifTrue, ifFalse) -> 
            if ifTrue.Type = typeof<unit> then 
                let fal = f ifFalse
                l [
                    $"if({f cond}){{"
                    yield! indent (f ifTrue).Lines
                    "}"
                    if ifFalse <> Expr.Value null then 
                        $"else {{"
                        yield! indent (f ifFalse).Lines
                        "}"
                ]
            else 
                $"({f ifTrue} ? {f cond} : {f ifFalse})" |>c
        | TryWith(body, _filterVar, _filterBody, catchVar, catchBody) -> failwithf "%A" e
        | TryFinally(body, finallyBody) -> failwithf "%A" e
        | VarSet(v, Call(None,m,[])) when m.Name = "initmut" -> l []
        | VarSet(v, e) -> $"{v.Name} = {f e}"|>c
        | Let(v, Lambdas(vs,body), b) -> 
            let inArgs = vs |> List.concat |> List.map (fun v -> $"{v.Name}") |> String.concat ", "
            l [
                $"def {v.Name}({inArgs}):"
                yield! indent (f body).Lines
                yield! (f b).Lines
            ]
        | Let(v, Call(None,m,[]), b) when m.Name = "initmut" -> f b
        | Let(v, e, b) when e.Type = typeof<unit> -> f (Expr.Sequential(e,b))
        | Let(v, e, b) -> 
            l [
                $"{v.Name} = {f e};"
                yield! (f b).Lines
            ]
        | Lambdas(vs, body) -> 
            let args = vs |> List.concat |> List.map (fun v -> $"{v.Name}") |> String.concat ", "
            $"{args} => {f body}" |>c
        | NewObject (ctor, args) -> failwithf "%A" e
            //match e with 
            //| BindQuote <@DateTime(Quote.withType "y",Quote.withType "m",Quote.withType "d")@> (Marker "y" (Value(:? int as y,_)) & Marker "m" (Value(:? int as m,_)) & Marker "d" (Value(:? int as d,_))) -> 
            //    $"%04d{y}-%02d{m}-%02d{d}"
            //| _ -> failwithf "%A" e
        | n -> failwithf "unknown expression '%A' in generated method" n
    f e

