namespace Qit.CSharp


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
    open FSharp.Quotations.DerivedPatterns
    open Qit.Quote

    
    let (===) a b = LanguagePrimitives.PhysicalEquality a b

    let traverse f =
        let rec fallback e =
            match e with
            | Let(v, value, body) ->
                let fixedValue = f fallback value
                let fixedBody = f fallback body
                if fixedValue === value && fixedBody === body then
                    e
                else
                    Expr.LetUnchecked(v, fixedValue, fixedBody)
            | ShapeVarUnchecked _ -> e
            | ShapeLambdaUnchecked(v, body) ->
                let fixedBody = f fallback body
                if fixedBody === body then
                    e
                else
                    Expr.Lambda(v, fixedBody)
            | ShapeCombinationUnchecked(shape, exprs) ->
                let exprs1 = List.map (f fallback) exprs
                if List.forall2 (===) exprs exprs1 then
                    e
                else
                    RebuildShapeCombinationUnchecked(shape, exprs1)
        fun e -> f fallback e
    let rightPipe = <@@ (|>) @@>
    let inlineRightPipe expr =
        let rec loop expr = traverse loopCore expr
        and loopCore fallback orig =
            match orig with
            | SpecificCall rightPipe (None, _, [operand; applicable]) ->
                let fixedOperand = loop operand
                match loop applicable with
                | Lambda(arg, body) ->
                    let v = Var("__temp", operand.Type)
                    let ev = Expr.Var v

                    let fixedBody = loop body
                    Expr.Let(v, fixedOperand, fixedBody.Substitute(fun v1 -> if v1 = arg then Some ev else None))
                | fixedApplicable -> Expr.Application(fixedApplicable, fixedOperand)
            | x -> fallback x
        loop expr    
    let inlineRightPipe1 expr =
        expr 
        |> traverseQuotation
            (fun q ->
                match q with 
                | BindQuote <@ (Quote.any "x") |> (Quote.withType "f" : AnyType -> AnyType) @> (Marker "x" x & Marker "f" f) ->
                    Some(Expr.Application(f,x))
                | _ -> None
            )
    let csreturn (x : 'a) : 'a = failwith ""
    let csFakeType () : 'a = failwith ""
    let csreturnignore (x : 'a) : unit = failwith ""
    let csreturnmeth = (methodInfo <@ csreturn @>).GetGenericMethodDefinition()
    let csFakeTypeMeth = (methodInfo <@ csFakeType @>).GetGenericMethodDefinition()
    let csreturnignoremeth = (methodInfo <@ csreturnignore @>).GetGenericMethodDefinition()
    let csReturnExpr (x : Expr) = Expr.Call(csreturnmeth.MakeGenericMethod(x.Type),[x])
    let csFakeTypeExpr (x : Expr) = Expr.Call(csFakeTypeMeth.MakeGenericMethod(x.Type),[])
    let csReturnIgnoreExpr (x : Expr) = Expr.Call(csreturnignoremeth.MakeGenericMethod(x.Type),[x])
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
    let (|CsReturn|_|) = (|SpecificCall|_|) <@ csreturn @>
    let (|CsFakeType|_|) = (|SpecificCall|_|) <@ csFakeType @>
    let (|CsReturnIgnore|_|) = (|SpecificCall|_|) <@ csreturnignore @>
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
    let (|BoolAnd|_|) = (|SpecificCall|_|) <@ (&&) @>
    let (|BoolOr|_|) = (|SpecificCall|_|) <@ (||) @>
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
    let rec typeStr (t : Type) = 
        if t.IsGenericType then 
            let targs = t.GetGenericArguments() |> Array.map typeStr
            let name =
                let name = t.FullName
                let i = name.IndexOf "`"
                name.Substring(0,i)
            sprintf "%s<%s>" name (targs |> String.concat ", ")
        else
            t.FullName
    
    let (|SeqMap|_|) = (|SpecificCall|_|) <@ Seq.map @>
    let select0<'a,'b> f a = <@@ System.Linq.Enumerable.Select(%%a,Func<'a,'b>(%%f)) @@>
    let select = TypeTemplate.create select0
    let orderBy0<'e,'k> f a = <@@ System.Linq.Enumerable.OrderBy(%%a,Func<'e,'k>(%%f)) :> 'e seq @@>
    let orderBy = TypeTemplate.create orderBy0
    let (|SeqSort|_|) = (|SpecificCall|_|) <@ Seq.sort @>
    let (|SeqSum|_|) =
        let x = (methodInfo <@ Seq.map @>).DeclaringType.GetMethod("Sum").GetGenericMethodDefinition()
        fun e -> 
            match e with 
            | Patterns.Call(None,minfo,[a]) when minfo.IsGenericMethod && minfo.GetGenericMethodDefinition() = x -> 
                Some (minfo.GetGenericArguments().[0],a)
            | _ -> None
    let sum0<'a> a = 
        let minfo = typeof<System.Linq.Enumerable>.GetMethod("Sum",[|typeof<'a seq>|])
        Expr.Call(minfo, [a])
    let sum = TypeTemplate.create sum0
    let rewriteSeqToLinq x =
        let rec loop x = 
            x
            |> traverseQuotation
                (fun q ->
                    match q with 
                    | SeqMap (None, [t1;t2], [a1; a2]) -> select [t1;t2] a1 a2 |> Some
                    | SeqSum (t1,a1) -> sum [t1] a1 |> Some
                    | BindQuote <@ Array.length (Quote.withType "a" : AnyType []) @> (Marker "a" a) -> 
                        Some(Expr.PropertyGet(a,a.Type.GetProperty("Length")))
                    | BindQuote <@ Seq.singleton (Quote.any "e") @> (Marker "e" e) -> 
                        let m = (methodInfo <@ System.Linq.Enumerable.Repeat @>).GetGenericMethodDefinition().MakeGenericMethod(e.Type)
                        Some(Expr.Call(m,[e;<@ 1 @>]))
                    | BindQuote <@ Seq.toArray (Quote.withType "e" : AnyType seq) @> (Marker "e" e) -> 
                        let m = (methodInfo <@ System.Linq.Enumerable.ToArray @>).GetGenericMethodDefinition().MakeGenericMethod(e.Type.GetGenericArguments().[0])
                        Some(Expr.Call(m,[e]))
                    | BindQuote <@ Seq.init (Quote.withType "c") (Quote.withType "e" : int -> AnyType) @> (Marker "e" e & Marker "c" c) -> 
                        let rangeMethod = (methodInfo <@ System.Linq.Enumerable.Range @>)
                        let range = Expr.Call(rangeMethod,[ <@@ 0 @@>; c])
                        let _domain,rg = FSharp.Reflection.FSharpType.GetFunctionElements(e.Type)
                        select [typeof<int>; rg] e range |> Some
                    | SeqSort (None, [t], [e]) ->
                        let v = Var("x",t)
                        let f = Expr.Lambda(v,Expr.Var v)
                        Some(orderBy [t;t] f e)
                    | _ -> None
                )
        loop x
    module Rw = 

        let tp (x : Type) = (typeStr x).Replace("+",",.")
            
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
                let (|NC|) x = f true scope x
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
                | WhileLoop(NS(e,cond), NC(e2,body)) -> ret [e] (Expr.WhileLoop(cond, letb [e2] body))
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
                    ret e (Expr.Call(o,meth,b)) (*
                | Applications(func,args) ->  
                    let eb = args |> List.map (fun i -> i |> List.map (f false scope)) 
                    let e = eb |> List.concat |> List.map fst
                    let b = eb |> List.map (fun i -> i |> List.map snd)
                    let vv = Var("appLambda", func.Type)
                    let e2,func = f canDef scope func
                    ret [yield! e;e2;[{Var = vv; Expr = func}]] (Expr.Applications(Expr.Var(vv),b)) *)
                | NewTuple(args) -> 
                    let e,b = args |> List.map (f false scope) |> List.unzip
                    ret e (Expr.NewTuple(b))
                | NewObject(cinfo,args) ->
                    let e,b = args |> List.map (f false scope) |> List.unzip
                    ret e (Expr.NewObject(cinfo,b))
                | Applications(func,args) ->  
                    let eb = args |> List.map (fun i -> i |> List.map (f false scope)) 
                    let e = eb |> List.concat |> List.map fst
                    let b = eb |> List.map (fun i -> i |> List.map snd)
                    let e2,func = f false scope func
                    ret [yield! e;e2] (Expr.Applications(func, b))
                | DefaultValue (t) -> [],e
                | Value (v, _ty) -> [],e
                | Sequential(NI(e1,b1), NI(e2,b2)) -> ret [e1;e2] (Expr.Sequential(b1,b2))
                | IfThenElse(cond, ifTrue, ifFalse) -> 
                    let et = e.Type
                    if et = typeof<unit> then 
                        let e1,cond = f false scope cond
                        let e2,ifTrue = f true scope ifTrue
                        let e3,ifFalse = f true scope ifFalse
                        ret [e1;e2;e3] (Expr.IfThenElse(cond,ifTrue,ifFalse))
                    else 
                        let v = Var(argName(), et, true)
                        let e1,cond = f false scope cond
                        let e2,ifTrue = f canDef scope (Expr.VarSet(v,ifTrue))
                        let e3,ifFalse = f canDef scope (Expr.VarSet(v,ifFalse))
                        ret [e1;[vr v (unchecked et)];e2;e3] (Expr.Sequential(Expr.IfThenElse(cond,ifTrue,ifFalse), Expr.Var v))
                | TryWith(body, _filterVar, _filterBody, catchVar, catchBody) -> failwithf "%A" e
                | TryFinally(body, finallyBody) -> failwithf "%A" e
                | TupleGet(NI(e1,b1),i) -> ret [e1] (Expr.TupleGet(b1,i))
                | VarSet(v, ((Let _ | Sequential _ | IfThenElse _) as e)) -> 
                    //printfn "--- %A -----" v.Name
                    //printfn "%A" e
                    //printfn "-----"
                    let e = insertVarSet v e
                    //printfn "%A" e
                    f canDef scope e
                | VarSet(v, NS(e,b)) -> 
                    ret [e; [doe(Expr.VarSet(v,b))]] nop
                | Let(v, Lambdas(vs,body), b) -> 
                    let scope2 = vs |> List.concat |> Set.ofList |> Set.union scope
                    let e00,b00 = f true scope2 body
                    //printfn "%A" b00
                    if canDef then 
                        let e1,b1 = f true scope b
                        ret [e00;e1] (Expr.Let(v, lambdas(vs,b00), b1)) 
                    else 
                        let e0 = [{ Var = v; Expr = lambdas(vs,b00)}]
                        let e1,b1 = f false scope b
                        ret [e00;e0;e1] b1
                | Lambdas(vs, body) -> 
                    let v = Var(argName(), e.Type)
                    let e1,bb = f canDef scope (Expr.Let(v,e,<@@ () @@>))
                    ret [e1;[doe bb]] (Expr.Var v)
                | NewDelegate(t,vs,NC(e2,body)) -> ret [] (Expr.NewDelegate(t,vs, letb [e2] body))
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
                | LetRecursive([v, Lambdas(vs,body)],rest) -> 
                    let scope2 = vs |> List.concat |> Set.ofList |> Set.union scope
                    let e00,b00 = f true scope2 body
                    //printfn "%A" b00
                    if canDef then 
                        let e1,b1 = f true scope rest
                        ret [e00;e1] (Expr.LetRecursive([v, lambdas(vs,b00)], b1)) 
                    else 
                        let e0 = [{ Var = v; Expr = lambdas(vs,b00)}]
                        let e1,b1 = f false scope rest
                        ret [e00;e0;e1] b1
                //| LetRecursive(l,b) -> 
                    
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
            |> traverseQuotation
                (fun e -> 
                    match e with 
                    | Patterns.Sequential(e,Patterns.Value(null,_))
                    | Patterns.Sequential(Patterns.Value(null,_),e) -> 
                        Some e
                    | _ -> None
                )   
    module Crap = 
        open UncheckedQuotations
        open Qit

        let checkTailCall v expr = true


        let rec rewriteTailCallToWhile expr = 
            let reduceOr v f xs = 
                if Seq.isEmpty xs then 
                    v
                else 
                    xs |> Seq.reduce f
            expr 
            |> traverseQuotation
                (fun q ->
                    match q with 
                    | LetRecursive([v, Lambdas(vs,body)],rest) when checkTailCall v body -> 
                        let vs2 = vs |> Seq.concat |> Seq.map (fun x -> Var(x.Name, x.Type, true)) |> Seq.toArray
                        let body = (body,Seq.zip vs2 (vs |> Seq.concat)) ||> Seq.fold (fun s (v,p) -> s |> Quote.replaceVar p (Expr.Var v))
                        let rec loop i = 
                            match i with 
                            | Sequential(e1,e2) -> Expr.Sequential(e1, loop e2)
                            | Let(v,e1,e2) -> Expr.Let(v,e1,loop e2)
                            | IfThenElse(c,e1,e2) -> 
                                let t = loop e1
                                let f = loop e2
                                Expr.IfThenElse(c,t,f)
                            | Applications(Var v0, args) when v0 = v -> 
                                if vs2.Length > 0 then 
                                    (vs2,args |> Seq.concat) 
                                    ||> Seq.map2 
                                        (fun v e -> 
                                            match e with 
                                            | Var v2 when v = v2 -> None 
                                            | _ -> Some(Expr.VarSet(v,e)))
                                    |> Seq.choose id
                                    |> reduceOr <@@ () @@> (fun a b -> Expr.Sequential(a,b))
                                else 
                                    <@@ () @@>
                            | q when q.Type <> typeof<unit> -> csReturnIgnoreExpr q
                        let newBody = loop body
                        let whl = Expr.Sequential(Expr.WhileLoop(<@@ true @@>, newBody), csFakeTypeExpr body)
                        if vs2.Length > 0 then 
                            let whl = (Seq.zip vs2 (vs |> Seq.concat),whl) ||> Seq.foldBack (fun (v,p) s -> Expr.Let(v,Expr.Var p,s))
                            //let init = (vs2,vs |> Seq.concat) ||> Seq.map2 (fun v e -> Expr.VarSet(v,Expr.Var e)) |> Seq.reduce (fun a b -> Expr.Sequential(a,b))
                            Some(Expr.Let(v, Rw.lambdas(vs,whl), rewriteTailCallToWhile rest))
                        else 
                            Some(Expr.Let(v, Rw.lambdas(vs,whl), rewriteTailCallToWhile rest))
                    | _ -> None
                )
            
        let simple expr = 
            expr 
            |> traverseQuotation
                (fun q ->
                    match q with 
                    | Application(Lambda(v,b),a) -> Expr.Let(v,a,b) |> Some
                    | _ -> None
                )
        let checkSingleLine expr = 
            let rec traverseQuotation q = 
                match q with
                | Sequential(e1,e2) -> false
                | Let(v,e1,e2) -> false
                | ForIntegerRangeLoop _ -> false
                | WhileLoop _ -> false
                | ShapeCombinationUnchecked(a, args) -> 
                    args |> List.forall traverseQuotation
                | ShapeLambdaUnchecked(v, body) -> false
                | ShapeVarUnchecked(v) -> true
            traverseQuotation expr
            
        let rewriteCond expr =
            expr 
            |> traverseQuotation 
                (fun e ->
                    match e with 
                    | Patterns.IfThenElse(c,t,f) when e.Type = typeof<bool> && checkSingleLine e -> 
                        let rec loop e = 
                            e 
                            |> traverseQuotation
                                (fun q ->
                                    match q with 
                                    | Patterns.IfThenElse(c,Patterns.Value((:? bool as tv),_),Patterns.Value((:? bool as fv),_)) when tv && not fv -> Some c
                                    | Patterns.IfThenElse(c,Patterns.Value((:? bool as tv),_),Patterns.Value((:? bool as fv),_)) when not tv && fv -> Some <@@ not %%c @@>
                                    | Patterns.IfThenElse(c,Patterns.Value((:? bool as tv),_),f) when tv ->
                                        Some(Expr.Call(Quote.methodInfo <@ (||) @>,[loop c; loop f]))
                                    | Patterns.IfThenElse(c,Patterns.Value((:? bool as tv),_),f) when not tv ->
                                        Some(Expr.Call(Quote.methodInfo <@ (&&) @>,[loop c; loop f]))
                                    | Patterns.IfThenElse(c,t,Patterns.Value((:? bool as fv),_)) when not fv ->
                                        Some(Expr.Call(Quote.methodInfo <@ (&&) @>,[loop c; loop t]))
                                    | Patterns.IfThenElse(c,t,f) ->
                                        let e1 = Expr.Call(Quote.methodInfo <@ (&&) @>,[loop c; loop t])
                                        Some(Expr.Call(Quote.methodInfo <@ (||) @>,[e1; loop f]))
                                    | _ -> None
                                )
                        loop e |> Some
                    | _ -> None
                )
                
        let rewriteReturn expr = 
            let expr = simple expr
            let rec traverseQuotation f q = 
                match f q with 
                | None ->
                    match q with
                    | Sequential(e1,e2) -> Expr.Sequential(e1, traverseQuotation f e2)
                    | Let(v,e1,e2) -> Expr.Let(v,e1,traverseQuotation f e2)
                    | IfThenElse(c,e1,e2) -> Expr.IfThenElse(c,traverseQuotation f e1, traverseQuotation f e2)
                    | ShapeCombinationUnchecked(a, args) -> 
                        let nargs = args //|> List.map (traverseQuotation f)
                        RebuildShapeCombinationUnchecked(a, nargs)
                    | ShapeLambdaUnchecked(v, body) -> Expr.Lambda(v, traverseQuotation f body)
                    | ShapeVarUnchecked(v) -> Expr.Var(v)
                | Some q -> q
            //printfn "%A" expr
            let mutable changeFlag = false
            let newExpr = 
                expr 
                |> traverseQuotation
                    (fun q ->
                        match q with 
                        | Value _ 
                        | AddressOf _
                        | Call _
                        | Application _
                        | Coerce _
                        | DefaultValue _
                        | FieldGet _
                        | PropertyGet _
                        | Var _
                        | TupleGet _ ->
                            //printfn "%A" q
                            changeFlag <- true
                            Some(csReturnExpr q)
                        | _ ->  
                            None
                    )
            if changeFlag then 
                Some newExpr 
            else
                None
        let rewriteReturnOnLambda expr =
            expr
            |> traverseQuotation
                (fun x ->
                    match x with 
                    | Lambdas(v,b) ->
                        let b = rewriteReturn b |> Option.defaultValue b
                        Some(Rw.lambdas(v, b))
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
            //printfn "%A" expr
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
                            //printfn "%A" q
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
            match expr with
            | Patterns.LetRecursive(l, body) -> 
                let vs = 
                    [|
                        for v,_ in l do 
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
                                Var(newName,v.Type,v.IsMutable)
                            else
                                v
                    |]
                let ovs = l |> List.map fst |> List.toArray
                let sub (e : Expr) = 
                    let mutable e = e
                    for i = 0 to vs.Length - 1 do 
                        e <- e.Substitute(fun v2 -> if v2 = ovs.[i] then Some (Expr.Var vs.[i]) else None)
                    e
                let vars = vars |> Set.union (vs |> Seq.map (fun i -> i.Name) |> Set.ofSeq)
                let l = 
                    l
                    |> List.mapi
                        (fun i (v,e) -> 
                            vs.[i],sub e
                        )
                let l = l |> List.map (fun (v,e) -> v, expand vars e)
                let body = sub body |> expand vars
                Expr.LetRecursive(l,body)
            | Patterns.Lambda(v, body) -> 
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
                    let body = body.Substitute(fun v2 -> if v = v2 then Some (Expr.Var newVar) else None)
                    Expr.Lambda(newVar,expand (Set.add newName vars) body)
                else
                    Expr.Lambda(v,expand (Set.add v.Name vars) body)
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
                    let body = body.Substitute(fun v2 -> if v = v2 then Some (Expr.Var newVar) else None)
                    Expr.Let(newVar,expand vars assign,expand (Set.add newName vars) body)
                else
                    Expr.Let(v,expand vars assign,expand (Set.add v.Name vars) body)
            | ExprShape.ShapeVar v -> Expr.Var v
            | ExprShape.ShapeLambda(v, expr) -> 
              Expr.Lambda(v, expand vars expr)
            | ExprShape.ShapeCombination(o, exprs) ->
              let fuck = List.map (expand vars) exprs
              let e = ExprShape.RebuildShapeCombination(o, fuck)
              e
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
        let e = q
        //printfn "22222222222222222222222222222222222222222222222222222222"
        //printfn "%A" q
        //printfn "22222222222222222222222222222222222222222222222222222222"
        match q with
        | AddressOf(expr) -> SyntaxFactory.PrefixUnaryExpression(SyntaxKind.AddressOfExpression, ex expr :?> _) :> _
        | AddressSet(expr1, expr2) ->  failwithf "AddressSet(%A, %A)" expr1 expr2
        | Applications(Var(v), args) ->
            let ns = 
                let f x = 
                    match x with 
                    | [v:Expr] -> exs v
                    | l -> sprintf "(%s)" (String.concat "," (l |> List.map exs))
                args |> List.map f |> String.concat ","
            $"{v.Name}({ns})" |> parse
        | Applications(f, args) ->
            let ns = 
                let f x = 
                    match x with 
                    | [v:Expr] -> exs v
                    | l -> sprintf "(%s)" (String.concat "," (l |> List.map exs))
                args |> List.map f |> String.concat ","
            $"{exs f}({ns})" |> parse
        | Application(Lambda(v,expr2), expr1) ->
            let e = Expr.Let(v,expr1,expr2)
            ex e
        | CsFakeType(None,[t1],[]) -> ";" |> parse
        | CsReturn(None,[t1],[CsFakeType(None,[t2],[])]) -> $";" |> parse
        | CsReturn(None,[t1],[e]) -> $"return {exs e};" |> parse
        | CsReturnIgnore(None,[t1],[e]) -> $"return {exs e};" |> parse
        | TypeOf(None,[], [e]) ->  $"typeof({exs e})" |> parse
        | NaN ->  "Double.NaN" |> parse
        | NaNSingle -> "Single.NaN" |> parse
        | MakeDecimal(args) -> $"{args[0]}m" |> parse
        | BoolAnd(None, [], [a1; a2]) -> $"({exs a1} && {exs a2})" |> parse
        | BoolOr(None, [], [a1; a2]) -> $"({exs a1} || {exs a2})" |> parse
        | LessThan(None, [t1], [a1; a2]) -> $"({exs a1} < {exs a2})" |> parse
        | GreaterThan(None, [t1], [a1; a2]) -> $"({exs a1} > {exs a2})" |> parse
        | LessThanOrEqual(None, [t1], [a1; a2]) -> $"({exs a1} <= {exs a2})" |> parse
        | GreaterThanOrEqual(None, [t1], [a1; a2]) -> $"({exs a1} >= {exs a2})" |> parse
        | Equals(None, [t1], [a1; a2]) ->  $"({exs a1} == {exs a2})" |> parse
        | NotEquals(None, [t1], [a1; a2]) ->  $"({exs a1} != {exs a2})" |> parse
        | Multiply(None, [t1; t2; _], [a1; a2]) -> $"({exs a1} * {exs a2})" |> parse
        | Addition(None, [t1; t2; _], [a1; a2]) ->  $"({exs a1} + {exs a2})" |> parse
        | Subtraction(None, [t1; t2; _], [a1; a2]) ->  $"({exs a1} - {exs a2})" |> parse
        | UnaryNegation(None, [t1], [a1]) ->  $"(-{exs a1})" |> parse
        | Division(None, [t1; t2; _], [a1; a2]) -> $"({exs a1} / {exs a2})" |> parse
        | UnaryPlus(None, [t1], [a1]) ->  $"(+{exs a1})" |> parse
        | Modulus(None, [t1; t2; _], [a1; a2]) ->  $"({exs a1} %% {exs a2})" |> parse
        | LeftShift(None, [t1], [a1; a2]) ->  $"({a1} << {a2})" |> parse
        | RightShift(None, [t1], [a1; a2]) -> $"({a1} >> {a2})" |> parse
        | And(None, [t1], [a1; a2]) -> $"({exs a1} & {exs a2})" |> parse
        | Or(None, [t1], [a1; a2]) ->  $"({exs a1} | {exs a2})" |> parse
        | Xor(None, [t1], [a1; a2]) ->  $"({exs a1} ^ {exs a2})" |> parse
        | Not(None, [t1], [a1]) -> $"(!{exs a1})" |> parse
        | Max(None, [t1], [a1; a2]) -> $"Math.Max({exs a1}, {exs a2})" |> parse
        | Min(None, [t1], [a1; a2]) ->  $"Math.Min({exs a1}, {exs a2})" |> parse
        | CallString(None, [t1], [a1]) -> $"(({exs a1}).ToString())" |> parse
        | CallByte(None, [t1], [a1]) -> failwithf "%A" e
        | CallSByte(None, [t1], [a1]) ->  failwithf "%A" e
        | CallUInt16(None, [t1], [a1]) ->  failwithf "%A" e
        | CallInt16(None, [t1], [a1]) ->  failwithf "%A" e
        | CallUInt32(None, [t1], [a1])  when t1 = typeof<string> ->  $"System.UInt32.Parse({exs a1})" |> parse
        | CallUInt32(None, [t1], [a1]) ->  $"(uint){exs a1}" |> parse
        | CallInt(None, [t1], [a1])
        | CallInt32(None, [t1], [a1]) when t1 = typeof<string> ->  $"System.Int32.Parse({exs a1})" |> parse
        | CallInt(None, [t1], [a1])
        | CallInt32(None, [t1], [a1]) ->  $"(int){exs a1}" |> parse
        | CallUInt64(None, [t1], [a1]) ->  failwithf "%A" e
        | CallInt64(None, [t1], [a1]) when t1 = typeof<string> ->  $"System.Int64.Parse({exs a1})" |> parse
        | CallInt64(None, [t1], [a1]) ->  $"(Int64){exs a1}" |> parse
        | CallSingle(None, [t1], [a1])
        | CallFloat32(None, [t1], [a1]) ->  $"float({exs a1})" |> parse
        | CallDouble(None, [t1], [a1])
        | CallFloat(None, [t1], [a1]) ->  $"float({exs a1})" |> parse
        | CallDecimal(None, [t1], [a1]) -> failwithf "%A" e
        | CallChar(None, [t1], [a1]) ->  failwithf "%A" e
        | Ignore(None, [t1], [a1]) ->  $"{exs a1};" |> parse
        | GetArray(None, [ty], [arr; index]) -> $"{arr}[{exs index}]" |> parse
        | GetArray2D(None, _ty, arr::indices)
        | GetArray3D(None, _ty, arr::indices)
        | GetArray4D(None, _ty, arr::indices) -> failwithf "%A" e
        | Abs(None, [t1], [a1]) ->  $"Math.Abs({exs a1})" |> parse
        | Acos(None, [t1], [a1]) -> $"Math.Acos({exs a1})" |> parse
        | Asin(None, [t1], [a1]) -> $"Math.Asin({exs a1})" |> parse
        | Atan(None, [t1], [a1]) -> $"Math.Atan({exs a1})" |> parse
        | Atan2(None, [t1;t2], [a1; a2]) -> $"Math.Atan2({exs a1},{exs a2})" |> parse
        | Ceil(None, [t1], [a1]) -> $"Math.Ceil({exs a1})" |> parse
        | Exp(None, [t1], [a1]) -> $"Math.Exp({exs a1})" |> parse
        | Floor(None, [t1], [a1]) -> $"Math.Floor({exs a1})" |> parse
        | Truncate(None, [t1], [a1]) -> $"Math.Truncate({exs a1})" |> parse
        | Round(None, [t1], [a1]) -> $"Math.Round({exs a1})" |> parse
        | Sign(None, [t1], [a1]) -> $"Math.Signum({exs a1})" |> parse
        | Log(None, [t1], [a1]) -> $"Math.Log({exs a1})" |> parse
        | Log10(None, [t1], [a1]) -> $"Math.Log10({exs a1})" |> parse
        | Sqrt(None, [t1; t2], [a1]) -> $"Math.Sqrt({exs a1})" |> parse
        | Cos(None, [t1], [a1]) -> $"Math.Cos({exs a1})" |> parse
        | Cosh(None, [t1], [a1]) -> $"Math.Cosh({exs a1})" |> parse
        | Sin(None, [t1], [a1]) -> $"Math.Sin({exs a1})" |> parse
        | Sinh(None, [t1], [a1]) -> $"Math.Sinh({exs a1})" |> parse
        | Tan(None, [t1], [a1]) -> $"Math.Tan({exs a1})" |> parse
        | Tanh(None, [t1], [a1]) -> $"Math.Tanh({exs a1})" |> parse
        | Pow(None, [t1; t2], [a1; a2]) -> $"Math.Pow({exs a1}, {exs a2})"|> parse
        | Op <@@ "".[0] @@> (a,b) -> sprintf "%s[%s]" (exs a) (exs b) |> parse
        | Op <@@ Array.empty.[0] @@> (a,b) -> sprintf "%s[%s]" (exs a) (exs b) |> parse
        | Cl <@@ Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions.SetArray @@> (args) 
          & Call(None, methodInfo, exprList) -> 
            sprintf "%s[%s] = %s;" (exs args.[0]) (exs args.[1]) (exs args.[2]) |> parse
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
            printfn "%A" (expr1, expr2, expr3)
            printfn "----- %A" (exs expr2)
            match expr1 with
            | Sequential(e1, e2) -> 
                let iff = Expr.IfThenElse(e2,expr2,expr3)
                sprintf "%s; %s;" (exs e1) (exs iff) |> parse
            | _ -> 
                if expr2.Type = typeof<unit> && expr3 = <@@()@@> then 
                    sprintf "if(%s) {%s}" (exs expr1) (exs expr2)  |> parse
                else
                    sprintf "if(%s) {%s} else {%s}" (exs expr1) (exs expr2) (exs expr3) |> parse
        | Lambdas(vars, expr) -> 
            let tp = 
                let f x = 
                    match x with 
                    | [v:Var] -> typeStr v.Type
                    | l -> sprintf "(%s)" (String.concat "," (l |> List.map (fun i -> typeStr i.Type)))
                vars |> List.map f |> String.concat ","
            let ns = 
                let f x = 
                    match x with 
                    | [v:Var] -> v.Name
                    | l -> sprintf "(%s)" (String.concat "," (l |> List.map (fun i -> i.Name)))
                vars |> List.map f |> String.concat ","
            let rt = 
                let rec loop t =
                    if FSharp.Reflection.FSharpType.IsFunction t then 
                        FSharp.Reflection.FSharpType.GetFunctionElements(t) |> snd |> loop
                    else t
                loop q.Type
            if rt = typeof<unit> then 
                sprintf $"(({ns}) => {{{exs expr}}})" |> parse
            else
                let expr = 
                    match rewriteReturn expr with 
                    | Some x -> x
                    | None -> expr
                sprintf $"(({ns}) => {{{exs expr}}})" |> parse
            //sprintf "((%s %s) => {%s})" (typeStr var1.Type) var1.Name (exs expr) |> parse
        | Lambda(var1, expr) -> 
            sprintf "((%s %s) => {%s})" (typeStr var1.Type) var1.Name (exs expr) |> parse
        | LetRecursive([v,(Lambdas(vs,body) as lam)], rest) -> ex(Expr.Let(v,lam,rest))
        | LetRecursive(varExprList, expr) -> failwith "let rec"
        //| Let(var, Lambda(v,b), expr2) -> 
        | Let(var, Lambdas([[v]], expr), expr2) when v.Type = typeof<unit> -> 
            let rt = 
                let rec loop t =
                    if FSharp.Reflection.FSharpType.IsFunction t then 
                        FSharp.Reflection.FSharpType.GetFunctionElements(t) |> snd |> loop
                    else t
                loop var.Type
            if rt = typeof<unit> then 
                sprintf $"System.Action {var.Name} = (() => {{{exs expr}}}); {exs expr2};" |> parse
            else
                let expr = 
                    match rewriteReturn expr with 
                    | Some x -> x
                    | None -> expr
                sprintf $"System.Func<{typeStr rt}> {var.Name} = (() => {{{exs expr}}}); {exs expr2};" |> parse
        | Let(var, Lambdas(vars, expr), expr2) -> 
            let tp = 
                let f x = 
                    match x with 
                    | [v:Var] -> typeStr v.Type
                    | l -> sprintf "(%s)" (String.concat "," (l |> List.map (fun i -> typeStr i.Type)))
                vars |> List.map f |> String.concat ","
            let ns = 
                let f x = 
                    match x with 
                    | [v:Var] -> v.Name
                    | l -> sprintf "(%s)" (String.concat "," (l |> List.map (fun i -> i.Name)))
                vars |> List.map f |> String.concat ","
            let rt = 
                let rec loop t =
                    if FSharp.Reflection.FSharpType.IsFunction t then 
                        FSharp.Reflection.FSharpType.GetFunctionElements(t) |> snd |> loop
                    else t
                loop var.Type
            if rt = typeof<unit> then 
                sprintf $"System.Action<{tp}> {var.Name} = (({ns}) => {{{exs expr}}}); {exs expr2};" |> parse
            else
                let expr = 
                    match rewriteReturn expr with 
                    | Some x -> x
                    | None -> expr
                sprintf $"System.Func<{tp},{typeStr rt}> {var.Name} = (({ns}) => {{{exs expr}}}); {exs expr2};" |> parse
        | Let(var, BindQuote <@@ Rw.initmut<AnyType> @@> _, expr2) ->
                sprintf "%s %s; %s;" (typeStr var.Type) var.Name (exs expr2) |> parse
        | Let(var, expr1, expr2) -> sprintf "%s %s = %s; %s;" (typeStr var.Type) var.Name (exs expr1) (exs expr2) |> parse
            //sprintf "var %s = %s; %s;" var.Name (exs x) (exs expr2) |> parse
        | NewArray(type1, exprList) -> 
            sprintf "new[] {%s}" (exprList |> List.map exs |> String.concat  ",") |> parse
        | NewDelegate(type1, vars, expr) -> 
            let tp = 
                vars |> List.map (fun x -> typeStr x.Type) |> String.concat ","
            let ns = vars |> List.map (fun x -> x.Name) |> String.concat ","
            let rt = 
                let rec loop t =
                    if FSharp.Reflection.FSharpType.IsFunction t then 
                        FSharp.Reflection.FSharpType.GetFunctionElements(t) |> snd |> loop
                    else t
                loop q.Type
            if rt = typeof<unit> then 
                sprintf $"(({ns}) => {{{exs expr}}})" |> parse
            else
                let expr = 
                    match rewriteReturn expr with 
                    | Some x -> x
                    | None -> expr
                sprintf $"(({ns}) => {{{exs expr}}})" |> parse
        | NewDelegate(type1, varList, expr) -> failwithf "NewDelegate(type1, varList, expr) %A" q
        | NewObject(constructorInfo, exprList) -> 
            sprintf "new %s(%s)" (typeStr constructorInfo.DeclaringType) (exprList |> Seq.map exs |> String.concat ", ") |> parse
        | NewRecord(type1, exprList) -> failwith "NewRecord(type1, exprList)"
        | NewTuple(exprList) -> 
            let tps = exprList |> List.map (fun x -> typeStr x.Type) |> String.concat ","
            exprList |> List.map exs |> String.concat "," |> sprintf "new System.Tuple<%s>(%s)" tps |> parse
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
        | TryFinally(expr1, expr2) -> $"try {{{exs expr1}}} finally {{{exs expr2}}}" |> parse
        | TryWith(expr1, var1, expr2, var2, expr3) -> failwith "TryWith(expr1, var1, expr2, var2, expr3)"
        | TupleGet(expr, int1) -> $"{exs expr}.Item{int1+1}" |> parse
        | TypeTest(expr, type1) -> $"{expr} is {typeStr type1}" |> parse
        | UnionCaseTest(expr, unionCaseInfo) -> failwith "UnionCaseTest(expr, unionCaseInfo)"
        //| ValueWithName(obj1, type1, name) when List.contains name vs -> name
        | Value (v, _ty) ->
            match v with
            | :? string as x -> $"\"{x}\""
            | :? int8 as x -> string x
            | :? uint8 as x -> string x
            | :? int16 as x -> string x
            | :? uint16 as x -> string x
            | :? int32 as x -> string x
            | :? uint32 as x -> string x
            | :? int64 as x -> string x
            | :? uint64 as x -> string x
            | :? char as x ->  $"'{x}'"
            | :? bool as x -> if x then "true" else "false"
            | :? float32 as x -> string x
            | :? float as x -> string x
            //| :? Enum as x when x.GetType().GetEnumUnderlyingType() = typeof<int32> -> ilg.Emit(mk_ldc (unbox<int32> v))
            | :? Type as ty -> failwithf "Value of type %A" v
            | :? decimal as x -> string x
            //| :? DateTime as x -> $"`{x:O}`"
            //| :? DateTimeOffset as x -> $"`{x:O}`"
            | null -> "null"
            | _ -> failwithf "unknown constant '%A' of type '%O" e (v.GetType())
            |> parse
        | VarSet(var, expr)  as qq -> sprintf "%s = %s;" var.Name (exs expr) |> parse (*
            //printfn "hi"
            let qq2 = rewriteAss var expr
            //sprintf "%s = %s;" var.Name (exs expr) |> parse
            match qq2 with
            | None -> sprintf "%s = %s;" var.Name (exs expr) |> parse
            | Some qq2 -> 
                //printfn "%A <> %A" qq qq2
                qq2 |> ex*)
        | Var(var) -> sprintf "%s" var.Name  |> parse
        | WhileLoop(expr1, expr2) -> 
            sprintf "while(%s) {%s}" (exs expr1) (exs expr2) |> parse
        | Applications(expr1, exprList) -> 
            let f x = 
                match x with 
                | [e] -> exs e
                | l -> sprintf "(%s)" (l |> List.map exs |> String.concat ", ")
            sprintf "%s(%s)" (exs expr1) (exprList |> Seq.map f |> String.concat ", ") |> parse
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

open Internal.Crap

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
    let rewriteShadowing a = rewriteShadowing a
    let rewriteConditionals a = rewriteCond a
    let toCSharpString (q : Expr) = 
        (ex q).NormalizeWhitespace().ToFullString() 
    let toFormattedCSharpString (q : Expr) = 
        use cw = new AdhocWorkspace()
        let format x  = Formatting.Formatter.Format(x,cw)
        C().Visit(ex q |> format).NormalizeWhitespace().ToFullString()
        