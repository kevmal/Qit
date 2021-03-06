﻿namespace Qit

open System
open Microsoft.FSharp.Core.CompilerServices
open System.Reflection
open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Quotations.Patterns
open System.Collections.Generic
open Qit.ProviderImplementation.ProvidedTypes
open Qit.UncheckedQuotations

module Expression = 
    open System.Linq.Expressions
    let evaluate (e : Expression) = 
        match e with 
        | :? LambdaExpression as f -> f.Compile().DynamicInvoke()
        | _ -> Expression.Lambda(e, []).Compile().DynamicInvoke()

module Reflection = 
    let decomposeFSharpFunctionType (t : Type) = 
        let rec loop (t : Type) acc = 
            if FSharp.Reflection.FSharpType.IsFunction t then 
                let d,r = FSharp.Reflection.FSharpType.GetFunctionElements(t)
                loop r (d :: acc)
            else
                List.rev acc, t
        loop t []

module ReflectionPatterns = 

    let (|FSharpFuncType|_|) (t : Type) = 
        if FSharp.Reflection.FSharpType.IsFunction t then 
            Some(Reflection.decomposeFSharpFunctionType t)
        else
            None

    let inline (|Attribute|_|) (minfo : MemberInfo) : 'a option = 
        let a  = minfo.GetCustomAttribute<'a>() 
        if isNull(box a) then 
            None
        else
            Some a

    let (|DeclaringType|) (minfo : MemberInfo) = 
        minfo.DeclaringType

    let (|Implements|_|) (t : Type) : 'a option = 
        let t2 = typeof<'a>
        if t2.IsGenericType then 
            if t2.GetGenericTypeDefinition().IsAssignableFrom(t.GetGenericTypeDefinition()) then 
                Some(Unchecked.defaultof<'a>)
            else   
                None
        else
            if t2.IsAssignableFrom(t) then 
                Some(Unchecked.defaultof<'a>)
            else   
                None

    

type AnyType = class end 


module internal Core = 
    open FSharp.Quotations.Evaluator.QuotationEvaluationExtensions
    let internal methodInfo q =
        match q with 
        | Patterns.Call(_, minfo, _)
        | DerivedPatterns.Lambdas(_, Patterns.Call(_, minfo, _)) -> minfo
        | x -> failwithf "getMethodInfo: Unexpected form %A" x

    let genericMethodInfo q =
        let methodInfo = methodInfo q
        if methodInfo.IsGenericMethod then
            methodInfo.GetGenericMethodDefinition()
        else
            methodInfo


    let castMeth = typeof<Expr>.GetMethod("Cast")
    let internal toTypedExpr (e : Expr) = 
        let t = e.Type
        castMeth.MakeGenericMethod(t).Invoke(null, [|e|])
        

    let rec internal rewriteNestedQuotes x =
        match x with
        | Patterns.QuoteTyped e -> typeof<Expr>.GetMethod("Value").MakeGenericMethod(x.Type).Invoke(null, [|toTypedExpr e|]) :?> Expr
        | Patterns.QuoteRaw e -> Expr.Value(e)
        | ExprShape.ShapeCombination(a, args) -> 
            let nargs = args |> List.map rewriteNestedQuotes
            ExprShape.RebuildShapeCombination(a, nargs)
        | ExprShape.ShapeLambda(v, body) -> Expr.Lambda(v, rewriteNestedQuotes body)
        | ExprShape.ShapeVar(v) -> Expr.Var(v)
        
    let evaluate(q : Expr<'a>) = 
        //(rewriteNestedQuotes q |> Expr.Cast<'a>)
        q.Evaluate()
        //FSharp.Linq.RuntimeHelpers.LeafExpressionConverter.EvaluateQuotation q :?> 'a  
    let evaluateUntyped(q : Expr) = 
        //let q2 = (rewriteNestedQuotes q)
        q.EvaluateUntyped()
        //FSharp.Linq.RuntimeHelpers.LeafExpressionConverter.EvaluateQuotation q

    let rec applySub f q = 
        let rec traverseQuotation acc0 q = 
            let (|Q|_|) q : (Expr*Expr) option = f acc0 q 
            let path = q :: acc0
            match q with
            | Q(a,b) -> 
                if Object.ReferenceEquals(a,q) then 
                    Choice1Of2 b
                else
                    Choice2Of2(a,b)
            | ExprShape.ShapeCombination(a, args) -> 
                let rec loop xs acc = 
                    match xs with 
                    | h :: t -> 
                        match traverseQuotation path h with 
                        | Choice1Of2(e) -> loop t (e :: acc)
                        | Choice2Of2(a,b) when Object.ReferenceEquals(a,h) -> loop t (b :: acc)
                        | x -> Choice2Of2 x
                    | [] -> 
                        Choice1Of2(List.rev acc)
                match loop args [] with 
                | Choice1Of2 nargs ->
                    Choice1Of2(ExprShape.RebuildShapeCombination(a, nargs))
                | Choice2Of2(Choice2Of2(a,b)) when Object.ReferenceEquals(a,q) -> 
                    Choice1Of2(b)
                | Choice2Of2 sub -> sub
            | ExprShape.ShapeLambda(v, body) -> 
                match traverseQuotation path body with 
                | Choice1Of2 e -> Expr.Lambda(v, e) |> Choice1Of2
                | Choice2Of2(a,b) when Object.ReferenceEquals(a,body) -> Expr.Lambda(v, b) |> Choice1Of2
                | x -> x
            | ExprShape.ShapeVar(v) -> Expr.Var(v) |> Choice1Of2
        match traverseQuotation [] q with 
        | Choice1Of2 e -> e
        | Choice2Of2(a,b) -> failwithf "Failed to sub %A for %A in %A" a b q

    //http://www.fssnip.net/1i/title/Traverse-quotation
    let rec traverseQuotation f q = 
        let q = defaultArg (f q) q
        match q with
        | ExprShape.ShapeCombination(a, args) -> 
            let nargs = args |> List.map (traverseQuotation f)
            ExprShape.RebuildShapeCombination(a, nargs)
        | ExprShape.ShapeLambda(v, body) -> Expr.Lambda(v, traverseQuotation f body)
        | ExprShape.ShapeVar(v) -> Expr.Var(v)
                
open Core
    

[<AllowNullLiteral>]
type QitOpAttribute() = inherit Attribute()

type QitBindingObj() = 
    abstract member Final : Expr -> Expr
    default x.Final(e) = e
    member val Var : Var option = None with get,set


open ReflectionPatterns
module Operators = 
    let escapedQuote (x : 'a Expr) = x
    let escapedQuoteMeth = (methodInfo <@ escapedQuote @>).GetGenericMethodDefinition()
    let escapedQuoteRaw (x : Expr) = x
    let escapedQuoteRawMeth = (methodInfo <@ escapedQuoteRaw @>)
    let spliceUntyped (x : Expr) : 'a = Unchecked.defaultof<_> //failwith "quoted code to Expr type"
    let spliceUntypedMeth = (methodInfo <@ spliceUntyped @>).GetGenericMethodDefinition()
    let splice (x : Expr<'a>) : 'a = Unchecked.defaultof<_> //failwith "quoted code to Expr type"
    let splice2Meth = (methodInfo <@ splice @>).GetGenericMethodDefinition()
    [<ReflectedDefinition; QitOp>]
    let (!%) x = splice x
    [<ReflectedDefinition; QitOp>]
    let (!%%) x = spliceUntyped x

    let rewriter (input : 'input) (f : Expr list -> Expr -> Expr -> (Expr*Expr) option) : 'a = Unchecked.defaultof<'a>
    let internal rewriterMeth = (methodInfo <@ rewriter @>).GetGenericMethodDefinition()

    [<ReflectedDefinition; QitOp>]
    let fieldGet (field : FieldInfo) (o : 'a) : 'b = !%%(Expr.FieldGet(<@ o @>,field))
    [<ReflectedDefinition; QitOp>]
    let fieldGetStatic (field : FieldInfo) : 'a = !%%(Expr.FieldGet(field))
    [<ReflectedDefinition; QitOp>]
    let fieldSet (field : FieldInfo) (value : 'a) (o : 'b) : unit =
        !%%(Expr.FieldSet(<@o@>,field,<@value@>))
    [<ReflectedDefinition; QitOp>]
    let fieldSetStatic (field : FieldInfo) (value : 'a) : unit = 
        !%%(Expr.FieldSet(field,<@value@>))
    [<ReflectedDefinition; QitOp>]
    let methodCall (method : MethodInfo) (args : obj list) (o : 'a) : 'b = failwith "methodCall"
    [<ReflectedDefinition; QitOp>]
    let methodCallStatic (method : MethodInfo) (args : obj list) : 'c  = failwith "methodCall"
    

type IHole = 
    abstract member Action : Expr list * Expr -> Expr*Expr

type IHole<'a> = 
    inherit IHole
    abstract member Marker : 'a
open  Operators
module Quote =
    let toExpression (q : Expr<'a>) = FSharp.Linq.RuntimeHelpers.LeafExpressionConverter.QuotationToExpression q  
    let evaluate(q : Expr<'a>) = evaluate q
    let evaluateUntyped(q : Expr) = evaluateUntyped q 
    let inline hole f = 
        {new IHole<'a> with
             member this.Action(arg2: Expr list, arg3: Expr): Expr*Expr = 
                f arg2 arg3
             member this.Marker: 'a = 
                 raise (System.NotImplementedException()) }
            
    let any name : AnyType = failwith "marker"
    let withType<'a> name : 'a = failwith "marker"

    let typed (q : Expr) : Expr<'a> = <@ %%q @>
    let untyped (q : Expr<_>) = q.Raw

    let methodInfo q = methodInfo q

    let genericMethodInfo q = genericMethodInfo q

    let applySub f q = applySub f q
    let traverseQuotation f q = traverseQuotation f q

    let replaceVar v1 v2 e =
        e
        |> traverseQuotation
            (fun q -> 
                match q with 
                | Patterns.Var(v) when v = v1 -> Some(v2)
                | _ -> None
            )

    let rec genMatch (t1 : Type) (t2 : Type) = 
        if t1.IsGenericType then 
            if t2.IsGenericType then 
                if t1.GetGenericTypeDefinition() <> t2.GetGenericTypeDefinition() then 
                    None
                else
                    genMatchAll (t1.GetGenericArguments()) (t2.GetGenericArguments())
            else
                None
        else
            Some [t1, [t2]]
            


    and genMatchAll (tps : Type seq) (args : Type seq) = 
        let results = 
            (tps,args) 
            ||> Seq.map2 genMatch
            |> Seq.fold 
                (fun all r ->
                    match all,r with 
                    | None,_ -> None 
                    | _,None -> None 
                    | Some all, Some l -> 
                        Some (l @ all)
                ) (Some [])
        match results with 
        | Some rs ->
            rs 
            |> Seq.groupBy
                (fun (t1,t2) -> t1)
            |> Seq.map 
                (fun (t1, ts) -> t1, ts |> Seq.toList |> List.collect snd |> List.distinct)
            |> Seq.toList
            |> Some

        | None -> None
    let reduceMatch (l : (Type*Type list) list) = 
        l
        |> List.map 
            (fun (t,l) ->
                match l with 
                | [t2] -> t,t2
                | [] -> failwithf "Unreachable"
                | l -> t, l |> List.filter (fun x -> x <> typeof<obj>) |> List.head
                | l -> failwithf "Multiple matches (%A) for %A" l t
            )
    let rec genericParameter (t : Type) = 
        if t.IsGenericType then 
            t.GetGenericArguments() |> Seq.exists genericParameter
        else
            t.IsGenericParameter

    let solveGenType (gt : Type) (l : (Type * Type) list) =
        assert (gt.IsGenericTypeDefinition)
        try
            let ts =  
                gt.GetGenericArguments()
                |> Array.map 
                    (fun x ->
                        l |> List.find(fun (t,_) -> t = x) |> snd
                    )
            gt.MakeGenericType(ts)
        with 
        | _ -> failwithf "Could not solve gen type %A with %A" gt l

    let solveGenMeth (gt : MethodInfo) (l : (Type * Type) list) =
        assert (gt.IsGenericMethodDefinition)
        try
            let ts =  
                gt.GetGenericArguments()
                |> Array.map 
                    (fun x ->
                        l |> List.find(fun (t,_) -> t = x) |> snd
                    )
            gt.MakeGenericMethod(ts)
        with 
        | _ -> failwithf "Could not solve gen type %A with %A" gt l
    let expandOperatorsUntypedTest (expr : Expr) = 
        let gmat q t1 t2 = 
            match genMatchAll t1 t2 with 
            | Some l -> reduceMatch l
            | None -> failwithf "Could not match %A to %A in %A" t1 t2 q
        let bindAll = BindingFlags.DeclaredOnly ||| BindingFlags.Public ||| BindingFlags.NonPublic ||| BindingFlags.Static ||| BindingFlags.Instance
        let rec loop replace expr = //strong expectedType expr = 
            expr
            |> UncheckedQuotations.traverseQuotation
                (fun q -> 
                    match q with
                    | Patterns.Call(None, m, args) when m.IsGenericMethod ->
                        let args = args |> List.map (loop replace)
                        let gm = m.GetGenericMethodDefinition()
                        let t1 = gm.GetParameters() |> Seq.map (fun x -> x.ParameterType) |> Seq.toArray
                        let t2 = args |> Seq.map (fun x -> x.Type) |> Seq.toArray
                        let c1 = gmat q t1 t2
                        let c2 = gmat q [gm.ReturnType] [m.ReturnType]
                        let c = c1 @ c2
                        let m = solveGenMeth gm c
                        Some(Expr.CallUnchecked(m, args))
                    | Patterns.Call(Some(Patterns.Var vv), m, args) when Map.containsKey vv replace ->
                        let v : Var = replace.[vv]
                        let m = v.Type.GetMethods() |> Seq.find (fun x -> m.MetadataToken = x.MetadataToken)
                        Some(Expr.CallUnchecked(Expr.Var v, m, args) |> loop replace)
                    | Patterns.PropertyGet(Some(Patterns.Var vv), m, args) when Map.containsKey vv replace ->
                        let v : Var = replace.[vv]
                        let m = v.Type.GetProperties() |> Seq.find (fun x -> m.MetadataToken = x.MetadataToken)
                        Some(Expr.PropertyGet(Expr.Var v, m, args) |> loop replace)
                    | Patterns.PropertySet(Some(Patterns.Var vv), m, args, vl) when Map.containsKey vv replace ->
                        let v : Var = replace.[vv]
                        let m = v.Type.GetProperties() |> Seq.find (fun x -> m.MetadataToken = x.MetadataToken)
                        Some(Expr.PropertySet(Expr.Var v, m, vl, args) |> loop replace)
                    | Patterns.Let(var, binding, body) when var.Type.IsGenericType -> 
                        let t = var.Type 
                        let gt = var.Type.GetGenericTypeDefinition()
                        let c1 = ctorContraints replace binding
                        let c2 = useConstraints replace var body
                        let tt = solveGenType gt (c1 @ c2)
                        if tt = t then 
                            Expr.Let(var, loop replace binding, loop replace body) |> Some
                        else
                            let v = Var(var.Name, tt, var.IsMutable)
                            let replace = Map.add var v replace
                            Expr.Let(v, applyCtor replace tt binding, loop replace body) |> Some
                    | _ -> None
                )
        and applyCtor replace tt e = 
            match e with 
            | Patterns.Let(var,binding,body) -> 
                let b2 = loop replace binding
                if b2.Type <> binding.Type then 
                    let v2 = Var(var.Name,b2.Type,var.IsMutable)
                    let replace = Map.add var v2 replace
                    Expr.Let(v2, loop replace binding, applyCtor replace tt body)
                else
                    Expr.Let(var, loop replace binding, applyCtor replace tt body)
            | Patterns.NewObject(ctor, args) -> 
                let gctor = 
                    let i = ctor.DeclaringType.GetConstructors() |> Seq.findIndex (fun x -> x = ctor)
                    tt.GetConstructors().[i]
                Expr.NewObject(gctor, args |> List.map (loop replace))
            | _ -> failwithf "39fm Unhandled %A" e
        and useConstraints replace v e = 
            let ra = ResizeArray()
            let rec inner expected q = 
                match q with
                | Patterns.Call(Some(Patterns.Var vv), m, args) when vv = v ->
                    let args = args |> List.map (loop replace)
                    let gdef = v.Type.GetGenericTypeDefinition()
                    //let i = v.Type.GetMethods(bindAll) |> Seq.findIndex (fun x -> x = m)
                    let gm = gdef.GetMethods(bindAll) |> Seq.find (fun x -> m.Name = x.Name && x.MetadataToken = m.MetadataToken)
                    match genMatchAll (gm.GetParameters() |> Seq.map (fun x -> x.ParameterType)) (args |> List.map (fun x -> x.Type)) with 
                    | Some c -> 
                        ra.Add(reduceMatch c)
                    | None -> failwithf "Could not reconcile %A" q 
                | Patterns.PropertyGet(Some(Patterns.Var vv), m, args) when vv = v ->
                    let args = args |> List.map (loop replace)
                    let gdef = v.Type.GetGenericTypeDefinition()
                    let gm = 
                        let i = v.Type.GetProperties(bindAll) |> Seq.findIndex (fun x -> x = m)
                        gdef.GetProperties(bindAll).[i]
                    match genMatch gm.PropertyType m.PropertyType with 
                    | Some c -> 
                        ra.Add(reduceMatch c)
                    | None -> failwithf "Could not reconcile %A" q 
                    match genMatchAll (gm.GetIndexParameters() |> Seq.map (fun x -> x.ParameterType)) (args |> List.map (fun x -> x.Type)) with 
                    | Some c -> 
                        ra.Add(reduceMatch c)
                    | None -> failwithf "Could not reconcile args in %A" q 
                | ShapeCombinationUnchecked(a, args) -> args |> List.iter (inner None)
                | ShapeLambdaUnchecked(v, body) -> inner None body
                | ShapeVarUnchecked(v) -> ()
            inner None expr
            ra |> Seq.concat |> Seq.toList
           
        and ctorContraints replace e = 
            match e with 
            | Patterns.Let(var,binding,body) -> 
                let b2 = loop replace binding
                if b2.Type <> binding.Type then 
                    let v2 = Var(var.Name,b2.Type,var.IsMutable)
                    let replace = Map.add var v2 replace
                    ctorContraints replace body
                else
                    ctorContraints replace body
            | Patterns.NewObject(ctor, args) -> 
                let gdef = ctor.DeclaringType.GetGenericTypeDefinition()
                //let gargs = gdef.GetGenericArguments()
                //let targs = ctor.DeclaringType.GetGenericArguments()
                let gctor = 
                    let i = ctor.DeclaringType.GetConstructors() |> Seq.findIndex (fun x -> x = ctor)
                    gdef.GetConstructors().[i]
                let ps = ctor.GetParameters()
                let gps = gctor.GetParameters()
                let rec loop2 i flag cs nargs = 
                    if i < args.Length then 
                        let a = loop replace args.[i]
                        let at = a.Type
                        let flag = flag || (at <> ps.[i].ParameterType)
                        if genericParameter gps.[i].ParameterType then 
                            match genMatch gps.[i].ParameterType at with
                            | None -> failwithf "Could not match types %A and %A in %A" gps.[i] at e
                            | Some(l) -> 
                                loop2 (i + 1) flag ((reduceMatch l) :: cs) (a :: nargs)
                        else
                            loop2 (i + 1) flag (cs) (a :: nargs)
                    else
                        flag,cs, nargs |> List.rev
                match loop2 0 false [] [] with 
                | _,cs,_ -> cs |> List.concat
            | _ -> failwithf "39fm Unhandled %A" e
        loop Map.empty expr
            
    (*   
    let expandOperatorsUntypedTest (expr : Expr) = 
        let bindAll = BindingFlags.DeclaredOnly ||| BindingFlags.Public ||| BindingFlags.NonPublic ||| BindingFlags.Static ||| BindingFlags.Instance
        let d = Dictionary<_,_>()
        let replace = Dictionary<_,_>()
        let rec loop expr = //strong expectedType expr = 
            expr
            |> traverseQuotation
                (fun q -> 
                    match q with
                    | Patterns.Call(Some o, method, args) ->
                        let eo = loop o
                        if eo.Type.IsGenericType then 
                            let gdef = eo.Type.GetGenericTypeDefinition()
                            let i = o.Type.GetMethods(bindAll) |> Seq.findIndex (fun m -> m = method)
                            let m = gdef.GetMethods(bindAll).[i]
                            let eargs = args |> List.map loop
                            let ts = eargs |> List.map (fun x -> x.Type)
                            let matchParameters = 
                                match genMatchAll (m.GetParameters() |> Array.map (fun x -> x.Type)) ts with 
                                | None -> failwithf "Could not infer splice type %A in %A" q expr
                                | Some l ->
                                    l
                                    |> List.choose
                                        (fun (x,l) ->
                                            if x.IsGenericParameter then 
                                                if List.Length l <> 1 then 
                                                    failwithf "Could not infer splice type %A in %A. %A could be %A" q expr x l
                                                else
                                                    l |> List.head |> Some
                                            else
                                                None
                                        )
                                    |> dict
                            

                        else
                            if method.IsGenericMethod then 
                                method.GetGenericMethodDefinition() |> Some
                            else
                                None
                        


                    | Patterns.Let(var, binding, body) when var.Type.IsGenericType ->
                        let gdef = var.Type.GetGenericTypeDefinition()
                        let v2 = Var(var.Name, gdef)
                        replace.Add(var,v2)
                        Expr.Let(v2,loop binding,loop body) |> Some
                    | Patterns.Call(Some(Patterns.Var v), method, args) when replace.ContainsKey v -> 
                        
                    | _ -> None
                )
        loop expr
    *)
    
    let expandOperatorsUnchecked (expr : Expr) = 
        let rec loop inSplice expr = 
            expr
            |> UncheckedQuotations.traverseQuotation
                (fun q -> 
                    match q with 
                    | Patterns.Let(var, binding, body) when typeof<QitBindingObj>.IsAssignableFrom(binding.Type) ->
                        let b = binding |> loop true |> evaluateUntyped  :?> QitBindingObj
                        b.Var <- Some var
                        let body = 
                            body.Substitute(fun x -> if x = var then Some (Expr.Value(b, binding.Type)) else None)
                            |> loop inSplice
                        b.Final(body) |> Some
                    | Patterns.Let(v,e,b) when inSplice -> 
                        b.Substitute(fun i -> if i = v then Some(e) else None)
                        |> loop inSplice 
                        |> Some
                    | Patterns.Call(o, Attribute (_ : QitOpAttribute) & DerivedPatterns.MethodWithReflectedDefinition(meth), args) -> 
                        let meth = meth 
                        let args = 
                            match o with 
                            | Some b -> [b] @ args
                            | None -> args
                        let res = 
                            match meth with 
                            | DerivedPatterns.Lambdas(v, body) -> 
                                let assign = args 
                                let assign = 
                                    if List.length assign < List.length v then 
                                        assign @ [ <@@ () @@> ]
                                    else
                                        assign
                                (v |> List.concat, assign)
                                ||> List.zip
                                |> Seq.fold 
                                    (fun (e : Expr) (v,a) -> 
                                        e.Substitute(fun x -> if x = v then Some a else None)
                                    ) body
                            | _ -> failwith "Unreachable"
                        res
                        |> loop inSplice 
                        |> Some
                    | Patterns.Call(None, minfo, [e]) when minfo.IsGenericMethod && minfo.GetGenericMethodDefinition() = splice2Meth -> 
                        let q = loop true e
                        Some(q |> evaluateUntyped :?> Expr)
                    | Patterns.Call(None, minfo, [e]) when minfo.IsGenericMethod && minfo.GetGenericMethodDefinition() = spliceUntypedMeth -> 
                        let q = loop true e
                        Some(q |> evaluateUntyped :?> _)
                    | Patterns.Application(Patterns.Lambda(v,b), arg) when inSplice -> 
                        Some(b.Substitute(fun i -> if i = v then Some arg else None) |> loop true)
                    | Patterns.Let(v, q, b) when inSplice && v.Type = typeof<Expr> ->
                        let expr = loop true q |> evaluateUntyped :?> Expr
                        Some(b.Substitute(fun i -> if i = v then Some (Expr.Value expr) else None) |> loop true)
                    | Patterns.Let(v, q, b) when inSplice && v.Type.IsGenericType && v.Type.GetGenericTypeDefinition() = typedefof<Expr<_>> ->
                        let expr = loop true q |> evaluateUntyped :?> Expr
                        let expr = typeof<Expr>.GetMethod("Cast").MakeGenericMethod(v.Type.GetGenericArguments().[0]).Invoke(null, [|expr|])
                        Some(b.Substitute(fun i -> if i = v then Some (Expr.Value(expr, v.Type)) else None) |> loop true)
                    | Patterns.QuoteRaw q when inSplice -> 
                        Some(Expr.Value(loop false q))
                    | Patterns.QuoteTyped q2 when inSplice -> 
                        let expr = loop false q2
                        let expr = typeof<Expr>.GetMethod("Cast").MakeGenericMethod(q2.Type).Invoke(null, [|expr|])
                        Some(Expr.Value(expr, q.Type))
                    | _ -> None
                )
        loop false expr

    let internal lunbox<'a> x : 'a = unbox x
    let internal lunboxMethod = match <@ lunbox<obj> (failwith "") @> with | Patterns.Call(_,minfo,_) -> minfo.GetGenericMethodDefinition() | _ -> failwith "lunboxMethod unreachable"
    
    let expandOperatorsUntyped (expr : Expr) = 
        let rec loop inSplice expr = 
            expr
            |> traverseQuotation
                (fun q -> 
                    match q with 
                    | Patterns.Let(var, binding, body) when typeof<QitBindingObj>.IsAssignableFrom(binding.Type) ->
                        let b = binding |> loop true |> evaluateUntyped  :?> QitBindingObj
                        b.Var <- Some var
                        let body = 
                            body.Substitute(fun x -> if x = var then Some (Expr.Value(b, binding.Type)) else None)
                            |> loop inSplice
                        b.Final(body) |> Some
                    //| Patterns.Let(v,((Patterns.QuoteRaw(q) | Patterns.QuoteTyped(q)) as e),b) when inSplice -> 
                    //    b.Substitute(fun i -> if i = v then Some(e) else None)
                    //    |> loop inSplice 
                    //    |> Some
                    | Patterns.Let(v,((Patterns.Lambda _ as r) as e),b) when inSplice -> 
                        b.Substitute(fun i -> if i = v then Some(e) else None)
                        |> loop inSplice 
                        |> Some
                    | Patterns.Let(v,e,b) when inSplice && e.GetFreeVars() |> Seq.isEmpty -> 
                        let e = lazyWrap inSplice v.Type e
                        b.Substitute(fun i -> if i = v then Some(e) else None)
                        |> loop inSplice 
                        |> Some
                    | Patterns.Let(v,e,b) when inSplice -> 
                        let e = lazyWrap inSplice v.Type e
                        b.Substitute(fun i -> if i = v then Some(e) else None)
                        |> loop inSplice 
                        |> Some
                    | Patterns.PropertyGet(o, Attribute (_ : QitOpAttribute) & DerivedPatterns.PropertyGetterWithReflectedDefinition(meth), args) 
                    | Patterns.Call(o, Attribute (_ : QitOpAttribute) & DerivedPatterns.MethodWithReflectedDefinition(meth), args) -> 
                        let meth = meth 
                        let args = 
                            match o with 
                            | Some b -> [b] @ args
                            | None -> args
                        let res = 
                            match meth with 
                            | DerivedPatterns.Lambdas(v, body) -> 
                                let assign = args 
                                let assign = 
                                    if List.length assign < List.length v then 
                                        assign @ [ <@@ () @@> ]
                                    else
                                        assign
                                (v |> List.concat, assign)
                                ||> List.zip
                                |> Seq.fold 
                                    (fun (e : Expr) (v,a) -> 
                                        e.Substitute(fun x -> if x = v then Some a else None)
                                    ) body
                            | e -> e
                            | _ -> failwith "Unreachable"
                        res
                        |> loop inSplice 
                        |> Some
                    | Patterns.Call(None, minfo, [e]) when minfo.IsGenericMethod && minfo.GetGenericMethodDefinition() = splice2Meth -> 
                        let q = loop true e
                        Some(q |> evaluateUntyped :?> Expr)
                    | Patterns.Call(None, minfo, [e]) when minfo.IsGenericMethod && minfo.GetGenericMethodDefinition() = spliceUntypedMeth -> 
                        let q = loop true e
                        Some(q |> evaluateUntyped :?> _)
                    | Patterns.Application(Patterns.Lambda(v,b), arg) when inSplice -> 
                        if arg.GetFreeVars() |> Seq.isEmpty then 
                            let arg = lazyWrap inSplice v.Type arg
                            Some(b.Substitute(fun i -> if i = v then Some arg else None) |> loop true)
                        else 
                            Some(b.Substitute(fun i -> if i = v then Some arg else None) |> loop true)
                    | Patterns.Call(None, m, [Patterns.QuoteRaw q]) when inSplice && m = escapedQuoteRawMeth -> 
                        Some(Expr.QuoteRaw(loop true q))
                    | Patterns.QuoteRaw q when inSplice -> 
                        Some(Expr.Value(loop false q))
                    | Patterns.Call(None, m, [Patterns.QuoteTyped q]) when inSplice && m.IsGenericMethod && m.GetGenericMethodDefinition() = escapedQuoteMeth -> 
                        Some(Expr.QuoteTyped(loop true q))
                    | Patterns.QuoteTyped q2 when inSplice -> 
                        let expr = loop false q2
                        let expr = typeof<Expr>.GetMethod("Cast").MakeGenericMethod(q2.Type).Invoke(null, [|expr|])
                        Some(Expr.Value(expr, q.Type))
                    | Patterns.Call(None, m, [a]) when not inSplice && m.IsGenericMethod && m.GetGenericMethodDefinition() = lunboxMethod -> Some(Expr.Value(evaluateUntyped q, q.Type))
                    | _ -> None
                )
        and lazyWrap inSplice tp e = 
            match e with 
            | Patterns.Value _ -> e
            | _ -> 
                let f = lazy (e |> loop inSplice |> evaluateUntyped)
                match <@@ lunbox f.Value @@> with 
                | Patterns.Call(None, minfo, args) -> Expr.Call(minfo.GetGenericMethodDefinition().MakeGenericMethod(tp), args)
                | _ -> failwithf "unbox never"
            
        loop false expr
    
    let expandOperators (expr : Expr<'a>) : Expr<'a> =
        expr |> expandOperatorsUntyped |> Expr.Cast

    let expandRewriters (expr : Expr) = 
        expr
        |> applySub
            (fun trail e ->
                match e with
                | Patterns.Call(None, m, [inp; f]) when m.IsGenericMethod && m.GetGenericMethodDefinition() = rewriterMeth -> 
                    let f : Expr list -> Expr -> Expr -> (Expr*Expr) option =  evaluateUntyped f :?> _
                    f trail e inp 
                | _ -> None
            )

    //let intoExpr (x : 'a) : Expr = <@@ () @@> //failwith "quoted code to Expr type"


    let rec traverseQuotationUnchecked f q = UncheckedQuotations.traverseQuotation f q

    let rec traverseQuotationRec f q = 
        let rec loop q = 
            match f q with 
            | Some(true,q) -> loop q
            | Some(false,q) -> q
            | None -> q
        let q = loop q
        match q with
        | ExprShape.ShapeCombination(a, args) -> 
            let nargs = args |> List.map (traverseQuotationRec f)
            ExprShape.RebuildShapeCombination(a, nargs)
        | ExprShape.ShapeLambda(v, body) -> Expr.Lambda(v, traverseQuotationRec f body)
        | ExprShape.ShapeVar(v) -> Expr.Var(v)

    let internal markerMethod = methodInfo <@ any "" @>
    let internal typedMarkerMethod = genericMethodInfo <@ withType "" @>
    let internal genericMethod (m : MethodInfo) = if m.IsGenericMethod then m.GetGenericMethodDefinition() else m

    let exprMatch a b =
        let markers = Dictionary<string,Expr>()
        let typedMarkers = Dictionary<string,Expr>()
        let rec exprEq (a : Expr) (b : Expr) = 
            let varRep (a : Var) (b : Var) = 
                if a.Name.StartsWith "__" then 
                    fun ((x : Expr),y) -> x.Substitute(fun v -> if v = a then Some (Expr.Var(b)) else None),y
                elif b.Name.StartsWith "__" then 
                    fun (y,(x : Expr)) -> y,x.Substitute(fun v -> if v = b then Some (Expr.Var(a)) else None)
                else    
                    id
            match (a,b) with
            | Call (None, m, [Value (name,_)]), a 
            | a, Call (None, m, [Value (name,_)]) when m = markerMethod -> 
                let name = name :?> string
                let scc, e = markers.TryGetValue(name)
                if scc then 
                    exprEq e a
                else
                    if name <> "" then markers.[name] <- a
                    true
            | Call (None, m, [Value (name,_)]), a 
            | a, Call (None, m, [Value (name,_)]) when genericMethod m = typedMarkerMethod -> 
                let name = name :?> string
                let tp = m.GetGenericArguments().[0]
                let scc, e = typedMarkers.TryGetValue(name)
                if scc then 
                    exprEq e a
                else    
                    if typeEq a.Type tp then
                        if name <> "" then typedMarkers.[name] <- a
                        true
                    else
                        false
            | AddressOf(e1), AddressOf(e2) -> exprEq e1 e2
            | AddressSet(a1, a2), AddressSet(b1, b2) ->  exprEq a1 b1 && exprEq a2 b2
            | Application(a1, a2), Application(b1, b2) -> exprEq a1 b1 && exprEq a2 b2
            | Call(exprOption, methodInfo, exprList),Call(exprOption1, methodInfo1, exprList1) -> 
                List.length exprList = List.length exprList1 &&
                    exprEqOpt exprOption exprOption1 &&
                    methEq methodInfo methodInfo1 &&
                    List.map2 exprEq exprList exprList1 |> List.fold (&&) true
            | Coerce(e,t),Coerce(e1,t1) -> typeEq t t1 && exprEq e e1
            | DefaultValue(type1),DefaultValue(type2) -> typeEq type1 type2
            | FieldGet(expr, fieldInfo), FieldGet(expr1, fieldInfo1) -> fieldInfo = fieldInfo1 && exprEqOpt expr expr1
            | FieldSet(exprOption, fieldInfo, expr), FieldSet(exprOption1, fieldInfo1, expr1) -> fieldInfo = fieldInfo1 && exprEq expr expr1 && exprEqOpt exprOption exprOption1
            | ForIntegerRangeLoop(var1, expr1, expr2, expr3), ForIntegerRangeLoop(var11, expr11, expr21, expr31) -> 
                varEq var1 var11 &&
                    exprEq expr1 expr11 &&
                    exprEq expr2 expr21 &&
                    (let expr3,expr31 = varRep var1 var11 (expr3,expr31) in exprEq expr3 expr31)
            | IfThenElse(expr1, expr2, expr3), IfThenElse(expr11, expr21, expr31) ->
                exprEq expr1 expr11 &&
                    exprEq expr2 expr21 &&
                    exprEq expr3 expr31
            | Lambda(var1, expr), Lambda(var11, expr1) -> 
                varEq var1 var11 &&
                    (let expr,expr1 = varRep var1 var11 (expr,expr1) in exprEq expr expr1)
            | LetRecursive(varExprList, expr), LetRecursive(varExprList1, expr1) -> 
                exprEq expr expr1 &&
                    List.length varExprList = List.length varExprList1 &&
                    List.map2 (fun (v1,e1) (v2,e2) -> varEq v1 v2 && (let e1,e2 = varRep v1 v2 (e1,e2) in exprEq e1 e2)) varExprList varExprList1 |> List.fold (&&) true
            | Let(var, expr1, expr2), Let(var1, expr11, expr21) -> 
                varEq var var1 &&
                    exprEq expr1 expr11 &&
                    (let expr2,expr21 = varRep var var1 (expr2,expr21) in exprEq expr2 expr21)
            | NewArray(type1, exprList), NewArray(type11, exprList1) -> 
                typeEq type1 type11 &&
                    List.length exprList = List.length exprList1 &&
                    List.map2 exprEq exprList exprList1 |> List.fold (&&) true
            | NewDelegate(type1, varList, expr), NewDelegate(type11, varList1, expr1) -> 
                typeEq type1 type11 &&
                    List.length varList = List.length varList1 &&
                    List.map2 varEq varList varList1 |> List.fold (&&) true &&
                    exprEq expr expr1
            | NewObject(constructorInfo, exprList), NewObject(constructorInfo1, exprList1) -> 
                constructorInfo = constructorInfo1 &&
                    List.length exprList = List.length exprList1 &&
                    List.map2 exprEq exprList exprList1 |> List.fold (&&) true
            | NewRecord(type1, exprList), NewRecord(type11, exprList1) -> 
                typeEq type1 type11 &&
                    List.length exprList = List.length exprList1 &&
                    List.map2 exprEq exprList exprList1 |> List.fold (&&) true
            | NewTuple(exprList), NewTuple(exprList1) -> 
                List.length exprList = List.length exprList1 &&
                    List.map2 exprEq exprList exprList1 |> List.fold (&&) true
            | NewUnionCase(unionCaseInfo, exprList), NewUnionCase(unionCaseInfo1, exprList1) -> 
                unionCaseInfo = unionCaseInfo1 &&
                    List.length exprList = List.length exprList1 &&
                    List.map2 exprEq exprList exprList1 |> List.fold (&&) true
            | PropertyGet(exprOption, propertyInfo, exprList), PropertyGet(exprOption1, propertyInfo1, exprList1) -> 
                exprEqOpt exprOption exprOption1 && 
                    propEq propertyInfo propertyInfo1 &&
                    List.length exprList = List.length exprList1 &&
                    List.map2 exprEq exprList exprList1 |> List.fold (&&) true
            | PropertySet(exprOption, propertyInfo, exprList, expr), PropertySet(exprOption1, propertyInfo1, exprList1, expr1) -> 
                exprEqOpt exprOption exprOption1 && 
                    propEq propertyInfo propertyInfo1 &&
                    List.length exprList = List.length exprList1 &&
                    List.map2 exprEq exprList exprList1 |> List.fold (&&) true &&
                    exprEq expr expr1
            | QuoteTyped(expr), QuoteTyped(expr1) -> exprEq expr expr1
            | QuoteRaw(expr), QuoteRaw(expr1) -> exprEq expr expr1
            | Sequential(expr1, expr2), Sequential(expr11, expr21) -> 
                exprEq expr1 expr11 &&
                    exprEq expr2 expr21
            | TryFinally(expr1, expr2), TryFinally(expr11, expr21) -> 
                exprEq expr1 expr11 &&
                    exprEq expr2 expr21
            | TryWith(expr1, var1, expr2, var2, expr3), TryWith(expr11, var11, expr21, var21, expr31) -> 
                exprEq expr1 expr11 &&
                    exprEq expr2 expr21 &&
                    exprEq expr3 expr31 &&
                    varEq var1 var11 &&
                    varEq var2 var21
            | TupleGet(expr, int1), TupleGet(expr1, int11) -> 
                exprEq expr expr1 &&
                    int1 = int11
            | TypeTest(expr, type1), TypeTest(expr1, type11) -> 
                exprEq expr expr1 &&
                    typeEq type1 type11
            | UnionCaseTest(expr, unionCaseInfo), UnionCaseTest(expr1, unionCaseInfo1) -> 
                unionCaseInfo = unionCaseInfo1 &&
                    exprEq expr expr1
            //| ValueWithName(obj1, type1, name) when List.contains name vs -> name
            | Value(obj1, type1), Value(obj11, type11) -> 
                obj1 = obj11 && typeEq type1 type11
            | VarSet(var, expr), VarSet(var1, expr1) -> 
                varEq var var1 &&
                    exprEq expr expr1
            | Var(var), Var(var1) -> varEq var var1
            | WhileLoop(expr1, expr2), WhileLoop(expr11, expr21) -> 
                exprEq expr1 expr11 &&
                    exprEq expr2 expr21
            | _ -> false
        and exprEqOpt (a : Expr option) (b : Expr option) = 
            if a.IsSome && b.IsSome then
                exprEq a.Value b.Value
            else
                a.IsNone && b.IsNone
        and varEq (a : Var) (b : Var) = 
            typeEq a.Type b.Type && (a.Name = b.Name || a.Name.StartsWith "__" || b.Name.StartsWith "__") && a.IsMutable = b.IsMutable
        and typeEq (a : Type) (b : Type) = 
            if a.IsArray && b.IsArray then 
                typeEq (a.GetElementType()) (b.GetElementType())
            elif a.IsGenericType && b.IsGenericType then 
                a.GetGenericTypeDefinition() = b.GetGenericTypeDefinition() &&
                    (Array.map2 typeEq (a.GetGenericArguments()) (b.GetGenericArguments())
                     |> Array.fold (&&) true)
            else
                a = typeof<AnyType> || b = typeof<AnyType> || a = b
        and propEq (a : PropertyInfo) (b : PropertyInfo) = 
            a = b || 
                (typeEq a.DeclaringType b.DeclaringType && a.Name = b.Name && typeEq a.PropertyType b.PropertyType)
        and methEq (a : MethodInfo) (b : MethodInfo) = 
            let genArgsEq() =
                let args1 = a.GetGenericArguments()
                let args2 = b.GetGenericArguments()
                args1.Length = args2.Length &&
                    ((args1, args2) 
                     ||> Seq.map2 typeEq 
                     |> Seq.contains false 
                     |> not )
            let checkGenericType() =
                if a.DeclaringType.IsGenericType && b.DeclaringType.IsGenericType then   
                    let adef = a.DeclaringType.GetGenericTypeDefinition()
                    let bdef = b.DeclaringType.GetGenericTypeDefinition()
                    if adef = bdef then
                        let nameEq() = a.Name = b.Name
                        let returnEq() = typeEq a.ReturnType b.ReturnType
                        let paramTpsEq() = 
                            let p1 = a.GetParameters()
                            let p2 = b.GetParameters()
                            p1.Length = p2.Length 
                            &&
                                (
                                    (p1, p2)
                                    ||> Seq.map2 (fun a b -> a.Name = b.Name && typeEq a.ParameterType b.ParameterType)
                                    |> Seq.contains false
                                    |> not
                                )
                        genArgsEq() && nameEq() && returnEq() && paramTpsEq()
                    else
                        false
                else
                    false
                        
            a = b 
                || (a.IsGenericMethod && b.IsGenericMethod && a.GetGenericMethodDefinition() = b.GetGenericMethodDefinition() && genArgsEq())
                || checkGenericType()
        markers, typedMarkers, exprEq a b
    
    let internal (|Quote|_|) (e : Expr) (x : Expr) = 
        let _,_,y = exprMatch e x
        if y then Some () else None

    let internal (|BindQuote|_|) (e : Expr) (x : Expr) = 
        let a,b,y = exprMatch e x
        if y then Some (a,b) else None

    //let pipe = getGenericMethodInfo <@(|>)@>
    let rec expand vars expr = 

      // First recursively process & replace variables
      let expanded = 
        match expr with
        // If the variable has an assignment, then replace it with the expression
        | ExprShape.ShapeVar v when Map.containsKey v vars -> vars.[v]
        // Apply 'expand' recursively on all sub-expressions
        | ExprShape.ShapeVar v -> Expr.Var v
        | Patterns.Call(body, DerivedPatterns.MethodWithReflectedDefinition meth, args) ->
            let this = match body with Some b -> Expr.Application(meth, b) | _ -> meth
            let res = Expr.Applications(this, [ for a in args -> [a]])
            expand vars res
        | ExprShape.ShapeLambda(v, expr) -> 
            Expr.Lambda(v, expand vars expr)
        | ExprShape.ShapeCombination(o, exprs) ->
            let fuck = List.map (expand vars) exprs
            let e = ExprShape.RebuildShapeCombination(o, fuck)
            e
            

      // After expanding, try reducing the expression - we can replace 'let'
      // expressions and applications where the first argument is lambda
      match expanded with
      //| Patterns.Let(v, Patterns.Call _, _) as expr -> expr
      //| E <@ marker "f" |> typedMarker "g" @> (Key "f" f, Key "g" g) -> Expr.Application(g, f)
      //| Patterns.Call(None, op, args) when op.IsGenericMethod && op.GetGenericMethodDefinition() = pipe -> 
      //      Expr.Application(args.[1],args.[0])
      | Patterns.Application(ExprShape.ShapeLambda(v, body), assign)
      | Patterns.Let(v, assign, body) when not v.IsMutable -> expand (Map.add v (expand vars assign) vars) body
      | _ -> expanded



      
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
            
    let rec str q =
        match q with
        | AddressOf(expr) -> sprintf "&(%s)" (str expr)
        | AddressSet(expr1, expr2) ->  failwithf "AddressSet(%s, %s)" (str expr1) (str expr2)
        | Application(expr1, Lambda(v,expr2)) ->
            let e = Expr.Let(v,expr1,expr2)
            str e
        | Call(exprOption, methodInfo, exprList) -> 
            let o = 
                match exprOption with 
                | Some v -> sprintf "(%s)" (str v)
                | None -> methodInfo.DeclaringType |> typeStr
            let args = exprList |> List.map str |> List.map (fun x -> sprintf "(%s)" x) |> String.concat ","
            if methodInfo.IsGenericMethod then
                let targs = methodInfo.GetGenericArguments() |> Array.map typeStr |> String.concat ","
                sprintf "(%s.%s<%s>(%s))" o methodInfo.Name targs args
            else
                sprintf "(%s.%s(%s))" o methodInfo.Name args
        | Coerce(expr, type1) -> sprintf "((%s) : %s)" (str expr) (typeStr type1)
        | DefaultValue(type1) -> sprintf "(%s())" (typeStr type1)
        | FieldGet(expr, fieldInfo) -> 
            match expr with
            | Some expr ->
                sprintf "((%s).%s)" (str expr) fieldInfo.Name
            | None ->
                sprintf "(%s)" fieldInfo.Name
        | FieldSet(exprOption, fieldInfo, expr) -> 
            match exprOption with
            | Some expr ->
                sprintf "(%s).%s <- %s" (str expr) fieldInfo.Name (str expr)
            | None ->
                sprintf "%s <- %s" fieldInfo.Name (str expr)
        | ForIntegerRangeLoop(var1, expr1, expr2, expr3) -> 
            sprintf "for %s = %s to %s do (%s)" (var1.Name) (str expr1) (str expr2) (str expr3)
        | IfThenElse(expr1, expr2, expr3) -> 
            sprintf "(if %s then %s else %s)" (str expr1) (str expr2) (str expr3)
        | Lambda(var1, expr) -> 
            sprintf "(fun (%s : %s) -> %s)" var1.Name (typeStr var1.Type) (str expr)
        | LetRecursive(varExprList, expr) -> 
            let mutable flag = true
            let s = 
                varExprList
                |> List.map 
                    (fun (v,e) ->
                        let l = 
                            if flag then
                                flag <- false
                                "let"
                            else
                                "and"
                        sprintf "%s (%s : %s) = (%s)" l v.Name (typeStr v.Type) (str e)
                    )
                |> String.concat " "
            s + " in " + sprintf "(%s)" (str expr)
        | Let(var, expr1, expr2) ->
            sprintf "let %s : %s = (%s) in (%s)" var.Name (typeStr var.Type) (str expr1) (str expr2)
        | NewArray(type1, exprList) -> 
            sprintf "[|%s|]" (exprList |> List.map (str >> sprintf "(%s)") |> String.concat ";")
        | NewDelegate(type1, varList, expr) -> failwith "NewDelegate(type1, varList, expr)"
        | NewObject(constructorInfo, exprList) -> 
            sprintf "(new %s(%s))"(typeStr constructorInfo.DeclaringType) (exprList |> List.map (str >> sprintf "(%s)") |> String.concat ",")
        | NewRecord(type1, exprList) -> failwith "NewRecord(type1, exprList)"
        | NewTuple(exprList) -> 
            sprintf "(%s)" (exprList |> List.map (str >> sprintf "(%s)") |> String.concat ",")
        | NewUnionCase(unionCaseInfo, exprList) -> 
            sprintf "(%s.%s(%s))"(typeStr unionCaseInfo.DeclaringType) unionCaseInfo.Name (exprList |> List.map (str >> sprintf "(%s)") |> String.concat ",")
        | PropertyGet(None, propertyInfo, exprList) -> 
            sprintf "(%s.%s(%s))"(typeStr propertyInfo.DeclaringType) propertyInfo.Name (exprList |> List.map (str >> sprintf "(%s)") |> String.concat ",")
        | PropertyGet(Some expr, propertyInfo, exprList) -> 
            sprintf "((%s).%s(%s))"(str expr) propertyInfo.Name (exprList |> List.map (str >> sprintf "(%s)") |> String.concat ",")
        | PropertySet(None, propertyInfo, exprList, expr) -> 
            sprintf "(%s.%s(%s)) <- (%s)"(typeStr propertyInfo.DeclaringType) propertyInfo.Name (exprList |> List.map (str >> sprintf "(%s)") |> String.concat ",") (str expr)
        | PropertySet(Some expr, propertyInfo, exprList, exprv) -> 
            sprintf "((%s).%s(%s)) <- (%s)"(str expr) propertyInfo.Name (exprList |> List.map (str >> sprintf "(%s)") |> String.concat ",") (str exprv)
        | QuoteTyped(expr) -> sprintf "<@ %s @>" (str expr)
        | QuoteRaw(expr) -> sprintf "<@@ %s @@>" (str expr)
        | Sequential(expr1, expr2) -> sprintf "(%s);(%s)" (str expr1) (str expr2)
        | TryFinally(expr1, expr2) -> sprintf "(try (%s) finally (%s))" (str expr1) (str expr2)
        | TryWith(expr1, var1, expr2, var2, expr3) -> failwith "TryWith(expr1, var1, expr2, var2, expr3)"
        | TupleGet(expr, int1) -> failwith "TupleGet(expr, int1)"
        | TypeTest(expr, type1) -> sprintf "((%s) :? %s)" (str expr) (typeStr type1)
        | UnionCaseTest(expr, unionCaseInfo) -> failwith "UnionCaseTest(expr, unionCaseInfo)"
        //| ValueWithName(obj1, type1, name) when List.contains name vs -> name
        | Value(obj1, type1) -> 
            if type1 = typeof<string> then
                let s = obj1 :?> string
                "\"" + 
                    s.Replace("\"","\\\"").Replace("\t","\\t").Replace("\n","\\n").Replace("\r","\\r")
                    + "\""
            elif isNull obj1 then
                "null"
            else    
                obj1.ToString()
        | VarSet(var, expr) -> sprintf "%s <- (%s)" var.Name (str expr)
        | Var(var) -> sprintf "(%s) "var.Name
        | WhileLoop(expr1, expr2) -> 
            sprintf "(while (%s) do (%s))" (str expr1) (str expr2)
        | x -> failwithf "%A" x


    let rec expandLambda e = 
        match e with 
        | Patterns.Application(ExprShape.ShapeLambda(v, body), assign) -> 
            Expr.Let(v,assign,expandLambda body)
        | _ -> e

    let decomposeLetBindings e =    
        let rec loop acc e = 
            match e with 
            | Patterns.Let(v,ass,body) -> 
                loop ((v,ass) :: acc) body
            | _ -> acc, e
        loop [] e
        
    open System.Linq.Expressions

    let toFuncExpression (x : Expr<'a>) = 
        if FSharp.Reflection.FSharpType.IsFunction typeof<'a> then 
            let rec func (m : Expression) ps = 
                match m with 
                | :? MethodCallExpression as x when x.Arguments.Count = 1 && (x.Arguments.[0] :? LambdaExpression) -> 
                    let lambda = x.Arguments.[0] :?> LambdaExpression
                    func lambda.Body (lambda.Parameters.[0] :: ps)
                | _ -> Expression.Lambda(m, ps |> List.rev)
            func (FSharp.Linq.RuntimeHelpers.LeafExpressionConverter.QuotationToExpression(x)) [] :?> Expression<_>
        else
            Expression.Lambda(FSharp.Linq.RuntimeHelpers.LeafExpressionConverter.QuotationToExpression(x)) :?> Expression<_>
    
    let toFuncExpression0 (f : Expr<'a>) : Expression<Func<'a>> = toFuncExpression f
    let toFuncExpression1 (f : Expr<'a -> 'b>) : Expression<Func<'a,'b>> = toFuncExpression f
    let toFuncExpression2 (f : Expr<'a -> 'b -> 'c>) : Expression<Func<'a,'b,'c>> = toFuncExpression f
    let toFuncExpression3 (f : Expr<'a -> 'b -> 'c -> 'd>) : Expression<Func<'a,'b,'c,'d>> = toFuncExpression f
    let toFuncExpression4 (f : Expr<'a -> 'b -> 'c -> 'd -> 'e>) : Expression<Func<'a,'b,'c,'d,'e>> = toFuncExpression f
    let toFuncExpression5 (f : Expr<'a -> 'b -> 'c -> 'd -> 'e -> 'f>) : Expression<Func<'a,'b,'c,'d,'e,'f>> = toFuncExpression f 
    let toFuncExpression6 (f : Expr<'a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g>) : Expression<Func<'a,'b,'c,'d,'e,'f,'g>> = toFuncExpression f
    let toFuncExpression7 (f : Expr<'a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'h>) : Expression<Func<'a,'b,'c,'d,'e,'f,'g,'h>> = toFuncExpression f
    let toFuncExpression8 (f : Expr<'a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'h -> 'i>) : Expression<Func<'a,'b,'c,'d,'e,'f,'g,'h,'i>> = toFuncExpression f 
    
    let spliceInExpression (e : Expression) : 'a = failwith ""
    let spliceInExpressionTyped (e : Expression<'a>) : 'a = failwith ""
    
    let internal spliceMeth = (methodInfo <@ spliceInExpression @>).GetGenericMethodDefinition()
    let internal spliceTypedMeth = (methodInfo <@ spliceInExpressionTyped @>).GetGenericMethodDefinition()
    (*
    let rewriteExpressionSplices (q : Expr<'a>) = 
        let (|Quote|_|) (e : Expr) (x : Expr) = 
            let _,_,y = exprMatch e x
            if y then Some () else None
        let (|BindQuote|_|) (e : Expr) (x : Expr) = 
            let a,b,y = exprMatch e x
            if y then Some (a,b) else None
        let (|AnyMarker|_|) k (anyType : IDictionary<string,Expr>, typed : IDictionary<string,Expr>) = 
            let scc,v = anyType.TryGetValue k
            if scc then Some v else None
        let (|TypedMarker|_|) k (anyType : IDictionary<string,Expr>, typed : IDictionary<string,Expr>) = 
            let scc,v = typed.TryGetValue k
            if scc then Some v else None
        q
        |> applySub
            (fun l x ->
                match x with
                | BindQuote <@ spliceInExpression (withType "e" : Expression<AnyType>) : AnyType @> (TypedMarker "e" e)
                | BindQuote <@ spliceInExpression (withType "e" : Expression) : AnyType @> (TypedMarker "e" e) ->
                    let expr = evaluateUntyped e :?> Expression
                    if expr.Type = x.Type then 
                        None
                    else
                        let newq = <@ FuncConvert.FromFunc (Operators.splice x)@> |> expandSplices 
                        Some(x,newq)
                | _ -> None
            )
    *)
    let expandExpressionSplices (e : 'e) = 
        let visitor = 
            {new ExpressionVisitor() with 
                member x.VisitMethodCall(e : MethodCallExpression) =
                    if e.Method.IsStatic && e.Method.IsGenericMethod && e.Method.GetGenericMethodDefinition() = spliceMeth then 
                        let a = Expression.Lambda(e.Arguments.[0],[]).Compile().DynamicInvoke() :?> Expression
                        //let intp = a.Type
                        //let expected = e.Method.ReturnType
                        //if intp = expected then 
                        //    a
                        //else
                        //    FuncConvert.
                        a
                    elif e.Method.IsStatic && e.Method.IsGenericMethod && e.Method.GetGenericMethodDefinition() = spliceTypedMeth then 
                        Expression.Lambda(e.Arguments.[0],[]).Compile().DynamicInvoke() :?> Expression
                    else
                        Expression.Call(x.Visit(e.Object), e.Method, e.Arguments |> Seq.map x.Visit) :> _
            }
        visitor.VisitAndConvert<'e>(e, "expandExpressionSplices")
    
    let rec exists f (q : Expr) = 
        if f q then 
            true
        else
            match q with
            | ShapeCombinationUnchecked(a, args) -> args |> List.exists (exists f)
            | ShapeLambdaUnchecked(v, body) -> exists f body
            | ShapeVarUnchecked(v) -> false
    
    let rec contains k (q : Expr)  = 
        match q with
        | Quote k -> true
        | ShapeCombinationUnchecked(a, args) -> args |> List.exists (contains k)
        | ShapeLambdaUnchecked(v, body) -> contains k body
        | ShapeVarUnchecked(v) -> false


    module internal Patterns = 

        let (|MethodCall|_|) (minfo : MethodInfo) = function
            | Patterns.Call (o, methodInfo, args) when methodInfo.Name = minfo.Name ->
                if methodInfo.IsGenericMethod then
                    let generic = methodInfo.GetGenericMethodDefinition() 
                    if minfo = generic then
                        let genericArgs = methodInfo.GetGenericArguments ()
                        Some (o, genericArgs, args)
                    else
                        None
                elif minfo = methodInfo then
                    Some (o, [||], args)
                else None
            | _ -> None
        let (|PropName|_|) name (p : PropertyInfo) = if p.Name = name then Some() else None

        let (|MethodName|_|) name (p : MethodInfo) = if p.Name = name then Some() else None
            
        let (|Quote|_|) (e : Expr) (x : Expr) = 
            let _,_,y = exprMatch e x
            if y then Some () else None

        let (|BindQuote|_|) (e : Expr) (x : Expr) = 
            let a,b,y = exprMatch e x
            if y then Some (a,b) else None

        let (|AnyMarker|_|) k (anyType : IDictionary<string,Expr>, typed : IDictionary<string,Expr>) = 
            let scc,v = anyType.TryGetValue k
            if scc then Some v else None
        
        let (|TypedMarker|_|) k (anyType : IDictionary<string,Expr>, typed : IDictionary<string,Expr>) = 
            let scc,v = typed.TryGetValue k
            if scc then Some v else None  
    open Patterns
    open Qit.ProviderImplementation.ProvidedTypes
    open ReflectionPatterns
    let compileLambdaWithRefs refs (q : Expr<'a>) = 
        let refs = 
            let ra = ResizeArray()
            q 
            |> traverseQuotation
                (fun x ->
                    match x with
                    | BindQuote <@ any "x" @> (AnyMarker "x" o) -> ra.Add o.Type.Assembly; None
                    | _ -> None
                )
            |> ignore
            Seq.append ra refs |> Seq.distinct |> Seq.toArray
        let asm = ProvidedAssembly()
        let t = ProvidedTypeDefinition(asm,"ns","tp",Some typeof<obj>,isErased=false)
        let m, build = 
            let rec f q (args : Expr list) = 
                match q,args with 
                | Lambda(v,body), h :: t -> 
                    f (body.Substitute(fun x -> if x = v then Some (h) else None)) t
                | Lambda(_, body), [] -> body
                | _,[] -> q
                | _ -> failwithf "Unexpected %A" (q,args)
            match typeof<'a> with 
            | FSharpFuncType (d,r) when d.Length = 1 && d.[0] = typeof<unit> -> 
                ProvidedMethod("meth", [], r, invokeCode = f q, isStatic = true), (fun mt -> Expr.Lambda(Var("", typeof<unit>), Expr.Call(mt, [])))
            | FSharpFuncType (d,r) ->  
                let args = d |> List.mapi (fun i t -> ProvidedParameter("p" + string i, t))
                let vs = args |> List.map (fun a -> Var(a.Name, a.ParameterType))
                let g mt = 
                    vs
                    |> List.foldBack (fun a body -> Expr.Lambda(a,body) )
                    <| Expr.Call(mt, vs |> List.map Expr.Var)
                ProvidedMethod("meth", args, r, invokeCode = f q, isStatic = true), g
            | _ -> 
                ProvidedMethod("meth", [], typeof<'a>, invokeCode = f q, isStatic = true), (fun mt -> Expr.Lambda(Var("", typeof<unit>), Expr.Call(mt, [])))
        t.AddMember m
        asm.AddTypes [t]
        let ctx = ProvidedTypesContext(refs |> Seq.filter (fun x -> not x.IsDynamic) |> Seq.map (fun x -> x.Location) |> Seq.toList, [], refs |> Seq.toList)//[System.Reflection.Assembly.GetExecutingAssembly()])
        let t2 = ctx.ConvertSourceProvidedTypeDefinitionToTarget(t)
        let compiler = AssemblyCompiler(t2.Assembly :?> _, ctx)
        let bytes = compiler.Compile(false)
        let a = System.Reflection.Assembly.Load(bytes)
        let r = a.GetTypes() |> Seq.head
        let mt = r.GetMethod("meth")
        FSharp.Linq.RuntimeHelpers.LeafExpressionConverter.EvaluateQuotation(build mt) :?> 'a
    let compileLambda q = compileLambdaWithRefs [] q
 
        

[<AutoOpen>]
module Extensions =
    open System.Linq.Expressions
    type Expression with 
        //static member Func(f : Expr<'a>) : Expression<Func<'a>> = Quote.toFuncExpression f
        static member Func(f : Expr<'a -> 'b>) : Expression<Func<'a,'b>> = Quote.toFuncExpression f
        static member Func(f : Expr<'a -> 'b -> 'c>) : Expression<Func<'a,'b,'c>> = Quote.toFuncExpression f
        static member Func(f : Expr<'a -> 'b -> 'c -> 'd>) : Expression<Func<'a,'b,'c,'d>> = Quote.toFuncExpression f
        static member Func(f : Expr<'a -> 'b -> 'c -> 'd -> 'e>) : Expression<Func<'a,'b,'c,'d,'e>> = Quote.toFuncExpression f
        static member Func(f : Expr<'a -> 'b -> 'c -> 'd -> 'e -> 'f>) : Expression<Func<'a,'b,'c,'d,'e,'f>> = Quote.toFuncExpression f
        static member Func(f : Expr<'a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g>) : Expression<Func<'a,'b,'c,'d,'e,'f,'g>> = Quote.toFuncExpression f
        static member Func(f : Expr<'a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'h>) : Expression<Func<'a,'b,'c,'d,'e,'f,'g,'h>> = Quote.toFuncExpression f
        static member Func(f : Expr<'a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'h -> 'i>) : Expression<Func<'a,'b,'c,'d,'e,'f,'g,'h,'i>> = Quote.toFuncExpression f


open Quote

type TypeTemplate<'a>() =  
    static let cache = Dictionary<MethodInfo, Dictionary<Type list, 'a>>()
    static let tryCache minfo (types : Type list) builder = 
        let scc,lu2 = cache.TryGetValue(minfo)
        if scc then 
            let scc,v = lu2.TryGetValue(types)
            if scc then 
                v
            else
                let v = builder()
                lu2.[types] <- v
                v
        else
            let lu2 = Dictionary()
            let v = builder()
            lu2.[types] <- v
            cache.[minfo] <- lu2
            v
    static member create ([<ReflectedDefinition(false)>] f : Expr<'a>) : Type list -> 'a  = 
        let makeMethod (minfo : MethodInfo) =
            if minfo.IsGenericMethod then
                let minfodef = minfo.GetGenericMethodDefinition()
                fun types -> minfodef.MakeGenericMethod(types |> Seq.toArray)
            else
                fun _ -> minfo
        match f with
        | DerivedPatterns.Lambdas(vs, Patterns.Call(o,minfo,args)) -> 
            let makeMethod = makeMethod minfo
            fun types -> 
                tryCache minfo types
                    (fun () ->
                        let method = makeMethod types
                        let lambda = 
                            let call = 
                                match o with 
                                | Some o -> Expr.Call(o,method,args)
                                | None -> Expr.Call(method,args)
                            (vs, call)
                            ||> List.foldBack
                                (fun v s -> 
                                    match v with 
                                    | [v] -> Expr.Lambda(v,s) 
                                    | l -> failwith "'lambas' tuple not suported" 
                                )
                        FSharp.Linq.RuntimeHelpers.LeafExpressionConverter.EvaluateQuotation lambda :?> 'a)
        | Patterns.Call(o,minfo,args) -> 
            let makeMethod = makeMethod minfo
            fun types -> 
                tryCache minfo types
                    (fun () ->
                        let method = makeMethod types
                        let parameters = method.GetParameters()
                        let vars = Array.init parameters.Length (fun i -> Var(sprintf "v%d" i, parameters.[i].ParameterType))
                        let body = 
                            match o with
                            | Some o -> Expr.Call(o,minfo,vars |> Array.map Expr.Var |> Array.toList)
                            | None -> Expr.Call(minfo,vars |> Array.map Expr.Var |> Array.toList)
                        let lambda = Array.foldBack (fun x s -> Expr.Lambda(x,s)) vars body
                        FSharp.Linq.RuntimeHelpers.LeafExpressionConverter.EvaluateQuotation lambda :?> 'a)
        | _ -> failwithf "Expecting Expr.Call got: \r\n --------- \r\n %A \r\n ---------" f

type ITemp<'b> =    
    abstract member Def<'a> : unit -> 'b

[<AutoOpen>]
module ITempExt = 
    type ITemp<'b> with 
        member x.Make (t:Type seq) = 
            let t = t |> Seq.toArray
            let t = 
                if t.Length > 1 then 
                    [| FSharp.Reflection.FSharpType.MakeTupleType (t) |]
                else
                    t
            typeof<ITemp<'b>>.GetMethod("Def").MakeGenericMethod(t).Invoke(x,[||]) :?> 'b
