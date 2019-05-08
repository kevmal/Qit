namespace Qit

open System
open Microsoft.FSharp.Core.CompilerServices
open System.Reflection
open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Quotations.Patterns
open System.Collections.Generic
open ProviderImplementation.ProvidedTypes


module Expression = 
    open System.Linq.Expressions
    let evaluate (e : Expression) = 
        match e with 
        | :? LambdaExpression as f -> f.Compile().DynamicInvoke()
        | _ -> Expression.Lambda(e, []).Compile().DynamicInvoke()


// Right from type provider SDK ProvidedTypes.fs
[<AutoOpen>]
module UncheckedQuotations =

    let qTy = typeof<Var>.Assembly.GetType("Microsoft.FSharp.Quotations.ExprConstInfo")
    assert (not (isNull qTy))
    let pTy = typeof<Var>.Assembly.GetType("Microsoft.FSharp.Quotations.PatternsModule")
    assert (not (isNull pTy))
    
    let bindAll = BindingFlags.DeclaredOnly ||| BindingFlags.Public ||| BindingFlags.NonPublic ||| BindingFlags.Static ||| BindingFlags.Instance
    // These are handles to the internal functions that create quotation nodes of different sizes. Although internal,
    // these function names have been stable since F# 2.0.
    let mkFE0 = pTy.GetMethod("mkFE0", bindAll)
    assert (not (isNull mkFE0))
    let mkFE1 = pTy.GetMethod("mkFE1", bindAll)
    assert (not (isNull mkFE1))
    let mkFE2 = pTy.GetMethod("mkFE2", bindAll)
    assert (mkFE2 |> isNull |> not)
    let mkFE3 = pTy.GetMethod("mkFE3", bindAll)
    assert (mkFE3 |> isNull |> not)
    let mkFEN = pTy.GetMethod("mkFEN", bindAll)
    assert (mkFEN |> isNull |> not)

    // These are handles to the internal tags attached to quotation nodes of different sizes. Although internal,
    // these function names have been stable since F# 2.0.
    let newDelegateOp = qTy.GetMethod("NewNewDelegateOp", bindAll)
    assert (newDelegateOp |> isNull |> not)
    let instanceCallOp = qTy.GetMethod("NewInstanceMethodCallOp", bindAll)
    assert (instanceCallOp |> isNull |> not)
    let staticCallOp = qTy.GetMethod("NewStaticMethodCallOp", bindAll)
    assert (staticCallOp |> isNull |> not)
    let newObjectOp = qTy.GetMethod("NewNewObjectOp", bindAll)
    assert (newObjectOp |> isNull |> not)
    let newArrayOp = qTy.GetMethod("NewNewArrayOp", bindAll)
    assert (newArrayOp |> isNull |> not)
    let appOp = qTy.GetMethod("get_AppOp", bindAll)
    assert (appOp |> isNull |> not)
    let instancePropGetOp = qTy.GetMethod("NewInstancePropGetOp", bindAll)
    assert (instancePropGetOp |> isNull |> not)
    let staticPropGetOp = qTy.GetMethod("NewStaticPropGetOp", bindAll)
    assert (staticPropGetOp |> isNull |> not)
    let instancePropSetOp = qTy.GetMethod("NewInstancePropSetOp", bindAll)
    assert (instancePropSetOp |> isNull |> not)
    let staticPropSetOp = qTy.GetMethod("NewStaticPropSetOp", bindAll)
    assert (staticPropSetOp |> isNull |> not)
    let instanceFieldGetOp = qTy.GetMethod("NewInstanceFieldGetOp", bindAll)
    assert (instanceFieldGetOp |> isNull |> not)
    let staticFieldGetOp = qTy.GetMethod("NewStaticFieldGetOp", bindAll)
    assert (staticFieldGetOp |> isNull |> not)
    let instanceFieldSetOp = qTy.GetMethod("NewInstanceFieldSetOp", bindAll)
    assert (instanceFieldSetOp |> isNull |> not)
    let staticFieldSetOp = qTy.GetMethod("NewStaticFieldSetOp", bindAll)
    assert (staticFieldSetOp |> isNull |> not)
    let tupleGetOp = qTy.GetMethod("NewTupleGetOp", bindAll)
    assert (tupleGetOp |> isNull |> not)
    let letOp = qTy.GetMethod("get_LetOp", bindAll)
    assert (letOp |> isNull |> not)
    let forIntegerRangeLoopOp = qTy.GetMethod("get_ForIntegerRangeLoopOp", bindAll)
    assert (forIntegerRangeLoopOp |> isNull |> not)
    let whileLoopOp = qTy.GetMethod("get_WhileLoopOp", bindAll)
    assert (whileLoopOp |> isNull |> not)
    let ifThenElseOp = qTy.GetMethod("get_IfThenElseOp", bindAll)
    assert (ifThenElseOp |> isNull |> not)
    let newUnionCaseOp = qTy.GetMethod("NewNewUnionCaseOp", bindAll)
    assert (newUnionCaseOp |> isNull |> not)

    type Microsoft.FSharp.Quotations.Expr with

        static member NewDelegateUnchecked (ty: Type, vs: Var list, body: Expr) =
            let e =  List.foldBack (fun v acc -> Expr.Lambda(v,acc)) vs body
            let op = newDelegateOp.Invoke(null, [| box ty |])
            mkFE1.Invoke(null, [| box op; box e |]) :?> Expr

        static member NewObjectUnchecked (cinfo: ConstructorInfo, args: Expr list) =
            let op = newObjectOp.Invoke(null, [| box cinfo |])
            mkFEN.Invoke(null, [| box op; box args |]) :?> Expr

        static member NewArrayUnchecked (elementType: Type, elements: Expr list) =
            let op = newArrayOp.Invoke(null, [| box elementType |])
            mkFEN.Invoke(null, [| box op; box elements |]) :?> Expr

        static member CallUnchecked (minfo: MethodInfo, args: Expr list) =
            let op = staticCallOp.Invoke(null, [| box minfo |])
            mkFEN.Invoke(null, [| box op; box args |]) :?> Expr

        static member CallUnchecked (obj: Expr, minfo: MethodInfo, args: Expr list) =
            let op = instanceCallOp.Invoke(null, [| box minfo |])
            mkFEN.Invoke(null, [| box op; box (obj::args) |]) :?> Expr

        static member ApplicationUnchecked (f: Expr, x: Expr) =
            let op = appOp.Invoke(null, [| |])
            mkFE2.Invoke(null, [| box op; box f; box x |]) :?> Expr

        static member PropertyGetUnchecked (pinfo: PropertyInfo, args: Expr list) =
            let op = staticPropGetOp.Invoke(null, [| box pinfo |])
            mkFEN.Invoke(null, [| box op; box args |]) :?> Expr

        static member PropertyGetUnchecked (obj: Expr, pinfo: PropertyInfo, ?args: Expr list) =
            let args = defaultArg args []
            let op = instancePropGetOp.Invoke(null, [| box pinfo |])
            mkFEN.Invoke(null, [| box op; box (obj::args) |]) :?> Expr

        static member PropertySetUnchecked (pinfo: PropertyInfo, value: Expr, ?args: Expr list) =
            let args = defaultArg args []
            let op = staticPropSetOp.Invoke(null, [| box pinfo |])
            mkFEN.Invoke(null, [| box op; box (args@[value]) |]) :?> Expr

        static member PropertySetUnchecked (obj: Expr, pinfo: PropertyInfo, value: Expr, ?args: Expr list) =
            let args = defaultArg args []
            let op = instancePropSetOp.Invoke(null, [| box pinfo |])
            mkFEN.Invoke(null, [| box op; box (obj::(args@[value])) |]) :?> Expr

        static member FieldGetUnchecked (pinfo: FieldInfo) =
            let op = staticFieldGetOp.Invoke(null, [| box pinfo |])
            mkFE0.Invoke(null, [| box op; |]) :?> Expr

        static member FieldGetUnchecked (obj: Expr, pinfo: FieldInfo) =
            let op = instanceFieldGetOp.Invoke(null, [| box pinfo |])
            mkFE1.Invoke(null, [| box op; box obj |]) :?> Expr

        static member FieldSetUnchecked (pinfo: FieldInfo, value: Expr) =
            let op = staticFieldSetOp.Invoke(null, [| box pinfo |])
            mkFE1.Invoke(null, [| box op; box value |]) :?> Expr

        static member FieldSetUnchecked (obj: Expr, pinfo: FieldInfo, value: Expr) =
            let op = instanceFieldSetOp.Invoke(null, [| box pinfo |])
            mkFE2.Invoke(null, [| box op; box obj; box value |]) :?> Expr

        static member TupleGetUnchecked (e: Expr, n:int) =
            let op = tupleGetOp.Invoke(null, [| box e.Type; box n |])
            mkFE1.Invoke(null, [| box op; box e |]) :?> Expr

        static member LetUnchecked (v:Var, e: Expr, body:Expr) =
            let lam = Expr.Lambda(v,body)
            let op = letOp.Invoke(null, [| |])
            mkFE2.Invoke(null, [| box op; box e; box lam |]) :?> Expr

        static member ForIntegerRangeLoopUnchecked (loopVariable, startExpr:Expr, endExpr:Expr, body:Expr) = 
            let lam = Expr.Lambda(loopVariable, body)
            let op = forIntegerRangeLoopOp.Invoke(null, [| |])
            mkFE3.Invoke(null, [| box op; box startExpr; box endExpr; box lam |] ) :?> Expr

        static member WhileLoopUnchecked (guard:Expr, body:Expr) = 
            let op = whileLoopOp.Invoke(null, [| |])
            mkFE2.Invoke(null, [| box op; box guard; box body |] ):?> Expr

        static member IfThenElseUnchecked (e:Expr, t:Expr, f:Expr) = 
            let op = ifThenElseOp.Invoke(null, [| |])
            mkFE3.Invoke(null, [| box op; box e; box t; box f |] ):?> Expr

        static member NewUnionCaseUnchecked (uci:Reflection.UnionCaseInfo, args:Expr list) = 
            let op = newUnionCaseOp.Invoke(null, [| box uci |])
            mkFEN.Invoke(null, [| box op; box args |]) :?> Expr
            
    type Shape = Shape of (Expr list -> Expr)

    let (|ShapeCombinationUnchecked|ShapeVarUnchecked|ShapeLambdaUnchecked|) e =
        match e with
        | NewObject (cinfo, args) ->
            ShapeCombinationUnchecked (Shape (function args -> Expr.NewObjectUnchecked (cinfo, args)), args)
        | NewArray (ty, args) ->
            ShapeCombinationUnchecked (Shape (function args -> Expr.NewArrayUnchecked (ty, args)), args)
        | NewDelegate (t, vars, expr) ->
            ShapeCombinationUnchecked (Shape (function [expr] -> Expr.NewDelegateUnchecked (t, vars, expr) | _ -> invalidArg "expr" "invalid shape"), [expr])
        | TupleGet (expr, n) ->
            ShapeCombinationUnchecked (Shape (function [expr] -> Expr.TupleGetUnchecked (expr, n) | _ -> invalidArg "expr" "invalid shape"), [expr])
        | Application (f, x) ->
            ShapeCombinationUnchecked (Shape (function [f; x] -> Expr.ApplicationUnchecked (f, x) | _ -> invalidArg "expr" "invalid shape"), [f; x])
        | Call (objOpt, minfo, args) ->
            match objOpt with
            | None -> ShapeCombinationUnchecked (Shape (function args -> Expr.CallUnchecked (minfo, args)), args)
            | Some obj -> ShapeCombinationUnchecked (Shape (function (obj::args) -> Expr.CallUnchecked (obj, minfo, args) | _ -> invalidArg "expr" "invalid shape"), obj::args)
        | PropertyGet (objOpt, pinfo, args) ->
            match objOpt with
            | None -> ShapeCombinationUnchecked (Shape (function args -> Expr.PropertyGetUnchecked (pinfo, args)), args)
            | Some obj -> ShapeCombinationUnchecked (Shape (function (obj::args) -> Expr.PropertyGetUnchecked (obj, pinfo, args) | _ -> invalidArg "expr" "invalid shape"), obj::args)
        | PropertySet (objOpt, pinfo, args, value) ->
            match objOpt with
            | None -> ShapeCombinationUnchecked (Shape (function (value::args) -> Expr.PropertySetUnchecked (pinfo, value, args) | _ -> invalidArg "expr" "invalid shape"), value::args)
            | Some obj -> ShapeCombinationUnchecked (Shape (function (obj::value::args) -> Expr.PropertySetUnchecked (obj, pinfo, value, args) | _ -> invalidArg "expr" "invalid shape"), obj::value::args)
        | FieldGet (objOpt, pinfo) ->
            match objOpt with
            | None -> ShapeCombinationUnchecked (Shape (function _ -> Expr.FieldGetUnchecked (pinfo)), [])
            | Some obj -> ShapeCombinationUnchecked (Shape (function [obj] -> Expr.FieldGetUnchecked (obj, pinfo) | _ -> invalidArg "expr" "invalid shape"), [obj])
        | FieldSet (objOpt, pinfo, value) ->
            match objOpt with
            | None -> ShapeCombinationUnchecked (Shape (function [value] -> Expr.FieldSetUnchecked (pinfo, value) | _ -> invalidArg "expr" "invalid shape"), [value])
            | Some obj -> ShapeCombinationUnchecked (Shape (function [obj;value] -> Expr.FieldSetUnchecked (obj, pinfo, value) | _ -> invalidArg "expr" "invalid shape"), [obj; value])
        | Let (var, value, body) ->
            ShapeCombinationUnchecked (Shape (function [value;Lambda(var, body)] -> Expr.LetUnchecked(var, value, body) | _ -> invalidArg "expr" "invalid shape"), [value; Expr.Lambda(var, body)])
        | ForIntegerRangeLoop (loopVar, first, last, body) ->
            ShapeCombinationUnchecked (Shape (function [first; last; Lambda(loopVar, body)] -> Expr.ForIntegerRangeLoopUnchecked (loopVar, first, last, body) | _ -> invalidArg "expr" "invalid shape"), [first; last; Expr.Lambda(loopVar, body)])
        | WhileLoop (cond, body) ->
            ShapeCombinationUnchecked (Shape (function [cond; body] -> Expr.WhileLoopUnchecked (cond,  body) | _ -> invalidArg "expr" "invalid shape"), [cond; body])
        | IfThenElse (g, t, e) ->
            ShapeCombinationUnchecked (Shape (function [g; t; e] -> Expr.IfThenElseUnchecked (g, t, e) | _ -> invalidArg "expr" "invalid shape"), [g; t; e])
        | TupleGet (expr, i) ->
            ShapeCombinationUnchecked (Shape (function [expr] -> Expr.TupleGetUnchecked (expr, i) | _ -> invalidArg "expr" "invalid shape"), [expr])
        | ExprShape.ShapeCombination (comb,args) ->
            ShapeCombinationUnchecked (Shape (fun args -> ExprShape.RebuildShapeCombination(comb, args)), args)
        | ExprShape.ShapeVar v -> ShapeVarUnchecked v
        | ExprShape.ShapeLambda (v, e) -> ShapeLambdaUnchecked (v,e)

    let RebuildShapeCombinationUnchecked (Shape comb,args) = 
        printfn "UNCHECKED %A" args
        comb args

    let rec traverseQuotation f q = 
        let q = defaultArg (f q) q
        match q with
        | ShapeCombinationUnchecked(a, args) -> 
            let nargs = args |> List.map (traverseQuotation f)
            RebuildShapeCombinationUnchecked(a, nargs)
        | ShapeLambdaUnchecked(v, body) -> Expr.Lambda(v, traverseQuotation f body)
        | ShapeVarUnchecked(v) -> Expr.Var(v)


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

module Operators = 
    
    type Splice() = class end
        //static member Var


    let spliceVar (o : 'a) (v : Var) (e : Expr) : 'r = failwith "spliceVar"

    let spliceInto (v : 'a) (f : (Expr -> Expr)) : 'b = failwith "spliceInto"
    let splice2Into (a : 'a) (b : 'b) (f : (Expr -> Expr -> Expr)) : 'c = failwith "splice2Into"
    let splice3Into (a : 'a) (b : 'b) (c : 'c) (f : (Expr -> Expr -> Expr -> Expr)) : 'd = failwith "splice3Into"
    let splice (e : Expr) : 'b = failwith "spliceInto"

    [<ReflectedDefinition>]
    let fieldGet (field : FieldInfo) (o : 'a) : 'b = 
        spliceInto o (fun o -> Expr.FieldGetUnchecked(o,field))
    [<ReflectedDefinition>]
    let fieldGetStatic (field : FieldInfo) : 'a = 
        splice (Expr.FieldGetUnchecked(field))
    [<ReflectedDefinition>]
    let fieldSet (field : FieldInfo) (value : 'a) (o : 'b) : unit =
        spliceInto o
            (fun o ->
                spliceInto value 
                    (fun value -> 
                        Expr.FieldSetUnchecked(o,field,value))
            )

    [<ReflectedDefinition>]
    let fieldSetStatic (field : FieldInfo) (value : 'a) : unit = 
        spliceInto value (fun value -> Expr.FieldSetUnchecked(field,value)) 
        
    [<ReflectedDefinition>]
    let methodCall (method : MethodInfo) (args : obj list) (o : 'a) : 'b = failwith "methodCall"
    [<ReflectedDefinition>]
    let methodCallStatic (method : MethodInfo) (args : obj list) : 'c  = failwith "methodCall"
    

type IHole = 
    abstract member Action : Expr list * Expr -> Expr*Expr
type IHole<'a> = 
    inherit IHole
    abstract member Marker : 'a

module Quote =
    let toExpression (q : Expr<'a>) = FSharp.Linq.RuntimeHelpers.LeafExpressionConverter.QuotationToExpression q  
    let evaluate(q : Expr<'a>) = FSharp.Linq.RuntimeHelpers.LeafExpressionConverter.EvaluateQuotation q :?> 'a  
    let evaluateUntyped(q : Expr) = FSharp.Linq.RuntimeHelpers.LeafExpressionConverter.EvaluateQuotation q
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

    let methodInfo q =
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

    //http://www.fssnip.net/1i/title/Traverse-quotation
    let rec traverseQuotation f q = 
        let q = defaultArg (f q) q
        match q with
        | ExprShape.ShapeCombination(a, args) -> 
            let nargs = args |> List.map (traverseQuotation f)
            ExprShape.RebuildShapeCombination(a, nargs)
        | ExprShape.ShapeLambda(v, body) -> Expr.Lambda(v, traverseQuotation f body)
        | ExprShape.ShapeVar(v) -> Expr.Var(v)
        
    //let intoExpr (x : 'a) : Expr = <@@ () @@> //failwith "quoted code to Expr type"
    let spliceUntyped (x : Expr) : 'a = Unchecked.defaultof<_> //failwith "quoted code to Expr type"
    let spliceUntypedMeth = (methodInfo <@ spliceUntyped @>).GetGenericMethodDefinition()
    let splice (x : Expr<'a>) : 'a = Unchecked.defaultof<_> //failwith "quoted code to Expr type"
    let splice2Meth = (methodInfo <@ splice @>).GetGenericMethodDefinition()
    let expandSpliceOp (expr : Expr) = 
        let rec loop inSplice expr = 
            expr
            |> traverseQuotation
                (fun q -> 
                    match q with 
                    | Patterns.Call(None, minfo, [e]) when minfo.IsGenericMethod && minfo.GetGenericMethodDefinition() = splice2Meth -> 
                        Some(loop true e |> evaluateUntyped :?> _)
                    | Patterns.Call(None, minfo, [e]) when minfo.IsGenericMethod && minfo.GetGenericMethodDefinition() = spliceUntypedMeth -> 
                        Some(loop true e |> evaluateUntyped :?> _)
                    | Patterns.QuoteRaw q when inSplice -> 
                        Some(Expr.Value(loop false q))
                    | Patterns.QuoteTyped q when inSplice -> 
                        Some(Expr.Value(loop false q))
                    | _ -> None
                )
        loop false expr

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
            if a.IsGenericType && b.IsGenericType then 
                a.GetGenericTypeDefinition() = b.GetGenericTypeDefinition() &&
                    (Array.map2 typeEq (a.GetGenericArguments()) (b.GetGenericArguments())
                     |> Array.fold (&&) true)
            else
                a = typeof<AnyType> || b = typeof<AnyType> || a = b
        and propEq (a : PropertyInfo) (b : PropertyInfo) = 
            a = b || 
                (typeEq a.DeclaringType b.DeclaringType && a.Name = b.Name && typeEq a.PropertyType b.PropertyType)
        and methEq (a : MethodInfo) (b : MethodInfo) = 
            a = b || 
                (a.IsGenericMethod && b.IsGenericMethod && a.GetGenericMethodDefinition() = b.GetGenericMethodDefinition() &&
                    (
                        let args1 = a.GetGenericArguments()
                        let args2 = b.GetGenericArguments()
                        args1.Length = args2.Length &&
                            (Array.map2 
                                (fun x1 x2 ->
                                    x1 = typeof<AnyType> || x2 = typeof<AnyType> || x1 = x2
                                ) args1 args2
                             |> Array.reduce (&&))
                    ))
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
        

    let rewriter (input : 'input) (f : Expr list -> Expr -> Expr -> (Expr*Expr) option) : 'a = Unchecked.defaultof<'a>
    let internal rewriterMeth = (methodInfo <@ rewriter @>).GetGenericMethodDefinition()
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
    open ProviderImplementation.ProvidedTypes
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
        let ctx = ProvidedTypesContext(refs |> Seq.map (fun x -> x.Location) |> Seq.toList, [], refs |> Seq.toList)//[System.Reflection.Assembly.GetExecutingAssembly()])
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
type TypeTemplate = TypeTemplate with 
    static member inline create ([<ReflectedDefinition(false)>] f : Expr<'a>) : Type seq -> 'a  = 
        let rec extractCall e = 
            match e with
            | Patterns.Lambda(_,body) -> extractCall body
            | Patterns.Call(o,minfo,args) -> minfo
            | _ -> failwithf "Expression not of expected form %A" e
        match f with
        | Patterns.Lambda (_,e) -> 
            let minfo = extractCall e
            let makeMethod =
                if minfo.IsGenericMethod then
                    let typeArgs = minfo.GetGenericArguments()
                    let minfodef = minfo.GetGenericMethodDefinition()
                    fun types -> 
                        minfodef.MakeGenericMethod(types |> Seq.toArray)
                else
                    fun _ -> minfo
            fun types -> 
                let method = makeMethod types
                let lambda = 
                    f
                    |> traverseQuotation
                        (fun e -> 
                            match e with
                            | Patterns.Call(Some o,_,args) -> Some(Expr.Call(o,method,args))
                            | Patterns.Call(None,_,args) -> Some(Expr.Call(method,args))
                            | _ -> None
                        )
                FSharp.Linq.RuntimeHelpers.LeafExpressionConverter.EvaluateQuotation lambda :?> 'a

        | Patterns.Call(o,minfo,args) -> 
            let makeMethod =
                if minfo.IsGenericMethod then
                    let typeArgs = minfo.GetGenericArguments()
                    let minfodef = minfo.GetGenericMethodDefinition()
                    fun types -> 
                        minfodef.MakeGenericMethod(types |> Seq.toArray)
                else
                    fun _ -> minfo
            fun types -> 
                let method = makeMethod types
                let parameters = method.GetParameters()
                let vars = Array.init parameters.Length (fun i -> Var(sprintf "v%d" i, parameters.[i].ParameterType))
                let body = 
                    match o with
                    | Some o -> Expr.Call(o,minfo,vars |> Array.map Expr.Var |> Array.toList)
                    | None -> Expr.Call(minfo,vars |> Array.map Expr.Var |> Array.toList)
                let lambda = Array.foldBack (fun x s -> Expr.Lambda(x,s)) vars body
                FSharp.Linq.RuntimeHelpers.LeafExpressionConverter.EvaluateQuotation lambda :?> 'a
        | _ -> failwithf "Expecting Expr.Call got: \r\n --------- \r\n %A \r\n ---------" f

