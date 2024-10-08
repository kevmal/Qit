namespace Qit.Tests
open Qit
open System.Linq.Expressions
open Xunit
open System
open System.Reflection
open FSharp.Quotations

module Basic = 
    
    [<Fact>]
    let spliceInExpression1() = 
        let e = Quote.toExpression <@ 1 + 2 + 3 @>
        let testSplice = 
            <@
                10 - (QitOp.spliceInExpression e)
            @>
        let v =
            testSplice
            |> Quote.toExpression
            |> Quote.expandExpressionSplices
        let v = Assert.IsType<int>(v|> Expression.evaluate)
        Assert.Equal(4, v)
    
    [<Fact>]
    let ``spliceInExpression Func``() = 
        let e = Expression.Func <@ fun a -> 1 + 2 + a @>
        let v = 
            <@
                10 - ((QitOp.spliceInExpressionTyped e).Invoke 3)
            @>
            |> Quote.toExpression
            |> Quote.expandExpressionSplices
            |> Expression.evaluate
        let v = Assert.IsType<int>(v)
        Assert.Equal(4, v)
               
    [<Fact>]
    let ``splice untyped quote 1``() = 
        let v = 
            <@
                let a = 1
                let (b : int, c : int) = 
                    !%%(Expr.NewTuple [ <@@ a + 20 @@>; <@@ a - 20 @@> ])
                c,b,c
            @> 
            |> Quote.expandOperators
            |> Quote.evaluateUntyped
        Assert.Equal((-19, 21, -19), v :?> _)
                
    [<Fact>]
    let ``splice untyped quote 2``() = 
        let v = 
            <@
                let a = 1
                let (b : int, c : int) = 
                    !%%( Expr.NewTuple [ <@@ a + !%(<@ 20 @>) @@>; <@@ a - 20 @@> ] )
                c,b,c
            @> 
            |> Quote.expandOperators
            |> Quote.evaluateUntyped
        Assert.Equal((-19, 21, -19), v :?> _)
        
    [<Fact>]
    let ``splice typed quote 1``() = 
        let v = 
            <@
                let a = 1
                let b,c = 
                    !%(Expr.NewTuple [ <@@ a + 20 @@>; <@@ a - 20 @@> ] |> Expr.Cast<int*int>)
                c,b,c
            @> 
            |> Quote.expandOperators
            |> Quote.evaluateUntyped
        Assert.Equal((-19, 21, -19), v :?> _)
                
    [<Fact>]
    let ``splice typed quote 2``() = 
        let v = 
            <@
                let a = 1
                let b, c = 
                    !%( Expr.NewTuple [ <@@ a + !%(<@ 20 @>) @@>; <@@ a - 20 @@> ] |> Expr.Cast<int*int> )
                c,b,c
            @> 
            |> Quote.expandOperators
            |> Quote.evaluateUntyped
        Assert.Equal((-19, 21, -19), v :?> _)

    [<Fact>]
    let ``staging 1``() = 
        let rec spower (n : int) : Expr<int> -> Expr<int> =
            if n = 0 then fun _ -> <@ 1 @>
            elif n = 1 then fun t -> <@ %t @>
            else fun x -> <@ %x * (%spower (n-1) x) @>
        let lift (stagedComp : Expr<'T> -> Expr<'S>) : Expr<'T -> 'S> =
            <@ fun (t:'T) -> !% (stagedComp <@ t @>) @>
        let f = spower 10 |> lift |> Quote.expandOperators |> Quote.evaluate
        Assert.Equal(pown 2 10, f 2)
        Assert.Equal(1, f 1)
        let one = spower 0 |> lift |> Quote.expandOperators
        match one with 
        | Patterns.Lambda(v,e) -> 
            Assert.Equal(<@@ 1 @@>, e)
        | _ -> Assert.Equal(<@@ fun t -> 1 @@>.ToString(), one.ToString())
        

    let allStatic = BindingFlags.DeclaredOnly ||| BindingFlags.Public ||| BindingFlags.NonPublic ||| BindingFlags.Static
    
    [<QitOp; ReflectedDefinition>]
    let invokeStatic (tp : Type) (methodName : string) (parameters : 'a) : 'b = 
        splice(
            match <@ parameters @> with 
            | Patterns.NewTuple(exprs) -> 
                let ptypes = exprs |> List.map (fun x -> x.Type) |> List.toArray
                match tp.GetMethod(methodName,allStatic,null,ptypes,null) with
                | null -> failwithf "Method %s with paremters (%s) not found in %s" methodName (ptypes |> Array.map (fun x -> x.Name) |> String.concat ",") tp.Name
                | m -> Expr.Call(m, exprs) |> Expr.Cast<'b>
            | Quote <@@()@@> -> 
                match tp.GetMethod(methodName,allStatic,null,[||],null) with
                | null -> failwithf "Method %s with no paremters not found in %s" methodName tp.Name
                | m -> Expr.Call(m, []) |> Expr.Cast<'b>
            | expr -> 
                match tp.GetMethod(methodName,allStatic,null,[|expr.Type|],null) with
                | null -> failwithf "Method %s with paremters (%s) not found in %s" methodName expr.Type.Name tp.Name
                | m -> Expr.Call(m, [expr]) |> Expr.Cast<'b>
        )
    
    [<Fact>]
    let ``splice real test case 1 ``() =
        let v  =
            <@ 
                invokeStatic typeof<DateTime> "Parse" ("2010-10-10") : DateTime
            @>
            |> Quote.expandOperators
            |> Quote.evaluate
        Assert.Equal(DateTime(2010,10,10), v)
        
    type StaticMethodNoParameters() = 
        static member A() = "A"

    [<Fact>]
    let ``splice real test case 2 ``() =
        let v  =
            <@ 
                invokeStatic typeof<StaticMethodNoParameters> "A" () : string
            @>
            |> Quote.expandOperators
            |> Quote.evaluate
        Assert.Equal("A", v)
        
    [<Fact>]
    let ``splice in splice 1``() = 
        let a = 
            <@ 
                splice
                    (
                        let x = <@ 32 @>
                        <@
                            !%x
                        @>
                    )
            @>
        let v = a |> Quote.expandOperators |> Quote.evaluate
        Assert.Equal(32, v)

    [<Fact>]
    let ``splice in splice with sides 1``() = 
        let a = 
            <@ 
                fun (i : int) -> 
                    splice
                        (
                            let ra = ResizeArray()
                            <@ 
                                splice
                                    (
                                        ra.Add 1
                                        ra.Add 1
                                        ra.Add 1
                                        let x = <@ 32 @>
                                        <@
                                            !%x
                                        @>
                                    )
                            @> |> Quote.expandOperators |> ignore
                            let c = ra.Count
                            <@ c + i @>
                        )
            @>
        let v = a |> Quote.expandOperators |> Quote.evaluate
        Assert.Equal(5, v 2)
        
    [<ReflectedDefinition>]
    let (|TryExprValue|_|) (e : Expr<'a>) : 'a option = 
        try 
            Quote.evaluate e |> Some
        with 
        | _ -> None

    [<ReflectedDefinition; QitOp>]
    let spliceTestFunc lag = 
        splice 
            (
                match <@ lag @> with 
                | TryExprValue p -> 
                    let e = 
                        if p = 0 then 
                            <@ 
                                printfn "1"
                            @>
                        else 
                            <@
                                printfn "2"
                            @>
                    <@
                        !%e
                        printfn "0"
                        1
                    @>
                | _ -> 
                    <@
                        if lag > 0 then 
                            ()
                        2
                    @>
            )        
    
    [<Fact>]
    let ``splice in splice 2``() = 
        let a = <@ spliceTestFunc 1 @>
        let v = a |> Quote.expandOperators |> Quote.evaluate
        Assert.Equal(1, v)
        
    [<Fact>]
    let ``splice in splice 3``() = 
        let a = 
            <@ 
                splice
                    (
                        let f a = <@ a + a @>
                        <@
                            !%(f 21)
                        @>
                    )
            @>
        let v = a |> Quote.expandOperators 
        Assert.Equal(<@ 21 + 21 @>, v)
        Assert.Equal(42, v|> Quote.evaluate)
        
    [<Fact>]
    let ``splice in splice 4``() = 
        let a = 
            <@ 
                splice
                    (
                        let f a = <@ a + a @>
                        let foo a = 
                            <@
                                !%(f a)
                            @>
                        foo (23 + 32)
                    )
            @>
        let v = a |> Quote.expandOperators 
        Assert.Equal(<@ 55 + 55 @>, v)
        Assert.Equal(110, v|> Quote.evaluate)

    [<Fact>]
    let ``splice unchecked 1``() = 
        let expr = 
            <@@
                let ra = ResizeArray<int>()
                !%%(<@@ 234 @@>)
                ra.Add(!%%(<@@ "" @@>))
            @@>
        expr |> Quote.expandOperatorsUnchecked  |> ignore
      
    type TestObj1() = 
        inherit QitBindingObj()
        member val C = 0 with get,set
        [<QitOp; ReflectedDefinition>]
        member x.Bleh() = 
            splice (
                x.C <- x.C + 1
                Expr.Value x.C |> Expr.Cast<int>)


    [<Fact>]
    let ``splice QitObj 1``() = 
        let expr = 
            <@
                let a = TestObj1()
                let a1 = a.Bleh()
                let a2 = a.Bleh()
                let a3 = a.Bleh()
                let a4 = a.Bleh()
                a1,a2,a3,a4
            @>
        let v = 
            expr
            |> Quote.expandOperators 
            |> Quote.evaluate
        Assert.Equal((1,2,3,4), v)
         

    type TestObj2() = 
        inherit QitBindingObj()
        let mutable c = 0
        [<QitOp; ReflectedDefinition>]
        member x.Bleh() = 
            splice (
                c <- c + 1
                Expr.Value c |> Expr.Cast<int>)


    [<Fact>]
    let ``splice QitObj 2``() = 
        let expr = 
            <@
                let a = TestObj2()
                let a1 = a.Bleh()
                let a2 = a.Bleh()
                let a3 = a.Bleh()
                let a4 = a.Bleh()
                a1,a2,a3,a4
            @>
        let v = 
            expr
            |> Quote.expandOperators 
            |> Quote.evaluate
        Assert.Equal((1,2,3,4), v)
        
    let allInstance = BindingFlags.DeclaredOnly ||| BindingFlags.Public ||| BindingFlags.NonPublic ||| BindingFlags.Instance

    type RType(tp : Type, e : Expr) = 
        inherit QitBindingObj()
        let mutable v = None
        member x.GetVar() = 
            match v with 
            | Some v -> v
            | None -> 
                match x.Var with 
                | Some q -> 
                    v <- Some(Var(q.Name, e.Type, q.IsMutable))
                    x.GetVar()
                | None -> failwith "Unreachable"
        [<QitOp; ReflectedDefinition>]
        member x.Invoke(methodName : string, parameters : 'a) = 
            splice(
                let oexpr = Expr.Var(x.GetVar())
                match <@@ parameters @@> with 
                | Patterns.NewTuple(exprs) -> 
                    let ptypes = exprs |> List.map (fun x -> x.Type) |> List.toArray
                    match tp.GetMethod(methodName,allInstance,null,ptypes,null) with
                    | null -> failwithf "Method %s with paremters (%s) not found in %s" methodName (ptypes |> Array.map (fun x -> x.Name) |> String.concat ",") tp.Name
                    | m -> Expr.Call(oexpr, m, exprs) |> Expr.Cast<'b>
                | Quote <@@()@@> -> 
                    match tp.GetMethod(methodName,allInstance,null,[||],null) with
                    | null -> failwithf "Method %s with no paremters not found in %s" methodName tp.Name
                    | m -> Expr.Call(oexpr, m, []) |> Expr.Cast<'b>
                | expr -> 
                    match tp.GetMethod(methodName,allInstance,null,[|expr.Type|],null) with
                    | null -> failwithf "Method %s with paremters (%s) not found in %s" methodName expr.Type.Name tp.Name
                    | m -> Expr.Call(oexpr, m, [expr]) |> Expr.Cast<'b>
            )
        override x.Final(expr) = Expr.Let(x.GetVar(), e, expr)

    [<QitOp; ReflectedDefinition>]
    let makeObj (tp : Type) (parameters : 'a) : RType =         
        let e = 
            match <@@ parameters @@> with 
            | Patterns.NewTuple(exprs) -> 
                let ptypes = exprs |> List.map (fun x -> x.Type) |> List.toArray
                match tp.GetConstructor(BindingFlags.All,null,ptypes,null) with
                | null -> failwithf "Ctor with paremters (%s) not found in %s" (ptypes |> Array.map (fun x -> x.Name) |> String.concat ",") tp.Name
                | m -> Expr.NewObject(m, exprs) 
            | Quote <@@()@@> -> 
                match tp.GetConstructor(BindingFlags.All,null,[||],null) with
                | null -> failwithf "Ctor with no paremters not found in %s" tp.Name
                | m -> Expr.NewObject(m, [])
            | expr -> 
                match tp.GetConstructor(BindingFlags.All,null,[|expr.Type|],null) with
                | null -> failwithf "Ctor with paremters (%s) not found in %s" expr.Type.Name tp.Name
                | m -> Expr.NewObject(m, [expr])
        RType(tp,e)
 
    type TestObj(a : int) = 
        member x.Vall(b : int) = a + b
    
    [<Fact>]
    let ``splice QitObj 3``() = 
        let a = 
            <@
                let a = makeObj typeof<TestObj> 1
                let b : int = a.Invoke("Vall", 2)
                let c : int = a.Invoke("Vall", 0)
                b + c
            @>
            |> Quote.expandOperators
            |> Quote.evaluate
        Assert.Equal(4, a)

    type Sum() = 
        inherit QitBindingObj()
        let exprsToSum = ResizeArray()
        [<QitOp; ReflectedDefinition>]
        member x.Add(e : int) = 
            splice (
                exprsToSum.Add(<@e@>)
                <@()@>
            )
        member x.SumExpr = 
            if exprsToSum.Count = 0 then 
                <@0@>
            else 
                exprsToSum |> Seq.reduce (fun a b -> <@ !%a + !%b @>) 
        [<QitOp; ReflectedDefinition>]
        member x.CurrentSum() = splice x.SumExpr
    
    
    [<Fact>]
    let ``splice QitObj 4``() = 
        let a = 
            <@ 
                let a = Sum()
                a.Add(2)
                a.Add("my string".Length)
                a.Add 5
                a.CurrentSum()
            @>
            |> Quote.expandOperators
            |> Quote.evaluate
        Assert.Equal(16, a)

    [<Fact>]
    let ``replaceVar in splice 1``() = 
        let a : Expr<int> = 
            <@ 
                splice
                    (
                        let v = Var("v",typeof<int>)
                        <@@ !%%(Expr.Var(v)) + 1 @@>
                        |> Quote.replaceVar v <@@23@@>
                        |> Expr.Cast
                    )
            @>
        let v = a |> Quote.expandOperators 
        Assert.Equal(<@ 23 + 1 @>, v)
        Assert.Equal(24, v|> Quote.evaluate)

    [<Fact>]
    let ``BindQuote any instance obj 1``() = 
        let a = <@ ResizeArray([2.0]).Add(2.0) @>
        match a with 
        | BindQuote <@ (Quote.withType "x" : ResizeArray<AnyType>).Add(Quote.any "v") @> (Marker "x" x & Marker "v" v) ->
            Assert.Equal(<@@ 2.0 @@>,v)
        | _ -> Assert.False(true)

    [<Fact>]
    let ``BindQuote any instance obj 2``() = 
        let a = <@ ResizeArray([2.0]).[0] @>
        match a with 
        | BindQuote <@ (Quote.withType "x" : ResizeArray<AnyType>).[Quote.withType "i"] : AnyType @> (Marker "x" x & Marker "i" i) ->
            Assert.Equal(<@@ 0 @@>, i)
        | _ -> Assert.False(true)
        
    // This was an error from not checking array types and only checking generic types. This could be simplified
    type ConcatBuilder<'a>() =
        member x.Yield(v : 'a) = [|v|]
        member x.Yield(v : 'a []) = v
        member x.Combine(a, b) = Array.append a b
        member x.Delay(f) : 'a [] = f()
    
    [<Fact>]
    let ``BindQuote any instance obj 3``() = 
        let a = <@ ConcatBuilder<int>() {yield 1} @>
        let a0 = 
            match a with
            | Patterns.Application(Patterns.Lambda(_,f),_) -> f
            | _ -> failwith "never"
        match a0 with 
        | BindQuote <@ (Quote.withType "x" : ConcatBuilder<AnyType>).Delay(Quote.withType "body") : AnyType []@> (Marker "x" x & Marker "body" b) ->
            ()
        | _ -> Assert.False(true)
    
    [<Fact>]
    let ``BindQuote any instance obj 4``() = 
        let isMatch = 
            match <@ [] : int list @> with 
            | BindQuote <@ [] : AnyType list @> _ -> true
            | _ -> false
        Assert.True(isMatch)

    [<Fact>]
    let ``BindQuote multiple matches 1``() = 
        let uselessIf1 = 
            <@  
                let a = 32
                if a > 100 then 
                    a + 1
                else
                    a + 2
            @>
        let result1 = uselessIf1 |> Quote.exists (function Quote <@if Quote.withType"" then Quote.withType<int> "myMarker" else Quote.withType<int> "myMarker" @> -> true | _ -> false)
        Assert.False(result1)
        let uselessIf2 = 
            <@  
                let a = 32
                if a > 100 then 
                    a + 1
                else
                    a + 1
            @>
        let result2 = uselessIf2 |> Quote.exists (function Quote <@if Quote.withType"" then Quote.withType<int> "myMarker" else Quote.withType<int> "myMarker" @> -> true | _ -> false)
        Assert.True(result2)


    //REVIEW: Should we just always match unit variables? 
    [<Fact>]
    let ``BindQuote unit lambda 1``() = 
        let a = <@ ConcatBuilder<int>() {yield 1} @>
        let a0 = 
            match a with
            | Patterns.Application(Patterns.Lambda(_,f),_) -> f
            | _ -> failwith "never"
        match a0 with 
        | BindQuote <@ (Quote.withType "x" : ConcatBuilder<AnyType>).Delay(fun (__unitvar : unit) -> Quote.withType "body") : AnyType []@> (Marker "x" x & Marker "body" b) ->
            ()
        | _ -> Assert.False(true)
        
    [<Fact>]
    let ``BindQuote unit lambda 2``() = 
        let a = <@ fun () -> 1@>
        match a with 
        | BindQuote <@ fun () -> Quote.any "x" @> (Marker "x" x) ->
            Assert.Equal(<@@ 1 @@>, x)
        | _ -> Assert.False(true)

    [<QitOp; ReflectedDefinition>]
    let qitOp1 (v : int) : int = 
        splice(
            let i = <@ v @> |> Quote.evaluate
            Expr.Value (i + 1000) |> Expr.Cast
        ) 
    [<QitOp; ReflectedDefinition>]
    let qitOp2 (v : int) (w : int) : int = 
        splice(
            let i = <@ v + w @> |> Quote.evaluate
            Expr.Value (i + 1000) |> Expr.Cast
        ) 

    [<Fact>]
    let ``expand qitop``() =
        let q1 = <@ qitOp1 22 @> |> Quote.expandOperators
        Assert.Equal(q1, <@1022@>)
        let q2 = <@ 22 |> qitOp1@> |> Quote.expandOperators
        Assert.Equal(q2, <@1022@>)
        let q3 = <@ 22 |> qitOp2 2@> |> Quote.expandOperators
        Assert.Equal(q3, <@1024@>)


    [<Fact>]
    let ``rewriter 1``() = 
        let myRewriter (trail : Expr list) (thisCall : Expr) (eleven : Expr) = Some(thisCall, <@@ %%eleven + 2 @@>)
        let v = 
            <@
                let a = 1
                let b = QitOp.rewriter (11) myRewriter
                b + 2
            @> 
            |> Quote.expandRewriters
            |> Quote.evaluateUntyped
        Assert.Equal(15, v :?> _)

    [<Fact>]
    let ``rewriter 2``() = 
        let myRewriter (trail : Expr list) (thisCall : Expr) (eleven : Expr) = 
            match trail with 
            | (_ :: createTuple :: _t) -> Some(createTuple, <@@ (22, (%%eleven : int)) @@>)
            | _ -> None
        let v = 
            <@
                let a = 1
                let b : int*int = 
                    (11, QitOp.rewriter (11) myRewriter)
                b
            @> 
            |> Quote.expandRewriters
            |> Quote.evaluateUntyped
        Assert.Equal((22,11), v :?> _)
    
module ProvidedTypes = 
    [<Fact>]
    let ``simple lambda compile``() = 
        let q = <@fun () -> System.DateTime(2000,1,1)@>
        let f = Quote.compileLambda q
        Assert.Equal(DateTime(2000,1,1), f())
    [<Fact>]
    let ``simple lambda compile with 1 arg``() = 
        let q = <@fun n -> System.DateTime(2000,1,n)@>
        let f = Quote.compileLambda q
        Assert.Equal(DateTime(2000,1,7), f 7)
        Assert.Equal(DateTime(2000,1,22), f 22)
    [<Fact>]
    let ``simple lambda compile with 2 arg``() = 
        let q = <@fun y n -> System.DateTime(y,1,n)@>
        let f = Quote.compileLambda q
        Assert.Equal(DateTime(2000,1,7), f 2000 7)
        Assert.Equal(DateTime(3000,1,22), f 3000 22)
    [<Fact>]
    let ``simple lambda compile with 3 different arg``() = 
        let q = <@fun a b c -> sprintf "%d%s%.1f" a b c@>
        let f = Quote.compileLambda q
        Assert.Equal("200____1.0", f 200 "____" 1.0)
    [<Fact>]
    let ``substraction 1``() = 
        let q = <@fun (a : int) (b : int) -> a - b@>
        let f = Quote.compileLambda q
        Assert.Equal(-10, f 10 20)
    [<Fact>]
    let ``array 1``() = 
        let q = <@fun (a : int []) -> a.[1] + a.[0]@>
        let f = Quote.compileLambda q
        Assert.Equal(9, f [|3;6|])
    [<Fact>]
    let ``get field 1``() = 
        let q = 
            <@fun (a : DateTime) (ticks) -> 
                let mutable aa = a
                aa.Ticks = ticks
            @>
        let f = Quote.compileLambda q
        let d = DateTime.Now
        Assert.True(f d d.Ticks)
    
    open Qit.Tests.Helpers
    [<Fact>]
    let ``get field 2``() = 
        let q = 
            <@fun (a : DateTime) -> 
                let mutable aa = TypeWithFields(a)
                aa.A.Ticks
            @>
        let f = Quote.compileLambda q
        let d = DateTime.Now
        Assert.Equal(d.Ticks, f d)

    [<Fact>]
    let ``get field 3``() = 
        let q = 
            <@fun (a : DateTime) -> 
                let aa = TypeWithFields(a)
                aa.A.Ticks
            @>
        let f = Quote.compileLambda q
        let d = DateTime.Now
        Assert.Equal(d.Ticks, f d)


    [<Fact>]
    let ``get field 4``() = 
        let q = 
            <@fun (a : DateTime) -> 
                a.Ticks
            @>
        let f = Quote.compileLambda q
        let d = DateTime.Now
        Assert.Equal(d.Ticks, f d)


    [<Fact>]
    let ``get field 5``() = 
        let q = 
            <@fun (a : DateTime) -> 
                let aa = TypeWithFields2(a)
                aa.A.Ticks
            @>
        let f = Quote.compileLambda q
        let d = DateTime.Now
        Assert.Equal(d.Ticks, f d)



    [<Fact>]
    let ``get field 6``() = 
        let q = 
            <@fun (a : DateTime) -> 
                let mutable aa = TypeWithFields2(a)
                aa.A.Ticks
            @>
        let f = Quote.compileLambda q
        let d = DateTime.Now
        Assert.Equal(d.Ticks, f d)



    [<Fact>]
    let ``get field 7``() = 
        let q = 
            <@fun (a : DateTime) -> 
                let mutable aa = TypeWithFields3(a)
                aa.A.[0].Ticks
            @>
        let f = Quote.compileLambda q
        let d = DateTime.Now
        Assert.Equal(d.Ticks, f d)


    [<Fact>]
    let ``get field 8``() = 
        let q = 
            <@fun (a : DateTime) -> 
                let mutable aa = TypeWithFields4(a)
                aa.A.[0].Ticks
            @>
        let f = Quote.compileLambda q
        let d = DateTime.Now
        Assert.Equal(d.Ticks, f d)

        
    [<Fact>]
    let ``ticks on TimeSpan``() = 
        let q = 
            <@fun (x : int) -> 
                let a = TimeSpan.FromMinutes 30.0
                a.Ticks
            @>
        let f = Quote.compileLambda q
        let d = DateTime.Now
        Assert.Equal((TimeSpan.FromMinutes 30.0).Ticks, f 2)
    
    [<Fact>]
    let ``ticks math 1``() = 
        let q = 
            <@fun (x : int) -> 
                let a = TimeSpan.FromMinutes 30.0
                let b = TimeSpan.FromMinutes 35.0
                let c = TimeSpan.FromMinutes 302.0
                TimeSpan(c.Ticks * ((a.Ticks - b.Ticks) / c.Ticks))
            @>
        let a = TimeSpan.FromMinutes 30.0
        let b = TimeSpan.FromMinutes 35.0
        let c = TimeSpan.FromMinutes 302.0
        let result = TimeSpan(c.Ticks * ((a.Ticks - b.Ticks) / c.Ticks))
        let f = Quote.compileLambda q
        let d = DateTime.Now
        Assert.Equal(result, f 2)
    
    [<Fact>]
    let ``call field meth 1``() = 
        let q = 
            <@fun (a : DateTime) -> 
                let aa = TypeWithFields4(a)
                aa.A.[0].AddMinutes(3.0).Ticks
            @>
        let f = Quote.compileLambda q
        let d = DateTime.Now
        let v = 
            fun (a : DateTime) (b : int) ->
               let aa = TypeWithFields4(a)
               aa.A.[0].AddMinutes(3.0).Ticks
        Assert.Equal(v d 1,f d)

    [<Fact>]
    let ``call field meth 2``() = 
        let q = 
            <@fun a offset mins (deltaMin : double) -> 
                let aa = TypeWithFields3(a)
                let i = 0
                ((TimeSpan.FromMinutes mins).Ticks * (((aa.A.[i].AddMinutes deltaMin).Ticks + (TimeSpan.FromMinutes offset).Ticks)/ (TimeSpan.FromMinutes mins).Ticks)) - (TimeSpan.FromMinutes offset).Ticks
                |> DateTime
            @>
        let f = Quote.compileLambda q
        let d = DateTime.Now
        let v = 
            fun a offset mins (deltaMin : double) -> 
                let aa = TypeWithFields3(a)
                ((TimeSpan.FromMinutes mins).Ticks * (((aa.A.[0].AddMinutes deltaMin).Ticks + (TimeSpan.FromMinutes offset).Ticks)/ (TimeSpan.FromMinutes mins).Ticks)) - (TimeSpan.FromMinutes offset).Ticks
                |> DateTime
        Assert.Equal(v d 0.0 45.0 1.0,f d 0.0 45.0 1.0)

    open Qit.ProviderImplementation.ProvidedTypes
    open Qit.UncheckedQuotations
    
    [<Fact>]
    let ``use constructed type 1``() = 
        let asm = ProvidedAssembly()
        let tp = ProvidedTypeDefinition(asm, "TestNamespace","TestClass", Some typeof<obj>, isErased = false)
        asm.AddTypes [tp]
        let objField = ProvidedField("anInteger", typeof<int>)
        tp.AddMembers [objField]
        objField.SetFieldAttributes(FieldAttributes.Assembly)
        let inpObj = ProvidedParameter("anInt", typeof<int>)
        let ctor = ProvidedConstructor([inpObj],  invokeCode = fun args -> Expr.FieldSet(args.[0], objField, args.[1]) )
        tp.AddMembers [ctor]
        let inpObj2 = ProvidedParameter("anInt", typeof<int>)
        let objMethod = ProvidedMethod("Add", [inpObj2], typeof<int>, invokeCode = fun args -> <@@ %%(Expr.FieldGet(args.[0], objField)) + (%%(args.[1]) : int) @@>)
        tp.AddMembers [objMethod]
        let lambdaUntyped = 
            let a = Var("a", typeof<int>)
            let param1 = Expr.Var(a)
            let b = Var("b", typeof<int>)
            let param2 = Expr.Var(b)
            let t = Var("t", tp)
            Expr.Lambda(a,
                Expr.Lambda(b,
                    Expr.Let(t,
                        Expr.NewObjectUnchecked(ctor, [param1]),
                        Expr.CallUnchecked(Expr.Var(t), objMethod, [param2])
                    )
                )
            )
        let lambda : Expr<int -> int -> int> = <@ %%lambdaUntyped @>
        let f = Quote.compileLambda lambda 
        Assert.Equal(3, f 1 2)


    [<Fact>]
    let ``use constructed type access anno record 1``() = 
        let asm = ProvidedAssembly()
        let tp = ProvidedTypeDefinition(asm, "TestNamespace","TestClass", Some typeof<obj>, isErased = false)
        asm.AddTypes [tp]
        let anonType = {| a = 32 |}
        let t = anonType.GetType()
        let p = t.GetProperty("a")
        let objField = ProvidedField("anInteger", t)
        tp.AddMembers [objField]
        objField.SetFieldAttributes(FieldAttributes.Assembly)
        let inpObj = ProvidedParameter("anObj", t)
        let ctor = ProvidedConstructor([inpObj], invokeCode = fun args -> 
            Expr.FieldSet(args.[0], objField, args.[1]))
        tp.AddMembers [ctor]
        let inpObj2 = ProvidedParameter("anInt", typeof<int>)
        let objMethod = ProvidedMethod("Add", [inpObj2], typeof<int>, invokeCode = fun args -> 
            <@@ %%(Expr.PropertyGet(Expr.FieldGet(args.[0], objField),p)) + (%%(args.[1]) : int) @@>)
        tp.AddMembers [objMethod]
        let lambdaUntyped = 
            let a = Var("a", t)
            let param1 = Expr.Var(a)
            let b = Var("b", typeof<int>)
            let param2 = Expr.Var(b)
            let t = Var("t", tp)
            Expr.Lambda(a,
                Expr.Lambda(b,
                    Expr.Let(t,
                        Expr.NewObjectUnchecked(ctor, [param1]),
                        Expr.CallUnchecked(Expr.Var(t), objMethod, [param2])
                    )
                )
            )
        let lambda : Expr<{| a: int |} -> int -> int> = <@ %%lambdaUntyped @>
        let f = Quote.compileLambda lambda 
        Assert.Equal(35, f anonType 3)



    [<Fact>]
    let ``use constructed type access anno record 2``() = 
        let asm = ProvidedAssembly()
        let tp = ProvidedTypeDefinition(asm, "TestNamespace","TestClass", Some typeof<obj>, isErased = false)
        asm.AddTypes [tp]
        let anonType = 
            {| 
                Date = DateTime(2020,1,1)
                DateOption = Some(DateTime(2020,1,1))
                Open = 1.0M
                Name = "Jow"
                NameOption = Some("Jow")
                Tuple = (1,2)
            |}
        let t = anonType.GetType()
        let objField = ProvidedField("backingObj", t)
        objField.SetFieldAttributes(FieldAttributes.Assembly)
        tp.AddMembers [objField]
        let inpObj = ProvidedParameter("anObj", t)
        let ctor = ProvidedConstructor([inpObj], invokeCode = fun args -> 
            Expr.FieldSet(args.[0], objField, args.[1]))
        tp.AddMembers [ctor]
        let properties = t.GetProperties()
        for p in properties do
            let prop = ProvidedProperty(p.Name, p.PropertyType, getterCode = fun args -> 
                Expr.PropertyGet(Expr.FieldGet(args.[0], objField), p))
            tp.AddMember(prop)

        let lambdaUntyped = 
            let a = Var("a", t)
            let param1 = Expr.Var(a)
            let t = Var("t", tp)
            Expr.Lambda(a,
                Expr.Let(t,
                    Expr.NewObjectUnchecked(ctor, [param1]),
                    Expr.PropertyGet(Expr.Var(t), tp.GetProperty("Date"))
                )
            )
        let lambda : Expr<{| 
            Date: DateTime
            DateOption: DateTime option
            Open: decimal
            Name: string
            NameOption: string option
            Tuple: int * int
        |} -> DateTime> = <@ %%lambdaUntyped @>
        let f = Quote.compileLambda lambda 
        Assert.Equal(DateTime(2020,1,1), f anonType)
