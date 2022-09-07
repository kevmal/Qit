namespace Qit.Tests
open Qit
open System.Linq.Expressions
open Xunit
open Qit.CSharp
open Qit.Operators
open System
open System.Reflection
open FSharp.Quotations

module Basic = 
    open Qit.Patterns
    [<Fact>]
    let spliceInExpression1() = 
        let e = Quote.toExpression <@ 1 + 2 + 3 @>
        let shit = 
            <@
                10 - (Quote.spliceInExpression e)
            @>
        let v =
            shit
            |> Quote.toExpression
            |> Quote.expandExpressionSplices
        let v = Assert.IsType<int>(v|> Expression.evaluate)
        Assert.Equal(4, v)
    [<Fact>]
    let ``spliceInExpression Func``() = 
        let e = Expression.Func <@ fun a -> 1 + 2 + a @>
        let v = 
            <@
                10 - ((Quote.spliceInExpressionTyped e).Invoke 3)
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
                                printfn "poo1"
                            @>
                        else 
                            <@
                                printfn "poo2"
                            @>
                    <@
                        !%e
                        printfn "poo"
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
                        let poo a = 
                            <@
                                !%(f a)
                            @>
                        poo (23 + 32)
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
                match tp.GetConstructor(bindAll,null,ptypes,null) with
                | null -> failwithf "Ctor with paremters (%s) not found in %s" (ptypes |> Array.map (fun x -> x.Name) |> String.concat ",") tp.Name
                | m -> Expr.NewObject(m, exprs) 
            | Quote <@@()@@> -> 
                match tp.GetConstructor(bindAll,null,[||],null) with
                | null -> failwithf "Ctor with no paremters not found in %s" tp.Name
                | m -> Expr.NewObject(m, [])
            | expr -> 
                match tp.GetConstructor(bindAll,null,[|expr.Type|],null) with
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
        
        


        
    [<Fact>]
    let ``splice untyped 1``() = 
        let map (f: Expr) (o: Expr) = <@@ Option.map !%%f !%%o @@>
        let expr = map <@ fun x -> x + 1 @> <@ Some 4 @>
        let v = 
            expr
            |> Quote.expandOperatorsUnchecked 
            |> Quote.expandOperatorsUntypedTest
            |> Quote.evaluateUntyped
        Assert.Equal(Some 5, v :?> _)
         
         
    [<Fact>]
    let ``splice untyped 2``() = 
        let p = <@@ 1 @@>
        let expr = 
            <@@
                let ra = ResizeArray()
                ra.Add(!%%p)
                ra.ToArray()
            @@>
        let v = 
            expr
            |> Quote.expandOperatorsUnchecked 
            |> Quote.expandOperatorsUntypedTest
            |> Quote.evaluateUntyped
        let v : int [] = Assert.IsType(v)
        Assert.Equal(1, v.[0])
         
                  
                  
    [<Fact(Skip="Does not work yet")>]
    let ``splice untyped 3``() = 
        let p = <@@ 0 @@>
        let expr = 
                     <@@
                         let ra = ResizeArray()
                         ra.Add(Unchecked.defaultof<_>)
                         ra.[0] = !%%p
                     @@>
        let v = 
                     expr
                     |> Quote.expandOperatorsUnchecked 
                     |> Quote.expandOperatorsUntypedTest
                     |> Quote.evaluateUntyped
        let v : bool = Assert.IsType(v)
        Assert.Equal(true, v)
                  
                           
        
        
    [<Fact>]
    let ``splice untyped property get 1``() = 
        let p = <@@ 1 @@>
        let expr = 
           <@@
               let ra = ResizeArray()
               ra.Add(!%%p)
               ra.[0]
           @@>
        let v = 
           expr
           |> Quote.expandOperatorsUnchecked 
           |> Quote.expandOperatorsUntypedTest
           |> Quote.evaluateUntyped
        let v : int = Assert.IsType(v)
        Assert.Equal(1, v)
        
        
    [<Fact>]
    let ``splice untyped property set 1``() = 
        let p = <@@ 1 @@>
        let expr = 
           <@@
               let ra = ResizeArray()
               ra.Add(!%%p)
               ra.[0] <- !%%p
               ra.[0]
           @@>
        let v = 
           expr
           |> Quote.expandOperatorsUnchecked 
           |> Quote.expandOperatorsUntypedTest
           |> Quote.evaluateUntyped
        let v : int = Assert.IsType(v)
        Assert.Equal(1, v)
        
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

    [<Fact>]
    let ``expand qitop``() =
        let q1 = <@ qitOp1 22 @> |> Quote.expandOperators
        Assert.Equal(q1, <@1022@>)
        //let q2 = <@ 22 |> qitOp1@> |> Quote.expandOperators
        //Assert.Equal(q2, <@1022@>)


(*               
    [<Fact>]
    let ``rewriter 1``() = 
        let v = 
            <@
                let a = 1
                let b = Quote.rewriter (11) (fun trail thisCall eleven -> Some(thisCall, <@@ !%%eleven + 2 @@> |> Quote.expandOperators))
                b + 2
            @> 
            |> Quote.expandRewriters
            |> Quote.evaluateUntyped
        Assert.Equal(15, v :?> _)
    [<Fact>]
    let ``rewriter 2``() = 
        let v = 
            <@
                let a = 1
                let b : int*int = 
                    (11, Quote.rewriter (11) 
                        (fun l _ eleven -> 
                            match l with 
                            | (_ :: createTuple :: _t) -> Some(createTuple, <@@ (22, (!%%eleven : int)) @@> |> Quote.expandOperators)
                            | _ -> failwith "no"))
                b
            @> 
            |> Quote.expandRewriters
            |> Quote.evaluateUntyped
        Assert.Equal((22,11), v :?> _)
*)               
               
module CSharp =
    open FSharp.Quotations
    open Microsoft.CodeAnalysis.CSharp
    open Microsoft.CodeAnalysis
    open System.Text

    type C() = 
        inherit CSharpSyntaxRewriter()
        override x.VisitEmptyStatement(_) = null |> box |> unbox
    
    let format (q : Expr) = 
        let c = Quote.toCSharpString q
        let poo = sprintf """
            namespace ns{
                public class tp{
                    static void meth()
                    {
                        %s;
                    }
                }
            }
                """ c |> CSharpSyntaxTree.ParseText
        use cw = new AdhocWorkspace()
        let format x  = Formatting.Formatter.Format(x,cw)
        C().Visit(poo.GetRoot()).NormalizeWhitespace().ToFullString().Split('\n') 
        |> Array.map (fun x -> x.Trim('\r'))
        |> Array.skip 6 
        |> Array.rev
        |> Array.skip 3
        |> Array.rev
        //|> Array.map (fun x -> x.Substring(12))
        |> Array.map (fun x -> x.Trim())
        |> String.concat "\r\n"
        |> (fun x -> Diagnostics.Debug.WriteLine x; x)
        //|> CSharpSyntaxTree.ParseText

    let formatWithType (q : Expr) = 
        let c = 
            let a = 
                (format q).Split('\n') 
                |> Array.map (fun x -> x.Trim('\r'))
            a.[a.Length - 1] <- sprintf "return %s" a.[a.Length - 1]
            a |> String.concat "\r\n"
        let poo = sprintf """
            namespace ns{
                public class tp{
                    public static %s meth()
                    {
                        %s;
                    }
                }
            }
                """ (q.Type.FullName) c |> CSharpSyntaxTree.ParseText
        use cw = new AdhocWorkspace()
        let format x  = Formatting.Formatter.Format(x,cw)
        C().Visit(poo.GetRoot()).NormalizeWhitespace().ToFullString()
    let eval q = 
        let asm = typeof<obj>.Assembly
        let mscorlib = Microsoft.CodeAnalysis.PortableExecutableReference.CreateFromFile(asm.Location);
        let fsharplib = Microsoft.CodeAnalysis.PortableExecutableReference.CreateFromFile(typeof<string list>.Assembly.Location);
        let str = formatWithType q
        let poo = str |> CSharpSyntaxTree.ParseText
        let compilation = CSharpCompilation.Create("foo", [poo], [mscorlib; fsharplib])
        let tmp = IO.Path.GetTempFileName() + ".dll"
        Diagnostics.Debug.WriteLine(tmp)
        let result = compilation.WithOptions(new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary)).Emit(tmp)
        if result.Success then 
            let asm = Reflection.Assembly.LoadFile(tmp)
            let t = asm.GetTypes() |> Seq.head 
            let m = t.GetMethod("meth",BindingFlags.Static ||| BindingFlags.Public)
            m.Invoke(null, [||])
        else    
            failwithf "compile fail\r\n------------------------\r\n%s\r\n------------------------\r\n%A" str  result.Diagnostics


    [<Fact>]
    let ``simple expr 1``() = 
        let q = <@ let a = 1 + 2 + 3 in 2 + a@>
        let e = Quote.toCSharpString q
        Assert.Equal("System.Int32 a = ((1 + 2) + 3);\r\n(2 + a);", e)
        Assert.Equal(8, eval q :?> int)
    
    
    [<Fact>]
    let ``shadowing 1``() = 
        let q = 
            <@ 
                let a = 1
                let b = a
                let a = 2
                a + b 
            @> |> Quote.rewriteShadowing
        let e = q |> format
        Assert.Equal("""System.Int32 a = 1;
System.Int32 b = a;
System.Int32 a__1 = 2;
(a__1 + b);""", e)
        Assert.Equal(3, eval q :?> int)
    
    
    [<Fact>]
    let ``shadowing 2``() = 
        let q = 
            <@ 
                let a = 1
                let b = a
                let a = 2
                let a__1 = 100
                a + b + a__1
            @> |> Quote.rewriteShadowing
        Assert.Equal(103, eval q :?> int)
    
    
    [<Fact>]
    let ``shadowing 3``() = 
        let q = 
            <@ 
                let a = 1
                let b = a
                let a__1 = 100
                let a = 2
                a + b + a__1
            @> |> Quote.rewriteShadowing
        Assert.Equal(103, eval q :?> int)
    
    [<Fact>]
    let ``shadowing 4``() = 
        let q = 
            <@ 
                let f x = 
                    let a = x
                    let x = 2
                    x + a
                (f 3) + 10
            @> |> Quote.rewriteShadowing
        let e = q |> format
        Assert.Equal(15, eval q :?> int)
    [<Fact>]
    let ``for loop 1``() = 
        let q = 
            <@ 
                let mutable a = 0
                for i = 1 to 100 do 
                    a <- a + i
                a
            @> |> Quote.rewriteShadowing
        let e = q |> format
        Assert.Equal(5050, eval q :?> int)
    [<Fact>]
    let ``while loop 1``() = 
        let q = 
            <@ 
                let mutable a = 0
                let mutable i = 100
                while i > 0 do 
                    a <- a + i
                    i <- i - 1
                a
            @> |> Quote.rewriteShadowing
        let e = q |> format
        Assert.Equal(5050, eval q :?> int)
    [<Fact>]
    let ``while loop 2``() = 
        let q = 
            <@ 
                let mutable a = 0
                let mutable i = 100
                while i > 0 && a < 10000 do 
                    a <- a + i
                    i <- i - 1
                a
            @> 
            |> Quote.rewriteConditionals
            |> Quote.rewriteShadowing
        let e = q |> format
        Assert.Equal(5050, eval q :?> int)
    [<Fact>]
    let ``let if then else 1``() = 
        let q = 
            <@ 
                let a = 20
                let b = 
                    if a < 30 then 
                        let c = 23
                        c + 22
                    else 
                        let d = 222
                        d - 22
                b - 100
            @> 
            |> Internal.Rw.firstPass
            |> Quote.rewriteConditionals
            |> Quote.rewriteShadowing
        let e = q |> format
        Assert.Equal(-55, eval q :?> int)
        
    [<Fact>]
    let ``new array 1``() = 
        let q = 
            <@ 
                [|
                    2
                    3 + 4
                    1
                |]
            @> 
            |> Quote.rewriteConditionals
            |> Quote.rewriteShadowing
        let e = q |> format
        let a = eval q :?> int []
        Assert.Equal(3, a.Length)
        Assert.Equal(2, a[0])
        Assert.Equal(7, a[1])
        Assert.Equal(1, a[2])

    [<Fact>]
    let ``generic type name 1``() = 
        let q = 
            <@



                let decodeString (s : string) = 
                    let num i = 
                        let mutable x = int s.[i] - 0x30
                        let mutable i = i + 1
                        while i < s.Length && Char.IsDigit s.[i] do 
                            x <- x * 10 + (int s.[i] - 0x30)
                            i <- i + 1
                        i, x

                    let rec loop (sb : StringBuilder) i = 
                        if i = s.Length || s.[i] = ']' then 
                            i + 1, sb.ToString()
                        elif Char.IsDigit s.[i] then 
                            let i, n = num i
                            let i, str = loop (StringBuilder()) (i + 1)
                            sb.Append(String.replicate n str) |> ignore
                            loop sb i
                        else 
                            sb.Append(s.[i]) |> ignore
                            loop sb (i + 1)

                    loop (StringBuilder()) 0 


                ()
            @>    
            |> Quote.rewriteConditionals
            |> Qit.CSharp.Internal.rewriteSeqToLinq
            |> Qit.CSharp.Internal.Rw.firstPass
            |> Qit.CSharp.Internal.inlineRightPipe
            |> Quote.rewriteShadowing
            |> format
        let q = 
            <@ 
                let f = fun (x : int seq) -> 1
                ()
            @>
            |> Qit.CSharp.Internal.Rw.firstPass
            |> format
        
        Assert.Equal("System.Func<System.Collections.Generic.IEnumerable<System.Int32>, System.Int32> f = ((x) =>\r\n{\r\nreturn 1;\r\n});\r\nnull;",q)
            
                  

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
        Assert.Equal("200crap1.0", f 200 "crap" 1.0)
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
 

module Rw = 
    open Qit.CSharp.Internal.Rw
    open Qit.CSharp.Internal
    open Qit.CSharp.Internal.Crap
    open System.Collections.Generic

    let eq = 
        {new IEqualityComparer<Expr> with
             member this.Equals(x: Expr, y: Expr): bool = 
                let _,_,m = Quote.exprMatch x y
                m
             member this.GetHashCode(obj: Expr): int = hash obj
        }
    let check (a : Expr) (b : Expr) = Assert.Equal(a,b,eq)
    [<Fact>]
    let ``simple if 1``() =
        <@ 
            if (let a = 1 in a + 6) > 0 then 
                2
            else
                8
        @>  
        |> firstPass
        |> check 
            <@ 
                let mutable __a = initmut
                __a <- 1
                let mutable __b = initmut
                if __a + 6 > 0 then 
                    __b <- 2
                else 
                    __b <- 8
                __b
            @>
            
    [<Fact>]
    let ``pipe map 1``() =
        <@ 
            [1;2;3]
            |> List.map (fun x -> x + 1)
            |> List.map (fun x -> x - 1)
        @>    
        |> firstPass
        |> check 
            <@ 
                let __map = fun x -> x + 1
                let __a1 = fun __l -> List.map __map __l
                let __map1 = fun x -> x - 1
                let __a2 = fun __l -> List.map __map1 __l
                [1;2;3]
                |> __a1
                |> __a2
            @>    

    [<Fact>]
    let ``while loop 1``() =
        <@ 
            let mutable a = 1
            let mutable b = 10
            while a < 100 do 
                b <- a + b
                a <- a + 1
            b
        @>    
        |> firstPass
        |> check 
            <@ 
                let mutable __a = initmut
                __a <- 1
                let mutable __b = initmut
                __b <- 10
                while __a < 100 do 
                    __b <- __a + __b
                    __a <- __a + 1
                __b
            @>    

    [<Fact>]
    let ``tail call 1``() =
        <@ 
            let rec loop i = 
                if i = 0 then 
                    10
                else
                    loop (i - 1) 
            loop 10
        @>    
        |> rewriteTailCallToWhile
        |> check 
            <@ 
                let loop (i : int) : int = 
                    let mutable i = i
                    while true do
                        if i = 0 then 
                            csreturnignore 10
                        else
                            i <- i - 1
                    csFakeType()
                loop 10
            @>    

            
                
        
            
                
        
                
        
                
        
    
