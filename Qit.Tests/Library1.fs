namespace Qit.Tests
open Qit
open System.Linq.Expressions
open Xunit
open Qit.CSharp
open System
open System.Reflection
open FSharp.Quotations

module Basic = 
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
                    Quote.spliceUntyped ( Expr.NewTuple [ <@@ a + 20 @@>; <@@ a - 20 @@> ] )
                c,b,c
            @> 
            |> Quote.expandSpliceOp
            |> Quote.evaluateUntyped
        Assert.Equal((-19, 21, -19), v :?> _)
                
    [<Fact>]
    let ``splice untyped quote 2``() = 
        let v = 
            <@
                let a = 1
                let (b : int, c : int) = 
                    Quote.spliceUntyped ( Expr.NewTuple [ <@@ a + Quote.splice <@ 20 @> @@>; <@@ a - 20 @@> ] )
                c,b,c
            @> 
            |> Quote.expandSpliceOp
            |> Quote.evaluateUntyped
        Assert.Equal((-19, 21, -19), v :?> _)
               
module CSharp =
    open FSharp.Quotations
    open Microsoft.CodeAnalysis.CSharp
    open Microsoft.CodeAnalysis

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
        |> Array.map (fun x -> x.Substring(12))
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
            failwithf "compile fail\r\n------------------------\r\n%s\r\n------------------------" str


    [<Fact>]
    let ``simple expr 1``() = 
        let q = <@ let a = 1 + 2 + 3 in 2 + a@>
        let e = Quote.toCSharpString q
        Assert.Equal("System.Int32 a = 1 + 2 + 3; 2 +\r\na ;", e)
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
a__1 + b;""", e)
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



