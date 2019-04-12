namespace Qit.Tests
open Qit
open System.Linq.Expressions
open Xunit
open Qit.CSharp

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
                
module CSharp =
    [<Fact>]
    let ``simple expr 1``() = 
        let e = Quote.toCSharpString <@ let a = 1 + 2 + 3 in 2 + a@>
        Assert.Equal("System.Int32 a; 1 + 2 + 3 ;  2 +\r\na ;", e)
    