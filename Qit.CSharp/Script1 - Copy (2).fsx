﻿#r "nuget:Microsoft.CodeAnalysis.CSharp"
#r "nuget:Microsoft.CodeAnalysis.Workspaces.Common"
#r "nuget:FSharp.Quotations.Evaluator"
#r "nuget:TextCopy"

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

<@ 
    let f x = 
        let a = x
        let x = 2
        x + a
    (f 3) + 10
@> 
|> Quote.rewriteConditionals
|> Quote.rewriteShadowing
|> Quote.toCSharpString
|> printfn "%s"

let q0 = 
    <@
        let check (candies : int []) (k : int64) (d : int): bool = failwith ""
            
        let maximumCandies (candies : int []) (k : int64) =
            let sum = candies |> Seq.map int64 |> Seq.sum
            let maxPer = sum / k |> int
            if maxPer <= 1 then 
                maxPer
            else 
                let mutable candidate = 1
                let mutable upper = maxPer
                while upper > candidate do 
                    let mid = (upper - candidate) / 2 + 1 + candidate |> min upper
                    if check candies k mid then 
                        candidate <- mid
                    else 
                        upper <- mid - 1
                candidate
        ()        
    @>
let q1 = 
    <@
        let check (candies : int []) (k : int64) (d : int) = 
            let mutable loop = true
            let mutable i = 0
            let mutable r = false
            while loop do 
                if k = 0L then 
                    r <- true 
                    loop <- false
                elif i >= candies.Length then 
                    r <- false 
                    loop <- false
                else 
                    let mutable c = candies.[i]
                    let mutable k = k
                    while c > 0 && k > 0 do 
                        c <- c - d
                        if c >= 0 then 
                            k <- k - 1L
                    i <- i - 1
            r
        ()
    @>
let q = 
    <@
        let check (candies : int []) (k : int64) (d : int) = 
            let mutable loop = true
            let mutable i = 0
            let mutable r = false
            while loop do 
                if k = 0L then 
                    r <- true 
                    loop <- false
                elif i >= candies.Length then 
                    r <- false 
                    loop <- false
                else 
                    let mutable c = candies.[i]
                    let mutable k = k
                    while c > 0 && k > 0 do 
                        c <- c - d
                        if c >= 0 then 
                            k <- k - 1L
                    i <- i - 1
            r
            
        let maximumCandies (candies : int []) (k : int64) =
            let sum = 0L //candies |> Seq.map int64 |> Seq.sum
            let maxPer = sum / k |> int
            if maxPer <= 1 then 
                maxPer
            else 
                let mutable candidate = 1
                let mutable upper = maxPer
                while upper > candidate do 
                    let mid = (upper - candidate) / 2 + 1 + candidate |> min upper
                    if check candies k mid then 
                        candidate <- mid
                    else 
                        upper <- mid - 1
                candidate
        ()        
    @>

open System 
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
    |> Array.map (fun x -> if x.Length < 12 then x else x.Substring(12))
    |> String.concat "\r\n"
    |> (fun x -> Diagnostics.Debug.WriteLine x; x)
    //|> CSharpSyntaxTree.ParseText



<@[|1;2;3|] |> Seq.map (fun x -> x + 1)  @>


//<@  Seq.map (fun x -> x + 1) [|1;2;3|] @>
<@[|1;2;3|] |> Seq.map (fun x -> x + 1) |> Seq.map (fun x -> x + 2) @>
|> Qit.CSharp.Internal.rewriteSeqToLinq
|> Quote.rewriteConditionals
|> Qit.CSharp.Internal.inlineRightPipe
|> Qit.CSharp.Internal.Rw.firstPass
|> Quote.rewriteShadowing
|> format
|> printfn "%s"

open System.Collections.Generic


open System.Text
let qq = <@@


let replicate (count: int) (str: string) =

    let len = str.Length

    if len = 0 || count = 0 then
        String.Empty

    elif len = 1 then
        new String(str.[0], count)

    elif count <= 4 then
        match count with
        | 1 -> str
        | 2 -> String.Concat(str, str)
        | 3 -> String.Concat(str, str, str)
        | _ -> String.Concat(str, str, str, str)

    else
        // Using the primitive, because array.fs is not yet in scope. It's safe: both len and count are positive.
        let target = Array.zeroCreate (len * count)

        let source = str.ToCharArray()

        // O(log(n)) performance loop:
        // Copy first string, then keep copying what we already copied
        // (i.e., doubling it) until we reach or pass the halfway point
        Array.Copy(source, 0, target, 0, len)
        let mutable i = len

        while i * 2 < target.Length do
            Array.Copy(target, 0, target, i, i)
            i <- i * 2

        // finally, copy the remain half, or less-then half
        Array.Copy(target, 0, target, i, target.Length - i)
        new String(target)
let decodeString (s : string) = 
    let num i = 
        let mutable x = int s.[i] - 0x30
        let mutable i = i + 1
        while i < s.Length && Char.IsDigit s.[i] do 
            x <- x * 10 + (int s.[i] - 0x30)
            i <- i + 1
        i, x

    let sb = StringBuilder()
    let rec loop i = 
        if i = s.Length || s.[i] = ']' then 
            i + 1
        elif Char.IsDigit s.[i] then 
            let start = sb.Length
            let i, n = num i
            let i = loop (i + 1)
            sb.Append(sb.ToString(start,sb.Length - start)) |> ignore
            loop i
        else 
            sb.Append(s.[i]) |> ignore
            loop (i + 1)
    loop 0 |> ignore
    sb.ToString()


() @@>
     


qq
|> Quote.rewriteConditionals
//|> rewriteTailCallToWhile
//|> rewriteReturnOnLambda
|> Qit.CSharp.Internal.rewriteSeqToLinq
|> Quote.traverseQuotation 
    (fun x -> 
        match x with 
        | BindQuote <@@ Quote.any "x" |> Quote.withType "f" : AnyType @@> (Marker "x" x & Marker "f" (Patterns.Lambda(v,Patterns.Call(o,mi,args)))) ->
            match o with 
            | Some tobj -> 
                Expr.Call(tobj,mi,args |> List.map (fun i -> match i with Patterns.Var v0 when v0 = v -> x | q -> q)) |> Some
            | _ -> 
                Expr.Call(mi,args |> List.map (fun i -> match i with Patterns.Var v0 when v0 = v -> x | q -> q)) |> Some
        | _ -> None
    )
|> Qit.CSharp.Internal.Rw.firstPass
|> Qit.CSharp.Internal.inlineRightPipe
|> Quote.traverseQuotation 
    (fun x -> 
        match x with 
        | Let(v,BindQuote <@@ Qit.CSharp.Internal.Rw.initmut<AnyType> @@> _, Sequential(VarSet(v2,e),e2)) when v = v2 ->
            Some(Expr.Let(v,e,e2))
        | _ -> None
    )
|> Quote.rewriteShadowing
|> format
|> (fun i -> TextCopy.ClipboardService.SetText i; i)
|> printfn "%s"






