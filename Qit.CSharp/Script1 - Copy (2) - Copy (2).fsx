#r "nuget:Microsoft.CodeAnalysis.CSharp"
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


type Player = 
    {
        PlayerId : int 
        mutable Score : int
    }
open System.Text


let qq = <@@

let (|Empty|_|) s = if String.IsNullOrEmpty s then Some() else None
let (|Dot|_|) (s : string) = 
    if s.StartsWith(".") then 
        Some s.[1..]
    else 
        None 
let (|Digits|_|) (s : string) = 
    let mutable i = 0 
    while i < s.Length && Char.IsDigit s.[i] do 
        i <- i + 1
    if i > 0 then 
        Some (s.[i..])
    else 
        None

let (|MaybeSign|) (s : string) = 
    if s.StartsWith "+" || s.StartsWith "-" then 
        s.[1..]
    else s

let (|Dec|_|) (s : string) = 
    match s with 
    | MaybeSign (Digits (Dot Empty) | Digits (Dot (Digits Empty)) | Dot(Digits Empty)) -> Some()
    | _ -> None
    
let (|Int|_|) (s : string) = 
    match s with 
    | MaybeSign (Digits Empty) -> Some ()
    | _ -> None
let (|E|_|) (s : string) = 
    if s.StartsWith "e" || s.StartsWith "E" then 
        Some s.[1..]
    else 
        None
    


let isNumber (s : string) = 
    match s with  
    | Dec 
    | Int 
    | E Int -> true
    | _ -> false

   


() @@>
     


qq
|> Quote.rewriteConditionals
|> rewriteTailCallToWhile
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






