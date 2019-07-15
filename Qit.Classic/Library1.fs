namespace Qit.Classic

open Qit.ReflectionPatterns
open System
open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Quotations.Patterns

module Quote = 
    open ProviderImplementation2.ProvidedTypes
    let compileLambdaFsi (q : Expr<'a>) = 
        let fname = IO.Path.GetTempFileName() + ".dll"
        let asm = AssemblyGenerator(fname)
        let t = ProviderImplementation2.ProvidedTypes.ProvidedTypeDefinition(asm.Assembly,"ns","tp",Some typeof<obj>,IsErased=false)
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
                ProvidedMethod("meth", [], r, IsStaticMethod = true, InvokeCode = f q), (fun mt -> Expr.Lambda(Var("", typeof<unit>), Expr.Call(mt, [])))
            | FSharpFuncType (d,r) ->  
                let args = d |> List.mapi (fun i t -> ProvidedParameter("p" + string i, t))
                let vs = args |> List.map (fun a -> Var(a.Name, a.ParameterType))
                let g mt = 
                    vs
                    |> List.foldBack (fun a body -> Expr.Lambda(a,body) )
                    <| Expr.Call(mt, vs |> List.map Expr.Var)
                ProvidedMethod("meth", args, r, InvokeCode = f q, IsStaticMethod = true), g
            | _ -> 
                ProvidedMethod("meth", [], typeof<'a>, InvokeCode = f q, IsStaticMethod = true), (fun mt -> Expr.Lambda(Var("", typeof<unit>), Expr.Call(mt, [])))
        t.AddMember m
        asm.Generate([t,None])
        let a = System.Reflection.Assembly.LoadFrom(fname)
        let r = a.GetTypes() |> Seq.head
        let mt = r.GetMethod("meth")
        FSharp.Linq.RuntimeHelpers.LeafExpressionConverter.EvaluateQuotation(build mt) :?> 'a
       
