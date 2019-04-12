namespace Qit
open System
open Microsoft.FSharp.Core.CompilerServices
open System.Reflection
open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Quotations.Patterns
open System.Collections.Generic

module Patterns = 
    open Quote

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