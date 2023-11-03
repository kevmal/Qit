namespace Qit
open System
open Microsoft.FSharp.Core.CompilerServices
open System.Reflection
open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Quotations.Patterns
open System.Collections.Generic

[<AutoOpen>]
module Patterns = 
    open Quote
    
    /// <summary>
    /// Match a call to a MethodInfo, destructures to (intance option * type args list * args list)
    /// </summary>
    /// <param name="minfo">MethodInfo being called.</param>
    /// <param name="expr">Matching expr.</param>
    let (|MethodCall|_|) (minfo : MethodInfo) (expr:Expr) = 
        match expr with
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

    /// <summary>
    /// Match name of PropertyInfo.
    /// </summary>
    /// <param name="name">Name to match</param>
    /// <param name="propertyInfo">PropertyInfo matching against</param>
    let (|PropertyName|_|) name (propertyInfo : PropertyInfo) = if propertyInfo.Name = name then Some() else None

    /// <summary>
    /// Match name of MethodInfo.
    /// </summary>
    /// <param name="name"></param>
    /// <param name="methodInfo"></param>
    let (|MethodName|_|) name (methodInfo : MethodInfo) = if methodInfo.Name = name then Some() else None
        
    /// <summary>
    /// Match name of FieldInfo.
    /// </summary>
    /// <param name="name"></param>
    /// <param name="fieldInfo"></param>
    let (|FieldName|_|) name (fieldInfo : FieldInfo) = if fieldInfo.Name = name then Some() else None
    
    /// <summary>
    /// Match quoted expression.
    /// </summary>
    /// <param name="expr">Expr to match</param>
    /// <param name="x">Expr matching against</param>
    let (|Quote|_|) (expr : Expr) (x : Expr) = 
        let _,_,y = exprMatch expr x
        if y then Some () else None

    /// <summary>
    /// Match quoted expression and extract bindings.
    /// </summary>
    /// <param name="expr">Expr to match. Can contain <c>Quote.any name</c> and <c>Quote.withType name</c> which will be extracted.</param>
    /// <param name="x">Expr matching against</param>
    let (|BindQuote|_|) (expr : Expr) (x : Expr) = 
        let a,b,y = exprMatch expr x
        if y then Some (a,b) else None

    /// <summary>
    /// Match quoted expression anywhere in the expression.
    /// </summary>
    /// <param name="expr">Expr to match</param>
    /// <param name="x">Expr matching against</param>
    let (|InnerQuote|_|) (expr : Expr) (x : Expr) = 
        let rec loop = function
            | Quote expr -> Some()
            | ExprShape.ShapeCombination(a_, args) -> args |> List.tryPick loop 
            | ExprShape.ShapeLambda(_, body) -> loop body
            | ExprShape.ShapeVar(_) -> None
        loop x
        
    /// <summary>
    /// Match quoted expression anywhere in the expression and extract bindings.
    /// </summary>
    /// <param name="expr"></param>
    /// <param name="x"></param>
    let (|InnerBindQuote|_|) (expr : Expr) (x : Expr) = 
        let rec loop = function
            | BindQuote expr d -> Some d
            | ExprShape.ShapeCombination(_, args) -> args |> List.tryPick loop 
            | ExprShape.ShapeLambda(_, body) -> loop body
            | ExprShape.ShapeVar(_) -> None
        loop x


    /// <summary>
    /// Match marker by name in extracted bindings. Untyped markers are matched first.
    /// </summary>
    /// <param name="markerName"></param>
    let (|Marker|_|) markerName (anyType : IDictionary<string,Expr>, typed : IDictionary<string,Expr>) = 
        let scc,v = anyType.TryGetValue markerName
        if scc then Some v else 
            let scc2,v2 = typed.TryGetValue markerName
            if scc2 then 
                Some v2 
            else
                None
    
    /// <summary>
    /// Match marker by name in extracted bindings. Only untyped markers are matched.
    /// </summary>
    /// <param name="markerName"></param>
    let (|AnyMarker|_|) markerName (anyType : IDictionary<string,Expr>, _typed : IDictionary<string,Expr>) = 
        let scc,v = anyType.TryGetValue markerName
        if scc then Some v else None
    
    /// <summary>
    /// Match marker by name in extracted bindings. Only typed markers are matched.
    /// </summary>
    /// <param name="markerName"></param>
    let (|TypedMarker|_|) markerName (_anyType : IDictionary<string,Expr>, typed : IDictionary<string,Expr>) = 
        let scc,v = typed.TryGetValue markerName
        if scc then Some v else None        