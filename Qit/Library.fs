namespace Qit

open System
open System.Reflection
open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Quotations.Patterns
open System.Collections.Generic
open Qit.ProviderImplementation.ProvidedTypes
open Qit.UncheckedQuotations

/// <summary>
/// Provides utilities for working with System.Linq.Expressions.
/// </summary>
module Expression = 
    open System.Linq.Expressions

    /// <summary>
    /// Evaluates a given System.Linq.Expressions.Expression.
    /// If the expression is a LambdaExpression, it compiles and invokes it directly.
    /// If the expression is not a LambdaExpression, it wraps the expression in a LambdaExpression with no parameters, compiles and invokes it.
    /// </summary>
    /// <param name="expression">The System.Linq.Expressions.Expression to evaluate.</param>
    /// <returns>The result of the evaluated expression.</returns>
    let evaluate (expression : Expression) = 
        match expression with 
        | :? LambdaExpression as f -> f.Compile().DynamicInvoke()
        | _ -> Expression.Lambda(expression, []).Compile().DynamicInvoke()


/// <summary>
/// Provides utilities for reflection
/// </summary>
module Reflection = 
    /// <summary>
    /// Decomposes an F# function type into its argument types and return type.
    /// This function recursively traverses the input type, accumulating argument types in a list.
    /// When it encounters a type that is not a function, it treats it as the return type.
    /// </summary>
    /// <param name="t">The F# function type to decompose.</param>
    /// <returns>A tuple where the first element is a list of argument types and the second element is the return type.</returns>
    let decomposeFSharpFunctionType (t : Type) = 
        let rec loop (t : Type) acc = 
            if FSharp.Reflection.FSharpType.IsFunction t then 
                let d,r = FSharp.Reflection.FSharpType.GetFunctionElements(t)
                loop r (d :: acc)
            else
                List.rev acc, t
        loop t []

    /// <summary>
    /// Pretty print type name
    /// </summary>
    /// <param name="t">Target Type</param>
    let rec typeToString (t : Type) = 
        if t.IsGenericType then 
            let targs = t.GetGenericArguments() |> Array.map typeToString
            let name =
                let name = t.FullName
                let i = name.LastIndexOf "`"
                name.Substring(0,i)
            sprintf "%s<%s>" name (targs |> String.concat ", ")
        else
            t.FullName

/// <summary>
/// Convinience extensions for reflection
/// </summary>
[<AutoOpen>]            
module ReflectionExt = 
    type BindingFlags with 
        /// <summary>
        /// A combination of flags that match all members.
        /// </summary>
        static member All = BindingFlags.DeclaredOnly ||| BindingFlags.Public ||| BindingFlags.NonPublic ||| BindingFlags.Static ||| BindingFlags.Instance

/// <summary>
/// Active patterns for reflection
/// </summary>
module ReflectionPatterns = 
    /// <summary>
    /// Active pattern for decomposing an F# function type into its argument types and return type.
    /// If the input type is a function, it will match out (args : Type list * returnType : Type).
    /// </summary>
    let (|FSharpFuncType|_|) (t : Type) = 
        if FSharp.Reflection.FSharpType.IsFunction t then 
            Some(Reflection.decomposeFSharpFunctionType t)
        else
            None
    
    /// <summary>
    /// Active pattern for extracting a specific attribute from a MemberInfo.
    /// </summary>
    let inline (|Attribute|_|) (minfo : MemberInfo) : 'a option = 
        let a  = minfo.GetCustomAttribute<'a>() 
        if isNull(box a) then 
            None
        else
            Some a

    /// <summary>
    /// Active pattern for extracting the declaring type of a MemberInfo.
    /// </summary>
    let (|DeclaringType|) (minfo : MemberInfo) = 
        minfo.DeclaringType

    /// <summary>
    /// Active pattern for checking if a Type implements a specific interface or inherits from a specific class.
    /// </summary>
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

/// <summary>
/// Type used in pattern matching to allow for wildcard type matching. See also <see cref="M:Qit.Quote.any"/> and <see cref="M:Qit.Quote.withType"/>.
/// 
/// </summary>
///
/// <example>
/// The following example shows how to use the AnyType type to match a list of any type.
/// <code>
/// match &lt;@ [] : int list @&gt; with 
/// | Quote &lt;@ [] : AnyType list @&gt; -> printfn "Matched!"
/// | _ -> printfn "No Match!"
/// </code>
/// </example>
///
/// <example>
/// Basic operator overloads allow to match generally over certain operators.
/// <code>
/// match &lt;@ 23.0 + 2.0 @&gt; with 
/// | Quote &lt;@ Quote.any "a" + Quote.any "b" @&gt; -> printfn "Matched!"
/// | _ -> printfn "No Match!"
/// </code>
/// </example>
type AnyType() = 
    static member (+)(a:AnyType,_:AnyType) = a
    static member (-)(a:AnyType,_:AnyType) = a
    static member (*)(a:AnyType,_:AnyType) = a
    static member (/)(a:AnyType,_:AnyType) = a
    static member (&&&)(a:AnyType,_:AnyType) = a
    static member (|||)(a:AnyType,_:AnyType) = a
    static member (<<<)(a:AnyType,_:AnyType) = a

module internal Core = 
    open FSharp.Quotations.Evaluator.QuotationEvaluationExtensions
    let internal methodInfo q =
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

    let castMeth = typeof<Expr>.GetMethod("Cast")

    let internal toTypedExpr (e : Expr) = 
        let t = e.Type
        castMeth.MakeGenericMethod(t).Invoke(null, [|e|])
        
    let rec internal rewriteNestedQuotes x =
        match x with
        | Patterns.QuoteTyped e -> typeof<Expr>.GetMethod("Value").MakeGenericMethod(x.Type).Invoke(null, [|toTypedExpr e|]) :?> Expr
        | Patterns.QuoteRaw e -> Expr.Value(e)
        | ExprShape.ShapeCombination(a, args) -> 
            let nargs = args |> List.map rewriteNestedQuotes
            ExprShape.RebuildShapeCombination(a, nargs)
        | ExprShape.ShapeLambda(v, body) -> Expr.Lambda(v, rewriteNestedQuotes body)
        | ExprShape.ShapeVar(v) -> Expr.Var(v)
        
    let evaluate(q : Expr<'a>) = q.Evaluate()
    let evaluateUntyped(q : Expr) = q.EvaluateUntyped()

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

    let rec traverseQuotation f q = 
        let q = defaultArg (f q) q
        match q with
        | ExprShape.ShapeCombination(a, args) -> 
            let nargs = args |> List.map (traverseQuotation f)
            ExprShape.RebuildShapeCombination(a, nargs)
        | ExprShape.ShapeLambda(v, body) -> Expr.Lambda(v, traverseQuotation f body)
        | ExprShape.ShapeVar(v) -> Expr.Var(v)
                
open Core
    

/// Functions and methods marked as QitOp and ReflectedDefinition will be expanded by Quote.expandOperators
[<AllowNullLiteral>]
type QitOpAttribute() = inherit Attribute()

/// <summary>
/// A type that captures the variable to which it's let-bound within an expression. Typically, this type would be inherited from, and when let-bound in an expression, 
/// the actual value would be evaluated and substituted in the body of the let-binding. The body is then expanded and passed to the <c>Final</c> method, 
/// where the result replaces the entire let-binding.
/// </summary>
///
/// <example>
/// <code>
/// open Qit
/// type Sum() = 
///     inherit QitBindingObj()
///     let exprsToSum = ResizeArray()
///     [&lt;QitOp; ReflectedDefinition&gt;]
///     member x.Add(e : int) = 
///         splice (
///             exprsToSum.Add(&lt;@e@&gt;)
///             &lt;@()@&gt;
///         )
///     member x.SumExpr = 
///         if exprsToSum.Count = 0 then 
///             &lt;@0@&gt;
///         else 
///             exprsToSum |> Seq.reduce (fun a b -> &lt;@ !%a + !%b @&gt;) 
///     [&lt;QitOp; ReflectedDefinition&gt;]
///     member x.CurrentSum() = splice x.SumExpr
/// 
/// &lt;@ 
///     let a = Sum()
///     a.Add(2)
///     let str = "my string"
///     a.Add(str.Length)
///     printfn "Current sum %d" (a.CurrentSum())
///     a.Add(5)
///     printfn "Current sum %d" (a.CurrentSum())
///     a.CurrentSum()
/// @&gt;
/// |> Quote.expandOperators
/// |> Quote.evaluate
/// 
/// // Current sum 11
/// // Current sum 16
/// // val it: int = 16
/// </code>
/// Here we define our <c>Sum</c> type which inherits from <c>QitBindingObj</c>. Methods and properties that are used within quotations typically have the <c>QitOp</c> and <c>ReflectedDefinition</c> attributes.
/// We use a separate <c>SumExpr</c> property since it uses quotation operators internally, and we don't want to expand those within the <c>CurrentSum</c> method, which is a <c>QitOp</c>. This is because the <c>QitOp</c> attribute
/// means <c>Quote.expandOperators</c> will expand the call, and we don't want to expand the <c>SumExpr</c> property call.
///
/// The resulting expression after expansion is similar to:
/// <code>
/// &lt;@ 
///     let str = "my string"
///     printfn "Current sum %d" (2 + str.Length)
///     printfn "Current sum %d" (2 + str.Length + 5)
///     2 + str.Length + 5
/// @&gt;
/// </code>
/// 
/// Had we provided an overload to the <c>Final</c> method, we could have further transformed the expression.
/// </example>
type QitBindingObj() = 
    /// <summary>
    /// An abstract method that is intended to be overridden by derived types to perform a final transformation on an expression before it replaces the let-binding.
    /// </summary>
    /// <param name="e">The expression to be transformed.</param>
    /// <returns>The transformed expression.</returns>
    abstract member Final : Expr -> Expr

    /// <summary>
    /// Provides a default implementation for the <c>Final</c> method that simply returns the input expression without any transformation.
    /// </summary>
    /// <param name="e">The expression to be returned.</param>
    /// <returns>The input expression.</returns>
    default x.Final(e) = e

    /// <summary>
    /// A property that holds an optional variable which may be used by derived types to reference the variable captured by the let-binding.
    /// </summary>
    member val Var : Var option = None with get, set

open ReflectionPatterns

/// <summary>
/// Operators to be used within quotations. 
/// </summary>
[<AutoOpen>]
module QitOp = 
   
    /// <summary>
    /// Include typed expression as is in quotation.
    /// </summary>
    /// <param name="expr">Typed expression to be included</param>
    let escapedQuote (expr : 'a Expr) = expr
    let internal escapedQuoteMeth = (methodInfo <@ escapedQuote @>).GetGenericMethodDefinition()

    /// <summary>
    /// Include untyped expression as is in quotation.
    /// </summary>
    /// <param name="expr">Untyped expression to be included</param>
    let escapedQuoteRaw (x : Expr) = x
    let internal escapedQuoteRawMeth = (methodInfo <@ escapedQuoteRaw @>)


    /// <summary>
    /// Splice Expr into quotation on Quote.expandOperators
    /// </summary>
    /// <param name="expr">Expr to splice in</param>
    let spliceUntyped (expr : Expr) : 'a = Unchecked.defaultof<_> 
    let internal spliceUntypedMeth = (methodInfo <@ spliceUntyped @>).GetGenericMethodDefinition()

    /// <summary>
    /// Splice an <c>Expr&lt;'t&gt;</c> into quotation on <c>Quote.expandOperators</c>
    /// </summary>
    /// <param name="expr">Expr&lt;'t&gt; to splice in</param>
    let splice (x : Expr<'a>) : 'a = Unchecked.defaultof<_>
    let internal splice2Meth = (methodInfo <@ splice @>).GetGenericMethodDefinition()



    /// <summary>
    /// Splice an <c>Expr</c> into quotation on Quote.expandOperators
    /// </summary>
    /// <param name="expr"><c>Expr</c> to splice in</param>
    [<ReflectedDefinition; QitOp>]
    let (!%) expr = splice expr
    
    /// <summary>
    /// Splice <c>Expr&lt;'t&gt;</c> into quotation on <c>Quote.expandOperators</c>
    /// </summary>
    /// <param name="expr"><c>Expr&lt;'t&gt;</c> to splice in</param>
    [<ReflectedDefinition; QitOp>]
    let (!%%) expr = spliceUntyped expr

    /// <summary>
    /// Define a rewriter within quoted code to be expanded by Quote.expandRewriters. Rewriter is a function of type  <c>trail : Expr list * thisCall : Expr * arg : Expr -> 'a</c>
    /// where trail is a list of expressions leading to the current expression, thisCall is the current expression and arg is the argument passed to rewrite. 
    /// <c>rewriteFunc</c> should return <c>(oldExpr, newExpr) option</c>, <c>None</c> would simply expand to the given input, <c>Some(oldExpr,newExpr)</c> would expand to the given input
    /// and further replace <c>oldExpr</c> with <c>newExpr</c> in the expression tree using reference equality.
    /// </summary>
    /// <param name="input">Input argument which is passed to <c>rewriteFunc</c></param>
    /// <param name="rewriteFunc">Function of type <c>trail : Expr list * thisCall : Expr * arg : Expr -> 'a</c></param>
    let rewriter (input : 'input) (rewriteFunc : Expr list -> Expr -> Expr -> (Expr*Expr) option) : 'a = Unchecked.defaultof<'a>
    let internal rewriterMeth = (methodInfo <@ rewriter @>).GetGenericMethodDefinition()

    /// <summary>
    /// Get field by <c>FieldInfo</c>. Expands to <c>Expr.FieldGet(&lt;@ o @&gt;,field)</c>.
    /// </summary>
    /// <param name="field"><c>FieldInfo</c> of field to get</param>
    /// <param name="o">Target obj</param>
    [<ReflectedDefinition; QitOp>]
    let fieldGet (field : FieldInfo) (o : 'a) : 'b = !%%(Expr.FieldGet(<@ o @>,field))
    
    /// <summary>
    /// Get static field by <c>FieldInfo</c>. Expands to <c>Expr.FieldGet(field)</c>.
    /// </summary>
    /// <param name="field"><c>FieldInfo</c> of field to get</param>
    [<ReflectedDefinition; QitOp>]
    let fieldGetStatic (field : FieldInfo) : 'a = !%%(Expr.FieldGet(field))
    
    /// <summary>
    /// Set field by <c>FieldInfo</c>. Expands to <c>Expr.FieldSet(&lt;@o@&gt;,field,&lt;@value@&gt;)</c>.
    /// </summary>
    /// <param name="field"><c>FieldInfo</c> of field to set</param>
    /// <param name="value">New field value</param>
    /// <param name="o">Target obj</param>
    [<ReflectedDefinition; QitOp>]
    let fieldSet (field : FieldInfo) (value : 'a) (o : 'b) : unit =
        !%%(Expr.FieldSet(<@o@>,field,<@value@>))
    
    /// <summary>
    /// Set static field by <c>FieldInfo</c>. Expands to <c>Expr.FieldSet(field,&lt;@value@&gt;)</c>.
    /// </summary>
    /// <param name="field"><c>FieldInfo</c> of field to set</param>
    /// <param name="value">New field value</param>
    [<ReflectedDefinition; QitOp>]
    let fieldSetStatic (field : FieldInfo) (value : 'a) : unit = 
        !%%(Expr.FieldSet(field,<@value@>))

    /// <summary>
    /// Call method by <c>MethodInfo</c>. Expands to <c>Expr.Call(&lt;@o@&gt;,method,args)</c>.
    /// </summary>
    /// <param name="method">MethodInfo of method to call</param>
    /// <param name="args">Method arguments</param>
    /// <param name="o">Target obj</param>
    [<ReflectedDefinition; QitOp>]
    let methodCall (method : MethodInfo) (args : obj list) (o : 'a) : 'b = failwith "methodCall"
    
    /// <summary>
    /// Call static method by <c>MethodInfo</c>. Expands to <c>Expr.Call(method,args)</c>.
    /// </summary>
    /// <param name="method"><c>MethodInfo</c> of method to call</param>
    /// <param name="args">Method arguments</param>
    [<ReflectedDefinition; QitOp>]
    let methodCallStatic (method : MethodInfo) (args : obj list) : 'c  = failwith "methodCall"

    /// <summary>
    /// Splice linq expression
    /// </summary>
    /// <param name="linqExpr">Linq expression to be cpliced</param>
    let spliceInExpression (linqExpr : System.Linq.Expressions.Expression) : 'a = failwith ""
    
    /// <summary>
    /// Splice linq expression
    /// </summary>
    /// <param name="linqExpr">Linq expression to be spliced</param>
    let spliceInExpressionTyped (linqExpr : System.Linq.Expressions.Expression<'a>) : 'a = failwith ""
    
    /// <summary>
    /// Used within a quotation to match an <c>Expr</c> of any type.
    /// </summary>
    /// <param name="name">Name of the marker to later retreive the match</param>
    let any (name : string) : AnyType = failwith "marker"

    /// <summary>
    /// Used within a quotation to match an <c>Expr</c> of specific type.
    /// </summary>
    /// <param name="name">Name of the marker to later retreive the match</param>
    let withType<'a> (name : string) : 'a = failwith "marker"

    /// <summary>
    /// Used within a quotation to match an <c>Expr</c> of any type.
    /// </summary>
    /// <param name="name">Name of the marker to later retreive the match</param>
    let (!@) (name : string) : 'a = failwith "marker"
    
    /// <summary>
    /// Used within a quotation to match an <c>Expr</c> of specific type.
    /// </summary>
    /// <param name="name">Name of the marker to later retreive the match</param>
    let (!@@) (name : string) : AnyType = failwith "marker"
    
/// <summary>
/// Functions for transforming, evaluation, and inspecting <c>Expr</c> and <c>Expr&lt;'a&gt;</c> objects.
/// </summary>
module Quote =
    /// Expr<'a> to System.Linq.Expressions.Expression
    let toExpression (expr : Expr<'a>) = FSharp.Linq.RuntimeHelpers.LeafExpressionConverter.QuotationToExpression(expr)

    /// <summary>
    /// Evaluate a ('a Expr)
    /// </summary>
    /// <param name="expr">('a Expr) to evaluate</param>
    /// <returns> Result of evaluation </returns>
    let evaluate(expr : Expr<'a>) = evaluate expr
    
    /// <summary>
    /// Evaluate Expr
    /// </summary>
    /// <param name="expr">Expr to evaluate</param>
    /// <returns> Result of evaluation </returns>
    let evaluateUntyped(expr : Expr) = evaluateUntyped expr
            
    /// <summary>
    /// Used within a quotation to match an Expr of any type.
    /// </summary>
    /// <param name="name">Name of the marker to later retreive the match</param>
    let any name : AnyType = failwith "marker"

    /// <summary>
    /// Used within a quotation to match an Expr of specific type.
    /// </summary>
    /// <param name="name">Name of the marker to later retreive the match</param>
    let withType<'a> name : 'a = failwith "marker"

    /// <summary>
    /// Raw Expr to typed Expr
    /// </summary>
    /// <param name="expr">Raw Expr to cast</param>
    /// <returns>Typed Expr</returns>
    let typed (expr : Expr) : Expr<'a> = <@ %%expr @>

    /// <summary>
    /// Typed Expr to Raw Expr
    /// </summary>
    /// <param name="expr">Typed Expr to cast</param>
    /// <returns>Raw Expr</returns>
    let untyped (q : Expr<_>) = q.Raw

    /// <summary>
    /// Extract MethodInfo from simple Expr
    /// </summary>
    /// <param name="expr">Expr to extract MethodInfo from</param>
    /// <returns>MethodInfo</returns>
    let methodInfo expr = methodInfo expr

    /// <summary>
    /// Extract MethodInfo from simple Expr. If the method is generic it will further extract the generic method info.
    /// </summary>
    /// <param name="expr">Expr to extract MethodInfo from</param>
    /// <returns>MethodInfo</returns>
    let genericMethodInfo expr = genericMethodInfo expr

    /// <summary>
    /// Apply a substitution to the expr.
    /// </summary>
    /// <param name="f">Substitutionn</param> //TODO
    /// <param name="expr">Target Expr</param>
    let applySubtitution f expr = applySub f expr
    
    /// <summary>
    /// Traverse quotation applying function to each subexpression, if the function returns None the subexpression is left unchanged.
    /// </summary>
    /// <param name="f">Traversal function</param>
    /// <param name="expr">Target Expr</param>
    /// <returns>Transformed Expr</returns>
    let traverse f expr = traverseQuotation f expr

    /// <summary>
    /// Traverse quotation applying function to each subexpression, if the function returns None the subexpression is left unchanged.
    /// </summary>
    /// <param name="f">Traversal function</param>
    /// <param name="expr">Target Expr</param>
    /// <returns>Transformed Expr</returns>
    [<Obsolete("Use traverse instead")>]
    let traverseQuotation f expr = traverseQuotation f expr

    /// <summary>
    /// Traverse quotation applying function to each subexpression, if the function returns None the subexpression is left unchanged. Uncheckd version skips type checks when building the Expr.
    /// </summary>
    /// <param name="f">Traversal function</param> 
    /// <param name="expr">Target Expr</param>
    /// <returns>Transformed Expr</returns>
    let rec traverseUnchecked f expr = UncheckedQuotations.traverseQuotation f expr
    
    /// <summary>
    /// Traverse quotation applying function to each subexpression, if the function returns None the subexpression is left unchanged. Uncheckd version skips type checks when building the Expr.
    /// </summary>
    /// <param name="f">Traversal function</param> 
    /// <param name="expr">Target Expr</param>
    /// <returns>Transformed Expr</returns>
    [<Obsolete("Use traverseUnchecked instead")>]
    let rec traverseQuotationUnchecked f expr = UncheckedQuotations.traverseQuotation f expr

    /// <summary>
    /// Traverse quotation applying function to each subexpression, if the function returns None the subexpression is left unchanged. 
    /// If the function returns Some(true,expr) the subexpression is replaced with expr and the traversal continues on expr.
    /// If the function returns Some(false,expr) the subexpression is replaced with expr and the traversal stops.
    /// </summary>
    /// <param name="f">Traversal function</param>
    /// <param name="expr">Target Expr</param>
    /// <returns>Transformed Expr</returns>
    let rec traverseRecursive f expr = 
        let rec loop q = 
            match f q with 
            | Some(true,q) -> loop q
            | Some(false,q) -> q
            | None -> q
        let q = loop expr
        match q with
        | ExprShape.ShapeCombination(a, args) -> 
            let nargs = args |> List.map (traverseRecursive f)
            ExprShape.RebuildShapeCombination(a, nargs)
        | ExprShape.ShapeLambda(v, body) -> Expr.Lambda(v, traverseRecursive f body)
        | ExprShape.ShapeVar(v) -> Expr.Var(v)
    
    /// <summary>
    /// Traverse quotation applying function to each subexpression, if the function returns None the subexpression is left unchanged. 
    /// If the function returns Some(true,expr) the subexpression is replaced with expr and the traversal continues on expr.
    /// If the function returns Some(false,expr) the subexpression is replaced with expr and the traversal stops.
    /// </summary>
    /// <param name="f">Traversal function</param>
    /// <param name="expr">Target Expr</param>
    /// <returns>Transformed Expr</returns>
    [<Obsolete("Use traverseRecursive instead")>]
    let rec traverseQuotationRec f expr = traverseRecursive f expr
    
    /// <summary>
    /// Replace every occurence of targetVar with replacementVar in expr.
    /// </summary>
    /// <param name="targetVar">Target var</param>
    /// <param name="replacementVar">Replacement Var</param>
    /// <param name="expr">Target Expr</param>
    /// <returns>Transformed Expr</returns>
    let replaceVar targetVar replacementVar expr =
        expr
        |> traverse
            (fun q -> 
                match q with 
                | Patterns.Var(v) when v = targetVar -> Some(replacementVar)
                | _ -> None
            )

    /// <summary>
    /// Expand all Qit operators in expresion. Unchecked version will skip type checks when building the expression.
    /// </summary>
    /// <param name="expr">Target Expr</param>
    /// <returns>Transformed Expr</returns>
    let expandOperatorsUnchecked (expr : Expr) = 
        let rec loop inSplice expr = 
            expr
            |> UncheckedQuotations.traverseQuotation
                (fun q -> 
                    match q with 
                    | Patterns.Let(var, binding, body) when typeof<QitBindingObj>.IsAssignableFrom(binding.Type) ->
                        let b = binding |> loop true |> evaluateUntyped  :?> QitBindingObj
                        b.Var <- Some var
                        let body = 
                            body.Substitute(fun x -> if x = var then Some (Expr.Value(b, binding.Type)) else None)
                            |> loop inSplice
                        b.Final(body) |> Some
                    | Patterns.Let(v,e,b) when inSplice -> 
                        b.Substitute(fun i -> if i = v then Some(e) else None)
                        |> loop inSplice 
                        |> Some
                    | Patterns.Call(o, Attribute (_ : QitOpAttribute) & DerivedPatterns.MethodWithReflectedDefinition(meth), args) -> 
                        let meth = meth 
                        let args = 
                            match o with 
                            | Some b -> [b] @ args
                            | None -> args
                        let res = 
                            match meth with 
                            | DerivedPatterns.Lambdas(v, body) -> 
                                let assign = args 
                                let assign = 
                                    if List.length assign < List.length v then 
                                        assign @ [ <@@ () @@> ]
                                    else
                                        assign
                                (v |> List.concat, assign)
                                ||> List.zip
                                |> Seq.fold 
                                    (fun (e : Expr) (v,a) -> 
                                        e.Substitute(fun x -> if x = v then Some a else None)
                                    ) body
                            | _ -> failwith "Unreachable"
                        res
                        |> loop inSplice 
                        |> Some
                    | Patterns.Call(None, minfo, [e]) when minfo.IsGenericMethod && minfo.GetGenericMethodDefinition() = splice2Meth -> 
                        let q = loop true e
                        Some(q |> evaluateUntyped :?> Expr)
                    | Patterns.Call(None, minfo, [e]) when minfo.IsGenericMethod && minfo.GetGenericMethodDefinition() = spliceUntypedMeth -> 
                        let q = loop true e
                        Some(q |> evaluateUntyped :?> _)
                    | Patterns.Application(Patterns.Lambda(v,b), arg) when inSplice -> 
                        Some(b.Substitute(fun i -> if i = v then Some arg else None) |> loop true)
                    | Patterns.Let(v, q, b) when inSplice && v.Type = typeof<Expr> ->
                        let expr = loop true q |> evaluateUntyped :?> Expr
                        Some(b.Substitute(fun i -> if i = v then Some (Expr.Value expr) else None) |> loop true)
                    | Patterns.Let(v, q, b) when inSplice && v.Type.IsGenericType && v.Type.GetGenericTypeDefinition() = typedefof<Expr<_>> ->
                        let expr = loop true q |> evaluateUntyped :?> Expr
                        let expr = typeof<Expr>.GetMethod("Cast").MakeGenericMethod(v.Type.GetGenericArguments().[0]).Invoke(null, [|expr|])
                        Some(b.Substitute(fun i -> if i = v then Some (Expr.Value(expr, v.Type)) else None) |> loop true)
                    | Patterns.QuoteRaw q when inSplice -> 
                        Some(Expr.Value(loop false q))
                    | Patterns.QuoteTyped q2 when inSplice -> 
                        let expr = loop false q2
                        let expr = typeof<Expr>.GetMethod("Cast").MakeGenericMethod(q2.Type).Invoke(null, [|expr|])
                        Some(Expr.Value(expr, q.Type))
                    | _ -> None
                )
        loop false expr

    let internal lunbox<'a> x : 'a = unbox x
    let internal lunboxMethod = match <@ lunbox<obj> (failwith "") @> with | Patterns.Call(_,minfo,_) -> minfo.GetGenericMethodDefinition() | _ -> failwith "lunboxMethod unreachable"
    
    let internal pipeRightMethod = genericMethodInfo <@ (|>) @>
    let internal pipeLeftMethod = genericMethodInfo <@ (<|) @>
                
    let internal (|PipeCall|_|) x = 
        match x with 
        | Patterns.Call(None,minfo,[value;f]) when minfo.IsGenericMethod && (minfo.GetGenericMethodDefinition() = pipeRightMethod || minfo.GetGenericMethodDefinition() = pipeLeftMethod) ->
            let rec loop acc x = 
                match x with 
                | Patterns.Let(v,e,b) when not v.IsMutable -> loop (Map.add v e acc) b
                | Patterns.Lambda(v,Patterns.Call(i,m,a)) -> 
                    let a = 
                        a 
                        |> List.map 
                            (fun x -> 
                                match x with 
                                | Patterns.Var(v) when Map.containsKey v acc -> acc.[v]
                                | Patterns.Var(vv) when v = vv -> value
                                | _ -> x
                            )
                    let varsNotAllBound = 
                        a
                        |> Seq.exists
                            (fun x ->
                                x.GetFreeVars() |> Seq.exists (fun v -> Map.containsKey v acc)
                            )
                    if varsNotAllBound then 
                        None
                    else
                        Some(i,m,a)
                | _ -> None
            loop Map.empty f
        | _ -> None

    let internal (|AnyCall|_|) expr = 
        match expr with 
        | PipeCall(i,m,a)
        | Patterns.Call(i,m,a) -> Some(i,m,a)
        | _ -> None
    /// <summary>
    /// Expand all Qit operators in untyped expresion.
    /// </summary>
    /// <param name="expr">Target Expr</param>
    /// <returns>Transformed Expr</returns>
    let expandOperatorsUntyped (expr : Expr) = 
        let rec loop inSplice expr = 
            expr
            |> traverse
                (fun q -> 
                    match q with 
                    | Patterns.Let(var, binding, body) when typeof<QitBindingObj>.IsAssignableFrom(binding.Type) ->
                        let b = binding |> loop true |> evaluateUntyped  :?> QitBindingObj
                        b.Var <- Some var
                        let body = 
                            body.Substitute(fun x -> if x = var then Some (Expr.Value(b, binding.Type)) else None)
                            |> loop inSplice
                        b.Final(body) |> Some
                    | Patterns.Let(v,((Patterns.Lambda _ as r) as e),b) when inSplice -> 
                        b.Substitute(fun i -> if i = v then Some(e) else None)
                        |> loop inSplice 
                        |> Some
                    | Patterns.Let(v,e,b) when inSplice && e.GetFreeVars() |> Seq.isEmpty -> 
                        let e = lazyWrap inSplice v.Type e
                        b.Substitute(fun i -> if i = v then Some(e) else None)
                        |> loop inSplice 
                        |> Some
                    | Patterns.Let(v,e,b) when inSplice -> 
                        let e = lazyWrap inSplice v.Type e
                        b.Substitute(fun i -> if i = v then Some(e) else None)
                        |> loop inSplice 
                        |> Some
                    | Patterns.PropertyGet(o, Attribute (_ : QitOpAttribute) & DerivedPatterns.PropertyGetterWithReflectedDefinition(meth), args) 
                    | AnyCall(o, Attribute (_ : QitOpAttribute) & DerivedPatterns.MethodWithReflectedDefinition(meth), args) -> 
                        let meth = meth 
                        let args = 
                            match o with 
                            | Some b -> [b] @ args
                            | None -> args
                        let res = 
                            match meth with 
                            | DerivedPatterns.Lambdas(v, body) -> 
                                let assign = args 
                                let assign = 
                                    if List.length assign < List.length v then 
                                        assign @ [ <@@ () @@> ]
                                    else
                                        assign
                                (v |> List.concat, assign)
                                ||> List.zip
                                |> Seq.fold 
                                    (fun (e : Expr) (v,a) -> 
                                        e.Substitute(fun x -> if x = v then Some a else None)
                                    ) body
                            | e -> e
                        res
                        |> loop inSplice 
                        |> Some
                    | Patterns.Call(None, minfo, [e]) when minfo.IsGenericMethod && minfo.GetGenericMethodDefinition() = splice2Meth -> 
                        let q = loop true e
                        Some(q |> evaluateUntyped :?> Expr)
                    | Patterns.Call(None, minfo, [e]) when minfo.IsGenericMethod && minfo.GetGenericMethodDefinition() = spliceUntypedMeth -> 
                        let q = loop true e
                        Some(q |> evaluateUntyped :?> _)
                    | Patterns.Application(Patterns.Lambda(v,b), arg) when inSplice -> 
                        if arg.GetFreeVars() |> Seq.isEmpty then 
                            let arg = lazyWrap inSplice v.Type arg
                            Some(b.Substitute(fun i -> if i = v then Some arg else None) |> loop true)
                        else 
                            Some(b.Substitute(fun i -> if i = v then Some arg else None) |> loop true)
                    | Patterns.Call(None, m, [Patterns.QuoteRaw q]) when inSplice && m = escapedQuoteRawMeth -> 
                        Some(Expr.QuoteRaw(loop true q))
                    | Patterns.QuoteRaw q when inSplice -> 
                        Some(Expr.Value(loop false q))
                    | Patterns.Call(None, m, [Patterns.QuoteTyped q]) when inSplice && m.IsGenericMethod && m.GetGenericMethodDefinition() = escapedQuoteMeth -> 
                        Some(Expr.QuoteTyped(loop true q))
                    | Patterns.QuoteTyped q2 when inSplice -> 
                        let expr = loop false q2
                        let expr = typeof<Expr>.GetMethod("Cast").MakeGenericMethod(q2.Type).Invoke(null, [|expr|])
                        Some(Expr.Value(expr, q.Type))
                    | Patterns.Call(None, m, [a]) when not inSplice && m.IsGenericMethod && m.GetGenericMethodDefinition() = lunboxMethod -> Some(Expr.Value(evaluateUntyped q, q.Type))
                    | _ -> None
                )
        and lazyWrap inSplice tp e = 
            match e with 
            | Patterns.Value _ -> e
            | _ -> 
                let f = lazy (e |> loop inSplice |> evaluateUntyped)
                match <@@ lunbox f.Value @@> with 
                | Patterns.Call(None, minfo, args) -> Expr.Call(minfo.GetGenericMethodDefinition().MakeGenericMethod(tp), args)
                | _ -> failwithf "unbox never"
            
        loop false expr
    

    /// <summary>
    /// Expand all Qit operators in Expr.
    /// </summary>
    /// <param name="expr">Target Expr</param>
    /// <returns>Transformed Expr</returns>
    let expandOperators (expr : Expr<'a>) : Expr<'a> =
        expr |> expandOperatorsUntyped |> Expr.Cast

    /// <summary>
    /// Expand all rewriters in Expr.
    /// </summary>
    /// <param name="expr">Target Expr</param>
    /// <returns>Transformed Expr</returns>
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


    let internal markerMethod1 = methodInfo <@ any "" @>
    let internal markerMethod2 = methodInfo <@ QitOp.any "" @>
    let internal markerMethod3 = methodInfo <@ !@@ "" @>
    let internal typedMarkerMethod1 = genericMethodInfo <@ withType "" @>
    let internal typedMarkerMethod2 = genericMethodInfo <@ QitOp.withType "" @>
    let internal typedMarkerMethod3 = genericMethodInfo <@ !@ "" @>
    let internal genericMethod (m : MethodInfo) = if m.IsGenericMethod then m.GetGenericMethodDefinition() else m

    let internal (|MarkerMethod|_|) (m : MethodInfo) = 
        if m = markerMethod1 then Some(None)
        elif m = markerMethod2 then Some(None)
        elif m = markerMethod3 then Some(None)
        elif m.IsGenericMethod then 
            let gm = m.GetGenericMethodDefinition() 
            if gm = typedMarkerMethod1 then Some(Some(m.GetGenericArguments().[0]))
            elif gm = typedMarkerMethod2 then Some(Some(m.GetGenericArguments().[0]))
            elif gm = typedMarkerMethod3 then Some(Some(m.GetGenericArguments().[0]))
            else None
        else None


    /// <summary>
    /// Attempts to match two Expr trees against each other. Quote.anyType and Quote.typed&lt;'a&gt; markers are extracted. 
    /// Variables starting with __ are treated as wildcards, otherwise their names must match.
    /// </summary>
    /// <param name="a">Expr to compare</param>
    /// <param name="b">Expr to compare</param>
    /// <returns>untypedMarkers:Dictionary * typedMarkers : Dictionary * matchResult : bool</returns>
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
            | Call (None, MarkerMethod(tpOpt), [Value (name,_)]), a 
            | a, Call (None, MarkerMethod(tpOpt), [Value (name,_)]) -> 
                match tpOpt with 
                | None ->
                    let name = name :?> string
                    match markers.TryGetValue(name) with 
                    | true, e ->
                        exprEq e a
                    | _ ->
                        if name <> "" then markers.[name] <- a
                        true
                | Some tp ->
                    let name = name :?> string
                    match typedMarkers.TryGetValue(name) with 
                    | true, e ->
                        exprEq e a
                    | _ -> 
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
                typeEq unionCaseInfo.DeclaringType unionCaseInfo1.DeclaringType &&
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
            if a.IsArray && b.IsArray then 
                typeEq (a.GetElementType()) (b.GetElementType())
            elif a.IsGenericType && b.IsGenericType then 
                a.GetGenericTypeDefinition() = b.GetGenericTypeDefinition() &&
                    (Array.map2 typeEq (a.GetGenericArguments()) (b.GetGenericArguments())
                     |> Array.fold (&&) true)
            else
                a = typeof<AnyType> || b = typeof<AnyType> || a = b
        and propEq (a : PropertyInfo) (b : PropertyInfo) = 
            a = b || 
                (typeEq a.DeclaringType b.DeclaringType && a.Name = b.Name && typeEq a.PropertyType b.PropertyType)
        and methEq (a : MethodInfo) (b : MethodInfo) = 
            let genArgsEq() =
                let args1 = a.GetGenericArguments()
                let args2 = b.GetGenericArguments()
                args1.Length = args2.Length &&
                    ((args1, args2) 
                     ||> Seq.map2 typeEq 
                     |> Seq.contains false 
                     |> not )
            let checkGenericType() =
                if a.DeclaringType.IsGenericType && b.DeclaringType.IsGenericType then   
                    let adef = a.DeclaringType.GetGenericTypeDefinition()
                    let bdef = b.DeclaringType.GetGenericTypeDefinition()
                    if adef = bdef then
                        let nameEq() = a.Name = b.Name
                        let returnEq() = typeEq a.ReturnType b.ReturnType
                        let paramTpsEq() = 
                            let p1 = a.GetParameters()
                            let p2 = b.GetParameters()
                            p1.Length = p2.Length 
                            &&
                                (
                                    (p1, p2)
                                    ||> Seq.map2 (fun a b -> a.Name = b.Name && typeEq a.ParameterType b.ParameterType)
                                    |> Seq.contains false
                                    |> not
                                )
                        genArgsEq() && nameEq() && returnEq() && paramTpsEq()
                    else
                        false
                else
                    false
                        
            a = b 
                || (a.IsGenericMethod && b.IsGenericMethod && a.GetGenericMethodDefinition() = b.GetGenericMethodDefinition() && genArgsEq())
                || checkGenericType()
        markers, typedMarkers, exprEq a b

    /// <summary>
    /// Check for equivalence between Exprs.
    /// </summary>
    /// <param name="a">Expr to check</param>
    /// <param name="b">Expr to check</param>
    let isEquivalent (a : Expr) (b : Expr) = 
        let _markers, _typedMarkers, eq = exprMatch a b
        eq

    let internal (|Quote|_|) (e : Expr) (x : Expr) = 
        let _,_,y = exprMatch e x
        if y then Some () else None

    let internal (|BindQuote|_|) (e : Expr) (x : Expr) = 
        let a,b,y = exprMatch e x
        if y then Some (a,b) else None

    /// <summary>
    /// Expand let bindings in Expr
    /// </summary>
    /// <param name="vars">Var replacements</param>
    /// <param name="expr">Target Expr</param>
    /// <returns>Expanded Expr</returns>
    let rec expand vars expr = 
      let expanded = 
        match expr with
        | ExprShape.ShapeVar v when Map.containsKey v vars -> vars.[v]
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
      match expanded with
      | Patterns.Application(ExprShape.ShapeLambda(v, body), assign)
      | Patterns.Let(v, assign, body) when not v.IsMutable -> expand (Map.add v (expand vars assign) vars) body
      | _ -> expanded
    
    let internal typeStr t = Reflection.typeToString t

    /// Simplified string representation of Expr
    let rec str q =
        match q with
        | AddressOf(expr) -> sprintf "&(%s)" (str expr)
        | AddressSet(expr1, expr2) -> sprintf "(%s) <- (%s)" (str expr1) (str expr2)
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
        | NewDelegate(type1, varList, expr) -> 
            sprintf "new %s(%s)" (typeStr type1) (varList |> List.map (fun v -> sprintf "(%s)" (v.Name)) |> String.concat ",")
        | NewObject(constructorInfo, exprList) -> 
            sprintf "(new %s(%s))"(typeStr constructorInfo.DeclaringType) (exprList |> List.map (str >> sprintf "(%s)") |> String.concat ",")
        | NewRecord(type1, exprList) -> 
            sprintf "(new %s(%s))" (typeStr type1) (exprList |> List.map (str >> sprintf "(%s)") |> String.concat ",")
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
        | TryWith(expr1, var1, expr2, var2, expr3) -> 
            sprintf "(try (%s) with | %s -> (%s) | %s -> (%s))" (str expr1) var1.Name (str expr2) var2.Name (str expr3)
        | TupleGet(expr, int1) -> sprintf "(%s)[%d]" (str expr) int1
        | TypeTest(expr, type1) -> sprintf "((%s) :? %s)" (str expr) (typeStr type1)
        | UnionCaseTest(expr, unionCaseInfo) -> 
            sprintf "((%s) :? %s)" (str expr) (typeStr unionCaseInfo.DeclaringType)
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
    /// <summary>
    /// Will expand the application of a lambda expression to a let binding
    /// </summary>
    /// <param name="expr">Target Expr</param>
    let rec expandLambda expr = 
        match expr with 
        | Patterns.Application(ExprShape.ShapeLambda(v, body), assign) -> 
            Expr.Let(v,assign,expandLambda body)
        | _ -> expr

    /// <summary>
    /// Extract succesive <c>let</c> bindings from an expression
    /// </summary>
    /// <param name="expr">Target Expr</param>
    /// <returns>Var*Expr bindings and body Expr</returns>
    let decomposeLetBindings expr =    
        let rec loop acc e = 
            match e with 
            | Patterns.Let(v,ass,body) -> 
                loop ((v,ass) :: acc) body
            | _ -> acc, e
        loop [] expr
        
    open System.Linq.Expressions

    /// <summary>
    /// Convert Expr of a F# function to an Expression.Lambda
    /// </summary>
    /// <param name="x"></param>
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
    
    let internal linqSpliceMeth = (methodInfo <@ spliceInExpression @>).GetGenericMethodDefinition()
    let internal linqSpliceTypedMeth = (methodInfo <@ spliceInExpressionTyped @>).GetGenericMethodDefinition()

    let expandExpressionSplices (e : 'e) = 
        let visitor = 
            {new ExpressionVisitor() with 
                member x.VisitMethodCall(e : MethodCallExpression) =
                    if e.Method.IsStatic && e.Method.IsGenericMethod && e.Method.GetGenericMethodDefinition() = linqSpliceMeth then 
                        let a = Expression.Lambda(e.Arguments.[0],[]).Compile().DynamicInvoke() :?> Expression
                        a
                    elif e.Method.IsStatic && e.Method.IsGenericMethod && e.Method.GetGenericMethodDefinition() = linqSpliceTypedMeth then 
                        Expression.Lambda(e.Arguments.[0],[]).Compile().DynamicInvoke() :?> Expression
                    else
                        Expression.Call(x.Visit(e.Object), e.Method, e.Arguments |> Seq.map x.Visit) :> _
            }
        visitor.VisitAndConvert<'e>(e, "expandExpressionSplices")
    
    /// <summary>
    /// Tests if any sub-Expr of the Expr satisfies the predicate 
    /// </summary>
    /// <param name="predicate">(Expr -> bool) to be applied to each sub-Expr</param>
    /// <param name="expr">Target Expr</param>
    let rec exists predicate (expr : Expr) = 
        if predicate expr then 
            true
        else
            match expr with
            | ShapeCombinationUnchecked(a, args) -> args |> List.exists (exists predicate)
            | ShapeLambdaUnchecked(v, body) -> exists predicate body
            | ShapeVarUnchecked(v) -> false
    
    /// <summary>
    /// Tests if the Expr contains the specified Expr.
    /// </summary>
    /// <param name="query">Expr to search for</param>
    /// <param name="expr">Target Expr</param>
    let rec contains query (expr : Expr)  = 
        match expr with
        | Quote query -> true
        | ShapeCombinationUnchecked(_, args) -> args |> List.exists (contains query)
        | ShapeLambdaUnchecked(_, body) -> contains query body
        | ShapeVarUnchecked(_) -> false


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
    
    /// <summary>
    /// Compiles Expr on lambda into an assembly and returns the lambda. Additional assembly references can be specified.
    /// </summary>
    /// <param name="refs">Assembly references to include</param>
    /// <param name="expr">Target expr</param>
    let compileLambdaWithRefs refs (expr : Expr<'a>) = 
        let q = expr
        let refs = 
            let ra = ResizeArray()
            q
            |> traverse
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
        let rt = typeof<int>.Assembly
        let cfg = CompilerServices.TypeProviderConfig(rt.GetType >> isNull >> not)
        cfg.ReferencedAssemblies <- refs |> Seq.filter (fun x -> not x.IsDynamic) |> Seq.map (fun x -> x.Location) |> Seq.toArray
        let ctx = ProvidedTypesContext(cfg, [], refs |> Seq.toList)//[System.Reflection.Assembly.GetExecutingAssembly()])
        let t2 = ctx.ConvertSourceProvidedTypeDefinitionToTarget(t)
        let compiler = AssemblyCompiler(t2.Assembly :?> _, ctx)
        let bytes = compiler.Compile(false)
        let a = System.Reflection.Assembly.Load(bytes)
        let r = a.GetTypes() |> Seq.head
        let mt = r.GetMethod("meth")
        FSharp.Linq.RuntimeHelpers.LeafExpressionConverter.EvaluateQuotation(build mt) :?> 'a

    /// <summary>
    /// Compiles Expr on lambda into an assembly and returns the lambda.
    /// </summary>
    /// <param name="expr">Expr to compile</param>
    let compileLambda expr = compileLambdaWithRefs [] expr
 
        
/// <summary>
/// Provides extension methods on System.Linq.Expressions.Expression.
/// </summary>
[<AutoOpen>]
module ExpressionExtensions =
    open System.Linq.Expressions
    type Expression with 
        static member Func(f : Expr<'a -> 'b>) : Expression<Func<'a,'b>> = Quote.toFuncExpression f
        static member Func(f : Expr<'a -> 'b -> 'c>) : Expression<Func<'a,'b,'c>> = Quote.toFuncExpression f
        static member Func(f : Expr<'a -> 'b -> 'c -> 'd>) : Expression<Func<'a,'b,'c,'d>> = Quote.toFuncExpression f
        static member Func(f : Expr<'a -> 'b -> 'c -> 'd -> 'e>) : Expression<Func<'a,'b,'c,'d,'e>> = Quote.toFuncExpression f
        static member Func(f : Expr<'a -> 'b -> 'c -> 'd -> 'e -> 'f>) : Expression<Func<'a,'b,'c,'d,'e,'f>> = Quote.toFuncExpression f
        static member Func(f : Expr<'a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g>) : Expression<Func<'a,'b,'c,'d,'e,'f,'g>> = Quote.toFuncExpression f
        static member Func(f : Expr<'a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'h>) : Expression<Func<'a,'b,'c,'d,'e,'f,'g,'h>> = Quote.toFuncExpression f
        static member Func(f : Expr<'a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'h -> 'i>) : Expression<Func<'a,'b,'c,'d,'e,'f,'g,'h,'i>> = Quote.toFuncExpression f


open Quote

type TypeTemplate<'a> private () =  
    static let cache = Dictionary<MethodInfo, Dictionary<Type list, 'a>>()
    static let tryCache minfo (types : Type list) builder = 
        let scc,lu2 = cache.TryGetValue(minfo)
        if scc then 
            let scc,v = lu2.TryGetValue(types)
            if scc then 
                v
            else
                let v = builder()
                lu2.[types] <- v
                v
        else
            let lu2 = Dictionary()
            let v = builder()
            lu2.[types] <- v
            cache.[minfo] <- lu2
            v
    /// <summary>
    /// Constructs a function given a generic function and a list of Type arguments
    /// </summary>
    /// <param name="f">Generic function to apply type arguments to</param>
    static member create ([<ReflectedDefinition(false)>] f : Expr<'a>) : Type list -> 'a  = 
        let makeMethod (minfo : MethodInfo) =
            if minfo.IsGenericMethod then
                let minfodef = minfo.GetGenericMethodDefinition()
                fun types -> minfodef.MakeGenericMethod(types |> Seq.toArray)
            else
                fun _ -> minfo
        match f with
        | DerivedPatterns.Lambdas(vs, Patterns.Call(o,minfo,args)) -> 
            let makeMethod = makeMethod minfo
            fun types -> 
                tryCache minfo types
                    (fun () ->
                        let method = makeMethod types
                        let lambda = 
                            let call = 
                                match o with 
                                | Some o -> Expr.Call(o,method,args)
                                | None -> Expr.Call(method,args)
                            (vs, call)
                            ||> List.foldBack
                                (fun v s -> 
                                    match v with 
                                    | [v] -> Expr.Lambda(v,s) 
                                    | l -> failwith "'lambas' tuple not suported" 
                                )
                        FSharp.Linq.RuntimeHelpers.LeafExpressionConverter.EvaluateQuotation lambda :?> 'a)
        | Patterns.Call(o,minfo,args) -> 
            let makeMethod = makeMethod minfo
            fun types -> 
                tryCache minfo types
                    (fun () ->
                        let method = makeMethod types
                        let parameters = method.GetParameters()
                        let vars = Array.init parameters.Length (fun i -> Var(sprintf "v%d" i, parameters.[i].ParameterType))
                        let body = 
                            match o with
                            | Some o -> Expr.Call(o,minfo,vars |> Array.map Expr.Var |> Array.toList)
                            | None -> Expr.Call(minfo,vars |> Array.map Expr.Var |> Array.toList)
                        let lambda = Array.foldBack (fun x s -> Expr.Lambda(x,s)) vars body
                        FSharp.Linq.RuntimeHelpers.LeafExpressionConverter.EvaluateQuotation lambda :?> 'a)
        | _ -> failwithf "Expecting Expr.Call got: \r\n --------- \r\n %A \r\n ---------" f

/// <summary>
/// Facilitates the use of inline type parameters. For non-inline use cases, refer to <see cref="M:Qit.TypeTemplate.create"/>.
///
/// </summary>
///
/// <example>
/// Suppose we have an object of type <c>obj</c>. Let's define it for illustrative purposes:
/// <code>
/// let myObj = box "hi"
/// </code>
/// If we wish to create a function that produces a typed tuple of <c>myObj, [myObj]</c>, it would typically require tedious reflection. With <c>ITypeTemplate</c>, this can be achieved as:
/// <code>
/// let myNewObj =  
///     { new ITypeTemplate&lt;obj&gt; with 
///         member _.Def&lt;'t&gt;() =
///             let t = myObj :?> 't
///             t, [t]
///     }.Make [myObj.GetType()]
/// </code>
/// We use <c>ITypeTemplate&lt;obj&gt;</c> since the actual returned type is <c>obj</c> (the type of <c>myNewObj</c>). The <c>Def&lt;'t&gt;</c> method defines a type parameter to work with (the actual type of <c>myObj</c>). Although <c>myNewObj</c> is of type <c>obj</c>, it can be used in functions/methods that accept a <c>string * (string list)</c> tuple.
/// </example>
///
/// <remarks>
/// Note that the complexity of this approach arises from the F# limitation that doesn't allow defining functions with type parameters within another function or method. Using an interface serves as a workaround.
/// </remarks>
type ITypeTemplate<'b> =    
    abstract member Def<'a> : unit -> 'b

[<AutoOpen>]
module TypeTemplateExt = 
    type ITypeTemplate<'b> with 
        member x.Make (t:Type seq) = 
            let t = t |> Seq.toArray
            let t = 
                if t.Length > 1 then 
                    [| FSharp.Reflection.FSharpType.MakeTupleType (t) |]
                else
                    t
            typeof<ITypeTemplate<'b>>.GetMethod("Def").MakeGenericMethod(t).Invoke(x,[||]) :?> 'b
