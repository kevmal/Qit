# Qit - Quotation toolkit

A collection of utilities for building, inspecting, transforming and executing F# quotations.

## Installation

Install from nuget at [https://www.nuget.org/packages/Qit/](https://www.nuget.org/packages/Qit/)

```fsharp
#r "nuget:Qit"

```

## Quick Tour

### Splicing

Splicing operators `!%` and `!%%` combined with `Quote.expandOperators` extend what can be spliced. Consider the quoted function `f`:

```fsharp
open Qit
open FSharp.Quotations

type MyType = |A of int | B of double

let f = 
    <@
        fun x -> 
            match x with 
            | A v -> A(v + 1)
            | B v -> B(v + 1.0)
    @>
```

Now, a bit contrived, but lets say we need to use the `Tag` property of `MyType` in a quoted expression. We can't just use `%(Expr.PropertyGet(<@x@>, pinfo))` because `x` is bound in the quotation. We can use `!%` to splice in the expression `x` and then use `Quote.expandOperators` to expand the spliced expression:

```fsharp
let f2 = 
    <@ 
        fun (x : MyType) -> 
            let tag = !%%(Expr.PropertyGet(<@x@>, typeof<MyType>.GetProperty("Tag")))
            printfn "Tag: %d" tag
            match x with 
            | A v -> A(v + 1)
            | B v -> B(v + 1.0)
    @>
    |> Quote.expandOperators

<@ (%f2) (A 1) @> |> Quote.evaluate
```

```
Tag: 0
```

```
A 2
```

Note that `!%` and `!%%` are also available as functions `QitOp.splice` and `QitOp.spliceUntyped` respectively.

### Matching

Simplified pattern matching:

```fsharp
let uselessIf = 
    <@ 
        let a = 34
        if true then
            a + 1
        else
            a - 2
    @>


let rec removeTrivialIfs expr = 
    expr
    |> Quote.traverse
        (fun q -> 
            match q with 
            | BindQuote <@if true then Quote.any "body" else Quote.any "" @> 
                (Marker "body" body)
            | BindQuote <@if false then Quote.any "" else Quote.any "body" @> 
                (Marker "body" body) -> 
                    Some(removeTrivialIfs body)
            | _ -> None
        )
```

`Quote.any` is matching any expression and binding it to a name which can then be extracted with the `Marker` pattern. `Quote.traverse` traverses the quotation and applies the given function to each subexpression optionally replacing it with the result of the function.
If we simply wanted to match with no binding we could have done

```fsharp
uselessIf
|> Quote.exists 
    (function 
     | Quote <@if true then Quote.any "body" else Quote.any "" @> -> 
        true 
     | _ -> false)
```

```
true
```

Again, `Quote.any` is matching any expression, but what about an expression of specific type? For that there's `Quote.withType<'t>`:

```fsharp
uselessIf
|> Quote.exists 
    (function 
     | Quote <@if true then Quote.withType<int> "" else Quote.withType<int> "" @> -> 
        true 
     | _ -> false)
```

```
true
```

```fsharp
uselessIf
|> Quote.exists 
    (function 
     |Quote <@if true then Quote.withType<double> "" else Quote.withType<double> "" @> -> 
        true 
     | _ -> false)
```

```
false
```

When binding to markers , the `Marker` pattern will extract both `Quote.any` and `Quote.withType` bindings. To be specific we could use the `AnyMarker` and `TypedMarker` patterns.
We used an empty string to signify that we're not interested in binding the matched expression. When specifying a name we expect bindings with the same name to be equivalent.

```fsharp
uselessIf
|> Quote.exists 
    (function 
     | Quote <@if true then Quote.withType<int> "myMarker" else Quote.withType<int> "myMarker" @> -> 
        true 
     | _ -> false)
```

```
false
```

Looking at `uselessIf` we can see that the true/false cases are different and so the match fails. Now when they're the same:

```fsharp
let uselessIf2 = 
    <@  
        let a = 32
        if a > 100 then 
            a + 1
        else
            a + 1
    @>

uselessIf2
|> Quote.exists 
    (function 
     | Quote <@ 
        if Quote.withType"" then 
            Quote.withType<int> "myMarker" 
        else Quote.withType<int> "myMarker"
       @> -> true 
     | _ -> false)
```

```
true
```

Variable names must also match unless prefixed with `__`.

```fsharp
uselessIf 
|> Quote.exists 
    (function 
     | Quote <@let a = Quote.any "" in Quote.any ""@> -> true 
     | _ -> false)
```

Original code has `let a` and so it matches.

```
Could not find reference ''
```

```fsharp
uselessIf 
|> Quote.exists 
    (function 
     |Quote <@let b = Quote.any "" in Quote.any ""@> -> true 
     | _ -> false)
```

```
false
```

Original code has `let a` which does not match `let b`

```fsharp
uselessIf 
|> Quote.exists 
    (function 
     | Quote <@let __b = Quote.any "" in Quote.any ""@> -> true 
     | _ -> false)
```

```
true
```

Now that we've prefixed the variable name with `__`, the name of the variable is no longer relevant and it matches.

### Reflection tools

When creating general transformations often quoting code is no longer useful in order to use the runtime `Type` of the expr. Reflection is used to apply type arguments to methods and types and then combined using `Expr.*`. The strategy encouraged here is to create a function with types parameters, use reflection once to apply the Type arguments, and call.
`TypeTemplate.create` is a convenience function to take a function with type parameters and return a function that takes `Type` arguments and applies them to the function. For example say we have,

```fsharp
let q0 = 
    <@ 
        let a = ResizeArray()
        a.Add 10
        a.Add 20
        a.Add 30
        a.ToArray()
    @>
```

and we want to replace the `ResizeArray.Add` method calls with `ResizeArray.AddRange([arg])`. We create a function with a type parameter that is otherwise not present in the function signature.

```fsharp
let addRange0<'a> (o : Expr) (arg : Expr) = 
    let ra  : 'a ResizeArray Expr = o |> Expr.Cast
    let arg : 'a Expr = arg |> Expr.Cast
    <@@ (%ra).AddRange([%arg]) @@>
```

We can then use `TypeTemplate.create` to create a function that takes `Type` arguments and applies them to `addRange0`.

```fsharp
let addRange = TypeTemplate.create addRange0
```

Now instead of the typical reflection mess we can just call the new `addRange` function. The call itself is a compiled expression which is cached on the type arguments given, reducing call overhead compared to `Type.Invoke`.

```fsharp
let result = 
    q0
    |> Quote.traverse
        (fun q -> 
            match q with 
            | BindQuote <@ (Quote.withType<AnyType ResizeArray> "ra").Add(Quote.any "v1") @> 
                (Marker "ra" ra & Marker "v1" v1) -> 
                    Some(addRange [v1.Type] ra v1)
            | _ -> None
        )

let expected = 
    <@
        let a = ResizeArray()
        a.AddRange [10]
        a.AddRange [20]
        a.AddRange [30]
        a.ToArray()
    @>

Quote.isEquivalent result expected
```

```
No value returned by any evaluator
```

If we wanted to inline this concept and forgo the caching provided by `TypeTemplate.create`, `ITypeTemplate<'ReturnType>.Def<'typeParameters>` can be used. Here `'typeParameters` would be either a single type or a tuple representing the needed type parameters. The `Make` method is used to apply the type parameters.

```fsharp
q0
|> Quote.traverse
    (fun q -> 
        match q with 
        | BindQuote <@ (Quote.withType<AnyType ResizeArray> "ra").Add(Quote.any "v1") @> 
            (Marker "ra" ra & Marker "v1" v1) -> 
                { new ITypeTemplate<Expr> with 
                    member _.Def<'a>() = <@@ (%%ra : 'a ResizeArray).AddRange([%%v1]) @@>
                }.Make [v1.Type]
                |> Some
        | _ -> None
    )
```


