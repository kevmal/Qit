#r "nuget:Microsoft.CodeAnalysis.CSharp"
#r "nuget:Microsoft.CodeAnalysis.Workspaces.Common"
#r "nuget:FSharp.Quotations.Evaluator"

#load @"..\Qit\ProvidedTypes.fs"
#load @"..\Qit\Library.fs"
#load @"..\Qit\Patterns.fs"

#load "trynew.fs"
#load "Library.fs"

#load @"trynew2.fs"








open Qit.CSharp3.Bleh
open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Quotations.Patterns
open Microsoft.FSharp.Quotations.DerivedPatterns
open Qit.UncheckedQuotations
open Qit.ProviderImplementation.ProvidedTypes
open System
open System.Reflection
open System.Collections.Generic


let (|SpecificCall|_|) templateParameter = 
    // Note: precomputation
    match templateParameter with
    | (Lambdas(_, Call(_, minfo1, _)) | Call(_, minfo1, _)) ->
        let targetType = minfo1.DeclaringType
        let minfo1 = targetType.GetMethod(minfo1.Name, bindAll)
        let isg1 = minfo1.IsGenericMethod
        let gmd = 
            if minfo1.IsGenericMethodDefinition then 
                minfo1
            elif isg1 then 
                minfo1.GetGenericMethodDefinition() 
            else null

        // end-of-precomputation

        (fun tm ->
           match tm with
           | Call(obj, minfo2, args)
              when (minfo1.MetadataToken = minfo2.MetadataToken &&
                    if isg1 then
                      minfo2.IsGenericMethod && gmd = minfo2.GetGenericMethodDefinition()
                    else
                      minfo1 = minfo2) ->
               Some(obj, (minfo2.GetGenericArguments() |> Array.toList), args)
           | _ -> None)
    | _ ->
         invalidArg "templateParameter" "The parameter is not a recognized method name"
                 
let isGenerated = true

let rec simplifyExpr q =
    match q with
    // Convert NewTuple to the call to the constructor of the Tuple type (only for generated types, 
    // the F# compile does the job for erased types when it receives the quotation)
    | NewTuple(items) when isGenerated ->
        let rec mkCtor args ty =
            let ctor, restTyOpt = Reflection.FSharpValue.PreComputeTupleConstructorInfo ty
            match restTyOpt with
            | None -> Expr.NewObjectUnchecked(ctor, List.map simplifyExpr args)
            | Some restTy ->
                let curr = [for a in Seq.take 7 args -> simplifyExpr a]
                let rest = List.ofSeq (Seq.skip 7 args)
                Expr.NewObjectUnchecked(ctor, curr @ [mkCtor rest restTy])
        let tys = [ for e in items -> e.Type ]
        let tupleTy = ProvidedTypeBuilder.MakeTupleType(tys, q.Type.IsValueType)
        simplifyExpr (mkCtor items tupleTy)

    // convert TupleGet to the chain of PropertyGet calls (only for generated types)
    | TupleGet(e, i) when isGenerated ->
        let rec mkGet (ty : Type) i (e: Expr)  =
            if ty.IsValueType then 
                let get index =
                        let fields = ty.GetFields() |> Array.sortBy (fun fi -> fi.Name) 
                        if index >= fields.Length then
                            invalidArg "index" (sprintf "The tuple index '%d' was out of range for tuple type %s" index ty.Name)
                        fields.[index]
                let tupleEncField = 7
                let fget = Expr.FieldGetUnchecked(e, get i)
                if i < tupleEncField then
                    fget
                else
                    let etys = ty.GetGenericArguments()
                    mkGet etys.[tupleEncField] (i - tupleEncField) fget
            else
                let pi, restOpt = Reflection.FSharpValue.PreComputeTuplePropertyInfo(ty, i)
                let propGet = Expr.PropertyGetUnchecked(e, pi)
                match restOpt with
                | None -> propGet
                | Some (restTy, restI) -> mkGet restTy restI propGet
        simplifyExpr (mkGet e.Type i (simplifyExpr e))

    | Value(value, ty) ->
        if value |> isNull |> not then
            let tyOfValue = value.GetType()
            transValue(value, tyOfValue, ty)
        else q
(*
    // Eliminate F# property gets to method calls
    | PropertyGet(obj, propInfo, args) ->
        match obj with
        | None -> simplifyExpr (Expr.CallUnchecked(propInfo.GetGetMethod(true), args))
        | Some o -> simplifyExpr (Expr.CallUnchecked(simplifyExpr o, propInfo.GetGetMethod(true), args))

    // Eliminate F# property sets to method calls
    | PropertySet(obj, propInfo, args, v) ->
            match obj with
            | None -> simplifyExpr (Expr.CallUnchecked(propInfo.GetSetMethod(true), args@[v]))
            | Some o -> simplifyExpr (Expr.CallUnchecked(simplifyExpr o, propInfo.GetSetMethod(true), args@[v]))
*)
    // Eliminate F# function applications to FSharpFunc<_, _>.Invoke calls
    | Application(f, e) ->
        simplifyExpr (Expr.CallUnchecked(simplifyExpr f, f.Type.GetMethod "Invoke", [ e ]) )

    // Eliminate F# union operations
    | NewUnionCase(ci, es) ->
        simplifyExpr (Expr.CallUnchecked(Reflection.FSharpValue.PreComputeUnionConstructorInfo ci, es) )

    // Eliminate F# union operations
    | UnionCaseTest(e, uc) ->
        let tagInfo = Reflection.FSharpValue.PreComputeUnionTagMemberInfo uc.DeclaringType
        let tagExpr =
            match tagInfo with
            | :? PropertyInfo as tagProp ->
                    simplifyExpr (Expr.PropertyGet(e, tagProp) )
            | :? MethodInfo as tagMeth ->
                    if tagMeth.IsStatic then simplifyExpr (Expr.Call(tagMeth, [e]))
                    else simplifyExpr (Expr.Call(e, tagMeth, []))
            | _ -> failwith "unreachable: unexpected result from PreComputeUnionTagMemberInfo. Please report this bug to https://github.com/fsprojects/FSharp.TypeProviders.SDK/issues"
        let tagNumber = uc.Tag
        simplifyExpr <@@ (%%(tagExpr): int) = tagNumber @@>

    // Eliminate F# record operations
    | NewRecord(ci, es) ->
        simplifyExpr (Expr.NewObjectUnchecked(Reflection.FSharpValue.PreComputeRecordConstructorInfo ci, es) )

    // Explicitly handle weird byref variables in lets (used to populate out parameters), since the generic handlers can't deal with byrefs.
    //
    // The binding must have leaves that are themselves variables (due to the limited support for byrefs in expressions)
    // therefore, we can perform inlining to translate this to a form that can be compiled
    | Let(v, vexpr, bexpr) when v.Type.IsByRef -> transLetOfByref v vexpr bexpr
    
    | Let(v, vexpr, bexpr) when v.Type = typeof<unit> 
        && (
            bexpr.GetFreeVars()
            |> Seq.exists (fun x -> x = v)
            |> not
        ) -> 
        Expr.Sequential(simplifyExpr vexpr, simplifyExpr bexpr)

    // Eliminate recursive let bindings (which are unsupported by the type provider API) to regular let bindings
    | LetRecursive(bindings, expr) -> simplifyLetRec bindings expr

    // Handle the generic cases
    | ShapeLambdaUnchecked(v, body) -> Expr.Lambda(v, simplifyExpr body)
    | ShapeCombinationUnchecked(comb, args) -> RebuildShapeCombinationUnchecked(comb, List.map simplifyExpr args)
    | ShapeVarUnchecked _ -> q

and simplifyLetRec bindings expr =
    // This uses a "lets and sets" approach, converting something like
    //    let rec even = function
    //    | 0 -> true
    //    | n -> odd (n-1)
    //    and odd = function
    //    | 0 -> false
    //    | n -> even (n-1)
    //    X
    // to something like
    //    let even = ref Unchecked.defaultof<_>
    //    let odd = ref Unchecked.defaultof<_>
    //    even := function
    //            | 0 -> true
    //            | n -> !odd (n-1)
    //    odd  := function
    //            | 0 -> false
    //            | n -> !even (n-1)
    //    X'
    // where X' is X but with occurrences of even/odd substituted by !even and !odd (since now even and odd are references)
    // Translation relies on typedefof<_ ref> - does this affect ability to target different runtime and design time environments?
    let vars = List.map fst bindings
    let refVars = vars |> List.map (fun v -> Var(v.Name, ProvidedTypeBuilder.MakeGenericType(typedefof<_ ref>, [v.Type])))

    // "init t" generates the equivalent of <@ ref Unchecked.defaultof<t> @>
    let init (t:Type) =
        let r = match <@ ref 1 @> with Call(None, r, [_]) -> r | _ -> failwith "Extracting MethodInfo from <@ 1 @> failed"
        let d = match <@ Unchecked.defaultof<_> @> with Call(None, d, []) -> d | _ -> failwith "Extracting MethodInfo from <@ Unchecked.defaultof<_> @> failed"
        let ir = ProvidedTypeBuilder.MakeGenericMethod(r.GetGenericMethodDefinition(), [ t ])
        let id = ProvidedTypeBuilder.MakeGenericMethod(d.GetGenericMethodDefinition(), [ t ])
        Expr.CallUnchecked(ir, [Expr.CallUnchecked(id, [])])

    // deref v generates the equivalent of <@ !v @>
    // (so v's type must be ref<something>)
    let deref (v:Var) =
        let m = match <@ !(ref 1) @> with Call(None, m, [_]) -> m | _ -> failwith "Extracting MethodInfo from <@ !(ref 1) @> failed"
        let tyArgs = v.Type.GetGenericArguments()
        let im = ProvidedTypeBuilder.MakeGenericMethod(m.GetGenericMethodDefinition(), Array.toList tyArgs)
        Expr.CallUnchecked(im, [Expr.Var v])

    // substitution mapping a variable v to the expression <@ !v' @> using the corresponding new variable v' of ref type
    let subst =
        let map = [ for v in refVars -> v.Name, deref v ] |> Map.ofList
        fun (v:Var) -> Map.tryFind v.Name map

    let refExpr = expr.Substitute(subst)

    // maps variables to new variables
    let varDict = [ for (v, rv) in List.zip vars refVars -> v.Name, rv ] |> dict

    // given an old variable v and an expression e, returns a quotation like <@ v' := e @> using the corresponding new variable v' of ref type
    let setRef (v:Var) e =
        let m = match <@ (ref 1) := 2 @> with Call(None, m, [_;_]) -> m | _ -> failwith "Extracting MethodInfo from <@ (ref 1) := 2 @> failed"
        let im = ProvidedTypeBuilder.MakeGenericMethod(m.GetGenericMethodDefinition(), [ v.Type ])
        Expr.CallUnchecked(im, [Expr.Var varDict.[v.Name]; e])

    // Something like
    //  <@
    //      v1 := e1'
    //      v2 := e2'
    //      ...
    //      refExpr
    //  @>
    // Note that we must substitute our new variable dereferences into the bound expressions
    let body =
        bindings
        |> List.fold (fun b (v, e) -> Expr.Sequential(setRef v (e.Substitute subst), b)) refExpr

    // Something like
    //   let v1 = ref Unchecked.defaultof<t1>
    //   let v2 = ref Unchecked.defaultof<t2>
    //   ...
    //   body
    (body, vars)
    ||> List.fold (fun b v -> Expr.LetUnchecked(varDict.[v.Name], init v.Type, b)) 
    |> simplifyExpr


and transLetOfByref v vexpr bexpr =
    match vexpr with
    | Sequential(e', vexpr') ->
        (* let v = (e'; vexpr') in bexpr => e'; let v = vexpr' in bexpr *)
        Expr.Sequential(e', transLetOfByref v vexpr' bexpr)
        |> simplifyExpr
    | IfThenElse(c, b1, b2) ->
        (* let v = if c then b1 else b2 in bexpr => if c then let v = b1 in bexpr else let v = b2 in bexpr *)
        //
        // Note, this duplicates "bexpr"
        Expr.IfThenElseUnchecked(c, transLetOfByref v b1 bexpr, transLetOfByref v b2 bexpr)
        |> simplifyExpr
    | Var _ ->
        (* let v = v1 in bexpr => bexpr[v/v1] *)
        bexpr.Substitute(fun v' -> if v = v' then Some vexpr else None)
        |> simplifyExpr
    | _ ->
        failwithf "Unexpected byref binding: %A = %A. Please report this bug to https://github.com/fsprojects/FSharp.TypeProviders.SDK/issues" v vexpr

and transValueArray (o: Array, ty: Type) =
    let elemTy = ty.GetElementType()
    let converter = getValueConverterForType elemTy
    let elements = [ for el in o -> converter el ]
    Expr.NewArrayUnchecked(elemTy, elements)

and transValueList(o, ty: Type, nil, cons) =
    let converter = getValueConverterForType (ty.GetGenericArguments().[0])
    o
    |> Seq.cast
    |> List.ofSeq
    |> fun l -> List.foldBack(fun o s -> Expr.NewUnionCase(cons, [ converter(o); s ])) l (Expr.NewUnionCase(nil, []))
    |> simplifyExpr

and getValueConverterForType (ty: Type) =
    if ty.IsArray then
        fun (v: obj) -> transValueArray(v :?> Array, ty)
    elif ty.IsGenericType && ty.GetGenericTypeDefinition() = typedefof<_ list> then
        let nil, cons =
            let cases = Reflection.FSharpType.GetUnionCases(ty)
            let a = cases.[0]
            let b = cases.[1]
            if a.Name = "Empty" then a, b
            else b, a

        fun v -> transValueList (v :?> System.Collections.IEnumerable, ty, nil, cons)
    else
        fun v -> Expr.Value(v, ty)

and transValue (v: obj, tyOfValue: Type, expectedTy: Type) =
    let converter = getValueConverterForType tyOfValue
    let r = converter v
    if tyOfValue <> expectedTy then Expr.Coerce(r, expectedTy)
    else r

let getFastFuncType (args: list<Expr>) resultType =
    let types =
        [|  for arg in args -> arg.Type
            yield resultType |]
    let fastFuncTy =
        match List.length args with
        | 2 -> typedefof<OptimizedClosures.FSharpFunc<_, _, _>>.MakeGenericType(types) 
        | 3 -> typedefof<OptimizedClosures.FSharpFunc<_, _, _, _>>.MakeGenericType(types) 
        | 4 -> typedefof<OptimizedClosures.FSharpFunc<_, _, _, _, _>>.MakeGenericType(types) 
        | 5 -> typedefof<OptimizedClosures.FSharpFunc<_, _, _, _, _, _>>.MakeGenericType(types) 
        | _ -> invalidArg "args" "incorrect number of arguments"
    fastFuncTy.GetMethod("Adapt")

let (===) a b = LanguagePrimitives.PhysicalEquality a b

let traverse f =
    let rec fallback e =
        match e with
        | Let(v, value, body) ->
            let fixedValue = f fallback value
            let fixedBody = f fallback body
            if fixedValue === value && fixedBody === body then
                e
            else
                Expr.LetUnchecked(v, fixedValue, fixedBody)
        | ShapeVarUnchecked _ -> e
        | ShapeLambdaUnchecked(v, body) ->
            let fixedBody = f fallback body
            if fixedBody === body then
                e
            else
                Expr.Lambda(v, fixedBody)
        | ShapeCombinationUnchecked(shape, exprs) ->
            let exprs1 = List.map (f fallback) exprs
            if List.forall2 (===) exprs exprs1 then
                e
            else
                RebuildShapeCombinationUnchecked(shape, exprs1)
    fun e -> f fallback e

let rightPipe = <@@ (|>) @@>
let inlineRightPipe expr =
    let rec loop expr = traverse loopCore expr
    and loopCore fallback orig =
        match orig with
        | SpecificCall rightPipe (None, _, [operand; applicable]) ->
            let fixedOperand = loop operand
            match loop applicable with
            | Lambda(arg, body) ->
                let v = Var("__temp", operand.Type)
                let ev = Expr.Var v

                let fixedBody = loop body
                Expr.Let(v, fixedOperand, fixedBody.Substitute(fun v1 -> if v1 = arg then Some ev else None))
            | fixedApplicable -> Expr.Application(fixedApplicable, fixedOperand)
        | x -> fallback x
    loop expr


let inlineValueBindings e =
    let map = Dictionary(HashIdentity.Reference)
    let rec loop expr = traverse loopCore expr
    and loopCore fallback orig =
        match orig with
        | Let(id, (Value(_) as v), body) when not id.IsMutable ->
            map.[id] <- v
            let fixedBody = loop body
            map.Remove(id) |> ignore
            fixedBody
        | ShapeVarUnchecked v ->
            match map.TryGetValue v with
            | true, e -> e
            | _ -> orig
        | x -> fallback x
    loop e


let optimizeCurriedApplications expr =
    let rec loop expr = traverse loopCore expr
    and loopCore fallback orig =
        match orig with
        | Application(e, arg) ->
            let e1 = tryPeelApplications e [loop arg]
            if e1 === e then
                orig
            else
                e1
        | x -> fallback x
    and tryPeelApplications orig args =
        let n = List.length args
        match orig with
        | Application(e, arg) ->
            let e1 = tryPeelApplications e ((loop arg)::args)
            if e1 === e then
                orig
            else
                e1
        | Let(id, applicable, (Lambda(_) as body)) when n > 0 ->
            let numberOfApplication = countPeelableApplications body id 0
            if numberOfApplication = 0 then orig
            elif n = 1 then Expr.Application(applicable, List.head args)
            elif n <= 5 then
                let resultType =
                    applicable.Type
                    |> Seq.unfold (fun t ->
                        if not t.IsGenericType then None else
                        let args = t.GetGenericArguments()
                        if args.Length <> 2 then None else
                        Some (args.[1], args.[1])
                    )
                    |> Seq.toArray
                    |> (fun arr -> arr.[n - 1])

                let adaptMethod = getFastFuncType args resultType
                let adapted = Expr.Call(adaptMethod, [loop applicable])
                let invoke = adapted.Type.GetMethod("Invoke", [| for arg in args -> arg.Type |])
                Expr.Call(adapted, invoke, args)
            else
                (applicable, args) ||> List.fold (fun e a -> Expr.Application(e, a))
        | _ ->
            orig
    and countPeelableApplications expr v n =
        match expr with
        // v - applicable entity obtained on the prev step
        // \arg -> let v1 = (f arg) in rest ==> f
        | Lambda(arg, Let(v1, Application(Var f, Var arg1), rest)) when v = f && arg = arg1 -> countPeelableApplications rest v1 (n + 1)
        // \arg -> (f arg) ==> f
        | Lambda(arg, Application(Var f, Var arg1)) when v = f && arg = arg1 -> n
        | _ -> n
    loop expr


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

open System
open Qit.ProviderImplementation.ProvidedTypes

let simple1 = 
    <@ 
        let a = 1
        let b = 2
        a + b
    @>

let forLoop1 = 
    <@ 
        let mutable a = 0
        for i = 0 to 100 do
            a <- a + 1
    @>
    
//let simp = QuotationSimplifier(true)
let q2 = forLoop1 |>inlineRightPipe |> optimizeCurriedApplications |> inlineValueBindings |> simplifyExpr //|> firstPass
    
let str = convExpr q2
let prn x = printfn "%O" x

q
|> inlineRightPipe 
|> optimizeCurriedApplications 
|> inlineValueBindings 
|> simplifyExpr //|> firstPass
|> Qit.CSharp.Quote.toCSharpString
|> prn



q
|> Qit.CSharp2.Quote.toCSharpString
|> prn

