#r @"C:\Users\User\.nuget\packages\fsharp.quotations.evaluator\1.1.3\lib\\net45\FSharp.Quotations.Evaluator.dll"
#load @"..\Qit\ProvidedTypes.fs"
#load @"..\Qit\Library.fs"
#load @"..\Qit\Patterns.fs"


type Bleh = {A : int}


let expr = <@ fun (a : Bleh) -> a.A @>

let f = Qit.Quote.compileLambda expr


typeof<Bleh>.Assembly.FullName