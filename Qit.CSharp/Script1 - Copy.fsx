


#r "nuget:ICSharpCode.Decompiler"
#r "nuget:Mono.Cecil"
#r "nuget:Vagabond"

open ICSharpCode.Decompiler
open ICSharpCode.Decompiler.CSharp
open Mono.Cecil

let ds = DecompilerSettings()
let d = CSharpDecompiler(typeof<unit>.Assembly.Location,ds)

let asm = Mono.Cecil.AssemblyDefinition.ReadAssembly(typeof<unit>.Assembly.Location)





let mp = asm.MainModule.GetType("Microsoft.FSharp.Collections.ArrayModule").Methods |> Seq.find (fun x -> x.Name.Contains "Map")
let eh = System.Reflection.Metadata.Ecma335.MetadataTokens.EntityHandle(mp.MetadataToken.ToInt32())

let poo = d.DecompileAsString([eh])

printfn "%s" poo

open MBrace.Vagabond

let vmanager = Vagabond.Initialize(cacheDirectory = @"C:\Users\User\Desktop\delme")


type Solution(nums) =
        
    let lu = nums |> Seq.indexed |> Seq.groupBy snd |> Seq.map (fun (g,xs) -> g, xs |> Seq.map fst |> Seq.toArray) |> dict

    let rng = System.Random()
    member __.Pick(target) = 
        let a = lu.[target]
        let j = rng.Next(a.Length)
        a.[j]
    

let pick (s: Solution) = s.Pick(23)
    
let asms = vmanager.ComputeObjectDependencies(pick,true)


	

let vagabondAssembly = vmanager.GetVagabondAssembly asms

