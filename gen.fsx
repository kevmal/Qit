open System
open System.IO
open System.Diagnostics

let run cmd args = 
    let p = new Process()
    p.StartInfo.WorkingDirectory <- __SOURCE_DIRECTORY__
    p.StartInfo.FileName <- cmd
    p.StartInfo.Arguments <- args
    p.StartInfo.UseShellExecute <- false
    p.Start() |> ignore
    p.WaitForExit()
    if p.ExitCode <> 0 then
        failwithf "Command failed: %s\r\nExitCode %d" cmd p.ExitCode
let (+/) a b = Path.Combine(a,b)
let cp from to_ = 
    File.Copy(from, to_, true)
    printfn "Copied %s to %s" from to_

run "dotnet" """fsdocs build --eval --strict --ignoreprojects --noapidocs --input solutionmd"""
cp (__SOURCE_DIRECTORY__ +/ "output" +/ "readme.md") (__SOURCE_DIRECTORY__ +/ "README.md")





