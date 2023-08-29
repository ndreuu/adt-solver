module Process.Process
open System.IO
open System.Text.RegularExpressions
open System.Threading.Tasks
// open ProofBased.Utils

open Fli

type ProcessResult = { 
    ExitCode : int; 
    StdOut : string; 
    StdErr : string 
}


open System

let trim (s: string) = s.TrimEnd([| '\r'; '\n' |])

let execute timeout processName processArgs =
    let psi = Diagnostics.ProcessStartInfo (processName, $"""{processArgs}""") 
    // let psi = Diagnostics.ProcessStartInfo ("bash", $"""-c "time {processName} {processArgs}" """) 
    psi.UseShellExecute <- false
    psi.RedirectStandardOutput <- true
    psi.RedirectStandardError <- true
    psi.CreateNoWindow <- true
    let proc = Diagnostics.Process.Start(psi) 
    let output = Text.StringBuilder()
    let error = Text.StringBuilder()
    proc.OutputDataReceived.Add(fun args -> output.Append(args.Data) |> ignore)
    proc.ErrorDataReceived.Add(fun args -> error.Append(args.Data) |> ignore)

    let text = proc.StandardOutput.ReadToEnd()
    let error = proc.StandardError.ReadToEnd()
    
    
    // error.Split('\n')
    // |>
    // printfn $"{ }"
    
    proc.WaitForExit()
    { ExitCode = proc.ExitCode
      StdOut = text |> trim
      StdErr = error  }

let asf () =
    let aasd = execute 0.1 "./z3" "-h"
    printfn $"{aasd}"
    
let tt () =
    let a = execute 0 "bash" """-c "time z3 fp.spacer.global=true /home/andrew/Downloads/jjj/dbg/lol/15/horn-input.smt2" """
    printfn $"{a.StdErr}"


// let runWithTimeout (timeout: int) (action: unit -> 'a) : 'a option =
//   let work = Task.Run (fun () -> Some (action ()))
//   let delay = Task.Delay(timeout).ContinueWith (fun _ -> None)
//   Task.WhenAny(work, delay).Result.Result
//
// let foreachFleTimeout timeout dir f g =
//   let files = Directory.GetFiles (dir, @"*.smt2")
//
//   for file in files do
//     runWithTimeout timeout f |> g file

let executeTl timeout processName processArgs =
    execute timeout $"{processName}" $"{processArgs}"

open SMTLIB2
open System
open System.Diagnostics
open System.Text


module FileSystem =
    let isDirectory path =
        if File.Exists(path) then File.GetAttributes(path).HasFlag(FileAttributes.Directory)
        else Directory.CreateDirectory(path) |> ignore; true

    type tmpFileConfig = {namer: (unit -> string) option; outputDir: path option; extension: string option}
    let createTempFile (config : tmpFileConfig) =
        let outputDir =
            match config.outputDir with
            | Some outputDirectory when isDirectory outputDirectory -> outputDirectory
            | _ -> Path.GetTempPath()
        let outputName =
            match config.namer with
            | Some namer -> namer
            | None -> fun () -> Path.GetFileNameWithoutExtension(Path.GetTempFileName())
        let ext =
            match config.extension with
            | Some ext -> ext
            | None -> "tmp"
        fun () -> Path.Combine(outputDir, $"{outputName ()}.{ext}")


[<AbstractClass>]
type Program () =
    abstract RunOnFile : path -> path -> bool
    abstract FileExtension : string
    default x.FileExtension = ".smt2"

    member private x.IsExtensionOK ext = ext = ".smt2"

    static member SaveFile (dst : path) (lines : string list) =
        Directory.CreateDirectory(Path.GetDirectoryName(dst)) |> ignore
        File.WriteAllLines(dst, lines)

    member private x.CheckedRunOnFile (path : path) path' =
        IdentGenerator.reset ()
        if x.IsExtensionOK <| Path.GetExtension(path) then
            let path' = Path.ChangeExtension(path', x.FileExtension)
            if x.RunOnFile path path' then Some path' else None
        else None

    abstract Run : path -> path option -> path option
    default x.Run (path : path) (outputPath : path option) =
        match () with
        | _ when File.Exists(path) ->
            let path' = FileSystem.createTempFile {outputDir=outputPath; extension=Some(Path.GetExtension(path)); namer=None} ()
            File.Delete(path')
            x.CheckedRunOnFile path path'
        | _ when Directory.Exists(path) ->
            let path' = FileSystem.createTempFile {outputDir=outputPath; extension=None; namer=None} ()
            walk_through_copy path path' (fun path path' -> x.CheckedRunOnFile path path' |> ignore)
            Some path'
        | _ -> failwith $"There is no such file or directory: %s{path}"





[<AbstractClass>]
type ProgramRunner () =
    inherit Program()

    let error = StringBuilder()
    let output = StringBuilder()

    abstract ShouldSearchForBinaryInEnvironment : bool
    abstract BinaryOptions : path -> string
    abstract BinaryName : string

    member private x.HandleErrorLineReceived(line : string) = error.AppendLine(line) |> ignore
    member private x.HandleOutputLineReceived(line : string) = output.AppendLine(line) |> ignore
    member private x.ErrorReceived () = error.ToString()
    member private x.OutputReceived () = output.ToString()
    member private x.ResetErrorReceiver () = error.Clear() |> ignore
    member private x.ResetOutputReceiver () = output.Clear() |> ignore

    member private x.WorkingDirectory (filename : path) =
        if x.ShouldSearchForBinaryInEnvironment
            then Environment.GetEnvironmentVariable(x.BinaryName)
            else filename
        |> Path.GetDirectoryName

    member private x.SetupProcess (psinfo : ProcessStartInfo) filename =
        let executable = Option.defaultValue x.BinaryName <| Dictionary.tryFind x.BinaryName psinfo.Environment
        let arguments = x.BinaryOptions filename
        let statisticsFile = Path.GetTempFileName()
        File.Delete(statisticsFile)
        psinfo.FileName <- "/usr/bin/time"
        psinfo.Arguments <- $"--output=%s{statisticsFile} --format=%%M,%%e %s{executable} %s{arguments}"
        // printfn $"Run: %s{psinfo.FileName} %s{psinfo.Arguments}"
        psinfo.WorkingDirectory <- x.WorkingDirectory filename
        executable, statisticsFile

    member x.RunProcessOn (srcPath : path) =
        x.ResetErrorReceiver ()
        x.ResetOutputReceiver ()
        use p = new Process()
        p.StartInfo.RedirectStandardOutput <- true
        p.StartInfo.RedirectStandardError <- true
        p.StartInfo.UseShellExecute <- false
        p.StartInfo.CreateNoWindow <- true
        p.StartInfo.WindowStyle <- ProcessWindowStyle.Hidden
        p.ErrorDataReceived.Add(fun e -> x.HandleErrorLineReceived e.Data)
        p.OutputDataReceived.Add(fun o -> x.HandleOutputLineReceived o.Data)
        let executable, statisticsFile = x.SetupProcess p.StartInfo srcPath

        p.Start() |> ignore
        p.BeginOutputReadLine()                     // output is read asynchronously
        p.BeginErrorReadLine()                      // error is read asynchronously: if we read both stream synchronously, deadlock is possible
                                                    // see: https://docs.microsoft.com/en-us/dotnet/api/system.diagnostics.processstartinfo.redirectstandardoutput?view=net-5.0#code-try-4

//        if p.HasExited then raise(Exception($"err: {x.ErrorReceived().Trim()}; out: {x.OutputReceived().Trim()}"))
        let st = p.StartTime
        let isChildProcess (pr : Process) =
            try
                pr.StartTime >= st && pr.ProcessName = executable
            with _ -> false
        let child_solver = Process.GetProcesses() |> List.ofArray |> List.filter isChildProcess |> List.tryHead

        let hasFinished = p.WaitForExit(100000)
        if hasFinished then p.WaitForExit() else
            try match child_solver with
                | Some child_solver -> child_solver.Kill(true)
                | _ -> p.Kill(true)
            with _ -> ()
        p.Close()
        let error = x.ErrorReceived().Trim()
        let output = x.OutputReceived().Trim()
        statisticsFile, hasFinished, error, output

type transformOptions = {tip: bool; sync_terms: bool; child_transformer: ProgramRunner option}
type solvingOptions = {keep_exists: bool; table: bool}
// type transformContext = {commands: transformedCommand list; diseqs: Map<sort, operation>}


type A () =
  inherit ProgramRunner ()
  override this.BinaryOptions file = $"-w- {file}"
  override this.ShouldSearchForBinaryInEnvironment = false
  override this.BinaryName = "redcsl"
  override this.RunOnFile var0 var1 = failwith "todo"
    
type RunRedlog () = 
  inherit ProgramRunner ()
  override this.BinaryOptions file = $"-w- {file}"
  override this.ShouldSearchForBinaryInEnvironment = false
  override this.BinaryName = "redcsl"
  override this.RunOnFile var0 var1 = failwith "todo"


    

type RunZ3 () = 
  inherit ProgramRunner ()
  override this.BinaryOptions file = $"fp.spacer.global=true fp.xform.inline_eager=true fp.xform.inline_linear=true {file}"
  override this.ShouldSearchForBinaryInEnvironment = true
  override this.BinaryName = "z3"
  override this.RunOnFile var0 var1 = failwith "todo"

let executeZ3 file =
    let r = RunZ3 ()
    let _, hasFinished, error, output = r.RunProcessOn file
    { StdErr = error; StdOut = output |> trim; ExitCode = if hasFinished then 1 else 0 }
    
    
    
// let tst () =
    // execute "redcsl" "-w- /home/andrew/adt-solver/smr/upd/false_cfg5_unambig/dbg/lol/1/a.smt2"
    // |> printfn "%O"

let sss () =
  execute -1 "./z3" "-T:5 /home/andrew/Downloads/jjj/xyn/smt-input.smt2"
  |> printfn "%O"