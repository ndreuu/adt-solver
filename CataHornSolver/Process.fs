module Process.Process

open System.IO

type ProcessResult =
  { ExitCode: int
    StdOut: string
    StdErr: string }


open System

let trim (s: string) = s.TrimEnd ([| '\r'; '\n' |])

let execute processName processArgs =
  // let psi = Diagnostics.ProcessStartInfo (processName, $"""{processArgs}""")
  let psi =
    Diagnostics.ProcessStartInfo (
      "bash",
      $"""-c "cd {FileInfo(System.Reflection.Assembly.GetExecutingAssembly().Location)
                    .Directory.FullName}; time {processName} {processArgs}" """
    )

  psi.UseShellExecute <- false
  psi.RedirectStandardOutput <- true
  psi.RedirectStandardError <- true
  psi.CreateNoWindow <- true
  let proc = Diagnostics.Process.Start (psi)
  let output = Text.StringBuilder ()
  let error = Text.StringBuilder ()
  proc.OutputDataReceived.Add (fun args -> output.Append (args.Data) |> ignore)
  proc.ErrorDataReceived.Add (fun args -> error.Append (args.Data) |> ignore)

  let text = proc.StandardOutput.ReadToEnd ()
  let error = proc.StandardError.ReadToEnd ()

  proc.WaitForExit ()

  { ExitCode = proc.ExitCode
    StdOut = text |> trim
    StdErr = error }
