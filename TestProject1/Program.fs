open SMTLIB2.Parser
module Program =

    [<EntryPoint>]
    let main _ =
      Parser().ParseFile "/home/andrew/sys/bm.vars.smt2"
      |> List.iter (fun x -> printfn "%s\n" <| x.ToString())
      0
