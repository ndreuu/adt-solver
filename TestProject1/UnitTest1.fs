module TestProject1

open Approximation
open NUnit.Framework
open SMTLIB2
open Utils
open Approximation.Linearization
open Approximation.SolverDeprecated


[<SetUp>]
let Setup () =
    ()

[<Test>]
let Test1 () =
    // let flip f a b = f b a
    // printfn "AAA"
    // let len = List.fold (fun acc _ -> acc + 1) 0  
    // // let count = List.fold (fun acc x -> (len 0) x + acc)
    // // let count = List.fold (fun acc x -> (+) acc <| len x)
    // // let count = List.fold ((+) <| len)
    // let count = List.fold (flip <| (len >> (+))) 0
    // count [[0;1;2]; [0;1]; [0]; []]
    // |> printfn "%d"
     // let cmds = RmNats.commands ("/home/andrew/Downloads/CAV2022Orig(9)/TIP.Original.Linear/tip2015_sort_ISortCount.smt2")
     
     // cmds
     // |> fun (cmds: originalCommand list) -> RmNats.nat_names cmds
     // |> RmNats.filter cmds
     // |> fun x -> List.fold (fun acc x -> sprintf "%s\n%O" acc x) "" x
     // |> printfn "%s" 
     // |> RmNats.string |> printf "%s"
     // RmNats.replace_nat "/home/andrew/Downloads/CAV2022Orig(9)/TIP.Original.Linear/tip2015_sort_ISortCount.smt2"
     // |> printfn "%s"
     // RmNats.commands "/home/andrew/Downloads/CAV2022Orig(9)/TIP.Original.Linear/tip2015_sort_ISortCount.smt2"
     // |> RmNats.constructors
     // |> List.fold (fun _ x -> printfn "%O"  x) ()
     // RmNats.change "/home/andrew/Downloads/false_productive_use_of_failure_app_inj1.smt2"
     // Evaluation.Interpreter.test_defs ()
     // Evaluation.Interpreter.test_eval ()
     Assert.Pass()
     
     
