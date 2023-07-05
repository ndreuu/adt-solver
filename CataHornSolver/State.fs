module CataHornSolver.State

open System.Diagnostics
open System.IO
open System.Timers

type State<'st, 'a> =
    State of ('st -> 'a * 'st)
    
let run state (State f) = f state

let onTimedEvent source (e: ElapsedEventArgs) =
    
    printfn $"""The Elapsed event was raised at {e.SignalTime.ToString "HH:mm:ss.fff"}"""
    
let bind binder stateful =
    State (fun state ->
        let result, state' = stateful |> run state
        binder result |> run state')

type StateBuilder() =
    let (>>=) stateful binder = bind binder stateful
    member _.Return x = State (fun st -> (x, st))
    member _.ReturnFrom x = x
    member _.Bind (st, f) = st >>= f
    member _.Zero () = State (fun st -> ((), st))
    member _.Combine (x, y) = x >>= (fun _ -> y)
    member _.Delay f = f ()

let state = StateBuilder ()

let writeA x =
    State (fun i -> 
        File.AppendAllText ("/home/andrew/Downloads/tttttt/a.txt", $"{x}\n"), i + 1)

let timer = new Timer 1000



let tttt =
    state {
        do! writeA "XYN"
        return! writeA "XYN2"
    } 



let go () =
    let s, a = run 0 tttt
    printfn $"{a}"
    ()


