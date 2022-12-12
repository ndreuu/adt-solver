module Utils

open System
open System.IO
open Microsoft.FSharp.Collections
open SMTLIB2

module RmNats =
  open Microsoft.FSharp.Collections
  open SMTLIB2.Parser
  open SMTLIB2.Prelude

  let p = Parser(false)
  
  let commands = p.ParseFile

  let string: originalCommand list -> string =
    List.fold (fun acc x -> sprintf "%s\n%O" acc x) ""
  //fst(name constr) and len of last

  let nat_constructors =
    List.fold
      (fun acc cmd ->
        match cmd with
        | Command (DeclareDatatype (name, constructors)) when name.Contains ("nat", StringComparison.OrdinalIgnoreCase) ->
          constructors
          |> List.map (fun (name, _, args) -> (name.ToString (), List.length args))
          |> (@) acc
        | Command (DeclareDatatypes vs) ->
          List.fold
            (fun _ (name: string, constructors) ->
              if name.Contains ("nat", StringComparison.OrdinalIgnoreCase) then
                constructors
                |> List.map (fun (name, _, args) -> (name.ToString (), List.length args))
                |> (@) acc
              else
                acc)
            acc
            vs
        | _ -> acc)
      []

  let int_sorts =
    List.unfold (fun state ->
      if state = 0 then
        None
      else
        Some (IntSort, state - 1))

  let constructors_to_fns =
    List.map (fun (name, cnt) -> Command (DeclareFun (name, int_sorts cnt, IntSort)))

  let nat_names =
    let rm_nat_data' acc cmd =
      let helper nats =
        function
        | Command (DeclareDatatype (name, _)) when name.Contains ("nat", StringComparison.OrdinalIgnoreCase) ->
          name :: nats
        | Command (DeclareDatatypes vs) ->
          List.fold
            (fun nats (name: string, _) ->
              if name.Contains ("nat", StringComparison.OrdinalIgnoreCase) then
                name :: nats
              else
                acc)
            acc
            vs
        | _ -> nats

      helper acc cmd

    List.fold rm_nat_data' []

  let filter cmds nat_names =
    List.fold
      (fun acc cmd ->
        match cmd with
        | Command (DeclareDatatype (name, _)) when nat_names |> List.contains name -> acc
        | Command (DeclareDatatypes types) ->
          (types
           |> (List.filter (function
             | name, _ when nat_names |> List.contains name -> false
             | _ -> true))
           |> fun defs ->
                match List.length defs with
                | 0 -> acc
                | _ -> Command (command.DeclareDatatypes defs) :: acc)
        | otherwise -> otherwise :: acc)
      []
      cmds
    |> List.rev

  let find k = List.filter <| (=) k >> List.head

  let replace_nat_str (nat_names: _ list) =
    List.map (fun cmd ->
      List.fold
        (fun (acc: string) (name: string) ->
          if (sprintf "%O" acc).Contains (name, StringComparison.OrdinalIgnoreCase) then
            (nat_names |> find name) |> fun name' -> acc.Replace (name', "Int")
          else
            acc)
        cmd
        nat_names)

  let replace_nat cmds =
    let nat_names = nat_names cmds

    nat_names
    |> filter cmds
    |> List.map (sprintf "%O")
    |> replace_nat_str nat_names
    |> function
      | x :: xs -> x :: (List.map (sprintf "%O") <| (constructors_to_fns (nat_constructors cmds))) @ xs
      | otherwise -> otherwise 
    |> List.fold (fun acc cmd -> sprintf "%s\n%s" acc cmd) ""
  
  let constructors_cnt =
    let add acc = function
      | Command (DeclareDatatype _) -> acc + 1 
      | Command (DeclareDatatypes vs) -> acc + List.length vs
      | _ -> acc
    
    List.fold add 0
  
  let nat_constructors_cnt =
    let add acc = function
      | Command (DeclareDatatype (name, _)) when name.Contains ("nat", StringComparison.OrdinalIgnoreCase) -> acc + 1 
      | Command (DeclareDatatypes vs) ->
          (List.length <| List.filter (fun (name:string, _) -> name.Contains ("nat", StringComparison.OrdinalIgnoreCase) ) vs) + acc
      | _ -> acc
    
    List.fold add 0
  
  let only_nat cmds = constructors_cnt cmds = nat_constructors_cnt cmds
  
  
  let change (file: string) =
     let cmds = commands file
     match only_nat cmds with
     | true -> printf "rm_mr"
     | false -> printfn "%s" <| replace_nat cmds 
      
      // File.WriteAllText(file, replace_nat file)
    // File.WriteAllText(replace_nat file, file)
    // only_nat <| commands file
    // replace_nat file, file
      
        
    
    // let rm_nat_data' acc cmd =
      // let helper nats =
        // function
        // | Command (DeclareDatatype (_, _))   ->
          // name :: nats
        // | Command (DeclareDatatypes vs) ->
          // List.fold
            // (fun nats (name: string, _) ->
              // if name.Contains ("nat", StringComparison.OrdinalIgnoreCase) then
                // name :: nats
              // else
                // acc)
            // acc
            // vs
        // | _ -> nats
      // helper acc cmd
    // List.fold rm_nat_data' []

    // List.map (fun (x: originalCommand) -> sprintf "%O" x)
// |>

// let filter cmds nat_names=
//   List.filter (function
//                | Command (DeclareDatatype (name, _))
//                | Command (DeclareDatatypes [(name, _)]) when nat_names |> List.contains name -> false
//                | _ -> true) cmds
