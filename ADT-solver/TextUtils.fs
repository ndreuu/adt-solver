module TextUtils

let balancedBracket (str: string) =
  let rec helper depth acc =
    function
    | _ when depth = 0 -> Some acc
    | h :: tl ->
      let inc =
        match h with
        | '(' -> 1
        | ')' -> -1
        | _ -> 0

      helper (depth + inc) (h :: acc) tl
    | _ -> None

  str.Substring 1
  |> Seq.toList
  |> helper 1 []
  |> function
    | Some cs ->
      List.fold (fun acc c -> sprintf "%c%s" c acc) "" cs
      |> (fun str -> sprintf "(%s" str)
      |> Some
    | None -> None  