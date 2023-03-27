module ProofBased.Utils

open System
open System.Text.RegularExpressions
open Z3Interpreter.AST


let flip f a b = f b a


let varsIdxs (str: string) =
  let var = Regex "a![0-9]+"

  let verIdxs =
    var.Matches str
    |> Seq.toArray
    |> Array.map (fun m -> (m.Value, m.Index + m.Value.Length + 1))
    |> Array.fold
         (fun (acc, added) ((name, value) as p) ->
           match added with
           | _ when added |> List.contains name -> (acc, added)
           | _ -> (p :: acc, name :: added))
         ([], [])
    |> fst
    |> List.rev

  verIdxs
  |> List.map (fun (v, i) ->
    str.Substring i
    |> balancedBracket
    |> function
      | Some s -> (v, s)
      | None -> failwith "Wrong proof format")

let substituteVars str varsIdxs =
  let mp =
    Regex(@"\(mp").Matches str
    |> fun mps -> mps[0].Index
    |> str.Substring
    |> balancedBracket
    |> function
      | Some s -> s
      | None -> "Wrong proof format"

  varsIdxs
  |> List.rev
  |> List.fold (fun (acc: string) (var: string, value) -> acc.Replace (var, value)) mp

let clean (str: string) =
  let weightStr = Regex ":weight [0-9]+\)|\(!"

  weightStr.Replace (str, String.Empty)
  |> fun str ->
       let rQuery = Regex "\(query"

       rQuery.Matches str
       |> Seq.toArray
       |> fun arr ->
            str.Substring arr[0].Index
            |> balancedBracket
            |> function
              | Some s -> str.Replace (s, "false") |> fun str -> str.Replace ("mp", "proof mp")
              | None -> "Wrong proof format"

let assertedPos str =
  Regex(@"\(asserted").Matches str
  |> Seq.toArray
  |> Array.map (fun m -> m.Index)
  |> Array.map (fun i ->
    str.Substring i
    |> balancedBracket
    |> function
      | Some s -> s
      | None -> failwith "Wrong proof format")
  |> Array.fold (fun (acc: string) a -> acc.Replace (a, "(asserted (=> false false))")) str





let proof dbg str =
  dbg ()
  assertedPos str |> fun str -> varsIdxs str |> substituteVars str |> clean



// let varsIdxs (str: string) =
//   let var = Regex "a![0-9]+"
//
//   let verIdxs =
//     var.Matches str
//     |> Seq.toArray
//     |> Array.map (fun m -> (m.Value, m.Index + m.Value.Length + 1))
//     |> Array.fold
//          (fun (acc, added) ((name, value) as p) ->
//            match added with
//            | _ when added |> List.contains name -> (acc, added)
//            | _ -> (p :: acc, name :: added))
//          ([], [])
//     |> fst
//     |> List.rev
//
//   verIdxs
//   |> List.map (fun (v, i) ->
//     str.Substring i
//     |> balancedBracket
//     |> function
//       | Some s -> (v, s)
//       | None -> failwith "Wrong proof format")
//
// let substituteVars str varsIdxs =
//   let mp =
//     Regex(@"\(mp").Matches str
//     |> fun mps -> mps[0].Index
//     |> str.Substring
//     |> balancedBracket
//     |> function
//       | Some s -> s
//       | None -> "Wrong proof format"
//
//   varsIdxs
//   |> List.rev
//   |> List.fold (fun (acc: string) (var: string, value) -> acc.Replace (var, value)) mp

// let clean (str: string) =
//   let weightStr = Regex ":weight [0-9]+\)|\(!"
//
//   weightStr.Replace (str, String.Empty)
//   |> fun str ->
//        let rQuery = Regex "\(query"
//
//        rQuery.Matches str
//        |> Seq.toArray
//        |> fun arr ->
//             str.Substring arr[0].Index
//             |> balancedBracket
//             |> function
//               | Some s -> str.Replace (s, "false") |> fun str -> str.Replace ("mp", "proof mp")
//               | None -> "Wrong proof format"
//
// let assertedPos str =
//   Regex(@"\(asserted").Matches str
//   |> Seq.toArray
//   |> Array.map (fun m -> m.Index)
//   |> Array.map (fun i ->
//     str.Substring i
//     |> balancedBracket
//     |> function
//       | Some s -> s
//       | None -> failwith "Wrong proof format")
//   |> Array.fold (fun (acc: string) a -> acc.Replace (a, "(asserted (=> false false))")) str






// let proof dbg str =
//   dbg ()
//   assertedPos str |> fun str -> varsIdxs str |> substituteVars str |> clean





// let aa () =
//   proof
//     @"(let ((a!1 (forall ((A Int) (B Int) (C Int) (D Int) (E Int))
//              (! (=> (and (last B C)
//                          (app D A B)
//                          (last A E)
//                          (not (= E C))
//                          (not (= A (- 1))))
//                     (query!0 A B C D E))
//                 :weight 0)) )
//       (a!2 (asserted (forall ((A Int) (B Int) (C Int) (D Int))
//                        (! (let ((a!1 (and (last B C)
//                                           (= A (+ 1 (* 3 D) (* (- 2) B)))
//                                           (not (= B (- 1))))))
//                             (=> a!1 (last A C)))
//                           :weight 0)) ))
//       (a!3 (forall ((A Int) (B Int))
//              (! (=> (= A (+ 3 (* 3 B))) (last A B)) :weight 0)))
//       (a!4 (asserted (forall ((A Int) (B Int) (C Int) (D Int) (E Int) (F Int))
//                        (! (let ((a!1 (and (app D E F)
//                                           (= B (+ 1 (* 3 C) (* (- 2) D)))
//                                           (= A (+ 1 (* 3 C) (* (- 2) F))))))
//                             (=> a!1 (app B E A)))
//                           :weight 0))))
//       (a!5 ((_ hyper-res 0 0)
//              (asserted (forall ((A Int)) (! (app (- 1) A A) :weight 0)))
//              (app (- 1) 3 3))))
// (let ((a!6 ((_ hyper-res 0 0 0 1 0 2 0 3)
//              (asserted a!1)
//              ((_ hyper-res 0 0 0 1)
//                a!2
//                ((_ hyper-res 0 0) (asserted a!3) (last (- 3) (- 2)))
//                (last (- 2) (- 2)))
//              ((_ hyper-res 0 0 0 1) a!4 a!5 (app 6 3 (- 2)))
//              ((_ hyper-res 0 0) (asserted a!3) (last 3 0))
//              (query!0 3 (- 2) (- 2) 6 0))))
//   (mp ((_ hyper-res 0 0 0 1 0 2 0 3)
//              (asserted a!1)
//              ((_ hyper-res 0 0 0 1)
//                a!2
//                ((_ hyper-res 0 0) (asserted a!3) (last (- 3) (- 2)))
//                (last (- 2) (- 2)))
//              ((_ hyper-res 0 0 0 1) (asserted (forall ((A Int) (B Int) (C Int) (D Int) (E Int) (F Int))
//                        (! (let ((a!1 (and (app D E F)
//                                           (= B (+ 1 (* 3 C) (* (- 2) D)))
//                                           (= A (+ 1 (* 3 C) (* (- 2) F))))))
//                             (=> a!1 (app B E A)))
//                           :weight 0))) ((_ hyper-res 0 0)
//              (asserted (forall ((A Int)) (! (app (- 1) A A) :weight 0)))
//              (app (- 1) 3 3)) (app 6 3 (- 2)))
//              ((_ hyper-res 0 0) (asserted a!3) (last 3 0))
//              (query!0 3 (- 2) (- 2) 6 0)) 
//         (asserted (=> (query!0 3 (- 2) (- 2) 6 0) false)) false)))"
//   |> fun vs -> printfn "%O" vs
