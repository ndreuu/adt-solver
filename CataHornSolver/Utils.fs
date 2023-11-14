module ProofBased.Utils

open System
open System.Numerics
open System.Text.RegularExpressions
open System.Threading.Tasks


let flip f a b = f b a
let swap (x, y) = y, x

open SMTLIB2

let inline join s (xs: string seq) = String.Join (s, xs)

module IntOps =
  let mulOp = ElementaryOperation ("*", [ IntSort; IntSort ], IntSort)
  let negOp = ElementaryOperation ("-", [ IntSort ], IntSort)
  let addOp = ElementaryOperation ("+", [ IntSort; IntSort ], IntSort)
  let neg = Expr.makeUnaryOp negOp
  let mult x y =
    match x, y with
    | Number v, _ when v = BigInteger.One -> y
    | _, Number v when v = BigInteger.One -> x
    | Number v, _  when v = BigInteger.MinusOne -> neg y
    | _, Number v  when v = BigInteger.MinusOne -> neg x
    | _ -> Expr.makeBinaryOp mulOp x y
  let add x y = Expr.makeBinaryOp addOp x y
  let minusOp = ElementaryOperation ("-", [ IntSort; IntSort ], IntSort)
  let eqOp = ElementaryOperation ("=", [ IntSort; IntSort ], BoolSort)
  let grOp = ElementaryOperation (">", [ IntSort; IntSort ], BoolSort)
  let lsOp = ElementaryOperation ("<", [ IntSort; IntSort ], BoolSort)
  let leqOp = ElementaryOperation ("<=", [ IntSort; IntSort ], BoolSort)
  let geqOp = ElementaryOperation (">=", [ IntSort; IntSort ], BoolSort)
  let modOp = ElementaryOperation ("mod", [ IntSort; IntSort ], IntSort)

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
      String.Concat(List.rev cs |> Array.ofList |> String)
      |> (fun str -> $"({str}" )
      |> Some
    | None -> None

let varsIdxs (str: string) =
  let var = Regex "a![0-9]+"

  let verIdxs =
    var.Matches str
    |> Seq.toArray
    |> Array.map (fun m -> (m.Value, m.Index + m.Value.Length + 1))
    |> Array.fold
      (fun (acc, added) (name, _ as p) ->
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

let randomValues: string list -> _ list =
  List.map (fun n -> (n, Random().NextInt64 (0L, 10L)))
  

let taskChild() : Async<unit> =
    async {
        printfn "Starting Child"

        let! ct = Async.CancellationToken
        printfn $"Cancellation token child: {ct.GetHashCode()}"

        use! c = Async.OnCancel(fun () -> printfn "Cancelled Task Child")

        while (true) do
            printfn "Waiting Child"

            do! Async.Sleep(100)
    }

let task  : Async<_ option> =
    async {
        printfn "Starting"
        let! ct = Async.CancellationToken
        printfn $"Cancellation token: {ct.GetHashCode()}"
        
        use! c = Async.OnCancel(fun () -> printfn "Cancelled")
        let foo = Some 1
        while true
          do Async.Sleep 60000 |> ignore
        
        return Some 1
        // do! taskChild()
    }



let rec loop () = printfn "l"; loop ()



let withTimeout timeout action =
  async {
    let! child = Async.StartChild (action, timeout)
    return! child
  }




let uniqs =
  let beginTkn = "(! "
  let endTkn = ":weight 0)"
  
  // let _ = beginTkn 
  
  
  1

module Weight =
  let weightPoses s =
    Regex(@"\(!").Matches s
    |> Seq.map (fun (x: Match) -> x.Index)
  
  let replaceBlock (s: string) block =   
    Regex("\(a!\d+").Matches block
    |> Seq.map (fun (x: Match) -> x.Value.[1..])
    |> Seq.fold (fun (s: string) x -> s.Replace(x, $"w{x}")) block
    |> fun b -> b.Replace(":weight 0)", "").Replace("(!", "")
    |> fun b' -> s.Replace(block, b')
  
  let rmWeightBlocks (s: string) =
    s.Replace("(!","").Replace(":weight 0)", "")

    // weightPoses s
    // |> Seq.map s.Substring
    // |> Seq.map balancedBracket
    // |> Seq.fold (fun s block ->
      // match block with Some b -> replaceBlock s b | _ -> s) s
    

  

let tettt () =
  let content = """sat
(
  (define-fun name_175 () Bool
    true)
  (define-fun name_216 () Bool
    true)
  (define-fun name_44 () Bool
    true)
  (define-fun name_220 () Bool
    true)
  (define-fun name_141 () Bool
    true)
  (define-fun name_159 () Bool
    true)
  (define-fun name_130 () Bool
    true)
  (define-fun name_95 () Bool
    true)
  (define-fun name_150 () Bool
    true)
  (define-fun name_121 () Bool
    true)
  (define-fun name_151 () Bool
    true)
  (define-fun name_160 () Bool
    true)
  (define-fun name_169 () Bool
    true)
  (define-fun name_122 () Bool
    true)
  (define-fun name_110 () Bool
    true)
  (define-fun name_176 () Bool
    true)
  (define-fun name_241 () Bool
    true)
  (define-fun name_17 () Bool
    true)
  (define-fun name_109 () Bool
    true)
  (define-fun name_97 () Bool
    true)
  (define-fun name_232 () Bool
    true)
  (define-fun name_154 () Bool
    true)
  (define-fun name_223 () Bool
    true)
  (define-fun name_213 () Bool
    true)
  (define-fun name_225 () Bool
    true)
  (define-fun name_221 () Bool
    true)
  (define-fun name_230 () Bool
    true)
  (define-fun name_157 () Bool
    true)
  (define-fun name_104 () Bool
    true)
  (define-fun name_16 () Bool
    true)
  (define-fun name_137 () Bool
    true)
  (define-fun name_144 () Bool
    true)
  (define-fun name_119 () Bool
    true)
  (define-fun name_156 () Bool
    true)
  (define-fun name_239 () Bool
    true)
  (define-fun name_158 () Bool
    true)
  (define-fun name_15 () Bool
    true)
  (define-fun name_118 () Bool
    true)
  (define-fun name_126 () Bool
    true)
  (define-fun name_124 () Bool
    true)
  (define-fun name_147 () Bool
    true)
  (define-fun name_120 () Bool
    true)
  (define-fun name_107 () Bool
    true)
  (define-fun name_4 () Bool
    true)
  (define-fun name_146 () Bool
    true)
  (define-fun name_7 () Bool
    true)
  (define-fun name_140 () Bool
    true)
  (define-fun name_127 () Bool
    true)
  (define-fun name_243 () Bool
    true)
  (define-fun name_162 () Bool
    true)
  (define-fun name_9 () Bool
    true)
  (define-fun name_217 () Bool
    true)
  (define-fun name_212 () Bool
    true)
  (define-fun name_125 () Bool
    true)
  (define-fun name_105 () Bool
    true)
  (define-fun name_155 () Bool
    true)
  (define-fun name_42 () Bool
    true)
  (define-fun name_129 () Bool
    true)
  (define-fun name_164 () Bool
    true)
  (define-fun name_231 () Bool
    true)
  (define-fun name_135 () Bool
    true)
  (define-fun name_131 () Bool
    true)
  (define-fun name_134 () Bool
    true)
  (define-fun name_11 () Bool
    true)
  (define-fun name_171 () Bool
    true)
  (define-fun name_228 () Bool
    true)
  (define-fun name_8 () Bool
    true)
  (define-fun name_142 () Bool
    true)
  (define-fun name_161 () Bool
    true)
  (define-fun name_215 () Bool
    true)
  (define-fun name_143 () Bool
    true)
  (define-fun name_111 () Bool
    true)
  (define-fun name_163 () Bool
    true)
  (define-fun name_103 () Bool
    true)
  (define-fun name_10 () Bool
    true)
  (define-fun name_3 () Bool
    true)
  (define-fun name_233 () Bool
    true)
  (define-fun name_174 () Bool
    true)
  (define-fun name_149 () Bool
    true)
  (define-fun name_242 () Bool
    true)
  (define-fun name_240 () Bool
    true)
  (define-fun name_238 () Bool
    true)
  (define-fun name_100 () Bool
    true)
  (define-fun name_226 () Bool
    true)
  (define-fun name_133 () Bool
    true)
  (define-fun name_219 () Bool
    true)
  (define-fun name_106 () Bool
    true)
  (define-fun name_145 () Bool
    true)
  (define-fun name_139 () Bool
    true)
  (define-fun name_117 () Bool
    true)
  (define-fun name_108 () Bool
    true)
  (define-fun name_224 () Bool
    true)
  (define-fun name_96 () Bool
    true)
  (define-fun name_166 () Bool
    true)
  (define-fun name_167 () Bool
    true)
  (define-fun name_165 () Bool
    true)
  (define-fun name_234 () Bool
    true)
  (define-fun name_173 () Bool
    true)
  (define-fun name_114 () Bool
    true)
  (define-fun name_112 () Bool
    true)
  (define-fun name_115 () Bool
    true)
  (define-fun name_227 () Bool
    true)
  (define-fun name_99 () Bool
    true)
  (define-fun name_229 () Bool
    true)
  (define-fun name_177 () Bool
    true)
  (define-fun name_214 () Bool
    true)
  (define-fun name_138 () Bool
    true)
  (define-fun name_222 () Bool
    true)
  (define-fun name_18 () Bool
    true)
  (define-fun name_236 () Bool
    true)
  (define-fun name_13 () Bool
    true)
  (define-fun name_20 () Bool
    true)
  (define-fun name_132 () Bool
    true)
  (define-fun name_98 () Bool
    true)
  (define-fun name_123 () Bool
    true)
  (define-fun name_170 () Bool
    true)
  (define-fun name_152 () Bool
    true)
  (define-fun name_101 () Bool
    true)
  (define-fun name_235 () Bool
    true)
  (define-fun name_218 () Bool
    true)
  (define-fun name_6 () Bool
    true)
  (define-fun name_19 () Bool
    true)
  (define-fun name_5 () Bool
    true)
  (define-fun name_12 () Bool
    true)
  (define-fun name_153 () Bool
    true)
  (define-fun name_43 () Bool
    true)
  (define-fun name_168 () Bool
    true)
  (define-fun name_136 () Bool
    true)
  (define-fun name_210 () Bool
    true)
  (define-fun name_116 () Bool
    true)
  (define-fun name_41 () Bool
    true)
  (define-fun name_237 () Bool
    true)
  (define-fun name_148 () Bool
    true)
  (define-fun name_113 () Bool
    true)
  (define-fun name_128 () Bool
    true)
  (define-fun name_211 () Bool
    true)
  (define-fun name_14 () Bool
    true)
  (define-fun name_102 () Bool
    true)
  (define-fun name_172 () Bool
    true)
  (define-fun Nothing_26 () Int
    0)
  (define-fun Z_2791 () Int
    0)
  (define-fun c_6 () Int
    1)
  (define-fun c_9 () Int
    0)
  (define-fun c_2 () Int
    0)
  (define-fun c_5 () Int
    0)
  (define-fun c_0 () Int
    0)
  (define-fun nil_473 () Int
    0)
  (define-fun nil_472 () Int
    0)
  (define-fun c_8 () Int
    0)
  (define-fun c_17 () Int
    0)
  (define-fun c_18 () Int
    1)
  (define-fun c_14 () Int
    0)
  (define-fun c_16 () Int
    0)
  (define-fun c_7 () Int
    1)
  (define-fun c_13 () Int
    1)
  (define-fun c_12 () Int
    0)
  (define-fun false_448 () Int
    0)
  (define-fun c_15 () Int
    1)
  (define-fun true_448 () Int
    1)
  (define-fun nil_474 () Int
    1)
  (define-fun c_1 () Int
    1)
  (define-fun c_11 () Int
    0)
  (define-fun c_10 () Int
    0)
  (define-fun c_19 () Int
    0)
  (define-fun c_4 () Int
    0)
  (define-fun c_3 () Int
    1)
  (define-fun ge_448_134_0 ((x!0 Int) (x!1 Int)) Bool
    true)
  (define-fun add_483_171_25 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun index_6 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (let ((a!1 (exists ((x!3 Int))
                  (and (or (not (<= x!3 1)) (not (>= x!2 5)))
                         (not (<= x!3 (- 1)))
                         (or (not (<= x!3 0)) (not (>= x!2 1)))
                         (or (not (>= x!3 1)) (= x!0 0))
                         (not (= x!2 0))
                         (= x!1 0))
                    )))
      (or (= x!0 0) a!1 (not (>= x!2 1)))))
  (define-fun formula_10 ((x!0 Int) (x!1 Int)) Bool
    true)
  (define-fun add_483_140_1 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun add_483_137_4 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun index_6_156_3 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (let ((a!1 (exists ((x!3 Int))
                  (and (or (not (<= x!3 1)) (not (>= x!2 5)))
                         (not (<= x!3 (- 1)))
                         (or (not (<= x!3 0)) (not (>= x!2 1)))
                         (or (not (>= x!3 1)) (= x!0 0))
                         (not (= x!2 0))
                         (= x!1 0))
                    )))
      (or (= x!0 0) a!1 (not (>= x!2 1)))))
  (define-fun add_483_143_3 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun dodeca_42_171_14 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun colouring_13 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (let ((a!1 (exists ((x!3 Int))
                  (let ((wa!1 (exists ((x!4 Int) (x!5 Int))
                                  (and (or (not (>= x!5 2)) (not (<= x!4 0)))
                                         (or (not (>= x!4 2)) (not (>= x!5 1)))
                                         (= x!3 1))
                                    ))
                          (wa!2 (and (or (not (>= x!1 2)) (not (<= x!3 0)))
                                    (or (not (>= x!3 2)) (not (>= x!1 1)))))
                          (wa!3 (exists ((x!4 Int) (x!5 Int))
                                  (and (not (>= x!1 1))
                                         (or (not (>= x!5 2)) (not (<= x!4 0)))
                                         (or (not (>= x!5 1)) (not (>= x!4 2)))
                                         (= x!3 1))
                                    ))
                          (wa!4 (exists ((x!4 Int) (x!5 Int) (x!6 Int))
                                  (and (not (>= x!1 1))
                                         (or (not (>= x!6 2)) (not (<= x!5 0)))
                                         (or (not (>= x!6 1)) (not (>= x!5 2)))
                                         (not (>= x!4 1))
                                         (= x!3 1))
                                    ))
                          (wa!5 (exists ((x!4 Int) (x!5 Int) (x!6 Int))
                                  (and (not (>= x!1 1))
                                         (or (not (>= x!6 2)) (not (<= x!5 0)))
                                         (or (not (>= x!5 2)) (not (>= x!6 1)))
                                         (not (>= x!4 1))
                                         (= x!3 2))
                                    )))
                      (and (or (= x!0 0) (not (= x!3 1)))
                           (or wa!1 wa!2 wa!3 wa!4 wa!5)))
                    ))
          (a!2 (exists ((x!3 Int))
                 (! (let ((a!1 (exists ((x!4 Int) (x!5 Int))
                                  (and (or (not (>= x!5 2)) (not (<= x!4 0)))
                                         (or (not (>= x!4 2)) (not (>= x!5 1)))
                                         (= x!3 1))
                                    ))
                          (a!2 (and (or (not (<= x!3 0)) (not (>= x!1 2)))
                                    (or (not (>= x!3 2)) (not (>= x!1 1)))))
                          (a!3 (exists ((x!4 Int) (x!5 Int))
                                  (and (not (>= x!1 1))
                                         (or (not (>= x!5 2)) (not (<= x!4 0)))
                                         (or (not (>= x!5 1)) (not (>= x!4 2)))
                                         (= x!3 1))
                                    ))
                          (a!4 (exists ((x!4 Int) (x!5 Int) (x!6 Int))
                                  (and (not (>= x!1 1))
                                         (or (not (>= x!6 2)) (not (<= x!5 0)))
                                         (or (not (>= x!6 1)) (not (>= x!5 2)))
                                         (not (>= x!4 1))
                                         (= x!3 1))
                                    ))
                          (a!5 (exists ((x!4 Int) (x!5 Int) (x!6 Int))
                                  (and (not (>= x!1 1))
                                         (or (not (>= x!6 2)) (not (<= x!5 0)))
                                         (or (not (>= x!5 2)) (not (>= x!6 1)))
                                         (not (>= x!4 1))
                                         (= x!3 2))
                                    )))
                      (and (or (= x!0 0) (not (= x!3 1)))
                           (or a!1 a!2 a!3 a!4 a!5)))
                    :weight 0))))
      (or a!1 a!2)))
  (define-fun formula_10_171_1 ((x!0 Int) (x!1 Int)) Bool
    true)
  (define-fun and_454 ((x!0 Int) (x!1 Int)) Bool
    (or (= x!0 0) (not (= x!1 1))))
  (define-fun primEnumFromTo_13 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun lt_468_27_0 ((x!0 Int) (x!1 Int)) Bool
    true)
  (define-fun add_483_146_3 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun primEnumFromTo_13_171_5 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun primEnumFromTo_13_171_3 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun gt_451 ((x!0 Int) (x!1 Int)) Bool
    true)
  (define-fun and_454_161_0 ((x!0 Int) (x!1 Int)) Bool
    (or (= x!0 0) (not (= x!1 1))))
  (define-fun dodeca_42_137_0 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun minus_469_171_31 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (let ((a!1 (exists ((x!3 Int) (x!4 Int))
                  (and (or (not (<= x!3 1)) (not (>= x!4 5)))
                         (not (<= x!3 (- 1)))
                         (or (not (<= x!3 0)) (not (>= x!4 1)))
                         (= x!1 (+ 1 x!4))
                         (= x!0 (+ 1 x!3)))
                    ))
          (a!2 (and (or (not (<= x!0 1)) (not (>= x!1 5)))
                    (not (<= x!0 (- 1)))
                    (or (not (<= x!0 0)) (not (>= x!1 1))))))
      (or a!1 a!2)))
  (define-fun add_483_146_2 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun formula_10_134_1 ((x!0 Int) (x!1 Int)) Bool
    true)
  (define-fun and_455_161_1 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (or (and (= x!0 1) (= x!1 1) (= x!2 1))
        (and (= x!0 0) (= x!1 1) (= x!2 0))
        (and (= x!0 0) (= x!1 0) (= x!2 0))
        (and (= x!0 0) (= x!1 0) (= x!2 1))))
  (define-fun add_483_171_26 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun minus_469_171_33 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (let ((a!1 (exists ((x!3 Int) (x!4 Int))
                  (and (or (not (<= x!3 1)) (not (>= x!4 5)))
                         (not (<= x!3 (- 1)))
                         (or (not (<= x!3 0)) (not (>= x!4 1)))
                         (= x!1 (+ 1 x!4))
                         (= x!0 (+ 1 x!3)))
                    ))
          (a!2 (and (or (not (<= x!0 1)) (not (>= x!1 5)))
                    (not (<= x!0 (- 1)))
                    (or (not (<= x!0 0)) (not (>= x!1 1))))))
      (or a!1 a!2)))
  (define-fun colouring_12_158_0 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (let ((a!1 (exists ((x!3 Int) (x!4 Int))
                  (and (or (not (>= x!4 2)) (not (<= x!3 0)))
                         (or (not (>= x!3 2)) (not (>= x!4 1)))
                         (= x!0 1))
                    ))
          (a!2 (and (or (not (>= x!2 2)) (not (<= x!0 0)))
                    (or (not (>= x!0 2)) (not (>= x!2 1)))))
          (a!3 (exists ((x!3 Int) (x!4 Int))
                  (and (not (>= x!2 1))
                         (or (not (>= x!4 2)) (not (<= x!3 0)))
                         (or (not (>= x!4 1)) (not (>= x!3 2)))
                         (= x!0 1))
                    ))
          (a!4 (exists ((x!3 Int) (x!4 Int) (x!5 Int))
                  (and (not (>= x!2 1))
                         (or (not (>= x!5 2)) (not (<= x!4 0)))
                         (or (not (>= x!5 1)) (not (>= x!4 2)))
                         (not (>= x!3 1))
                         (= x!0 1))
                    ))
          (a!5 (exists ((x!3 Int) (x!4 Int) (x!5 Int))
                  (and (not (>= x!2 1))
                         (or (not (>= x!5 2)) (not (<= x!4 0)))
                         (or (not (>= x!4 2)) (not (>= x!5 1)))
                         (not (>= x!3 1))
                         (= x!0 2))
                    )))
      (or a!1 a!2 a!3 a!4 a!5)))
  (define-fun x_127342_171_18 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (let ((a!1 (exists ((x!3 Int) (x!4 Int))
                  (and (or (not (>= x!4 2)) (= x!4 x!3)) (= x!1 x!0))
                    )))
      (or (= x!1 x!0) a!1 (not (>= x!1 2)))))
  (define-fun dodeca_45_146_0 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun primEnumFromTo_13_171_7 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun dodeca_47_171_4 ((x!0 Int) (x!1 Int)) Bool
    true)
  (define-fun dodeca_44_143_0 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun dodeca_44_171_10 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun x_127342_171_17 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (let ((a!1 (exists ((x!3 Int) (x!4 Int))
                  (and (or (not (>= x!4 2)) (= x!4 x!3)) (= x!1 x!0))
                    )))
      (or (= x!1 x!0) a!1 (not (>= x!1 2)))))
  (define-fun primEnumFromTo_13_171_9 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun colouring_12_156_1 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (let ((a!1 (exists ((x!3 Int) (x!4 Int))
                  (and (or (not (>= x!4 2)) (not (<= x!3 0)))
                         (or (not (>= x!3 2)) (not (>= x!4 1)))
                         (= x!0 1))
                    ))
          (a!2 (and (or (not (>= x!2 2)) (not (<= x!0 0)))
                    (or (not (>= x!0 2)) (not (>= x!2 1)))))
          (a!3 (exists ((x!3 Int) (x!4 Int))
                  (and (not (>= x!2 1))
                         (or (not (>= x!4 2)) (not (<= x!3 0)))
                         (or (not (>= x!4 1)) (not (>= x!3 2)))
                         (= x!0 1))
                    ))
          (a!4 (exists ((x!3 Int) (x!4 Int) (x!5 Int))
                  (and (not (>= x!2 1))
                         (or (not (>= x!5 2)) (not (<= x!4 0)))
                         (or (not (>= x!5 1)) (not (>= x!4 2)))
                         (not (>= x!3 1))
                         (= x!0 1))
                    ))
          (a!5 (exists ((x!3 Int) (x!4 Int) (x!5 Int))
                  (and (not (>= x!2 1))
                         (or (not (>= x!5 2)) (not (<= x!4 0)))
                         (or (not (>= x!4 2)) (not (>= x!5 1)))
                         (not (>= x!3 1))
                         (= x!0 2))
                    )))
      (or a!1 a!2 a!3 a!4 a!5)))
  (define-fun and_454_164_1 ((x!0 Int) (x!1 Int)) Bool
    (or (= x!0 0) (not (= x!1 1))))
  (define-fun and_455 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (or (and (= x!0 1) (= x!1 1) (= x!2 1))
        (and (= x!0 0) (= x!1 1) (= x!2 0))
        (and (= x!0 0) (= x!1 0) (= x!2 0))
        (and (= x!0 0) (= x!1 0) (= x!2 1))))
  (define-fun add_483_137_5 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun add_483_137_7 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun primEnumFromTo_13_171_11 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun add_483_171_29 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun dodeca_46_171_6 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun minus_469_130_2 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (let ((a!1 (exists ((x!3 Int) (x!4 Int))
                  (and (or (not (<= x!3 1)) (not (>= x!4 5)))
                         (not (<= x!3 (- 1)))
                         (or (not (<= x!3 0)) (not (>= x!4 1)))
                         (= x!1 (+ 1 x!4))
                         (= x!0 (+ 1 x!3)))
                    ))
          (a!2 (and (or (not (<= x!0 1)) (not (>= x!1 5)))
                    (not (<= x!0 (- 1)))
                    (or (not (<= x!0 0)) (not (>= x!1 1))))))
      (or a!1 a!2)))
  (define-fun x_127342_171_19 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (let ((a!1 (exists ((x!3 Int) (x!4 Int))
                  (and (or (not (>= x!4 2)) (= x!4 x!3)) (= x!1 x!0))
                    )))
      (or (= x!1 x!0) a!1 (not (>= x!1 2)))))
  (define-fun dodeca_46_149_0 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun minus_469_171_32 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (let ((a!1 (exists ((x!3 Int) (x!4 Int))
                  (and (or (not (<= x!3 1)) (not (>= x!4 5)))
                         (not (<= x!3 (- 1)))
                         (or (not (<= x!3 0)) (not (>= x!4 1)))
                         (= x!1 (+ 1 x!4))
                         (= x!0 (+ 1 x!3)))
                    ))
          (a!2 (and (or (not (<= x!0 1)) (not (>= x!1 5)))
                    (not (<= x!0 (- 1)))
                    (or (not (<= x!0 0)) (not (>= x!1 1))))))
      (or a!1 a!2)))
  (define-fun add_483_137_3 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun minus_469_171_27 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (let ((a!1 (exists ((x!3 Int) (x!4 Int))
                  (and (or (not (<= x!3 1)) (not (>= x!4 5)))
                         (not (<= x!3 (- 1)))
                         (or (not (<= x!3 0)) (not (>= x!4 1)))
                         (= x!1 (+ 1 x!4))
                         (= x!0 (+ 1 x!3)))
                    ))
          (a!2 (and (or (not (<= x!0 1)) (not (>= x!1 5)))
                    (not (<= x!0 (- 1)))
                    (or (not (<= x!0 0)) (not (>= x!1 1))))))
      (or a!1 a!2)))
  (define-fun x_127342_171_16 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (let ((a!1 (exists ((x!3 Int) (x!4 Int))
                  (and (or (not (>= x!4 2)) (= x!4 x!3)) (= x!1 x!0))
                    )))
      (or (= x!1 x!0) a!1 (not (>= x!1 2)))))
  (define-fun add_483_143_1 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun le_448 ((x!0 Int) (x!1 Int)) Bool
    true)
  (define-fun dodeca_42 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun dodeca_43_171_12 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun le_448_127_0 ((x!0 Int) (x!1 Int)) Bool
    true)
  (define-fun minus_469_21_0 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (let ((a!1 (exists ((x!3 Int) (x!4 Int))
                  (and (or (not (<= x!3 1)) (not (>= x!4 5)))
                         (not (<= x!3 (- 1)))
                         (or (not (<= x!3 0)) (not (>= x!4 1)))
                         (= x!1 (+ 1 x!4))
                         (= x!0 (+ 1 x!3)))
                    ))
          (a!2 (and (or (not (<= x!0 1)) (not (>= x!1 5)))
                    (not (<= x!0 (- 1)))
                    (or (not (<= x!0 0)) (not (>= x!1 1))))))
      (or a!1 a!2)))
  (define-fun x_127342_171_15 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (let ((a!1 (exists ((x!3 Int) (x!4 Int))
                  (and (or (not (>= x!4 2)) (= x!4 x!3)) (= x!1 x!0))
                    )))
      (or (= x!1 x!0) a!1 (not (>= x!1 2)))))
  (define-fun colouring_13_171_20 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (exists ((x!3 Int))
       (let ((wa!1 (exists ((x!4 Int) (x!5 Int))
                       (and (or (not (>= x!5 2)) (not (<= x!4 0)))
                              (or (not (>= x!4 2)) (not (>= x!5 1)))
                              (= x!3 1))
                         ))
               (wa!2 (and (or (not (<= x!3 0)) (not (>= x!1 2)))
                         (or (not (>= x!3 2)) (not (>= x!1 1)))))
               (wa!3 (exists ((x!4 Int) (x!5 Int))
                       (and (not (>= x!1 1))
                              (or (not (>= x!5 2)) (not (<= x!4 0)))
                              (or (not (>= x!5 1)) (not (>= x!4 2)))
                              (= x!3 1))
                         ))
               (wa!4 (exists ((x!4 Int) (x!5 Int) (x!6 Int))
                       (and (not (>= x!1 1))
                              (or (not (>= x!6 2)) (not (<= x!5 0)))
                              (or (not (>= x!6 1)) (not (>= x!5 2)))
                              (not (>= x!4 1))
                              (= x!3 1))
                         ))
               (wa!5 (exists ((x!4 Int) (x!5 Int) (x!6 Int))
                       (and (not (>= x!1 1))
                              (or (not (>= x!6 2)) (not (<= x!5 0)))
                              (or (not (>= x!5 2)) (not (>= x!6 1)))
                              (not (>= x!4 1))
                              (= x!3 2))
                         )))
           (and (or (= x!0 0) (not (= x!3 1))) (or wa!1 wa!2 wa!3 wa!4 wa!5)))
         ))
  (define-fun minus_469_171_23 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (let ((a!1 (exists ((x!3 Int) (x!4 Int))
                  (and (or (not (<= x!3 1)) (not (>= x!4 5)))
                         (not (<= x!3 (- 1)))
                         (or (not (<= x!3 0)) (not (>= x!4 1)))
                         (= x!1 (+ 1 x!4))
                         (= x!0 (+ 1 x!3)))
                    ))
          (a!2 (and (or (not (<= x!0 1)) (not (>= x!1 5)))
                    (not (<= x!0 (- 1)))
                    (or (not (<= x!0 0)) (not (>= x!1 1))))))
      (or a!1 a!2)))
  (define-fun add_483_140_3 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun add_483_171_22 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun lt_468 ((x!0 Int) (x!1 Int)) Bool
    true)
  (define-fun add_483_137_2 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun le_448_23_0 ((x!0 Int) (x!1 Int)) Bool
    true)
  (define-fun dodeca_44 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun index_6_156_2 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (let ((a!1 (exists ((x!3 Int))
                  (and (or (not (<= x!3 1)) (not (>= x!2 5)))
                         (not (<= x!3 (- 1)))
                         (or (not (<= x!3 0)) (not (>= x!2 1)))
                         (or (not (>= x!3 1)) (= x!0 0))
                         (not (= x!2 0))
                         (= x!1 0))
                    )))
      (or (= x!0 0) a!1 (not (>= x!2 1)))))
  (define-fun add_483_171_28 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun dodeca_47_152_0 ((x!0 Int) (x!1 Int)) Bool
    true)
  (define-fun index_6_155_2 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (let ((a!1 (exists ((x!3 Int))
                  (and (or (not (<= x!3 1)) (not (>= x!2 5)))
                         (not (<= x!3 (- 1)))
                         (or (not (<= x!3 0)) (not (>= x!2 1)))
                         (or (not (>= x!3 1)) (= x!0 0))
                         (not (= x!2 0))
                         (= x!1 0))
                    )))
      (or (= x!0 0) a!1 (not (>= x!2 1)))))
  (define-fun colouring_12_155_0 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (let ((a!1 (exists ((x!3 Int) (x!4 Int))
                  (and (or (not (>= x!4 2)) (not (<= x!3 0)))
                         (or (not (>= x!3 2)) (not (>= x!4 1)))
                         (= x!0 1))
                    ))
          (a!2 (and (or (not (<= x!0 0)) (not (>= x!2 2)))
                    (or (not (>= x!0 2)) (not (>= x!2 1)))))
          (a!3 (and (or (not (>= x!2 2)) (not (<= x!0 0)))
                    (or (not (>= x!0 2)) (not (>= x!2 1)))))
          (a!4 (exists ((x!3 Int) (x!4 Int))
                  (and (not (>= x!2 1))
                         (or (not (>= x!4 2)) (not (<= x!3 0)))
                         (or (not (>= x!4 1)) (not (>= x!3 2)))
                         (= x!0 1))
                    ))
          (a!5 (exists ((x!3 Int) (x!4 Int) (x!5 Int))
                  (and (not (>= x!2 1))
                         (or (not (>= x!5 2)) (not (<= x!4 0)))
                         (or (not (>= x!5 1)) (not (>= x!4 2)))
                         (not (>= x!3 1))
                         (= x!0 1))
                    ))
          (a!6 (exists ((x!3 Int) (x!4 Int) (x!5 Int))
                  (and (not (>= x!2 1))
                         (or (not (>= x!5 2)) (not (<= x!4 0)))
                         (or (not (>= x!4 2)) (not (>= x!5 1)))
                         (not (>= x!3 1))
                         (= x!0 2))
                    )))
      (or a!1 a!2 a!3 a!4 a!5 a!6)))
  (define-fun add_483_19_0 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun ge_448 ((x!0 Int) (x!1 Int)) Bool
    true)
  (define-fun add_483_140_4 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun colouring_12 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (let ((a!1 (exists ((x!3 Int) (x!4 Int))
                  (and (or (not (>= x!4 2)) (not (<= x!3 0)))
                         (or (not (>= x!3 2)) (not (>= x!4 1)))
                         (= x!0 1))
                    ))
          (a!2 (and (or (not (>= x!2 2)) (not (<= x!0 0)))
                    (or (not (>= x!0 2)) (not (>= x!2 1)))))
          (a!3 (exists ((x!3 Int) (x!4 Int))
                  (and (not (>= x!2 1))
                         (or (not (>= x!4 2)) (not (<= x!3 0)))
                         (or (not (>= x!4 1)) (not (>= x!3 2)))
                         (= x!0 1))
                    ))
          (a!4 (exists ((x!3 Int) (x!4 Int) (x!5 Int))
                  (and (not (>= x!2 1))
                         (or (not (>= x!5 2)) (not (<= x!4 0)))
                         (or (not (>= x!5 1)) (not (>= x!4 2)))
                         (not (>= x!3 1))
                         (= x!0 1))
                    ))
          (a!5 (exists ((x!3 Int) (x!4 Int) (x!5 Int))
                  (and (not (>= x!2 1))
                         (or (not (>= x!5 2)) (not (<= x!4 0)))
                         (or (not (>= x!4 2)) (not (>= x!5 1)))
                         (not (>= x!3 1))
                         (= x!0 2))
                    )))
      (or a!1 a!2 a!3 a!4 a!5)))
  (define-fun primEnumFromTo_13_171_13 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun dodeca_45 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun index_6_158_1 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (let ((a!1 (exists ((x!3 Int))
                  (and (or (not (<= x!3 1)) (not (>= x!2 5)))
                         (not (<= x!3 (- 1)))
                         (or (not (<= x!3 0)) (not (>= x!2 1)))
                         (or (not (>= x!3 1)) (= x!0 0))
                         (not (= x!2 0))
                         (= x!1 0))
                    )))
      (or (= x!0 0) a!1 (not (>= x!2 1)))))
  (define-fun primEnumFromTo_13_127_1 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun add_483_143_2 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun x_127342 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (let ((a!1 (exists ((x!3 Int) (x!4 Int))
                  (and (or (not (>= x!4 2)) (= x!4 x!3)) (= x!1 x!0))
                    )))
      (or (= x!1 x!0) a!1 (not (>= x!1 2)))))
  (define-fun index_6_157_1 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (let ((a!1 (exists ((x!3 Int))
                  (and (or (not (<= x!3 1)) (not (>= x!2 5)))
                         (not (<= x!3 (- 1)))
                         (or (not (<= x!3 0)) (not (>= x!2 1)))
                         (or (not (>= x!3 1)) (= x!0 0))
                         (not (= x!2 0))
                         (= x!1 0))
                    )))
      (or (= x!0 0) a!1 (not (>= x!2 1)))))
  (define-fun add_483_171_24 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun index_6_130_1 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (let ((a!1 (exists ((x!3 Int))
                  (and (or (not (<= x!3 1)) (not (>= x!2 5)))
                         (not (<= x!3 (- 1)))
                         (or (not (<= x!3 0)) (not (>= x!2 1)))
                         (or (not (>= x!3 1)) (= x!0 0))
                         (not (= x!2 0))
                         (= x!1 0))
                    )))
      (or (= x!0 0) a!1 (not (>= x!2 1)))))
  (define-fun colouring_12_164_0 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (let ((a!1 (exists ((x!3 Int) (x!4 Int))
                  (and (or (not (>= x!4 2)) (not (<= x!3 0)))
                         (or (not (>= x!3 2)) (not (>= x!4 1)))
                         (= x!0 1))
                    ))
          (a!2 (and (or (not (<= x!0 0)) (not (>= x!2 2)))
                    (or (not (>= x!0 2)) (not (>= x!2 1)))))
          (a!3 (exists ((x!3 Int) (x!4 Int))
                  (and (not (>= x!2 1))
                         (or (not (>= x!4 2)) (not (<= x!3 0)))
                         (or (not (>= x!4 1)) (not (>= x!3 2)))
                         (= x!0 1))
                    ))
          (a!4 (exists ((x!3 Int) (x!4 Int) (x!5 Int))
                  (and (not (>= x!2 1))
                         (or (not (>= x!5 2)) (not (<= x!4 0)))
                         (or (not (>= x!5 1)) (not (>= x!4 2)))
                         (not (>= x!3 1))
                         (= x!0 1))
                    ))
          (a!5 (exists ((x!3 Int) (x!4 Int) (x!5 Int))
                  (and (not (>= x!2 1))
                         (or (not (>= x!5 2)) (not (<= x!4 0)))
                         (or (not (>= x!4 2)) (not (>= x!5 1)))
                         (not (>= x!3 1))
                         (= x!0 2))
                    )))
      (or a!1 a!2 a!3 a!4 a!5)))
  (define-fun minus_469_171_21 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (let ((a!1 (exists ((x!3 Int) (x!4 Int))
                  (and (or (not (<= x!3 1)) (not (>= x!4 5)))
                         (not (<= x!3 (- 1)))
                         (or (not (<= x!3 0)) (not (>= x!4 1)))
                         (= x!1 (+ 1 x!4))
                         (= x!0 (+ 1 x!3)))
                    ))
          (a!2 (and (or (not (<= x!0 1)) (not (>= x!1 5)))
                    (not (<= x!0 (- 1)))
                    (or (not (<= x!0 0)) (not (>= x!1 1))))))
      (or a!1 a!2)))
  (define-fun lt_468_133_0 ((x!0 Int) (x!1 Int)) Bool
    true)
  (define-fun add_483_127_2 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun add_483_146_1 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun dodeca_45_171_8 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun x_127342_166_0 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (let ((a!1 (exists ((x!3 Int) (x!4 Int))
                  (and (or (not (>= x!4 2)) (= x!4 x!3)) (= x!1 x!0))
                    )))
      (or (= x!1 x!0) a!1 (not (>= x!1 2)))))
  (define-fun formula_10_133_1 ((x!0 Int) (x!1 Int)) Bool
    true)
  (define-fun dodeca_47 ((x!0 Int) (x!1 Int)) Bool
    true)
  (define-fun and_454_171_2 ((x!0 Int) (x!1 Int)) Bool
    (or (= x!0 0) (not (= x!1 1))))
  (define-fun add_483 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun index_6_157_2 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (let ((a!1 (exists ((x!3 Int))
                  (and (or (not (<= x!3 1)) (not (>= x!2 5)))
                         (not (<= x!3 (- 1)))
                         (or (not (<= x!3 0)) (not (>= x!2 1)))
                         (or (not (>= x!3 1)) (= x!0 0))
                         (not (= x!2 0))
                         (= x!1 0))
                    )))
      (or (= x!0 0) a!1 (not (>= x!2 1)))))
  (define-fun add_483_171_30 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun gt_451_126_0 ((x!0 Int) (x!1 Int)) Bool
    true)
  (define-fun minus_469 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (let ((a!1 (and (or (not (<= x!0 1)) (not (>= x!1 5)))
                    (not (<= x!0 (- 1)))
                    (or (not (<= x!0 0)) (not (>= x!1 1)))))
          (a!2 (exists ((x!3 Int) (x!4 Int))
                  (and (or (not (<= x!3 1)) (not (>= x!4 5)))
                         (not (<= x!3 (- 1)))
                         (or (not (<= x!3 0)) (not (>= x!4 1)))
                         (= x!1 (+ 1 x!4))
                         (= x!0 (+ 1 x!3)))
                    )))
      (or a!1 a!2)))
  (define-fun add_483_140_5 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun dodeca_46 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun add_483_137_6 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun colouring_12_157_0 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (let ((a!1 (exists ((x!3 Int) (x!4 Int))
                  (and (or (not (>= x!4 2)) (not (<= x!3 0)))
                         (or (not (>= x!3 2)) (not (>= x!4 1)))
                         (= x!0 1))
                    ))
          (a!2 (and (or (not (<= x!0 0)) (not (>= x!2 2)))
                    (or (not (>= x!0 2)) (not (>= x!2 1)))))
          (a!3 (and (or (not (>= x!2 2)) (not (<= x!0 0)))
                    (or (not (>= x!0 2)) (not (>= x!2 1)))))
          (a!4 (exists ((x!3 Int) (x!4 Int))
                  (and (not (>= x!2 1))
                         (or (not (>= x!4 2)) (not (<= x!3 0)))
                         (or (not (>= x!4 1)) (not (>= x!3 2)))
                         (= x!0 1))
                    ))
          (a!5 (exists ((x!3 Int) (x!4 Int) (x!5 Int))
                  (and (not (>= x!2 1))
                         (or (not (>= x!5 2)) (not (<= x!4 0)))
                         (or (not (>= x!5 1)) (not (>= x!4 2)))
                         (not (>= x!3 1))
                         (= x!0 1))
                    ))
          (a!6 (exists ((x!3 Int) (x!4 Int) (x!5 Int))
                  (and (not (>= x!2 1))
                         (or (not (>= x!5 2)) (not (<= x!4 0)))
                         (or (not (>= x!4 2)) (not (>= x!5 1)))
                         (not (>= x!3 1))
                         (= x!0 2))
                    )))
      (or a!1 a!2 a!3 a!4 a!5 a!6)))
  (define-fun dodeca_43 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun dodeca_43_140_0 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun add_483_137_1 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun index_6_155_1 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (let ((a!1 (exists ((x!3 Int))
                  (and (or (not (<= x!3 1)) (not (>= x!2 5)))
                         (not (<= x!3 (- 1)))
                         (or (not (<= x!3 0)) (not (>= x!2 1)))
                         (or (not (>= x!3 1)) (= x!0 0))
                         (not (= x!2 0))
                         (= x!1 0))
                    )))
      (or (= x!0 0) a!1 (not (>= x!2 1)))))
  (define-fun add_483_149_1 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun gt_451_29_0 ((x!0 Int) (x!1 Int)) Bool
    true)
  (define-fun add_483_140_2 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun add_483_152_1 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun ge_448_25_0 ((x!0 Int) (x!1 Int)) Bool
    true)
  (define-fun add_483_143_4 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
)
"""
  
  

  
  printfn $"{Weight.rmWeightBlocks content}" 
  
  // let p = Parser.Parser false
  // let cmds = p.ParseFile "/home/andrew/Downloads/dbg/lol/6/kek.smt2"
  // for c in cmds do printfn $">{c}"
  ()
  

let aa () =
  // let work = async {
  //   do loop ()
  //   printfn "Done" }
  //
  // let workWithTimeOut timeOut = async {
  //     let! comp = Async.StartChild (work, timeOut)
  //     return! comp }
  
  // let mutable  c: Stopwatch = Stopwatch ()
  // c.Start ()
  
  Async.AwaitTask((Task.Delay 500).ContinueWith(fun _ -> loop ()), 10000)
  |> Async.RunSynchronously
  |> function Some x -> printfn $"{x}" 
  // let c = CancellationToken true
  
  // Async.RunSynchronously (async { return loop () }, 5000, c)
  // while (c.ElapsedMilliseconds < 5000) do
    // printfn "HERE"
    // loop ()
    // Task.Delay(1)
  
  // System.Threading.Timer.ActiveCount
  // workWithTimeOut 1000000 |> Async.Start // prints "Done"
  // workWithTimeOut 200 |> Async.Start // throws System.TimeoutException
  
  // let cts = new CancellationTokenSource()   
  // Async.Start(workWithTimeOut 400 200, cts.Token)
  // Thread.Sleep 100
  // cts.Cancel() // throws System.OperationCanceledException
  
  

let ppppp () =
    let p = Parser.Parser false
    let cmds = p.ParseFile "/home/andrew/Downloads/dbg/lol/3/out.smt2"
    // let cmds = p.ParseFile "/home/andrew/Downloads/dbg/lol/3/horn-input.smt2"
    for cmd in cmds do
        printfn $"> {cmd}"
    