module Tree.Tree

type 'T tree = Node of 'T * 'T tree list

module Tree =
  let rec fmap f =
    function
    | Node (v, vs) -> Node (f v, List.map (fmap f) vs)

  let rec fmap2 f x y =
    match (x, y) with
    | Node (v1, vs1), Node (v2, vs2) -> Node (f v1 v2, List.map2 (fmap2 f) vs1 vs2)

  let rec fold f x =
    function
    | Node (v, ts) -> f (List.fold (fold f) x ts) v

  let value (Node (v, _)) = v

  let kids =
    function
      | Node (_, []) -> []
      | Node (_, xs) -> xs