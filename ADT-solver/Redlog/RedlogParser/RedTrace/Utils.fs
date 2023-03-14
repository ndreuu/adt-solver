module RedlogParser.RedTrace.Utils

open SMTLIB2.Prelude

let mulOp = ElementaryOperation ("*", [ IntSort; IntSort ], IntSort)
let negOp = ElementaryOperation ("-", [ IntSort ], IntSort)
let addOp = ElementaryOperation ("+", [ IntSort; IntSort ], IntSort)
let eqOp = ElementaryOperation ("=", [ IntSort; IntSort ], BoolSort)
let grOp = ElementaryOperation (">", [ IntSort; IntSort ], BoolSort)

let lsOp = ElementaryOperation ("<", [ IntSort; IntSort ], BoolSort)
let leqOp = ElementaryOperation ("<=", [ IntSort; IntSort ], BoolSort)
let geqOp = ElementaryOperation (">=", [ IntSort; IntSort ], BoolSort)
let modOp = ElementaryOperation ("mod", [ IntSort; IntSort ], IntSort)

