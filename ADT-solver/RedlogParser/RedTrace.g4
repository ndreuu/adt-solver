grammar RedTrace;

prog : PREAMBULA expr POSTAMBULA EOF;

expr : '(' and expr+ ')'
     | '(' or expr+ ')'
     | '(' ncgong body nil ')'
     | '(' equal body nil ')'
     | '(' neq body nil ')'
     | '(' leq body nil ')'
     | '(' geq body nil ')'
     | '(' ball id expr expr ')'
     ;

mul : factor
    | power (factor | num)+
    | power '(' mul+ ')'
    ;

body : '('('('mul')' | factor | num)+')';
ncgong : '(' NCONG ('('mul')' | factor | num) ')';

factor : '('power'.'number')';
power : '('id'.'number')';
num : '.'number;

number : NUM;
id : ID;
and : AND;
or : OR;
equal : EQUAL;
neq : NEQ;
leq : LEQ;
geq : GEQ;
ball : BALL;
nil : NIL;

AND : 'and';
OR : 'or';
EQUAL : 'equal';
LEQ : 'leq';
NEQ : 'neq';
GEQ : 'geq';
NCONG : 'ncong';
BALL : 'ball';
NIL : 'nil';

PREAMBULA : '(!*fof (pasf)';
POSTAMBULA : 't)';
ID : '!_'?[a-z]+NUM;
NUM : '0' | '-'?[1-9][0-9]*;
WS : [ \t\n]+ -> skip;















