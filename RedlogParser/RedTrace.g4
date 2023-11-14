grammar RedTrace;

prog : PREAMBULA formula POSTAMBULA EOF;

formula : '(' and formula+ ')'
     | '(' or formula+ ')'
     | '(' ncgong polynom nil ')'
     | '(' cong polynom nil ')'
     | '(' equal_zero polynom nil ')'
     | '(' gr polynom nil ')'
     | '(' ls polynom nil ')'
     | '(' neq polynom nil ')'
     | '(' leq polynom nil ')'
     | '(' geq polynom nil ')'
     | '(' ball id formula formula ')'
     | false
     ;

polynom : '(' power? polynom+ ('.'number)? ')' | monom ('.'number)? | '.'number | number;
monom : '(' power '.' number ')';
ncgong : '(' NCONG polynom+ ')' ;
cong : '(' CONG polynom+ ')' ;
power : '('id'.'number')';

number : NUM;
id : ID;
and : AND;
or : OR;
equal_zero : EQUAL;
gr : GR;
ls : LS;
neq : NEQ;
leq : LEQ;
geq : GEQ;
ball : BALL;
nil : NIL;
false : FALSE;

AND : 'and';
OR : 'or';
EQUAL : 'equal';
GR : 'greaterp';
LS : 'lessp';
LEQ : 'leq';
NEQ : 'neq';
GEQ : 'geq';
NCONG : 'ncong';
CONG : 'cong';
BALL : 'ball';
NIL : 'nil';
FALSE : 'false';

PREAMBULA : '(!*fof (pasf)';
POSTAMBULA : 't)';
ID : '!_'?[a-z]+('_'?)NUM;
NUM : '0' | '-'?[1-9][0-9]*;
WS : [ \t\n]+ -> skip;















