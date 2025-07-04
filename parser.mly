%{
  open Inliner

%}
 
%token LET IN IF THEN ELSE FUN EQ INLINE
%token SEMISEMI

%token <int> INT
%token <string> IDENT

%token EOF LPAREN RPAREN 
%token  RIGHT_ARROW

%nonassoc  LET
%nonassoc  IN
%nonassoc  IF
%right     RIGHT_ARROW
                
%nonassoc  IDENT LPAREN RPAREN    

%start prog         /* the entry point */

%type <Inliner.e list>  prog
%type <Inliner.e>  exp
%type <Inliner.x>  pat

%%

prog :
 | e=exp SEMISEMI es=prog    { e::es }
 | e=exp SEMISEMI EOF        { [e] } 
;

exp :
| LPAREN e=exp RPAREN              { e }
| x=IDENT                          { Var(x) }
| n=INT                            { Const(n) }
| FUN p=pat RIGHT_ARROW e1=exp     { Fun(p,e1) }
| INLINE e=exp   { match e with 
                   | Fun(x,e') -> InlineFun(x,e')
                   | _ -> Printf.printf "should be an expression"; exit 0 }
| LET p=pat EQ e1=exp IN e2=exp    { Let(p,e1,e2) }
/* | LET REC pat EQ exp IN expression { LetRec($3,$5,$7) }*/
| IF e1=exp THEN e2=exp ELSE e3=exp  { If(e1,e2,e3) }
| exp exp                          { App($1,$2) }
;

pat:
x=IDENT { x }