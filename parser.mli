
(* The type of tokens. *)

type token = 
  | THEN
  | SEMISEMI
  | RPAREN
  | RIGHT_ARROW
  | LPAREN
  | LET
  | INT of (int)
  | INLINE
  | IN
  | IF
  | IDENT of (string)
  | FUN
  | EQ
  | EOF
  | ELSE

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Inliner.e list)
