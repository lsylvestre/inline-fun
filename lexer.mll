{
  open Parser
  exception Eof
}

let ident = ['a'-'z''_'] ['a'-'z''A'-'Z''0'-'9''_']*

rule token = parse
| (('-'?)['0'-'9']+) as lxm
                    { let n = int_of_string lxm in
	                    INT(n) }
| '('                { LPAREN }
| ')'                { RPAREN }
| "let"              { LET }
| "fun"              { FUN }
| "inline"           { INLINE }
| "in"               { IN }
| "if"               { IF }
| "then"             { THEN }
| "else"             { ELSE }
| "="                { EQ }
| "->"               { RIGHT_ARROW }
| ";;"               { SEMISEMI }
| ident as id        { IDENT id }
| ['\n''\r']         { (Lexing.new_line lexbuf) ; (token lexbuf) }
| [' ' '\t']         { token lexbuf }    (* skip blanks *)
| "(*"               { comment lexbuf }  (* comment until closing *)
| eof                { EOF }
| _  as lxm { 
       let Lexing.{pos_lnum=l1;pos_cnum=c1;pos_bol=b1} = Lexing.lexeme_start_p lexbuf in
       let Lexing.{pos_lnum=l2;pos_cnum=c2;pos_bol=b2} = Lexing.lexeme_end_p lexbuf in
       Printf.printf "From line %d, characters %d, to line %d characters %d\n" l1 (c1-b1) l2 (c2-b2);
       Printf.printf "Unexpected character: %c\n" lxm;
       exit 0 }

and comment = parse
| "*)"        { token lexbuf }
| ['\n''\r']  { Lexing.new_line lexbuf; comment lexbuf }
| eof         { Printf.printf "unclosed comment"; exit 0 }
| _           {comment lexbuf } 
