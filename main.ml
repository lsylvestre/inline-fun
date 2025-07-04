open Inliner

let _ =
  if Array.length Sys.argv < 2 then exit 0 else ();
  let fname = Sys.argv.(1) in
  let ic = open_in fname in
  let lexbuf = Lexing.from_channel ic in
  let es = Parser.prog Lexer.token lexbuf in
  close_in ic;
  
  List.iter (fun e ->
      let e' = inl e in
      Format.(fprintf std_formatter "@[<v>source {%a}@,@,check: %s@,@,inlining: {%a}@,---------------------------------------@,@]" 
         print_exp e 
         (check_ok e)
         print_exp e')) es
    ;;