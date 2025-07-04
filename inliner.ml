type x = string
type e = Fun of x * e
       | InlineFun of x * e
       | Const of int
       | Var of x
       | App of e * e
       | Let of x * e * e
       | If of e * e * e

let fun_ x e        = Fun(x,e)
let inline_fun_ x e = InlineFun(x,e)
let const n         = Const n
let var x           = Var x
let let_ x e1 e2    = Let(x,e1,e2)
let app e1 e2       = App(e1,e2)
let if_ e1 e2 e3    = If(e1,e2,e3)

let rec print_exp fmt e =
  let open Format in
  match e with
  | Fun(x,e) -> fprintf fmt "@[<v 3>(fun %s ->@,%a)@]" x print_exp e
  | InlineFun(x,e) -> fprintf fmt "@[<v 3>(inline fun %s ->@,%a)@]" x print_exp e
  | Const(n) -> fprintf fmt "%d" n
  | Var(x) -> fprintf fmt "%s" x
  | App(e1,e2) -> fprintf fmt "@[<v>(%a %a)@]" print_exp e1 print_exp e2
  | Let(x,e1,e2) -> fprintf fmt "@[<v>(let %s = %a in@,@[<v 0>%a@])@]" x print_exp e1 print_exp e2
  | If(e1,e2,e3) -> fprintf fmt "@[<v>(@[<v 2>if %a then %a@]@,@[<v 2>else %a@])@]" print_exp e1 print_exp e2 print_exp e3

let rec subst x ev e =
  match e with
  | Fun(y,e') -> if x = y then e else
                 Fun(y, subst x ev e')
  | InlineFun(y,e') -> if x = y then e else
                       InlineFun(y, subst x ev e')
  | Const _ -> e
  | Var y -> if x = y then ev else e
  | App(e1, e2) -> App(subst x ev e1, subst x ev e2)
  | Let(y, e1, e2) -> if x = y then e else 
                      Let(y, subst x ev e1, subst x ev e2)
  | If(e1, e2, e3) -> If(subst x ev e1, subst x ev e2, subst x ev e3)

let rec is_value = function
| Fun _ | InlineFun _ | Const _ | Var _ -> true
| _ -> false

let gensym =
  let c = ref 0 in
  fun () -> incr c; "$"^(string_of_int !c) ;;

(* ****************************************** *)
(* intuition : 1/ « inline » duplique le corps
               2/ propage l'argument (lui même inliné) 
               3 la propagation de l'argument est une substitution quand c'est possible 
                     (i.e. quand l'argument est une valeur ou une variable)
                  et sinon, introduit un let/in (pour maintenir le partage)
   ----------------------------------------
   avec en particulier :
   1/ Inl{let f = inline fun x -> e in e'} ~> Inl{e'[(inline fun x -> e)/f]}
   2/ Inl{((inline fun x -> e) v)} ~> Inl{e[v/x]}
   3/ Inl{((inline fun x -> e) e0)} ~> Inl{let x = e0 in e} si e0 n'est pas une valeur
*)
let rec inl e =
  match e with
  | Fun(x,e') -> Fun(x,inl e')
  | InlineFun(x,e') -> InlineFun(x,inl e')
  | Const _ -> e
  | Var _ -> e
  | Let(x,e1,e2) -> 
      (match inl e1 with
      | (InlineFun _) as v -> inl (subst x v e2)
      | e1' -> Let(x,e1',inl e2))
  | App(e1,e2) -> 
      (match inl e1, inl e2 with
      | (InlineFun(x,e3)), e4 -> 
          if is_value e4 then inl (subst x e4 e3)
          else let z = gensym () in
               (* avoid captures *)
               Let(z,e4,subst x (Var z) e3)
      | e1',e2' -> App(e1',e2'))
  | If(e1, e2, e3) -> If(inl e1, inl e2, inl e3)
(* ****************************************** *)
      
type k = Arrow of k * k | Opaque | Unknown of var ref
and var = Instance of k | N of int

let new_unknown =
  let c = ref 0 in
  fun () -> incr c; Unknown (ref (N !c)) ;;

let rec canon = function
| Arrow(k1,k2) -> Arrow(canon k1, canon k2)
| Opaque -> Opaque
| Unknown({contents=Instance k} as v) ->
    let k' = canon k in
    v := Instance k';
    k'
| Unknown _ as kv -> kv


exception CannotUnify

let rec unify k1 k2 =
  match canon k1,canon k2 with
  | Unknown({contents=N n} as r), Unknown({contents=N m}) ->
      if n = m then () else r := N n
  | Unknown({contents=N _} as r), k
  | k, Unknown({contents=N _} as r) ->
      r := Instance k
  | Opaque,Opaque -> ()
  | Arrow(k3,k4), Arrow(k5,k6) ->
      unify k3 k5;
      unify k4 k6
  | _ -> raise CannotUnify

let rec check env e =
  match e with
  | Const _ -> Opaque
  | Var x -> (match List.assoc_opt x env with
              | None -> 
                  (* here, free variables are supposed to be predefined objects, wich are opaque *)
                  Opaque
              | Some k -> k)
  | Fun(_,e') ->
      let _ = check env e' in
      Opaque
  | InlineFun(x,e') ->
      let v = new_unknown () in
      let env' = (x,v)::env in
      let k = check env' e' in
      Arrow(v,k)
  | App(e1,e2) ->
      let k1 = check env e1 in
      let k2 = check env e2 in
      (match canon k1 with
       | Opaque -> Opaque
       | Arrow(v,k) -> unify v k2; k
       | Unknown _ -> Opaque (* ok ? *)
       )
  | Let(x,e1,e2) ->
      let k1 = check env e1 in
      check ((x,k1)::env) e2
  | If(e1,e2,e3) ->
      let k1 = check env e1 in
      let k2 = check env e2 in
      let k3 = check env e3 in
      unify k1 Opaque;
      unify k2 Opaque;
      unify k3 Opaque;
      Opaque


let check_ok e =
  try 
    let _ = check [] e in 
    true 
  with CannotUnify -> false
      