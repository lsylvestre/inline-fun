let f = fun x -> g x in
f 42 ;;


let f = inline fun x -> g x in
f 42 ;;

let f = inline fun x -> fun y -> add x y in
(f 42) 32 ;;

let f = inline fun x -> (inline fun y -> add x y) in
(f 42) 32 ;;


let f = (* inline *) fun g -> (g 42) in
let g1 = inline (fun x -> h x) in
f g1 ;;


let f = inline fun g -> g 42 in
let square = inline fun x -> (mult x) x in
f square ;;

let f = inline fun g -> g (h 6) in
let square = inline fun x -> (mult x) x in
f square ;;

let pid = inline fun int ->
          inline fun derivative ->
          fun p ->
          fun i ->
          fun d ->
          fun u -> let z = int u in
                   let bla = derivative p in
                   z in
let int = inline fun h -> fun x -> h x in
let h = (* inline *) fun y -> inc y in
pid (int h) ;;


(* ko because at least one branch of the conditional 
   is an inlined function *)
let f = if bar 5 then (inline fun x -> x)
                 else (inline fun x -> g x) in
f 42 ;;

(* idem *)
let id = inline fun x -> x in
let f = if bar 5 then id else (fun x -> x) in
f 42 ;;


(* ko if h is inline *)
let f = inline fun g -> if bar 5 then g else g in
let h = (* inline*) fun x -> j x in
f h ;;



