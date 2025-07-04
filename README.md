# inline-fun

This small (very experimental) high-order language has
a two kinds of functions : normal functions and functions 
to be inlined at compile-time.

## Syntax

```
e := fun x -> e
   | inline fun x -> e
   | c
   | x
   | e e
   | let x = e in e
   | if e then e else e

<prog> ::= e1 ;; e2 ;; ... en
```

## Usage

```
$ make
$ ./inliner test/test.ml
```

For each expression in the source program, the prototype prints
- the source expression,
- the result ("[ok]" or "[ko]") of a (type-based) static analysis rejecting stange expressions 
  such as `if e then (inline fun x -> x) else fun (y -> y)) 42`
- the inlined expression.
