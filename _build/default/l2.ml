(*Want functions. Abstract a piece of code on some paramter(s) so this code 
can be reused without having to rewrite this out!*)


(* 2015-10-13   -*-ocaml-*- *)
(* Peter Sewell                                                       *)

(* This file contains an interpreter, pretty-printer and type-checker
   for the language L1.  To make it go, copy it into a working
   directory, ensure OCaml is available, and type

       ocamlc l1_ocaml.ml 

   That will build an executable a.out, and typing
      
      ./a.out

   will show the reduction sequence of < l1:=3;!l1 , {l1=0 } >.

   You can edit the file and recompile to run

      doit2 ();

   to run the type-checker on the same simple example; you can try
   other examples analogously.  This file doesn't have a parser for
   l1, so you'll have to enter the abstract syntax directly, eg

      prettyreduce (Seq( Assign ("l1",Integer 3), Deref "l1"), [("l1",0)]);

*)


(* *********************)
(* the raw abstract syntax - then the new abstract syntax which respects alpha conversion for local scoping of variables. *)
(* *********************)

type loc = string

type oper = Plus | GTEQ

type var_raw = string


(* types *)

type type_expr =
  | Int
  | Unit
  | Bool
  | Func of type_expr * type_expr

type type_loc =
  | Intref


type expr_raw = 
   Integer_raw of int
 | Boolean_raw of bool
 | Op_raw of expr_raw * oper * expr_raw
 | If_raw of expr_raw * expr_raw * expr_raw
 | Assign_raw of loc * expr_raw
 | Deref_raw of loc
 | Skip_raw
 | Seq_raw of expr_raw * expr_raw
 | While_raw of expr_raw * expr_raw
 | Var_raw of var_raw
 | Fn_raw of var_raw * type_expr * expr_raw
 | App_raw of expr_raw * expr_raw
 | Let_raw of var_raw * type_expr * expr_raw * expr_raw
 | Letrecfn_raw of var_raw * type_expr * var_raw * type_expr * expr_raw * expr_raw



type expr = 
    Integer of int
  | Boolean of bool
  | Op of expr * oper * expr
  | If of expr * expr * expr
  | Assign of loc * expr
  | Deref of loc
  | Skip
  | Seq of expr * expr
  | While of expr * expr
  | Var of int
  | Fn of type_expr * expr
  | App of expr * expr
  | Let of  type_expr * expr * expr
  | Letrecfn of type_expr * type_expr * expr * expr


(*Cool, now we need a way of resolving a raw expr into a real expr  -essentially for any variable, 
we go up to the most recent scope where its defined, and count how many scopes we passed through to get there!*)

(*First lets count from a list of raw_expressions! (which will be the vars of exprs that define scope)*)
let rec find_first x lst m  = 
  match lst with 
  | [] -> None
  | hd::tl-> if hd = x then Some m else find_first x tl (m+1)

(*Here lst will be our current function stack!*)

exception Resolve of string

let rec resolve lst raw = 
  match raw with
  | Integer_raw n -> Integer n 
  | Boolean_raw n -> Boolean n
  | Op_raw (e1, oper, e2) -> Op (resolve lst e1, oper,  resolve lst e2)
  | If_raw (e1, e2, e3) -> If (resolve lst e1, resolve lst e2, resolve lst e3)
  | Assign_raw (loc, e) -> Assign (loc, resolve lst e)
  | Deref_raw loc -> Deref loc 
  | Skip_raw -> Skip
  | Seq_raw (e1,e2) -> Seq (resolve lst e1, resolve lst e2)
  | While_raw (e1,e2) -> While (resolve lst e1, resolve lst e2)
  | Var_raw x -> (match (find_first x lst 0) with 
    | None -> raise (Resolve "NOT FECKIN CLOSED")
    | Some m -> Var m)
  | Fn_raw (v1, t , e) -> Fn (t , resolve (v1::lst) e)
  | App_raw (e1, e2) -> App(resolve lst e1, resolve lst e2)
  | Let_raw (x, t, e1,e2) -> Let(t, resolve lst e1, resolve (x::lst) e2)
  | Letrecfn_raw (f,tf,y, ty, e1,e2) -> Letrecfn(tf, ty , resolve (y::(f::lst)) e1, resolve (f::lst) e2)



(*Having got our expressions using De Brujin indices -can implement substitution
We can just do multiple subs as a sequence of single subs*)
(*type should be expr -> var -> expr -> expr*)
(*IN fact : can just do as expr -> int -> expr -> expr using De Brujin! hence why we did it. Can just pattern match to Var m otherwise*)
let rec sub e1 m e2 = 
  match e2 with
  | Integer _ | Boolean _ | Skip  -> e2
  | Op (e,oper, e') -> Op( sub e1 m e , oper,  sub e1 m e')
  | If (e, e', e'') -> If ( sub e1 m e, sub e1 m e' , sub e1 m e'')
  | Assign (loc, e) -> Assign (loc, sub e1 m e)
  | Deref loc -> Deref loc
  | Seq(e, e') -> Seq ( sub e1 m e , sub e1 m e')
  | While( e ,e') -> While ( sub e1 m e, sub e1 m e')
  (*Now we get down to business*)
  | Var n as e2 -> if n=m then e1 else e2
  | Fn (t, e) -> Fn(t, sub e1 (m+1) e) 
  | App (e ,e') -> App(sub e1 m e, sub e1 m e')
  | Let(t, e, e') -> Let(t, sub e1 m e, sub e1 (m+1) e' )
  | Letrecfn(tf,ty,e,e') -> Letrecfn(tf ,ty , sub e1 (m+2) e, sub e1 (m+1) e') 

 

  let is_value v = 
  match v with
  | Integer _ -> true
  | Boolean _ -> true
  | Skip -> true
  | Fn _ -> true
  | _ -> false

(* **********************************)
(* an interpreter for the semantics *)
(* **********************************)

  (* In the semantics, a store is a finite partial function from
  locations to integers.  In the implementation, we represent a store
  as a list of loc*int pairs containing, for each l in the domain of
  the store, exactly one element of the form (l,n).  The operations

    lookup : store -> loc         -> int option
    update : store -> (loc * int) -> store option

  both return NONE if given a location that is not in the domain of
  the store.  This is not a very efficient implementation, but it is
  simple. *)

type store = (loc * int) list

let rec lookup s l = 
  match s with
  | [] -> None
  | (l',n')::s' -> 
    if l=l' then Some n' else lookup s' l 

let rec update' front s (l,n) = 
  match s with
  | [] -> None
  | (l',n')::s' ->
    if l=l' then 
      Some(front @ ((l,n)::s'))
    else 
      update' ((l',n')::front) s' (l,n)

let update s (l,n) = update' [] s (l,n)


  (* now define the single-step function

     reduce :  expr * store -> (expr * store) option 

  which takes a configuration (e,s) and returns either None, if it has
  no transitions, or Some (e',s'), if it has a transition (e,s) -->
  (e',s'). 

  Note that the code depends on global properties of the semantics,
  including the fact that it defines a deterministic transition
  system, so the comments indicating that particular lines of code
  implement particular semantic rules are not the whole story.  *)


(*We dont need an exception - since we're using options*)
exception Reduce of string (*I believe this is to capture non-closedness - which happens when we locate a free variable!*)

(*Aha - and we do indeed need some helper functions for implementing the reduction in the recursive case - for 
swapping and shifting the De Brujin indices*)


(*Shift,
I dont this this just increases de brujin indices >=n by 1.

Instead - we think of it as increasing any variables OF DEPTH >=c relative to the root of e, by 1. Hence why we have to incremeny by 1
Indeed consider e = fn(x:T => x+1), this has tree:  fn
                                                     \
                                                      Var 0 +1
The De Bruijn index is 0 becuase its bound to the closest function
If I call shift 0 e, I dont want to increment this variable - it has 'depth 1' in e. Kinda a dual notion here
The DB index of a variable is the number of binding sites passed to get to its binding site
The Cut off here is now many binding sites we take to get to the variable.
Kinda badly worded. : “shift d 0 e increases all De Bruijn indices k >= 0 by d.”
That statement is literally true only if you interpret it at the top level and only for occurrences that are not under additional binders. But it ignores that the value of c changes as you recurse.                                                      
                                                      *)
let rec shift n e = 
  match e with 
  | Integer _| Boolean _ | Deref _ | Skip  as e -> e
  | Op (e1,oper,e2) -> Op (shift n e1, oper , shift n e2)
  | If(e1,e2,e3) -> If( shift n e1, shift n e2, shift n e3)
  | Assign (loc, e) -> Assign (loc, shift n e)
  | While(e1,e2) -> While (shift n e1, shift n e2)
  | Seq(e1,e2) -> Seq(shift n e1, shift n e2)
  | Var m -> if m>=n then Var (m+1) else Var m
  | Fn (t,e) -> Fn (t, shift (n+1) e) (*In his implementation is (n+1) though Im not quite sure why :/*)
  | App (e1,e2)-> App (shift n e1, shift n e2)
  | Let (t,e1,e2)-> Let( t , shift n  e1, shift (n+1) e2)
  | Letrecfn (tf, ty , e1, e2) -> Letrecfn( tf,ty, shift (n+2) e1, shift (n+1_) e2 ) 



(*Now take an expression, and swap any variables in the expression wtih DB inedx n with those of n+1 - however if we pass further into the function, increment n*)
let rec swap n e = 
   match e with 
  | Integer _| Boolean _ | Deref _ | Skip  as e -> e
  | Op (e1,oper,e2) -> Op (swap n e1, oper , swap n e2)
  | If(e1,e2,e3) -> If( swap n e1, swap n e2, swap n e3)
  | Assign (loc, e) -> Assign (loc, swap n e)
  | While(e1,e2) -> While (swap n e1, swap n e2)
  | Seq(e1,e2) -> Seq(swap n e1, swap n e2)
  | Var m -> if m=n then Var (m+1) else if m = (n+1) then Var n else Var m
  | Fn (t,e) -> Fn (t, swap (n+1) e) 
  | App (e1,e2)-> App (swap n e1, swap n e2)
  | Let (t,e1,e2)-> Let( t , swap n e1, swap (n+1) e2) 
  | Letrecfn (tf, ty , e1, e2) -> Letrecfn( tf,ty, swap (n+2) e1, swap (n+1) e2)




(*First few cases are copied straight from L1!*)
(*We note that we're using CBV (call by value) so we reduce the expression that will be an input first, moreover since we're dealing with 
our abstract syntax trees, we again neednt worry about whehter associativity and such is being done correctly, we can just assume some parser has done this job for us!*)
let rec reduce (e,s) = 
  match e with
  | Integer _ -> None
  | Boolean _ -> None
  | Op (e1,opr,e2) -> 
      (match (e1,opr,e2) with
      | (Integer n1, Plus, Integer n2) -> Some(Integer (n1+n2), s)   (*op + *)
      | (Integer n1, GTEQ, Integer n2) -> Some(Boolean (n1 >= n2), s)(*op >=*)
      | (e1,opr,e2) -> (                                               
          if (is_value e1) then 
            (match reduce (e2,s) with
            | Some (e2',s') -> Some (Op(e1,opr,e2'),s')     (* (op2) *)
            | None -> None )                           
          else 
            (match reduce (e1,s) with
            | Some (e1',s') -> Some(Op(e1',opr,e2),s')      (* (op1) *)
            | None -> None ) ) )
  | If (e1,e2,e3) ->
      (match e1 with
      | Boolean(true) -> Some(e2,s)                         (* (if1) *)
      | Boolean(false) -> Some(e3,s)                        (* (if2) *)
      | _ -> 
          (match reduce (e1,s) with
          | Some(e1',s') -> Some(If(e1',e2,e3),s')          (* (if3) *)
          | None -> None ))
  | Deref l -> 
      (match lookup s l with
      | Some n -> Some(Integer n,s)                         (* (deref) *)
      | None -> None )                  
  | Assign (l,e) ->                                  
      (match e with                                                  
      | Integer n -> 
          (match update  s (l,n) with
          | Some s' -> Some(Skip, s')                       (* (assign1) *)
          | None -> None)                                   
      | _ -> 
          (match reduce (e,s) with
          | Some (e',s') -> Some(Assign (l,e'), s')         (* (assign2) *)
          | None -> None  ) )                          
  | While (e1,e2) -> Some( If(e1,Seq(e2,While(e1,e2)),Skip),s) (* (while) *)
  | Skip -> None                                     
  | Seq (e1,e2) ->                                   
    (match e1 with                                                
    | Skip -> Some(e2,s)                                    (* (seq1) *)
    | _ -> 
        (match reduce (e1,s) with
        | Some (e1',s') -> Some(Seq (e1',e2), s')           (* (seq2) *)
        | None -> None ) )
  | Var _ -> raise (Reduce "UNBOUND VARIABLE - program not closed!")
  | Fn _ -> None
  | App (e1, e2) -> 
      if not (is_value e1) then
        (match reduce (e1,s) with 
        |None -> None 
        |Some (e1,s) -> Some (App(e1, e2) , s))
      else if not (is_value e2) then
        (match reduce (e2,s) with 
        |None -> None 
        |Some (e2,s) -> Some (App(e1, e2) , s))
      else (match e1 with
      | Fn(_, e) -> Some( sub e1 0 e, s ) 
      | _ -> None)
  | Let(t, e1 ,e2) -> if is_value e1 then Some ( sub e1 0 e2, s) else 
    (match reduce(e1, s) with None -> None | Some (e1,s) -> Some (Let(t,e1,e2) ,s)  )
  | Letrecfn(tf,ty,e1,e2) -> 
      let enew = Fn(ty, Letrecfn(tf,ty,shift 2 e1, swap 0 e1)) in 
        Some (sub enew 0 e2, s)
    




  (* now define the many-step evaluation function

     evaluate :  expr * store -> (expr * store) option 

  which takes a configuration (e,s) and returns the unique (e',s')
  such that   (e,s) -->* (e',s') -/->.  *)

let rec evaluate (e,s) = 
  match reduce (e,s) with
  | None -> (e,s)
  | Some (e',s') -> evaluate (e',s')


(* **********************************)
(* typing                           *)
(* **********************************)


(* in the semantics, type environments gamma are partial functions
from locations to the singleton set {intref}. Here, just as we did for
stores, we represent them as a list of loc*type_loc pairs containing,
for each l in the domain of the type environment, exactly one element
of the form (l,intref).  *)


(* ****************)
(* type inference *)
(* ****************)


(* First - what should Gamma be? Well we have our usual partial map from locations to Type_loc- which we treat as a list.
For Variable types - we can just a stack and De Bruijn indices to give the position in the stack.*)
type typeEnv = (loc*type_loc) list  * type_expr list




(* infertype : typeEnv -> expr -> type_L1 option *)

(* again, we depend on a uniqueness property, without which we would
have to have infertype return a type_L1 list of all the possible types *)




let rec infertype gamma e = let (gamma1, gamma2) = gamma in
  match e with 
  | Integer _ -> Some Int
  | Boolean _ -> Some Bool
  | Op (e1,opr,e2) -> 
      (match (infertype gamma e1, opr, infertype gamma e2) with
      | (Some Int, Plus, Some Int) -> Some Int
      | (Some Int, GTEQ, Some Int) -> Some Bool
      | _ -> None)
  | If (e1,e2,e3) ->
    (match (infertype gamma e1, infertype gamma e2, infertype gamma e3) with
    | (Some Bool, Some t2, Some t3) -> 
        (if t2=t3 then Some t2 else None)
    | _ -> None)
  | Deref l ->
     (match lookup gamma1 l with
     | Some Intref -> Some Int
     | None -> None)
  | Assign (l,e) ->
      (match (lookup gamma1 l, infertype gamma e) with
      | (Some Intref,Some Int) -> Some Unit
      | _ -> None)
  | Skip -> Some Unit
  | Seq (e1,e2) ->
     (match (infertype gamma e1, infertype gamma e2) with
     | (Some Unit, Some t2) -> Some t2
     | _ -> None )
  | While (e1,e2) -> 
      (match (infertype gamma e1, infertype gamma e2) with
      | (Some Bool, Some Unit) -> Some Unit 
      | _ -> None )
  | Var n -> List.nth_opt gamma2 n
  | App (e1,e2) -> ( match (infertype gamma e1, infertype gamma e2) with
    | (Some (Func(t1,t2)), Some t) -> if t1 =t then Some t2 else None
    | _ -> None)
  | Fn (t1,e) ->  
    (match infertype (gamma1, t1::gamma2)  e with
    | Some t2 -> Some (Func (t1,t2))
    | None -> None)
  | Let (t,e1,e2) -> (match (infertype gamma e1, infertype (gamma1, t::gamma2) e2) with
    |(Some t1, Some t2) -> if t1 =t then Some t2 else None
    | _ -> None )
  | Letrecfn (tf,ty, e1,e2)-> match( infertype (gamma1,ty::(tf::gamma2)) e1,  infertype (gamma1, tf::gamma2) e2 ) with
    |  (Some t1, Some t2 ) -> if tf = Func (ty,t1) then Some t2 else None
    | _ -> None 



(* ****************** *)
(* testing machinery  *)
(* ****************** *)
(*;
load "Listsort";
load "Int";
load "Bool";
*)

(* pretty print expressions *)
let rec prettyprinttype = function
| Int -> "int"
| Bool -> "bool"
| Unit -> "unit"
| Func (t1,t2) -> "(" ^ prettyprinttype t1 ^ "->"^  prettyprinttype t2 ^ ")"


let prettyprintop op = 
  match op with
  | Plus -> "+"
  | GTEQ ->">="
             
let rec prettyprintexpr e = 
  match e with            
  | Integer n -> string_of_int  n
  | Boolean b -> string_of_bool b
  | Op (e1,opr,e2) ->
      "(" ^ (prettyprintexpr e1) ^ (prettyprintop opr) 
      ^ (prettyprintexpr e2) ^ ")"
  | If (e1,e2,e3) ->
      "if " ^ (prettyprintexpr e1 ) ^ " then " ^ (prettyprintexpr e2)
      ^ " else " ^ (prettyprintexpr e3)
  | Deref l -> "!" ^ l
  | Assign (l,e) ->  l ^ ":=" ^ (prettyprintexpr e)
  | Skip -> "skip"
  | Seq (e1,e2) ->  (prettyprintexpr e1 ) ^ ";" ^ (prettyprintexpr e2)
  | While (e1,e2) ->  
      "while " ^ (prettyprintexpr e1 ) 
      ^ " do " ^ (prettyprintexpr e2)
  | Var n -> "Var" ^ string_of_int n
  | App (e1,e2) -> prettyprintexpr e1 ^ prettyprintexpr e2
  | Fn(t, e) -> "fn :" ^ prettyprinttype t ^ "=> " ^ prettyprintexpr e
  | Let(t,e1,e2) -> "let val :" ^ prettyprinttype t ^ " = " ^ prettyprintexpr e1 ^ " in " ^ prettyprintexpr e2 ^ " end"
  | Letrecfn(tf,ty,e1,e2) -> "let val rec :" ^ prettyprinttype tf ^ " = " ^ prettyprintexpr (Fn(ty,e1)) ^ " in " ^ prettyprintexpr e2 ^ " end"
(* pretty print stores, first sorting by location names for readability *)



let rec rawprintstore s = 
  match s with
  | [] -> ""
  | ((l,n)::pairs) ->
    l ^ "=" ^ (string_of_int n) 
    ^ " " ^ (rawprintstore pairs)

let prettyprintstore pairs = 
  let pairs' = List.sort 
      (function (l,n) -> function (l',n') -> compare l l')
      pairs
  in
  "{" ^ rawprintstore pairs' ^ "}" 

(* pretty print configurations *)

let prettyprintconfig (e,s) = 
  "< " ^ (prettyprintexpr e) 
  ^ " , " ^ (prettyprintstore s) ^ " >"

(* do a reduction sequence, printing the initial state and the state
   after each reduction step *)

let rec prettyreduce' (e,s) = 
    match reduce (e,s) with
    | Some (e',s') -> 
        ( Printf.printf "%s" ("\n -->  " ^ prettyprintconfig (e',s') ) ;
          prettyreduce' (e',s'))
    | None -> (Printf.printf "%s" "\n -/->  " ; 
               if is_value e then 
                 Printf.printf "(a value)\n" 
               else 
                 Printf.printf "(stuck - not a value)" )
          
let rec prettyreduce (e,s) = (Printf.printf "%s" ("      "^(prettyprintconfig (e,s))) ;
                              prettyreduce' (e,s))

(* **************)
(* simple tests *)
(* **************)

(* l1:=3;!l1 *)
let e = Seq( Assign ("l1",Integer 3), Deref "l1")

(* {l1=0 } *)
let s = [("l1",0)]

let doit () = 
  prettyreduce (e, s)
    

(*
 infertype [("l1",intref)] (Seq( Assign ("l1",Integer 3), Deref "l1"));;
*)
let doit2 () = infertype ([("l1",Intref)] ,[])(Seq( Assign ("l1",Integer 3), Deref "l1"))

let _ = doit ()

