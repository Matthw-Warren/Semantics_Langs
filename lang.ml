type loc = string
type store  = (loc * int) list 


type oper = Plus | GTEQ 

type expr = 
  | Integer of int
  | Boolean of bool
  | Op of expr * oper * expr
  | If of expr * expr * expr
  | Assign of loc * expr
  | Deref of loc
  | Skip
  | Seq of expr * expr
  | While of expr * expr




let rec lookup store loc  =
match store with
|[] -> None
|(l,value)::tl -> if l = loc then Some value else lookup tl loc


let rec update' front s (l,n) = 
  match s with
  | [] -> None
  | (l',n')::s' ->
    if l=l' then 
      Some(front @ ((l,n)::s'))
    else 
      update' ((l',n')::front) s' (l,n)

let update s l n = update' [] s (l,n)


(*Now we implement reduction of configurations  - ie. steps in our transition system
Because there is no ambiguity - ie. is a deterministic system, we can just use a funciton to do this!
Can just pattern match the left hand side and apply our funcitons.*)


(*First, if we've reached a value - then we're at a terminus, ie. we're at a stuck state*)
let is_value v = 
  match v with
  |Integer _ |Boolean _ | Skip -> true
  | _ -> false


type type_L1= Int | Bool | Unit

type type_loc = Intref

(*Then we need a Gamma thing*)
type typeEnv = (loc* type_loc) list


let rec infertype gamma e =
  (*Now we just need to walk through our statements defininig the Ternary relation!*)
  match e with 
  | Integer _ -> Some Int
  | Boolean _ -> Some Bool
  | Op (e1,oper,e2) ->
    (match (infertype gamma e1, infertype gamma e2) with
    |(Some Int, Some Int)->
      (match oper with 
      | Plus -> Some Int
      | GTEQ -> Some Bool)
    | _ -> None)
  | If (e1,e2,e3) -> 
    (match infertype gamma e1 with 
    |Some Bool -> (match (infertype gamma e2, infertype gamma e3) with
      | (Some a, Some b) -> if a=b then Some a else None
      | _ -> None)
    | _ -> None)
  | Assign (loc, e) -> (match lookup gamma loc with 
   |Some Intref -> (match infertype gamma e with
    | Some Int -> Some Unit
    | _ -> None)
   | None -> None)
  | Deref loc -> (match lookup gamma loc with
    | Some Intref -> Some Int
    | None -> None)
  | Skip -> Some Unit
  | Seq (e1,e2) -> (match (infertype gamma e1, infertype gamma e2) with
    | (Some Unit, Some t) -> Some t
    | _ -> None)
  | While (e1,e2) -> (match (infertype gamma e1, infertype gamma e2) with
    | (Some Bool, Some Unit) -> Some Unit
    | _ -> None)




let rec reduce (e,s) = 
  match e with
  |Integer _ | Boolean _ | Skip -> None
  | Op (e1, op ,e2) -> (
    match (e1,e2) with
    | (Integer x, Integer y) -> 
      (match op with
      |Plus ->Some (Integer (x+y), s)
      |GTEQ -> Some (Boolean (x>=y),s))
    | (e1, e2) -> if is_value e2 then 
      (match reduce (e1,s) with 
      | None ->None
      | Some (e1,s) -> Some (Op (e1,op,e2), s))
    else 
      (match reduce (e2,s) with
      |None -> None
      |Some (e2,s) -> Some( Op (e1, op, e2), s))
  )
  | Deref loc -> 
    (match lookup s loc with
    | Some x -> Some (Integer x, s) 
    | None -> None
    )
  | Assign (loc,exp)-> 
    (match exp with
    | Integer x -> 
      (match update s loc x with
      |Some sprime -> Some (Integer x, sprime)
      |None -> None
      )
    | e -> 
      (match reduce (e,s) with
      |Some (e,s) -> Some (Assign (loc, e), s)
      |None -> None)
    )  
  | Seq(e1,e2)->
    (match e1 with
    |Integer _ | Boolean _ -> Some (e2,s)
    |Skip -> Some (e2,s)
    |e -> 
      (match reduce (e,s) with 
      |Some (e,s)-> Some (Seq (e,e2),s)
      |None ->None ))
  | If (e1,e2,e3) ->
    (match e1 with 
    |Boolean b -> if b then Some (e2,s) else Some (e3,s)
    |e -> 
      (match reduce(e,s) with
      |Some (e,s) -> Some (If (e,e2,e3), s) 
      |None ->None)
    )
  | While (e1,e2) -> 
    let inner = Seq(e2, (While (e1,e2))) in
    Some (If (e1,inner, Skip),s)


(*Then we can recursively call this until we get a None
 - at which point we're in a stuck state!*)

let rec evaluate (e,s) =
  match reduce (e,s) with
  |None -> (e,s)
  |Some (e',s')-> evaluate (e',s')




(*Now we just implement some nice pretty printing*)


let pp_oper op = match op with Plus -> "+" | GTEQ -> ">=" 


let rec pp_store_helper store curr =
  match store with 
  | [] -> curr ^ "}"
  | [(loc, value)] -> curr ^  loc ^ "->" ^ (string_of_int value) ^ "}"
  | (loc, value)::tl -> let curr = curr ^ loc ^ "->" ^ (string_of_int value) ^ ", " in
   pp_store_helper tl curr

let pp_store store = pp_store_helper store "{"

let rec pp_exp e = 
  match e with            
  | Integer n -> string_of_int  n
  | Boolean b -> string_of_bool b
  | Op (e1,opr,e2) ->
      "(" ^ (pp_exp e1) ^ (pp_oper opr) 
      ^ (pp_exp e2) ^ ")"
  | If (e1,e2,e3) ->
      "if " ^ (pp_exp e1 ) ^ " then " ^ (pp_exp e2)
      ^ " else " ^ (pp_exp e3)
  | Deref l -> "!" ^ l
  | Assign (l,e) ->  l ^ ":=" ^ (pp_exp e)
  | Skip -> "skip"
  | Seq (e1,e2) ->  (pp_exp e1 ) ^ ";" ^ (pp_exp e2)
  | While (e1,e2) ->  
      "while " ^ (pp_exp e1 ) 
      ^ " do " ^ (pp_exp e2)

  
let prettyprintconfig (e,s) = 
  "< " ^ (pp_exp e) 
  ^ " , " ^ (pp_store s) ^ " >"

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

  

(***Exercise 1*)
(*Cant make an expression that corresp to multiplication by including another couple of locations in our store.*)
let mull1l2 = Seq( 
  Seq(  
    Seq( Assign("l3", Deref "l1"), Assign( "l4", Integer 0)) ,

    While( Op( Deref "l3", GTEQ, Integer 1  ) ,
     Seq( Assign( "l4" , Op(Deref "l4", Plus, Deref"l2")), Assign( "l3", Op(Deref "l3", Plus, Integer (-1)))) ))
 
 
 ,Assign( "l2", Deref "l4"))

let e = While ( Op( Deref "l1" , GTEQ, Integer 1),
Seq( mull1l2,
 Assign("l1" , Op(Deref "l1", Plus , Integer (-1)))) )


(* {l1=0 } *)
let s = [("l1",10); ("l2", 1); ("l3", 0) ; ("l4", 0)]



(*** Exercise 2 check*)
let e =
  Seq( Assign("l0", Integer 7), Assign( "l1", Op( Deref "l0", Plus , Integer 2)) )

let s = [("l0", 0) ; ("l1", 0)]





(***Ex 4 test*)

let e = Op( Deref("l0"), Plus, Deref("l1"))
let s= [("l0", 23); ("l1", 34)]


(***Ex 5 Test*)
let e = Seq ( Assign ( "l0" , Integer 100 ), Deref "l0" ) 
let s = [("l0", 1)]

let doit () = 
  prettyreduce (e, s)
    

let () = doit ()



