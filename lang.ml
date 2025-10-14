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


let rec update_helper left right loc newvalue = 
match right with
| [] -> None
| (l,_) ::tl -> 
  if (l= loc) then Some (List.concat [ left; [(loc, newvalue)]; tl])
  else update_helper (List.concat [left; [(l,newvalue)]]) tl loc newvalue

let update store loc newvalue = update_helper [] store loc newvalue



(*Now we implement reduction of configurations  - ie. steps in our transition system
Because there is no ambiguity - ie. is a deterministic system, we can just use a funciton to do this!
Can just pattern match the left hand side and apply our funcitons.*)


(*First, if we've reached a value - then we're at a terminus, ie. we're at a stuck state*)
let is_value v = 
  match v with
  |Integer _ |Boolean _ | Skip -> true
  | _ -> false


let rec reduce (e,s) = 
  match e with
  |Integer _ | Boolean _ | Skip -> None
  | Op (e1, op ,e2) -> (
    match (e1,e2) with
    | (Integer x, Integer y) -> 
      (match op with
      |Plus ->Some (Integer (x+y), s)
      |GTEQ -> Some (Boolean (x<=y),s))
    | (e1, e2) -> if is_value e1 then 
      (match reduce (e2,s) with 
      | None ->None
      | Some (e2,s) -> Some (Op (e1,op,e2), s))
    else 
      (match reduce (e1,s) with
      |None -> None
      |Some (e1,s) -> Some( Op (e1, op, e2), s))
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
      |Some sprime -> Some (Skip, sprime)
      |None -> None
      )
    | e -> 
      (match reduce (e,s) with
      |Some (e,s) -> Some (Assign (loc, e), s)
      |None -> None)
    )  
  | Seq(e1,e2)->
    (match e1 with
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

  

let e = Seq( Assign ("l1",Integer 3), Deref "l1")

(* {l1=0 } *)
let s = [("l1",0)]

let doit () = 
  prettyreduce (e, s)
    

let () = doit ()
