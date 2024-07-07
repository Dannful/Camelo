type bop = Sum | Sub | Mul | Div 
         | Eq | Gt | Lt | Neq
         | And | Or

          
type tipo = 
    Int 
  | Bool
  | Arrow of tipo * tipo
  | List of tipo
  | Maybe of tipo
  
(* 
e:: = n | b | e1 bop e2 | if e1 then e2 else e3 | x
| fn x:T => e | let x:T = e1 in e2 | e1 e2  
*)
type expr = 
    Nv of int
  | Bv of bool 
  | Bop of bop * expr * expr 
  | If  of expr * expr * expr 
  | Id  of string 
  | Fun of string * tipo * expr
  | Let of string * tipo *  expr * expr
  | App of expr * expr
  | Nothing of tipo
  | Just of expr
  | Nil of tipo
  | MatchMaybe of expr * expr * string * expr
  | MatchList of expr * expr * string * string * expr
  | Cons of expr * expr
  | Pipe of expr * expr

  
(*=========== TYPEINFER ===================*)           
type tyEnv =  (string * tipo) list
    
let rec lookup (g:tyEnv) (x:string) : tipo option = 
  match g with 
    [] -> None
  | (y,t):: tail -> if x=y then Some t else lookup tail x
           
exception TypeError
let rec typeinfer (g:tyEnv) (e:expr) : tipo = 
  match e with 
    Nv _ -> Int
  | Bv _ -> Bool 
    
  | Bop(o,e1,e2) -> 
      let t1 = typeinfer g e1  in
      let t2 = typeinfer g e2  in
      (match o with
         Sum | Sub | Mul | Div ->
           if (t1=Int) && (t2=Int) then Int else raise TypeError
       | Eq | Gt | Lt | Neq ->
           if (t1=Int) && (t2=Int) then Bool else raise TypeError
       | And | Or -> 
           if (t1=Bool) && (t2=Bool) then Bool else raise TypeError
      ) 
       
  | If(e1,e2,e3) ->  
      let t1 = typeinfer g e1  in
      if (t1=Bool) then
        let t2 = typeinfer g e2  in
        let t3 = typeinfer g e3  in
        if (t2=t3) then t2 else raise TypeError
      else raise TypeError
                      
  | Id x ->
      (match lookup g x with
         None -> raise TypeError
       | Some t -> t)
      
  | Fun(x,t,e1) -> 
      let g' = (x,t)::g in 
      let t1 = typeinfer g' e1 in 
      Arrow(t,t1)
                     
  | Let(x,t,e1,e2) -> 
      let t1 = typeinfer g e1 in 
      let g' = (x,t)::g in
      let t2 = typeinfer g' e2 in
      if t1=t then t2 else raise TypeError
      
                        
  | App(e1,e2) -> 
      let t1 = typeinfer g e1  in
      (match t1 with
         Arrow(t,t') -> 
           let t2 = typeinfer g e2  in
           if t=t2 then t' else raise TypeError
       | _ -> raise TypeError)
  
  | Nothing t -> Maybe t
    
  | Just e -> Maybe (typeinfer g e)
                 
  | Nil t -> List t
    
  | MatchMaybe(e1, e2, x, e3) ->
      let t1 = typeinfer g e1 in
      (match t1 with
         Maybe t ->
           let t2 = typeinfer g e2 in
           let g' = (x, t)::g in
           let t3 = typeinfer g' e3 in
           if t2=t3 then t2 else raise TypeError
       | _ -> raise TypeError)
      
  | MatchList(e1, e2, x, xs, e3) ->
      let t1 = typeinfer g e1 in
      (match t1 with
         List t ->
           let t2 = typeinfer g e2 in
           let g' = (xs, List t)::((x, t)::g) in
           let t3 = typeinfer g' e3 in
           if t2=t3 then t2 else raise TypeError
       | _ -> raise TypeError)
      
  | Cons(e1, e2) ->
      let t1 = typeinfer g e1 in
      let t2 = typeinfer g e2 in
      (match t2 with
         List t ->
           if t=t1 then List t else raise TypeError
       | _ -> raise TypeError)
      
  | Pipe(e1, e2) ->
      let t1 = typeinfer g e1 in
      let t2 = typeinfer g e2 in
      (match t2 with
         Arrow(input, output) ->
           if t1=input then output else raise TypeError
       | _ -> raise TypeError)
      
     
      
 

(* ======= AVALIADOR =========================*)

let rec value (e:expr) : bool =
  match e with
    Nv _ | Bv _ | Fun _ | Nothing _ | Just _ | Nil _ | Cons(_, _) -> true 
  | _ -> false

exception NoRuleApplies
  
let rec subs (v:expr) (x:string) (e:expr) = 
  match e with 
    Nv _ -> e
  | Bv _ -> e
  | Bop(o,e1,e2) -> Bop(o,  subs v x e1,   subs v x e2)
  | If(e1,e2,e3) -> If(subs v x e1, subs v x e2, subs v x e3)
                       
  | Id y           -> 
      if x=y then v else e 
  | Fun(y,t,e1)    -> 
      if x=y then e else Fun(y,t,subs v x e1)
  | Let(y,t,e1,e2) -> 
      if x=y then Let(y,t,subs v x e1,e2) 
      else Let(y,t,subs v x e1,subs v x e2)
      
  | App(e1,e2)  -> App(subs v x e1, subs v x e2)
                     
  | Nothing _ -> e
    
  | Nil _ -> e
    
  | Just e1 -> Just (subs v x e1)
                 
  | MatchList(e1, e2, y, ys, e3) ->
      if x=y then MatchList(subs v x e1, subs v x e2, y, ys, e3)
      else MatchList(subs v x e1, subs v x e2, y, ys, subs v x e3) 
          
  | MatchMaybe(e1, e2, y, e3) ->
      if x=y then MatchMaybe(subs v x e1, subs v x e2, y, e3)
      else MatchMaybe(subs v x e1, subs v x e2, y, subs v x e3) 
          
  | Pipe(e1, e2) -> Pipe(subs v x e1, subs v x e2)
                      
  | Cons(e1, e2) -> Cons(subs v x e1, subs v x e2)
      
 
exception DivZero 
exception FixTypeInfer
  
let rec compute (o:bop) (v1:expr) (v2:expr) = 
  match (v1,v2) with
    (Nv n1, Nv n2) -> 
      (match o with 
         Sum -> Nv (n1+n2)
       | Sub -> Nv (n1-n2)
       | Mul -> Nv (n1*n2)
       | Div -> if n2 != 0 then Nv (n1/n2) else raise DivZero
       | Eq -> Bv(n1==n2)
       | Gt -> Bv(n1>n2)
       | Lt -> Bv(n1<n2)
       | Neq -> Bv(n1!=n2)
       | _   -> raise FixTypeInfer)
  | (Bv b1, Bv b2) ->
      (match o with 
         And -> Bv(b1 && b2)
       | Or  -> Bv(b1 || b2)
       | _   -> raise FixTypeInfer)
  | _ -> raise FixTypeInfer 
           
let rec step (e:expr) : expr = 
  match e with
    Nv _ -> raise NoRuleApplies
  | Bv _ -> raise NoRuleApplies
              
  | Bop(o,v1,v2) when (value v1) && (value v2) -> 
      compute o v1 v2
  | Bop(o,v1,e2) when value v1 ->
      let e2' = step e2 in Bop(o,v1,e2')
  | Bop(o,e1,e2)  ->
      let e1' = step e1 in Bop(o,e1',e2)
                     
  | If(Bv true, e2, e3) -> e2
  | If(Bv false, e2, e3) -> e3 
  | If(e1, e2, e3) ->
      let e1' = step e1 in If(e1', e2, e3)


  | Id _ -> raise NoRuleApplies
  | Fun(x,t,e1) -> raise NoRuleApplies
                     
  | Let(x,t,v1,e2) when value v1 -> subs v1 x e2   (*  {v1/x} e2 *)
  | Let(x,t,e1,e2) -> 
      let e1' = step e1 in Let(x,t,e1',e2) 
      
  | App(Fun(x,t,e1), v2) when value v2 -> 
      subs v2 x e1
  | App(v1,e2) when value v1 ->
      let e2' = step e2 in App(v1,e2')
  | App(e1,e2)  ->
      let e1' = step e1 in App(e1',e2)
  
  | Nothing t -> raise NoRuleApplies
                   
  | Nil t -> raise NoRuleApplies
               
  | Cons(_, _) -> raise NoRuleApplies
               
  | Just v when value v -> raise NoRuleApplies
                             
  | Just e1 -> Just (step e1)
                 
  | MatchMaybe(v1, e2, x, e3) when value v1 ->
      (match v1 with
         Nothing _ -> e2
       | Just e4 -> subs e4 x e3
       | _ -> raise FixTypeInfer)
      
  | MatchMaybe(e1, e2, x, e3) -> MatchMaybe(step e1, e2, x, e3)
                                   
  | MatchList(v1, e2, x, xs, e3) when value v1 ->
      (match v1 with
         Nil _ -> e2
       | Cons(head, tail) -> subs tail xs (subs head x e3)
       | _ -> raise FixTypeInfer)
      
  | MatchList(e1, e2, x, xs, e3) -> MatchList(step e1, e2, x, xs, e3) 
                                      
  | Pipe(v1, v2) when (value v1) && (value v2) -> App(v2, v1)
                                                    
  | Pipe(e1, v2) when value v2 -> Pipe(step e1, v2)
                                    
  | Pipe(e1, e2) -> Pipe(e1, step e2) 
  
let rec eval (e:expr): expr = 
  try 
    let e' = step e in
    eval e' 
  with
    NoRuleApplies -> e 
                       

(*===== INTEPRETADOR ========================*)

let rec strofexpr (e:expr) = failwith "não implementado"
let rec stroftipo (t:tipo) = failwith "não implementado"
    
    
  
let rec interpretador (e:expr) : unit = 
  try
    let t = typeinfer []  e in
    let v = eval e in
    print_endline ((strofexpr e) ^ ":" ^ (stroftipo t) ^ 
                   " = " ^ (strofexpr v))
  with 
    TypeError -> print_endline "Erro de tipo"
  

(*======== TESTES ===================*) 

(* 
let a:int = 10 in
let b:int = 0 in 
a / b
*)

let tst1 = Let("a", Int, Nv 10, 
               Let ("b", Int, Nv 0, 
                    Bop (Div, Id "a", Id "b")))
(*

let dobro : int -> int = fn x:int => x * 2 in
dobro 10
*)   
  
let tst2 = Let("dobro", Arrow(Int,Int),Fun("x",Int,Bop (Mul, Id "x", Nv 2)) , 
               App(Id "dobro", Nv 10))
    
    (*

let dobro : int -> int = fn x:int => x * 2 in
        dobro 
   *)   
  
let tst3 = Let("dobro", Arrow(Int,Int),Fun("x",Int,Bop (Mul, Id "x", Nv 2)) , 
               Id "dobro")
 
    (* teste para subs  *)

    (*  fn x:int => x + z  *)
let expr1 = Fun("x",Int,  Bop(Sum, Id "x", Id "z"))
    
    (* let x = x + 10 in 2 * x *)
let expr2 = Let("x", Int, Bop(Sum, Id "x", Nv 10), 
                Bop(Mul, Nv 2, Id "x"))
    
