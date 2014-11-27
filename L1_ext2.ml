(*
  Nomes: Alexandre Leuck, Bruno Pinto Silva
  Cartões: 220493, 217446
*)

(* Sintaxe de termos e tipos *)

type op 
 = Soma                              (* + *)
 | MaiorIgual                      (* >= *)
|Sub;;

type tipo
   = TBool                           (* bool *)
   | TInt                            (* int  *)
   | TFun of tipo * tipo               (* T1 -> T2 *)
   | TList of tipo
   | T;;                         (* Raise ou empty list *)


type termo
   (* n, usando os literais do OCAML *)
 = Num  of int
   (* b, usando os literais do OCAML *)
 | Bool of bool
   (* e1 op e2 *)
 | Op   of op * termo * termo
   (* if e1 then e2 else e3 *)
 | If   of termo * termo * termo
   (* x *)
 | Var  of string
   (* e1 e2 *)
 | App  of termo * termo
   (* fun x:T => e *)
 | Fun  of string * tipo * termo
   (* let x:T=e1 in e2 *)
 | Let  of string * tipo * termo * termo
   (*let rec f:T->T’ = fun x:T => e1 in e2 *)
 | LetR of string * tipo * termo * termo
   (* exceç*)
 | Empty
 | Cons of termo * termo
 | Raise ;; 

let ambienteVazio = ( [] : (string * tipo) list ) ;;
exception NoRuleApplies ;;
exception TypeError ;;
exception UnboundVar ;;

let rec tipoAmbiente v a = match a with
    [] -> raise UnboundVar
  | first::rest -> if fst first = v 
      then snd first
      else tipoAmbiente v rest ;;

let rec tipoDe e a = match e with 
    Num _ -> TInt
  | Bool _ -> TBool
  | Var x -> tipoAmbiente x a
  | Op(Soma, e1, e2) -> if (tipoDe e1 a = TInt && tipoDe e2 a = TInt)
      then TInt 
      else raise TypeError
  | Op(Sub, e1, e2) ->  if (tipoDe e1 a = TInt && tipoDe e2 a = TInt)
      then TInt 
      else raise TypeError
  | Op(MaiorIgual, e1, e2) ->  if (tipoDe e1 a = TInt && tipoDe e2 a = TInt)
      then TBool 
      else raise TypeError
  | If( e0, e1, e2)->
      let e = tipoDe e2 a 
        in if tipoDe e0 a = TBool
          then
            if (tipoDe e1 a = e) 
              then e 
              else raise TypeError
          else raise TypeError
  | Fun (var, tipo, e)-> 
      let a2 = ((var, tipo) :: a) in TFun(tipo, tipoDe e a2)
  | Let(x, t, e1, e2) ->
      if(tipoDe e1 a = t)
        then let a2 = ((x, t) :: a)
          in tipoDe e2 a2
        else raise TypeError
  | LetR(f, t, e1, e2) -> let a1 = ((f,t) :: a) in
      if tipoDe e1 a1 = t
        then tipoDe e2 a1
        else raise TypeError
  | App(e1, e2) ->
      let te1 = tipoDe e1 a in let te2 = tipoDe e2 a in
        (match te1 with
            TFun(tArg,tRet) -> if (te2 = tArg)
              then tRet
              else raise TypeError
			| _ -> raise TypeError)
  | Cons(head,tails) -> 
      let t1 = tipoDe head a in let lt1 = tipoDe tails a in
        if lt1 == TList t1 or lt1 == TList T
          then TList t1
          else raise TypeError
  | _ -> raise NoRuleApplies;;


(* {v/x} t *)
(* substitui : termo -> string -> termo -> termo *)
let rec substitui v x t = match t with  
    Op(op,t1,t2) -> Op(op, substitui v x t1, substitui v x t2)
  | If(t1,t2,t3) -> If(substitui v x t1, substitui v x t2, substitui v x t3)
  | App(t1,t2) -> App(substitui v x t1, substitui v x t2)
  | Fun(y,tipo,termo) -> ( if compare x y == 0 
      then Fun(y, tipo, termo)
      else Fun(y, tipo, substitui v x termo))
  | Let(y, tipo, termo1, termo2) -> ( if compare x y == 0
      then Let(y, tipo, substitui v x termo1, termo2)
      else Let(y, tipo, substitui v x termo1, substitui v x termo2))
  | LetR(y, tipo, termo1, termo2) -> if compare x y == 0
      then LetR(y, tipo, termo1, termo2)
      else LetR(y, tipo, substitui v x termo1, substitui v x termo2)
  | Var(y) -> (if compare y x == 0
      then v
      else Var(y))
  |_-> t;;


let rec passo t = match t with    
  (*Operações basicas*)
  (*op+*)
   Op(Sub, Num e1, Num e2)-> Num (e1-e2)         
  |Op(Soma, Num e1, Num e2)-> Num (e1+e2)         
  (*op>=*)
  | Op(MaiorIgual, Num e1, Num e2) -> if e1 >= e2 then Bool true else Bool false   
  (*OP2*)
  | Op(op, Num e1, e2)->
    let e3 = passo e2
        in Op(op, Num e1, e3)
  (*OP1*)
  | Op(op, e1, e2)->
    let e3 = passo e1
        in Op(op, e3, e2)
  (*IF*)
  | If(Bool true, e2, e3)->e2
  | If(Bool false, e2, e3)->e3
  | If(t1, e2, e3)->
    let t1' = passo t1
        in If(t1', e2, e3)
  (*LET*)
  | Let(y,tipo1,t1,t2) -> (match t1 with
        Num _ -> (substitui t1 y t2)
      | Bool _ -> (substitui t1 y t2)
      | Fun(_,_,_) -> (substitui t1 y t2)
      | _ -> Let(y, tipo1, passo t1, t2))
  (* LET RET *)
  | LetR(f,t,e1,e2) -> (match e1 with
        Fun(x,tArg,efun) -> substitui (Fun(x, tArg, LetR(f,t,e1,efun))) f e2
      | _ -> raise NoRuleApplies)
  (*APP*)
  | App(Fun(y,tipo,t1), t2) -> (match t2 with
      Num _ -> substitui t2 y t1
    | Bool _ -> substitui t2 y t1
    | Fun(_,_,_) -> substitui t2 y t1
    | _ -> App(Fun(y,tipo,t1), passo t2))
  | App(t1,t2) -> App(passo t1, t2)
  | _ -> raise NoRuleApplies;;


(*
Testes:

int foo(int x)
{
if(0 >= x)
	return 0;
else
	return x + foo(x-1);
}

ou

int foo(int x)
{
	return (x*(x+1))/2;
}
main() { foo(5); }

tipoDe (
	LetR ( "y" ,  
	TFun(TInt, TInt),   
	Fun("x",  TInt, If(Op( MaiorIgual ,Num 0, Var "x" ), Num 0 , Op(Soma, Var "x", App(Var "y", Op(Sub, Var "x", Num 1) ))) ),          
	App(Var  "y", Num 5))
		) []

passo(passo(passo(passo(passo(passo(passo(passo(passo(passo(passo(passo(passo(passo(passo(passo(passo(passo(passo(passo(passo(passo(passo(passo(passo(passo(passo(passo(passo(passo(passo(passo(passo(passo(passo(
LetR ( "y" ,  
	TFun(TInt, TInt),   
	Fun("x", TInt , If(Op( MaiorIgual ,Num 0, Var "x" ), Num 0 , Op(Soma, Var "x", App(Var "y", Op(Sub, Var "x", Num 1) ))) ),          
	App(Var  "y", Num 5))
)))))))))))))))))))))))))))))))))))

*)

let rec run t = match t with
| Num _ -> t
| Bool _ -> t
| Fun(_,_,_) -> t
| _ -> run (passo t) ;;