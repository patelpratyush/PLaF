(*
  Homework 5
  Student name 1: Pratyush Patel
  Student name 2: David Amin
*)


open ReM
open Dst
open Parser_plaf.Ast
open Parser_plaf.Parser
       
let rec chk_expr : expr -> texpr tea_result = function 
  | Int _n -> return IntType
  | Var id -> apply_tenv id
  | IsZero(e) ->
    chk_expr e >>= fun t ->
    if t=IntType
    then return BoolType
    else error "isZero: expected argument of type int"
  | Add(e1,e2) | Sub(e1,e2) | Mul(e1,e2)| Div(e1,e2) ->
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
    if (t1=IntType && t2=IntType)
    then return IntType
    else error "arith: arguments must be ints"
  | ITE(e1,e2,e3) ->
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
    chk_expr e3 >>= fun t3 ->
    if (t1=BoolType && t2=t3)
    then return t2
    else error "ITE: condition not boolean or types of then and else do not match"
  | Let(id,e,body) ->
    chk_expr e >>= fun t ->
    extend_tenv id t >>+
    chk_expr body
  | Proc(var,Some t1,e) ->
    extend_tenv var t1 >>+
    chk_expr e >>= fun t2 ->
    return @@ FuncType(t1,t2)
  | Proc(_var,None,_e) ->
    error "proc: type declaration missing"
  | App(e1,e2) ->
    chk_expr e1 >>=
    pair_of_funcType "app: " >>= fun (t1,t2) ->
    chk_expr e2 >>= fun t3 ->
    if t1=t3
    then return t2
    else error "app: type of argument incorrect"
  | Letrec([(_id,_param,None,_,_body)],_target) | Letrec([(_id,_param,_,None,_body)],_target) ->
    error "letrec: type declaration missing"
  | Letrec([(id,param,Some tParam,Some tRes,body)],target) ->
    extend_tenv id (FuncType(tParam,tRes)) >>+
    (extend_tenv param tParam >>+
     chk_expr body >>= fun t ->
     if t=tRes 
     then chk_expr target
     else error
         "LetRec: Type of recursive function does not match
declaration")

  (* REFS TYPE CHECKING *)
  | NewRef(e) ->
    chk_expr e >>= fun te ->
    return @@ RefType(te)
  | DeRef(e) -> 
    chk_expr e >>= fun tes ->
    (match tes with
    | RefType(tr) -> return tr
    | _ -> error "DeRef: argumient must be a reference")
  | SetRef(e1,e2) -> 
    chk_expr e1 >>= fun tes1 ->
    chk_expr e2 >>= fun tes2 ->
    (match tes1 with
    | RefType(tr) -> 
      if tr=tes2 
      then return UnitType 
      else error "SetRef: types do not match"
    | _ -> error "setref: Expected a reference type")
  | BeginEnd([]) -> 
    return UnitType
  | BeginEnd(es) -> 
    chk_exprs es >>= fun tes ->
    return @@ List.hd (List.rev tes)


  (* LIST TYPE CHECKING *)
  | EmptyList(None) ->
    return @@ ListType(UnitType)
  | EmptyList(Some t)->
    return @@ ListType(t)
  | Cons(e1, e2) -> 
    chk_expr e1 >>= fun te1 ->
    chk_expr e2 >>= fun te2 ->
    (match te2 with
    | ListType(t) -> 
      if t=te1 
      then return te2
      else error "cons: type of head and tail do not match"
    | _ -> error "Cons: second argument must be a list")
  | IsEmpty(e) -> 
    chk_expr e >>= fun te ->
    (match te with
    | ListType(_) -> return BoolType
    | TreeType(_) -> return BoolType
    | _ -> error "IsEmpty: argument must be a list")
  | Hd(e) ->
    chk_expr e >>= fun te ->
    (match te with
    | ListType(t) -> return t
    | _ -> error "Hd: argument must be a list")
  | Tl(e) -> 
    chk_expr e >>= fun te ->
    (match te with
    | ListType(_) -> return te
    | _ -> error "Tl: argument must be a list")

  (* TREES TYPE CHECKING *)
  | EmptyTree(None) -> 
    return @@ TreeType(UnitType)
  | EmptyTree(Some t) -> 
    return @@ TreeType(t)
  | Node(de, le, re) -> 
    chk_expr de >>= fun tde ->
    chk_expr le >>= fun tle ->
    chk_expr re >>= fun tre ->
    (match tle, tre with
    | TreeType(t1), TreeType(t2) -> 
      if t1=t2 && t1=tde
      then return @@ TreeType(t1)
      else error "Node: types of left, right and data do not match"
    | _ -> error "Node: left and right must be trees")
  | CaseT(target,emptycase,id1,id2,id3,nodecase) ->
    chk_expr target >>= fun t ->
    extend_tenv id1 t >>+
    extend_tenv id2 (TreeType t) >>+
    extend_tenv id3 (TreeType t) >>+
    chk_expr nodecase >>= fun node ->
    chk_expr emptycase >>= fun empty ->
    if empty=node
    then return node
    else error "CaseT: cases are not of same type"
  | Debug(_e) ->
    string_of_tenv >>= fun str ->
    print_endline str;
    error "Debug: reached breakpoint"
  | _ -> failwith "chk_expr: implement"    
and
  chk_exprs es =
  match es with
  | [] -> return []
  | h::t ->
    chk_expr h >>= fun th ->
    chk_exprs t >>= fun l ->
    return (th::l) 
and
  chk_prog (AProg(_,e)) =
  chk_expr e

(* Type-check an expression *)
let chk (e:string) : texpr result =
  let c = e |> parse |> chk_prog
  in run_teac c

let chkpp (e:string) : string result =
  let c = e |> parse |> chk_prog
  in run_teac (c >>= fun t -> return @@ string_of_texpr t)