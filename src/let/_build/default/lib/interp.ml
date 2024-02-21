open Parser_plaf.Ast
open Parser_plaf.Parser
open Ds
    
(** [eval_expr e] evaluates expression [e] *)
let rec eval_expr : expr -> exp_val ea_result =
  fun e ->
  match e with
  | Int(n) ->
    return (NumVal n)
  | Var(id) ->
    apply_env id
  | Add(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1+n2))
  | Sub(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1-n2))
  | Mul(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1*n2))
  | Div(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    if n2==0
    then error "Division by zero"
    else return (NumVal (n1/n2))
  | Let(id,def,body) ->
    eval_expr def >>= 
    extend_env id >>+
    eval_expr body 
  | ITE(e1,e2,e3) ->
    eval_expr e1 >>=
    bool_of_boolVal >>= fun b ->
    if b 
    then eval_expr e2
    else eval_expr e3
  | IsZero(e) ->
    eval_expr e >>=
    int_of_numVal >>= fun n ->
    return (BoolVal (n = 0))
  | Pair(e1,e2) ->
    eval_expr e1 >>= fun ev1 ->
    eval_expr e2 >>= fun ev2 ->
    return (PairVal(ev1,ev2))
  | Fst(e) ->
    eval_expr e >>=
    pair_of_pairVal >>= fun (l,_) ->
    return l
  | Snd(e) ->
    eval_expr e >>=
    pair_of_pairVal >>= fun (_,r) ->
    return r
  | Debug(_e) ->
    string_of_env >>= fun str ->
    print_endline str; 
    error "Debug called"
  | IsEmpty(e) ->
    eval_expr e >>= (function
    | TreeVal Empty -> return (BoolVal true)
    | TreeVal _ -> return (BoolVal false)
    | _ -> error "Expected a tree")
  | EmptyTree(_t) ->
    return (TreeVal Empty)
  | Node(e1, e2, e3) ->
    eval_expr e1 >>= fun v1 ->
    eval_expr e2 >>= fun v2 ->
    eval_expr e3 >>= fun v3 ->
    (match v2, v3 with
      | TreeVal t1, TreeVal t2 -> return (TreeVal (Node(v1, t1, t2)))
      | _ -> error "Expected trees")
  | CaseT(e1, e2, id1, id2, id3, e3) ->
    let a = eval_expr e1 in
    let left = eval_expr e2 in
    let right = eval_expr e3 in
    a >>= (function
      | TreeVal Empty -> left
      | TreeVal (Node(v1, t1, t2)) -> 
        extend_env id1 v1 >>+
        extend_env id2 (TreeVal t1) >>+
        extend_env id3 (TreeVal t2) >>+
        right
      | _ -> error "Expected a tree")
  | Record(fs) ->
    record_helper fs >>= fun _ ->
    eval_exprs (List.map (fun (_, e) -> e) fs |> List.map snd) >>= fun vs ->
    return (RecordVal(List.combine (List.map fst fs) vs))
  | Proj(e,id) -> 
    eval_expr e >>= proj_helper >>= fun fs ->
    (try return (List.assoc id fs) with 
    | Not_found -> error "Proj: field does not exist")
  | _ -> failwith "Not implemented yet!"

and 
  eval_exprs : expr list -> (exp_val list) ea_result =
  fun es ->
  match es with
  | [] -> return []
  | h::t -> eval_expr h >>= fun i ->
    eval_exprs t >>= fun l ->
    return (i::l)


(** [eval_prog e] evaluates program [e] *)
let eval_prog (AProg(_,e)) =
  eval_expr e

(** [interp s] parses [s] and then evaluates it *)
let interp (e:string) : exp_val result =
  let c = e |> parse |> eval_prog
  in run c
