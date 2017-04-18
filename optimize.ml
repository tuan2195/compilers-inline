open Types
open Printf
open Instruction
open Expr
open Pretty

let rec rm_dup ls =
    let rec rm_from ls x =
        (match ls with
        | [] -> []
        | n::rs when n = x -> rm_from rs x
        | _ -> List.hd ls :: rm_from (List.tl ls) x ) in
    match ls with
    | [] -> []
    | x::rs ->
        let new_ls = rm_from rs x in
        x::rm_dup new_ls

let rec free_a ae env =
    match ae with
    | ALet(name, expr, body, _) ->
        free_c expr env @ free_a body (name::env)
    | ALetRec(expr_ls, body, _) ->
        free_a body (env @ (List.map fst expr_ls))
    | ASeq(expr, rest, _) ->
        free_c expr env @ free_a rest env
    | ACExpr(e) ->
        free_c e env
and free_c ce env =
    match ce with
    | CIf(con, thn, els, _) ->
        free_i con env @
        free_a thn env @
        free_a els env
    | CPrim1(_, e, _) ->
        free_i e env
    | CPrim2(_, e1, e2, _) ->
        free_i e1 env @
        free_i e2 env
    | CApp(func, args, _) ->
        free_i func env @
        List.flatten (List.map (fun x -> free_i x env) args)
    | CTuple(args, _) ->
        List.flatten (List.map (fun x -> free_i x env) args)
    | CGetItem(tup, idx, _) ->
        free_i tup env @ free_i idx env
    | CSetItem(tup, idx, expr, _) ->
        free_i tup env @ free_i idx env @ free_i expr env
    | CLambda(args, expr, _) ->
        free_a expr args
    | CInline(args, expr, _) ->
        free_a expr args
    | CAExpr br ->
        free_a br env
    | CImmExpr i ->
        free_i i env
and free_i ie env =
    match ie with
    | ImmNum _ | ImmBool _ -> []
    | ImmId(x, _) ->
        (try ignore (List.find (fun s -> s = x) env); [] with Not_found -> [x])

let free_vars ae = rm_dup (free_a ae [])

let rec strip ls =
    match ls with
    | [] -> []
    | ILineComment(_)::rest -> strip rest
    | IInstrComment(i, _)::rest -> i::strip rest
    | i::rest -> i::strip rest

let peephole ls =
    let rec opt ls =
        match ls with
        | [] -> []
        | IMov(RegOffset(o1, b1), Reg(r1))::IMov(Reg(r2), RegOffset(o2, b2))::rest ->
            if o1 = o2 && b1 = b2 && r1 = r2 then
                (List.hd ls)::opt rest
            else
                (List.hd ls)::opt (List.tl ls)
        | what::rest ->
            what::opt rest in
    opt (strip ls)

let purity_env (prog : tag aprogram) : (string, bool) Hashtbl.t =
  let hash : (string, bool) Hashtbl.t = Hashtbl.create 0 in
  let rec helpA ae =
      match ae with
      | ALet(name, ce, ae, _) ->
          Hashtbl.add hash name (helpC ce); helpA ae
      | ALetRec(ls, ae, _) ->
          helpRecLet ls (List.map (fun (n, _) -> (n, true)) ls);
          helpA ae
      | ASeq(ce, rest, _) -> ignore(helpC ce); helpA rest;
      | ACExpr ce -> helpC ce
  and helpC ce =
      match ce with
      | CIf(con, thn, els, _) ->
          let a = helpA thn in let b = helpA els in a && b
      | CPrim1(op, e, _) ->
          helpI e && (match op with
          | Add1 | Sub1 | Not -> true
          | Print | PrintStack | IsNum | IsBool | IsTuple -> false)
      | CPrim2(op, e1, e2, _) ->
          let a = helpI e1 in let b = helpI e2 in
          a && b && (match op with
          | Plus | Minus | Times | Less | Greater | LessEq | GreaterEq | And | Or -> true
          | Eq -> false)
      | CApp(func, args, _) -> helpI func && List.for_all helpI args
      | CTuple(ls, _) -> false
      | CGetItem(tup, idx, _) -> helpI tup && helpI idx
      | CSetItem(tup, idx, value, _) -> false
      | CLambda(args, body, _) | CInline(args, body, _) ->
          List.iter (fun x -> Hashtbl.add hash x true) args;
          ignore(helpA body);
          true;
      | CAExpr br -> helpA br
      | CImmExpr e -> helpI e
  and helpI (imm : tag immexpr) : bool =
      match imm with
      | ImmNum _ -> true
      | ImmBool _ -> true
      | ImmId(x, _) -> Hashtbl.find hash x
  and helpRecLet funcs original =
      List.iter (fun (n, b) -> Hashtbl.add hash n b) original;
      let new_ls = List.map (fun (n, b) -> (n, helpC b)) funcs in
      if new_ls = original then ()
      else (List.iter (fun (n, _) -> Hashtbl.remove hash n) original;
      helpRecLet funcs new_ls)
  in ignore(helpA prog); hash

let rec string_of_simple s =
  match s with
  | Id s -> s
  | Num n -> string_of_int n
  | Bool b -> string_of_bool b
  | Prim1(op, arg) -> sprintf "%s(%s)" (string_of_op1 op) (string_of_simple arg)
  | Prim2(op, left, right) -> sprintf "%s(%s, %s)" (string_of_op2 op) (string_of_simple left) (string_of_simple right)
  | App(f, args) -> sprintf "%s(%s)" (string_of_simple f) (ExtString.String.join ", " (List.map string_of_simple args))
;;
let rec simple_to_cexpr simple =
  let rec s_to_imm s =
    match s with
    | Id n -> ImmId(n, ())
    | Num n -> ImmNum(n, ())
    | Bool b -> ImmBool(b, ())
    | _ -> failwith "Impossible"
  in match simple with
  | Prim1(op, arg) -> CPrim1(op, s_to_imm arg, ())
  | Prim2(op, left, right) -> CPrim2(op, s_to_imm left, s_to_imm right, ())
  | App(f, args) -> CApp(s_to_imm f, List.map s_to_imm args, ())
  | _ -> CImmExpr (s_to_imm simple)
;;
let imm_to_simple i =
  match i with
  | ImmId(n, _) -> Id n
  | ImmNum(n, _) -> Num n
  | ImmBool(b, _) -> Bool b
;;
let cexpr_to_simple_opt cexp =
  match cexp with
  | CPrim1(op, arg, _) -> Some (Prim1(op, imm_to_simple arg))
  | CPrim2(op, left, right, _) -> Some (Prim2(op, imm_to_simple left, imm_to_simple right))
  | CApp(f, args, _) -> Some (App(imm_to_simple f, List.map imm_to_simple args))
  | CImmExpr i -> Some (imm_to_simple i)
  | _ -> None
;;

let rec untagA ae =
    match ae with
    | ALet(name, ce, ae, _) -> ALet(name, untagC ce, untagA ae, ())
    | ALetRec(ls, ae, _) -> ALetRec(List.map (fun (name, ce) -> (name, untagC ce)) ls, untagA ae, ())
    | ASeq(ce, rest, _) -> ASeq(untagC ce, untagA rest, ())
    | ACExpr ce -> ACExpr(untagC ce)
and untagC ce =
    match ce with
    | CPrim1(op, e, _) -> CPrim1(op, untagI e, ())
    | CPrim2(op, e1, e2, _) -> CPrim2(op, untagI e1, untagI e2, ())
    | CIf(cond, thn, els, _) -> CIf(untagI cond, untagA thn, untagA els, ())
    | CTuple(vals, _) -> CTuple(List.map untagI vals, ())
    | CGetItem(tup, idx, _) -> CGetItem(untagI tup, untagI idx, ())
    | CSetItem(tup, idx, rhs, _) -> CSetItem(untagI tup, untagI idx, untagI rhs, ())
    | CApp(func, args, _) -> CApp(untagI func, List.map untagI args, ())
    | CLambda(args, body, _) -> CLambda(args, untagA body, ())
    | CInline(args, body, _) -> CInline(args, untagA body, ())
    | CAExpr br -> CAExpr(untagA br)
    | CImmExpr i -> CImmExpr (untagI i)
and untagI ie =
    match ie with
    | ImmId(x, _) -> ImmId(x, ())
    | ImmNum(n, _) -> ImmNum(n, ())
    | ImmBool(b, _) -> ImmBool(b, ())

let get_num imm = match imm with
    | ImmNum(x, _) -> x
    | _ -> failwith "Type error: get_num"

let get_bool imm = match imm with
    | ImmBool(x, _) -> x
    | _ -> failwith "Type error: get_bool"

let get_id imm = match imm with
    | ImmId(x, _) -> x
    | _ -> failwith "Type error: get_id"

let is_const ie =
    match ie with
    | ImmId _ -> false
    | _ -> true

let is_num imm = match imm with
    | ImmNum _ -> true
    | ImmBool _ -> false
    | _ -> failwith "Type error: is_num"

let is_bool imm = not(is_num imm)

let const_fold prog =
    let rec try_add name ce ls = match ce with
        | CImmExpr imm -> (name, imm)::ls
        | CAExpr(ACExpr ce) -> try_add name ce ls
        | _ -> ls in
    let calc i1 i2 op =
        let n = op (get_num i1) (get_num i2) in
        if n > 1073741823 || n < -1073741824 then
            failwith "Integer overflow during constant folding"
        else n in
    (* We use assoc lists instead of Hashtbl to avoid scoping problems *)
    let rec helpA ae env =
        match ae with
        | ALet(name, ce, ae, _) ->
            let ans = helpC ce env in
            ALet(name, ans, helpA ae (try_add name ans env), ())
        | ALetRec(ls, ae, _) ->
            ALetRec(List.map (fun (name, ce) -> (name, helpC ce env)) ls, helpA ae env, ())
        | ASeq(ce, rest, _) ->
            ASeq(helpC ce env, helpA rest env, ())
        | ACExpr ce ->
            ACExpr(helpC ce env)
    and helpC ce env =
        match ce with
        | CPrim1(op, e, _) ->
            (match e with
            | ImmId(name, _) ->
                if List.mem_assoc name env then helpC (CPrim1(op, List.assoc name env, ())) env else ce
            | _ -> (match op with
                | Add1 when is_num e -> CImmExpr(ImmNum(((get_num e) + 1), ()))
                | Sub1 when is_num e -> CImmExpr(ImmNum(((get_num e) - 1), ()))
                | Not when is_bool e -> CImmExpr(ImmBool(not(get_bool e), ()))
                | IsNum -> CImmExpr(ImmBool(is_num e, ()))
                | IsBool -> CImmExpr(ImmBool(is_bool e, ()))
                | _ -> ce))
        | CPrim2(op, e1, e2, _) ->
            (match e1, e2 with
            | ImmId(id1, _), ImmId(id2, _) ->
                 let ne1 = if List.mem_assoc id1 env then List.assoc id1 env else e1 in
                 let ne2 = if List.mem_assoc id2 env then List.assoc id2 env else e2 in
                 CPrim2(op, ne1, ne2, ())
            | ImmId(id, _), _ ->
                 if List.mem_assoc id env then CPrim2(op, List.assoc id env, e2, ()) else ce
            | _, ImmId(id, _) ->
                 if List.mem_assoc id env then CPrim2(op, e1, List.assoc id env, ()) else ce
            | _ -> (match op with
                | Plus when is_num e1 && is_num e2 -> CImmExpr(ImmNum(calc e1 e2 ( + ), ()))
                | Minus when is_num e1 && is_num e2 -> CImmExpr(ImmNum(calc e1 e2 ( - ), ()))
                | Times when is_num e1 && is_num e2 -> CImmExpr(ImmNum(calc e1 e2 ( * ), ()))
                | Less when is_num e1 && is_num e2 -> CImmExpr(ImmBool((get_num e1) < (get_num e2), ()))
                | Greater when is_num e1 && is_num e2 -> CImmExpr(ImmBool((get_num e1) > (get_num e2), ()))
                | LessEq when is_num e1 && is_num e2 -> CImmExpr(ImmBool((get_num e1) <= (get_num e2), ()))
                | GreaterEq when is_num e1 && is_num e2 -> CImmExpr(ImmBool((get_num e1) >= (get_num e2), ()))
                | Eq when is_num e1 && is_num e2 -> CImmExpr(ImmBool((get_num e1) = (get_num e2), ()))
                | And when is_bool e1 && is_bool e2 -> CImmExpr(ImmBool((get_bool e1) && (get_bool e2), ()))
                | Or when is_bool e1 && is_bool e2 -> CImmExpr(ImmBool((get_bool e1) || (get_bool e2), ()))
                | _ -> ce))
        | CIf(con, thn, els, _) ->
            CIf(helpI con env, helpA thn env, helpA els env, ())
        | CApp(func, args, _) ->
            CApp(helpI func env, List.map (fun x -> helpI x env) args, ())
        | CTuple(ls, _) ->
            CTuple(List.map (fun x -> helpI x env) ls, ())
        | CGetItem(tup, idx, _) ->
            CGetItem(helpI tup env, helpI idx env, ())
        | CSetItem(tup, idx, rhs, _) ->
            CSetItem(helpI tup env, helpI idx env, helpI rhs env, ())
        | CLambda(args, body, _) ->
            CLambda(args, helpA body env, ())
        | CInline(args, body, _) ->
            CInline(args, helpA body env, ())
        | CAExpr br ->
            CAExpr(helpA br env)
        | CImmExpr i ->
            CImmExpr(helpI i env)
    and helpI ie env =
        match ie with
        | ImmId(name, _) when List.mem_assoc name env -> List.assoc name env
        | _ -> ie in
    helpA (untagA prog) []

let rename prog =
    let gen_name ce tag =
        match ce with
        | CPrim1(_, _, t) -> sprintf "Prim1_%d" t
        | CPrim2(_, _, _, t) -> sprintf "Prim2_%d" t
        | CIf(_, _, _, t) -> sprintf "If_%d" t
        | CAExpr _ -> sprintf "AE_%d" tag
        | CTuple(_, t) -> sprintf "Tup_%d" t
        | CGetItem(_, _, t) -> sprintf "Get_%d" t
        | CSetItem(_, _, _, t) -> sprintf "Set_%d" t
        | CApp(_, _, t) -> sprintf "App_%d" t
        | CLambda(_, _, t) -> sprintf "App_%d" t
        | CInline(_, _, t) -> sprintf "Inline_%d" t
        | CImmExpr _ -> sprintf "Imm_%d" tag in
    let rec helpA ae ls =
        match ae with
        | ALet(name, ce, ae, t) ->
            let new_name = gen_name ce t in
            let new_ls = (name,new_name)::ls in
            ALet(new_name, helpC ce new_ls, helpA ae new_ls, ())
        | ALetRec(decls, ae, t) ->
            let (temp_map, temp_decls) = List.split (List.mapi
                (fun i (name, ce) -> let new_name = sprintf "%s_LR%d" (gen_name ce i) t in ((name, new_name), (new_name, ce))) decls) in
            let new_map = temp_map @ ls in
            let new_decls = List.map (fun (name, ce) -> (name, helpC ce new_map)) temp_decls in
            ALetRec(new_decls, helpA ae new_map, ())
        | ASeq(ce, rest, t) -> ASeq(helpC ce ls, helpA rest ls, ())
        | ACExpr ce -> ACExpr(helpC ce ls)
    and helpC (ce : tag cexpr) ls =
        let helpI x = helpI x ls in
        match ce with
        | CPrim1(op, e, _) -> CPrim1(op, helpI e, ())
        | CPrim2(op, e1, e2, _) -> CPrim2(op, helpI e1, helpI e2, ())
        | CIf(cond, thn, els, _) -> CIf(helpI cond, helpA thn ls, helpA els ls, ())
        | CTuple(vals, _) -> CTuple(List.map helpI vals, ())
        | CGetItem(tup, idx, _) -> CGetItem(helpI tup, helpI idx, ())
        | CSetItem(tup, idx, rhs, _) -> CSetItem(helpI tup, helpI idx, helpI rhs, ())
        | CApp(func, args, _) -> CApp(helpI func, List.map helpI args, ())
        | CLambda(args, body, _) -> CLambda(args, helpA body ls, ())
        | CInline(args, body, _) -> CInline(args, helpA body ls, ())
        | CAExpr br -> CAExpr(helpA br ls)
        | CImmExpr i -> CImmExpr (helpI i)
    and helpI ie ls =
        match ie with
        | ImmId(x, _) when List.mem_assoc x ls -> ImmId(List.assoc x ls, ())
        | _ -> untagI ie
    in helpA prog []

let inline_expand prog =
    let try_add name ce ls =
        match ce with
        | CInline(args, body, _) -> (name,(args,body))::ls
        | _ -> ls in
    let rec expand body map =
        let rec expandA ae map =
            let helpC x = expandC x map in
            let helpA x = expandA x map in
            match ae with
            | ALet(name, ce, ae, _) -> ALet(name, helpC ce, helpA ae, ())
            | ALetRec(ls, ae, _) -> ALetRec(List.map (fun (name, ce) -> (name, helpC ce)) ls, helpA ae, ())
            | ASeq(ce, rest, _) -> ASeq(helpC ce, helpA rest, ())
            | ACExpr ce -> ACExpr(helpC ce)
        and expandC ce map =
            let helpA x = expandA x map in
            let helpI x = expandI x map in
            match ce with
            | CPrim1(op, e, _) -> CPrim1(op, helpI e, ())
            | CPrim2(op, e1, e2, _) -> CPrim2(op, helpI e1, helpI e2, ())
            | CIf(cond, thn, els, _) -> CIf(helpI cond, helpA thn, helpA els, ())
            | CTuple(vals, _) -> CTuple(List.map helpI vals, ())
            | CGetItem(tup, idx, _) -> CGetItem(helpI tup, helpI idx, ())
            | CSetItem(tup, idx, rhs, _) -> CSetItem(helpI tup, helpI idx, helpI rhs, ())
            | CApp(func, args, _) -> CApp(helpI func, List.map helpI args, ())
            | CLambda(args, body, _) -> CLambda(args, body, ())
            | CInline(args, body, _) -> CInline(args, body, ())
            | CAExpr(br) -> CAExpr(helpA br)
            | CImmExpr i -> CImmExpr (helpI i)
        and expandI ie map =
            match ie with
            | ImmId(x, _) when List.mem_assoc x map -> untagI (List.assoc x map)
            | _ -> untagI ie in
        const_fold (expandA body map)
    and helpA ae ls =
        match ae with
        | ALet(name, ce, ae, _) ->
            let new_ls = try_add name ce ls in
            ALet(name, helpC ce new_ls, helpA ae new_ls, ())
        | ALetRec(recls, ae, _) ->
            let new_ls = List.fold_left (fun ls (name, ce) -> try_add name ce ls) ls recls in
            ALetRec(recls, helpA ae new_ls, ())
        | ASeq(ce, rest, _) -> ASeq(helpC ce ls, helpA rest ls, ())
        | ACExpr ce -> ACExpr(helpC ce ls)
    and helpC ce ls =
        match ce with
        | CIf(cond, thn, els, _) -> CIf(untagI cond, helpA thn ls, helpA els ls, ())
        | CApp(func, args, _) ->
            (match func with
            | ImmId(name, _) when List.mem_assoc name ls ->
                let (func_args, expr) = List.assoc name ls in
                let map = (try List.combine func_args args with
                    | _ -> failwith "Wrong arity for inline function") in
                CAExpr(expand expr map)
            | _ -> untagC ce)
        | CLambda(args, body, _) -> CLambda(args, helpA body ls, ())
        | CInline(args, body, _) -> CInline(args, helpA body ls, ())
        | CAExpr br -> CAExpr(helpA br ls)
        | _ -> untagC ce in
    helpA (untagA prog) []

let branch_elim prog =
    let rec helpA ae =
        match ae with
        | ALet(name, ce, ae, _) -> ALet(name, helpC ce, helpA ae, ())
        | ALetRec(ls, ae, _) -> ALetRec(List.map (fun (name, ce) -> (name, helpC ce)) ls, helpA ae, ())
        | ASeq(ce, rest, _) -> ASeq(helpC ce, helpA rest, ())
        | ACExpr ce -> ACExpr(helpC ce)
    and helpC ce =
        match ce with
        | CIf(cond, thn, els, _) ->
            (match cond with
            | ImmBool(x, _) -> if x then CAExpr(helpA thn) else CAExpr(helpA els)
            | _ -> CIf(untagI cond, helpA thn, helpA els, ()))
        | CAExpr br -> CAExpr(helpA br)
        | CLambda(args, body, _) -> CLambda(args, helpA body, ())
        | CInline(args, body, _) -> CInline(args, helpA body, ())
        | _ -> untagC ce in
    helpA prog

let cleanup prog =
    let rec helpA ae =
        match ae with
        | ALet(name, ce, ae, _) -> ALet(name, helpC ce, helpA ae, ())
        | ALetRec([], ae, _) -> helpA ae
        | ALetRec(ls, ae, _) -> ALetRec(List.map (fun (name, ce) -> (name, helpC ce)) ls, helpA ae, ())
        | ASeq(ce, rest, _) -> ASeq(helpC ce, helpA rest, ())
        | ACExpr(CAExpr x) -> helpA x
        | ACExpr ce -> ACExpr(helpC ce)
    and helpC ce =
        match ce with
        | CIf(cond, thn, els, _) -> CIf(cond, helpA thn, helpA els, ())
        | CAExpr(ACExpr ce) -> helpC ce
        | CAExpr br -> CAExpr(helpA br)
        | CLambda(args, body, _) -> CLambda(args, helpA body, ())
        | CInline(args, body, _) -> CInline(args, helpA body, ())
        | _ -> untagC ce
    in helpA (untagA prog)

let cse prog =
    (*We use assoc lists instead of Hashtbl to avoid scoping problems *)
    let purity = purity_env prog in
    let rec helpA e eql =
        match e with
        | ALet(name, ce, ae, _) ->
            if not(Hashtbl.find purity name) then ALet(name, untagC ce, helpA ae eql, ()) else
            let new_ce = helpC ce eql in
            (match cexpr_to_simple_opt new_ce with
            | Some sex -> ALet(name, new_ce, helpA ae ((sex, name)::eql), ())
            | None -> ALet(name, new_ce, helpA ae eql, ()))
        | ALetRec(ls, ae, _) ->
            ALetRec(List.map (fun (name, body) -> name, helpC body eql) ls, helpA ae eql, ())
        | ASeq(ce, rs, _) -> ASeq(helpC ce eql, helpA rs eql, ())
        | ACExpr ce -> ACExpr(helpC ce eql)
    and helpC e eql =
        match e with
        | CPrim1 _ | CPrim2 _ | CApp _ | CImmExpr _ ->
            (match cexpr_to_simple_opt e with
            | Some sex when List.mem_assoc sex eql -> CImmExpr(ImmId(List.assoc sex eql, ()))
            | _ -> (match e with
                | CPrim1(op, i, _) -> CPrim1(op, helpI i eql, ())
                | CPrim2(op, e1, e2, _) -> CPrim2(op, helpI e1 eql, helpI e2 eql, ())
                | CApp(func, args, _) -> CApp(untagI func, List.map (fun x -> helpI x eql) args, ())
                | CImmExpr i -> CImmExpr(helpI i eql)
                | _ -> failwith "Impossible"))
        | CAExpr br -> CAExpr(helpA br eql)
        | CTuple(ls, _) -> CTuple(List.map (fun x -> helpI x eql) ls, ())
        | CGetItem(tup, idx, _) -> CGetItem(helpI tup eql, helpI idx eql, ())
        | CSetItem(tup, idx, rhs, _) -> CSetItem(helpI tup eql, helpI idx eql, helpI rhs eql, ())
        | CIf(cond, thn, els, _) -> CIf(untagI cond, helpA thn eql, helpA els eql, ())
        | CLambda(args, body, _) -> CLambda(args, helpA body eql, ())
        | CInline(args, body, _) -> CInline(args, helpA body eql, ())
    and helpI i eql =
        let sex = imm_to_simple i in
        match i with
        | ImmId _ when List.mem_assoc sex eql -> ImmId(List.assoc sex eql, ())
        | _ -> untagI i in
    helpA prog []

let dae (prog : tag aprogram) : unit aprogram =
    let purity = purity_env prog in
    let rec helpA e =
        match e with
        | ALet(name, ce, ae, _) ->
            let new_ae, used_ls = helpA ae in
            let new_ce, used_ce = helpC ce in
            if List.mem name used_ls then
                ALet(name, new_ce, new_ae, ()), used_ce @ used_ls
            else if not(Hashtbl.find purity name) then
                ASeq(new_ce, new_ae, ()), used_ce @ used_ls
            else new_ae, used_ls
        | ALetRec(ls, ae, _) ->
            (* TODO: Eliminate dead mutually-recursive functions *)
            let new_ae, used_ae = helpA ae in
            let used_ls = List.flatten (List.map (fun x -> snd (helpC (snd x))) ls) in
            let cleanup = List.flatten (List.map
                (fun x -> if List.mem (fst x) (used_ae @ used_ls) then [x] else [] ) ls) in
            let new_temp = List.map (fun (f, b) -> let (n, ls) = helpC b in ((f, n), ls)) cleanup in
            let new_ls = List.map fst new_temp in
            let used_new = List.flatten (List.map snd new_temp) in
            ALetRec(new_ls, new_ae, ()), used_ae @ used_new
        | ASeq(ce, rest, _) ->
            let new_ce, used_ce = helpC ce in
            let new_rest, used_rest = helpA rest in
            ASeq(new_ce, new_rest, ()), used_ce @ used_rest
        | ACExpr ce ->
            let new_ce, used_ce = helpC ce in
            ACExpr(new_ce), used_ce
     and helpC ce =
        match ce with
        | CPrim1(op, e, _) ->
            untagC ce, helpI e
        | CPrim2(op, e1, e2, _) ->
            untagC ce, helpI e1 @ helpI e2
        | CIf(cond, thn, els, _) ->
            let new_thn, used_thn = helpA thn in
            let new_els, used_els = helpA els in
            CIf(untagI cond, new_thn, new_els, ()), helpI cond @ used_thn @ used_els
        | CTuple(vals, _) ->
            (untagC ce, List.flatten (List.map helpI vals))
        | CGetItem(tup, idx, _) ->
            (untagC ce, helpI tup @ helpI idx)
        | CSetItem(tup, idx, rhs, _) ->
            untagC ce, helpI tup @ helpI idx @ helpI rhs
        | CApp(name, args, _) ->
            untagC ce, helpI name @ (List.flatten (List.map helpI args))
        | CLambda(ls, body, _) ->
            let new_body, used_body = helpA body in
            CLambda(ls, new_body, ()), used_body
        | CInline(ls, body, _) ->
            let new_body, used_body = helpA body in
            CInline(ls, new_body, ()), used_body
        | CAExpr br ->
            let new_br, used_br = helpA br in
            CAExpr(new_br), used_br
        | CImmExpr i ->
            untagC ce, helpI i
    and helpI i =
        match i with
        | ImmId(x, _) -> [x]
        | _ -> [] in
    fst (helpA prog)

let finalize prog =
    let rec not_inline bind =
        match snd bind with
        | CInline _ -> false
        | _ -> true in
    let rec helpA ae =
        match ae with
        | ALet(name, ce, ae, _) ->
            (match ce with
            | CInline _ -> helpA ae
            | _ -> ALet(name, helpC ce, helpA ae, ()))
        | ALetRec(ls, ae, _) ->
            ALetRec(List.map (fun x -> (fst x, helpC (snd x))) (List.filter not_inline ls), helpA ae, ())
        | ASeq(ce, rest, _) -> ASeq(helpC ce, helpA rest, ())
        | ACExpr(CAExpr x) -> helpA x
        | ACExpr ce -> ACExpr(helpC ce)
    and helpC ce =
        match ce with
        | CIf(cond, thn, els, _) -> CIf(untagI cond, helpA thn, helpA els, ())
        | CAExpr(ACExpr ce) -> helpC ce
        | CAExpr br -> CAExpr(helpA br)
        | CLambda(args, body, _) -> CLambda(args, helpA body, ())
        | _ -> untagC ce
    in cleanup (helpA prog)

let optimize prog =
    let pass prog debug =
        let renamed = atag (rename prog) in
        let inlined = atag (inline_expand renamed) in
        let const_prog = atag (const_fold inlined) in
        let dae_prog = atag (dae const_prog) in
        let dbe_prog = atag (branch_elim dae_prog) in
        let cse_prog = atag (cse dbe_prog) in
        let cleaned = atag (cleanup cse_prog) in
        if debug then (
            (*printf "Original:\n%s\n" (string_of_aprogram prog);*)
            (*printf "Renamed:\n%s\n" (string_of_aprogram renamed);*)
            (*printf "Inlined:\n%s\n" (string_of_aprogram inlined);*)
            (*printf "Const/tagged:\n%s\n" (string_of_aprogram const_prog);*)
            (*printf "Dead assigment elim:\n%s\n" (string_of_aprogram dae_prog);*)
            (*printf "Dead branch elim:\n%s\n" (string_of_aprogram dbe_prog);*)
            printf "Cleanup:\n%s\n" (string_of_aprogram cleaned);)
        else ();
        cleaned in
    let rec optimal prog =
        let new_prog = pass prog true in
        if prog = new_prog then new_prog
        else optimal new_prog in
    atag (finalize (optimal prog))
