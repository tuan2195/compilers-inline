
    and helpA ae ls d =
        match ae with
        | ALet(name, ce, ae, _) ->
            let new_ls = try_add name ce ls in
            ALet(name, helpC ce new_ls d, helpA ae new_ls d, ())
        | ALetRec(recls, ae, _) ->
            let new_ls = List.fold_left (fun ls (name, ce) -> try_add name ce ls) ls recls in
            ALetRec(recls, helpA ae new_ls d, ())
        | ASeq(ce, rest, _) -> ASeq(helpC ce ls d, helpA rest ls d, ())
        | ACExpr ce -> ACExpr(helpC ce ls d)
    and helpC ce ls d =
        match ce with
        | CIf(cond, thn, els, _) -> CIf(untagI cond, helpA thn ls d, helpA els ls d, ())
        | CAExpr(br, _) -> CAExpr(helpA br ls d, ())
        | CApp(func, args, _) ->
            (match func with
            | ImmId(name, _) when List.mem_assoc name ls ->
                let (func_args, expr) = List.assoc name ls in
                let map = (try List.combine func_args args with
                    | _ -> failwith "Wrong arity for inline function") in
                let e = expand expr map in
                (*if d < max_recursion_depth then CAExpr(helpA e ls (d+1), ())*)
                (*else CAExpr(e ,())*)
                CAExpr(e ,())
            | _ -> untagC ce)
        | CLambda(args, body, _) -> CLambda(args, helpA body ls d, ())
        | CInline(args, body, _) -> CInline(args, helpA body ls d, ())
        | _ -> untagC ce in
    helpA (untagA prog) [] 0
*untagA prog*)

let macro_expand (p : 'a program) : unit program =
    let get_name e =
        match e with
        | EId(x, _) -> x
        | _ -> failwith "Not an ID" in
    let try_add (name, _, expr, _) =
        match expr with
        | EMacro(args, body, _) -> [(name, (List.map fst args, body))]
        | _ -> [] in
    let not_macro (_, _, expr, _) =
        match expr with
        | EMacro _ -> false
        | _ -> true in
    let rec expand expr args ls =
        let sub x = expand x args ls in
        match expr with
        | EId(x, _) when List.mem_assoc x args -> List.assoc x args
        | EId _ | ENumber _ | EBool _-> expr
        (*| ELet of 'a bind list * 'a expr * 'a*)
        (*| ELetRec of 'a bind list * 'a expr * 'a*)
        | EPrim1(op, e, _) -> EPrim1(op, sub e, ())
        | EPrim2(op, e1, e2, _) -> EPrim2(op, sub e1, sub e2, ())
        | EIf(c, t, f, _) -> EIf(sub c, sub t, sub f, ())
        | ETuple(vals, _) -> ETuple(List.map sub vals, ())
        | EGetItem(tup, idx, _) -> EGetItem(sub tup, sub idx, ())
        | ESetItem(tup, idx, rhs, _) -> ESetItem(sub tup, sub idx, sub rhs, ())
        | EGetItemExact(tup, idx, _) -> EGetItemExact(sub tup, idx, ())
        | ESetItemExact(tup, idx, rhs, _) -> ESetItemExact(sub tup, idx, sub rhs, ())
        | ESeq(stmts, _) -> ESeq(List.map sub stmts, ())
        | EApp(func, args, loc) -> EApp(sub func, List.map sub args, ())
        | _ -> failwith "That's some fucked up macro"
    and help e ls =
        let hlp x = help x ls in
        match e with
        | ELet(binds, expr, _) ->
            let funcs = List.flatten(List.map try_add binds) in
            let new_binds = List.filter not_macro binds in
            ELet(new_binds, help expr (funcs @ ls), ())
        | ELetRec(binds, expr, _) ->
            let funcs = List.flatten(List.map try_add binds) in
            let new_binds = List.filter not_macro binds in
            ELetRec(new_binds, help expr (funcs @ ls), ())
        | EPrim1(op, e, _) -> EPrim1(op, hlp e, ())
        | EPrim2(op, e1, e2, _) -> EPrim2(op, hlp e1, hlp e2, ())
        | EIf(c, t, f, _) -> EIf(hlp c, hlp t, hlp f, ())
        | ETuple(vals, _) -> ETuple(List.map hlp vals, ())
        | EGetItem(tup, idx, _) -> EGetItem(hlp tup, hlp idx, ())
        | ESetItem(tup, idx, rhs, _) -> ESetItem(hlp tup, hlp idx, hlp rhs, ())
        | EGetItemExact(tup, idx, _) -> EGetItemExact(hlp tup, idx, ())
        | ESetItemExact(tup, idx, rhs, _) -> ESetItemExact(hlp tup, idx, hlp rhs, ())
        | ESeq(stmts, _) -> ESeq(List.map hlp stmts, ())
        | ENumber _ | EBool _ | EId _ -> e
        | EApp(func, args, _) ->
            (* Help first or after expansion? *)
            let name = get_name func in
            if List.mem_assoc name ls then
                let (func_args, expr) = List.assoc name ls in
                let map = (try List.combine func_args args with
                    | _ -> failwith "Wrong arity for macrod function") in
                (*printf "original program:\n%s\n" (string_of_expr p);*)
                (*hlp (expand expr map ls)*)
                let e = (expand expr map ls) in
                printf "expanded program:\n%s\n" (string_of_expr e); hlp e
            else EApp(hlp func, List.map hlp args, ())
        | _ -> failwith "Unsupported... Yet" in
    let e = help p [] in e

