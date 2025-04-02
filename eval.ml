open Ast

(* Define runtime values *)
type value =
  | BoolVal of bool
  | IntVal of int
  | FloatVal of float
  | VectorIntVal of int * int list
  | MatrixIntVal of int * int * int list list
  | VectorFloatVal of int * float list
  | MatrixFloatVal of int * int * float list list

(* Environment for variable bindings *)
type env = (string * value) list

exception RuntimeError of string

let lookup env id =
    try List.assoc id env
    with Not_found -> raise (RuntimeError ("Unbound variable: " ^ id))

(* Evaluate expressions and statements *)

let rec eval_expr env expr =
    match expr with
    | BoolConst b -> BoolVal b
    | IntConst i -> IntVal i
    | FloatConst f -> FloatVal f
    | ConstVector_int (n, lst) -> VectorIntVal (n, lst)
    | ConstMatrix_int (a, b, mat) -> MatrixIntVal (a, b, mat)
    | ConstVector_float (n, lst) -> VectorFloatVal (n, lst)
    | ConstMatrix_float (a, b, mat) -> MatrixFloatVal (a, b, mat)
    | Var id -> lookup env id
    | BinOp ("&&", e1, e2) -> (
        match eval_expr env e1 with
        | BoolVal false -> BoolVal false
        | BoolVal true -> eval_expr env e2
        | _ -> raise (RuntimeError "&&: left operand not boolean") )
    | BinOp ("||", e1, e2) -> (
        match eval_expr env e1 with
        | BoolVal true -> BoolVal true
        | BoolVal false -> eval_expr env e2
        | _ -> raise (RuntimeError "||: left operand not boolean") )
    | BinOp (op, e1, e2) -> (
        let v1 = eval_expr env e1 in
        let v2 = eval_expr env e2 in
        match (op, v1, v2) with
        (* Arithmetic Operations *)
        | "+", IntVal a, IntVal b -> IntVal (a + b)
        | "-", IntVal a, IntVal b -> IntVal (a - b)
        | "*", IntVal a, IntVal b -> IntVal (a * b)
        | "/", IntVal a, IntVal b -> IntVal (a / b)
        | "%", IntVal a, IntVal b -> IntVal (a mod b)
        | "+", FloatVal a, FloatVal b -> FloatVal (a +. b)
        | "-", FloatVal a, FloatVal b -> FloatVal (a -. b)
        | "*", FloatVal a, FloatVal b -> FloatVal (a *. b)
        | "/", FloatVal a, FloatVal b -> FloatVal (a /. b)
        | "+", FloatVal a, IntVal b -> FloatVal (a +. float_of_int b)
        | "-", FloatVal a, IntVal b -> FloatVal (a -. float_of_int b)
        | "*", FloatVal a, IntVal b -> FloatVal (a *. float_of_int b)
        | "/", FloatVal a, IntVal b -> FloatVal (a /. float_of_int b)
        | "+", IntVal a, FloatVal b -> FloatVal (float_of_int a +. b)
        | "-", IntVal a, FloatVal b -> FloatVal (float_of_int a -. b)
        | "*", IntVal a, FloatVal b -> FloatVal (float_of_int a *. b)
        | "/", IntVal a, FloatVal b -> FloatVal (float_of_int a /. b)
        | "+", VectorIntVal (n, a), VectorIntVal (m, b) when n = m ->
            VectorIntVal (n, List.map2 ( + ) a b)
        | "-", VectorIntVal (n, a), VectorIntVal (m, b) when n = m ->
            VectorIntVal (n, List.map2 ( - ) a b)
        | "+", VectorFloatVal (n, a), VectorFloatVal (m, b) when n = m ->
            VectorFloatVal (n, List.map2 ( +. ) a b)
        | "-", VectorFloatVal (n, a), VectorFloatVal (m, b) when n = m ->
            VectorFloatVal (n, List.map2 ( -. ) a b)
        | "+", MatrixIntVal (a, b, m1), MatrixIntVal (c, d, m2)
          when a = c && b = d ->
            MatrixIntVal (a, b, List.map2 (List.map2 ( + )) m1 m2)
        | "-", MatrixIntVal (a, b, m1), MatrixIntVal (c, d, m2)
          when a = c && b = d ->
            MatrixIntVal (a, b, List.map2 (List.map2 ( - )) m1 m2)
        | "+", MatrixFloatVal (a, b, m1), MatrixFloatVal (c, d, m2)
          when a = c && b = d ->
            MatrixFloatVal (a, b, List.map2 (List.map2 ( +. )) m1 m2)
        | "-", MatrixFloatVal (a, b, m1), MatrixFloatVal (c, d, m2)
          when a = c && b = d ->
            MatrixFloatVal (a, b, List.map2 (List.map2 ( -. )) m1 m2)
        (* Relational Operations *)
        | "==", IntVal a, IntVal b -> BoolVal (a = b)
        | "!=", IntVal a, IntVal b -> BoolVal (a <> b)
        | "<", IntVal a, IntVal b -> BoolVal (a < b)
        | "<=", IntVal a, IntVal b -> BoolVal (a <= b)
        | ">", IntVal a, IntVal b -> BoolVal (a > b)
        | ">=", IntVal a, IntVal b -> BoolVal (a >= b)
        | "==", FloatVal a, FloatVal b -> BoolVal (a = b)
        | "!=", FloatVal a, FloatVal b -> BoolVal (a <> b)
        | "<", FloatVal a, FloatVal b -> BoolVal (a < b)
        | "<=", FloatVal a, FloatVal b -> BoolVal (a <= b)
        | ">", FloatVal a, FloatVal b -> BoolVal (a > b)
        | ">=", FloatVal a, FloatVal b -> BoolVal (a >= b)
        | "==", FloatVal a, IntVal b -> BoolVal (a = float_of_int b)
        | "!=", FloatVal a, IntVal b -> BoolVal (a <> float_of_int b)
        | "<", FloatVal a, IntVal b -> BoolVal (a < float_of_int b)
        | "<=", FloatVal a, IntVal b -> BoolVal (a <= float_of_int b)
        | ">", FloatVal a, IntVal b -> BoolVal (a > float_of_int b)
        | ">=", FloatVal a, IntVal b -> BoolVal (a >= float_of_int b)
        | "==", IntVal a, FloatVal b -> BoolVal (float_of_int a = b)
        | "!=", IntVal a, FloatVal b -> BoolVal (float_of_int a <> b)
        | "<", IntVal a, FloatVal b -> BoolVal (float_of_int a < b)
        | "<=", IntVal a, FloatVal b -> BoolVal (float_of_int a <= b)
        | ">", IntVal a, FloatVal b -> BoolVal (float_of_int a > b)
        | ">=", IntVal a, FloatVal b -> BoolVal (float_of_int a >= b)
        (* Boolean Operations *)
        | "&&", BoolVal a, BoolVal b -> BoolVal (a && b)
        | "||", BoolVal a, BoolVal b -> BoolVal (a || b)
        | "==", BoolVal a, BoolVal b -> BoolVal (a = b)
        | "!=", BoolVal a, BoolVal b -> BoolVal (a <> b)
        (* Scalar Multiplication *)
        | "*", IntVal s, VectorIntVal (n, v) ->
            VectorIntVal (n, List.map (( * ) s) v)
        | "*", FloatVal s, VectorIntVal (n, v) ->
            VectorFloatVal (n, List.map (fun x -> s *. float_of_int x) v)
        | "*", IntVal s, VectorFloatVal (n, v) ->
            VectorFloatVal (n, List.map (fun x -> float_of_int s *. x) v)
        | "*", FloatVal s, VectorFloatVal (n, v) ->
            VectorFloatVal (n, List.map (( *. ) s) v)
        | "*", IntVal s, MatrixIntVal (a, b, m) ->
            MatrixIntVal (a, b, List.map (List.map (( * ) s)) m)
        | "*", FloatVal s, MatrixIntVal (a, b, m) ->
            MatrixFloatVal
              (a, b, List.map (List.map (fun x -> s *. float_of_int x)) m)
        | "*", IntVal s, MatrixFloatVal (a, b, m) ->
            MatrixFloatVal
              (a, b, List.map (List.map (fun x -> float_of_int s *. x)) m)
        | "*", FloatVal s, MatrixFloatVal (a, b, m) ->
            MatrixFloatVal (a, b, List.map (List.map (( *. ) s)) m)
        | _ -> raise (RuntimeError "Invalid operation or type mismatch") )
    | Abs e -> (
        let v = eval_expr env e in
        match v with
        | IntVal i -> IntVal (abs i)
        | FloatVal f -> FloatVal (abs_float f)
        | _ -> raise (RuntimeError "Abs: expected int or float") )
    | Neg e -> (
        let v = eval_expr env e in
        match v with
        | IntVal i -> IntVal (-i)
        | FloatVal f -> FloatVal (-.f)
        | BoolVal b -> BoolVal (not b)
        | _ -> raise (RuntimeError "Neg: expected int, float, or bool") )
    | DotProduct (e1, e2) -> (
        let v1 = eval_expr env e1 in
        let v2 = eval_expr env e2 in
        match (v1, v2) with
        | VectorFloatVal (n, a), VectorFloatVal (m, b) when n = m ->
            FloatVal (List.fold_left2 (fun acc x y -> acc +. (x *. y)) 0.0 a b)
        | VectorIntVal (n, a), VectorIntVal (m, b) when n = m ->
            IntVal (List.fold_left2 (fun acc x y -> acc + (x * y)) 0 a b)
        | _ -> raise (RuntimeError "DotProduct: incompatible types/sizes") )
    | Angle (e1, e2) -> (
        let v1 = eval_expr env e1 in
        let v2 = eval_expr env e2 in
        match (v1, v2) with
        | VectorFloatVal (n, a), VectorFloatVal (m, b) when n = m ->
            FloatVal
              (acos
                 ( List.fold_left2 (fun acc x y -> acc +. (x *. y)) 0.0 a b
                 /. ( sqrt (List.fold_left (fun acc x -> acc +. (x *. x)) 0.0 a)
                    *. sqrt
                         (List.fold_left (fun acc x -> acc +. (x *. x)) 0.0 b)
                    ) ) )
        | VectorIntVal (n, a), VectorIntVal (m, b) when n = m ->
            IntVal
              (int_of_float
                 (acos
                    ( List.fold_left2
                        (fun acc x y -> acc +. float_of_int (x * y))
                        0.0 a b
                    /. ( sqrt
                           (List.fold_left
                              (fun acc x -> acc +. float_of_int (x * x))
                              0.0 a )
                       *. sqrt
                            (List.fold_left
                               (fun acc x -> acc +. float_of_int (x * x))
                               0.0 b ) ) ) ) )
        | _ -> raise (RuntimeError "Angle: incompatible types/sizes") )
    | Dimension e -> (
        let v = eval_expr env e in
        match v with
        | VectorIntVal (n, _) -> IntVal n
        | VectorFloatVal (n, _) -> IntVal n
        | MatrixIntVal (a, _, _) -> IntVal a
        | MatrixFloatVal (a, _, _) -> IntVal a
        | _ -> raise (RuntimeError "Dimension: expected vector or matrix") )
    | MatrixMultiply (e1, e2) -> (
        let v1 = eval_expr env e1 in
        let v2 = eval_expr env e2 in
        let transpose m =
            List.init
              (List.length (List.hd m))
              (fun i -> List.map (fun row -> List.nth row i) m)
        in
        match (v1, v2) with
        | MatrixIntVal (a, b, m1), MatrixIntVal (c, d, m2) when b = c ->
            let m2t = transpose m2 in
            let result =
                List.map
                  (fun row ->
                    List.map
                      (fun col ->
                        List.fold_left2 (fun acc x y -> acc + (x * y)) 0 row col )
                      m2t )
                  m1
            in
            MatrixIntVal (a, d, result)
        | MatrixFloatVal (a, b, m1), MatrixFloatVal (c, d, m2) when b = c ->
            let m2t = transpose m2 in
            let result =
                List.map
                  (fun row ->
                    List.map
                      (fun col ->
                        List.fold_left2
                          (fun acc x y -> acc +. (x *. y))
                          0.0 row col )
                      m2t )
                  m1
            in
            MatrixFloatVal (a, d, result)
        | _ ->
            raise
              (RuntimeError
                 "MatrixMultiply: incompatible shapes or unsupported types" ) )
    | Magnitude e -> (
        match eval_expr env e with
        | VectorFloatVal (_, lst) ->
            FloatVal
              (sqrt (List.fold_left (fun acc x -> acc +. (x *. x)) 0.0 lst))
        | VectorIntVal (_, lst) ->
            FloatVal
              (sqrt
                 (List.fold_left
                    (fun acc x -> acc +. float_of_int (x * x))
                    0.0 lst ) )
        | _ -> raise (RuntimeError "Magnitude: expected vector") )
    | Transpose e -> (
        let transpose mat =
            List.init
              (List.length (List.hd mat))
              (fun i -> List.map (fun row -> List.nth row i) mat)
        in
        match eval_expr env e with
        | MatrixIntVal (a, b, m) -> MatrixIntVal (b, a, transpose m)
        | MatrixFloatVal (a, b, m) -> MatrixFloatVal (b, a, transpose m)
        | _ -> raise (RuntimeError "Transpose: expected a matrix") )
    | Determinant e -> (
        let minor m i j =
            List.mapi
              (fun _ row -> List.filteri (fun c _ -> c <> j) row)
              (List.filteri (fun r _ -> r <> i) m)
        in
        let rec det_int m =
            match m with
            | [ [ x ] ] -> x
            | _ ->
                List.mapi
                  (fun j elem ->
                    let sign = if j mod 2 = 0 then 1 else -1 in
                    sign * elem * det_int (minor m 0 j) )
                  (List.hd m)
                |> List.fold_left ( + ) 0
        and det_float m =
            match m with
            | [ [ x ] ] -> x
            | _ ->
                List.mapi
                  (fun j elem ->
                    let sign = if j mod 2 = 0 then 1.0 else -1.0 in
                    sign *. elem *. det_float (minor m 0 j) )
                  (List.hd m)
                |> List.fold_left ( +. ) 0.0
        in
        match eval_expr env e with
        | MatrixIntVal (a, b, m) when a = b -> IntVal (det_int m)
        | MatrixFloatVal (a, b, m) when a = b -> FloatVal (det_float m)
        | _ -> raise (RuntimeError "Determinant: expected square matrix") )
    | IndexAccess (e1, e2) -> (
        let v1 = eval_expr env e1 in
        let v2 = eval_expr env e2 in
        match (v1, v2) with
        | VectorIntVal (n, lst), IntVal i when i >= 0 && i < n ->
            IntVal (List.nth lst i)
        | VectorFloatVal (n, lst), IntVal i when i >= 0 && i < n ->
            FloatVal (List.nth lst i)
        | MatrixIntVal (a, b, m), IntVal i when i >= 0 && i < a ->
            VectorIntVal (b, List.nth m i)
        | MatrixFloatVal (a, b, m), IntVal i when i >= 0 && i < a ->
            VectorFloatVal (b, List.nth m i)
        | _ -> raise (RuntimeError "IndexAccess: invalid index or type") )
    | Input opt_path -> (
        match opt_path with
        | Some filepath -> (
            let chan =
                try open_in filepath
                with _ ->
                  raise (RuntimeError ("Cannot open file: " ^ filepath))
            in
            let lexbuf = Lexing.from_channel chan in
            try
              let parsed_expr = Parser.expr Lexer.token lexbuf in
              close_in chan;
              let v = eval_expr env parsed_expr in
              v
            with
            | Parsing.Parse_error ->
                close_in chan;
                raise (RuntimeError "Syntax error in input file")
            | Failure msg ->
                close_in chan;
                raise (RuntimeError ("Runtime error: " ^ msg)))
        | None -> (
            print_string "Enter value:\n";
            flush stdout;
            let lexbuf = Lexing.from_channel stdin in
            try
              let parsed_expr = Parser.expr Lexer.token lexbuf in
              let v = eval_expr env parsed_expr in
              v
            with
            | Parsing.Parse_error -> raise (RuntimeError "Syntax error in input")
            | Failure msg ->
                raise (RuntimeError ("Lexing error: " ^ msg)) ) )

let rec eval_stmt env stmt =
    match stmt with
    | Assign (id, e) ->
        let v = eval_expr env e in
        (id, v) :: List.remove_assoc id env
    | AssignIndex (index_expr, value_expr) ->
        let rec extract_target_and_indices e acc =
            match e with
            | IndexAccess (base, IntConst i) ->
                extract_target_and_indices base (i :: acc)
            | IndexAccess (base, idx_expr) -> (
                match eval_expr env idx_expr with
                | IntVal i -> extract_target_and_indices base (i :: acc)
                | _ -> raise (RuntimeError "Index must be an integer") )
            | Var id -> (id, acc)
            | _ -> raise (RuntimeError "Index assignment must target a variable")
        in

        let id, indices = extract_target_and_indices index_expr [] in
        let value = eval_expr env value_expr in
        let current = lookup env id in

        let updated =
            match (current, indices, value) with
            (* Vector cases *)
            | VectorIntVal (n, lst), [ i ], IntVal x when i >= 0 && i < n ->
                VectorIntVal
                  (n, List.mapi (fun j y -> if j = i then x else y) lst)
            | VectorFloatVal (n, lst), [ i ], FloatVal x when i >= 0 && i < n ->
                VectorFloatVal
                  (n, List.mapi (fun j y -> if j = i then x else y) lst)
            (* Matrix cases *)
            | MatrixIntVal (a, b, mat), [ i; j ], IntVal x
              when i >= 0 && i < a && j >= 0 && j < b ->
                let new_mat =
                    List.mapi
                      (fun row_idx row ->
                        if row_idx = i then
                          List.mapi
                            (fun col_idx elem -> if col_idx = j then x else elem)
                            row
                        else row )
                      mat
                in
                MatrixIntVal (a, b, new_mat)
            | MatrixFloatVal (a, b, mat), [ i; j ], FloatVal x
              when i >= 0 && i < a && j >= 0 && j < b ->
                let new_mat =
                    List.mapi
                      (fun row_idx row ->
                        if row_idx = i then
                          List.mapi
                            (fun col_idx elem -> if col_idx = j then x else elem)
                            row
                        else row )
                      mat
                in
                MatrixFloatVal (a, b, new_mat)
            | _ -> raise (RuntimeError "Invalid or unsupported index assignment")
        in
        (id, updated) :: List.remove_assoc id env
    | If (e, s1, s2_opt) -> (
        match eval_expr env e with
        | BoolVal true -> eval_block env s1
        | BoolVal false -> (
            match s2_opt with Some s2 -> eval_block env s2 | None -> env )
        | _ -> raise (RuntimeError "If condition must be boolean") )
    | While (e, body) ->
        let rec while_loop env =
            match eval_expr env e with
            | BoolVal true -> while_loop (eval_block env body)
            | BoolVal false -> env
            | _ -> raise (RuntimeError "While condition must be boolean")
        in
        while_loop env
    | For (init_stmt, e1, e2, body) -> (
        match init_stmt with
        | Assign (id, e3) -> (
            let env = eval_stmt env init_stmt in
            let v1 = eval_expr env e1 in
            let v2 = eval_expr env e2 in
            let v3 = eval_expr env e3 in
            match (v1, v2, v3) with
            | IntVal i, IntVal j, IntVal _ ->
                let rec for_loop env k =
                    if k > j then env
                    else
                      let env' = (id, IntVal k) :: List.remove_assoc id env in
                      let env'' = eval_block env' body in
                      for_loop env'' (k + 1)
                in
                for_loop env i
            | _ -> raise (RuntimeError "For loop bounds must be integers") )
        | _ -> raise (RuntimeError "For loop requires initializer assignment") )
    | Print id ->
        let v = lookup env id in
        let s =
            match v with
            | IntVal i -> string_of_int i
            | FloatVal f -> string_of_float f
            | BoolVal b -> string_of_bool b
            | VectorIntVal (_, lst) ->
                "[" ^ String.concat ", " (List.map string_of_int lst) ^ "]"
            | VectorFloatVal (_, lst) ->
                "[" ^ String.concat ", " (List.map string_of_float lst) ^ "]"
            | MatrixIntVal (_, _, m) ->
                String.concat "\n"
                  (List.map
                     (fun row ->
                       "["
                       ^ String.concat ", " (List.map string_of_int row)
                       ^ "]" )
                     m )
            | MatrixFloatVal (_, _, m) ->
                String.concat "\n"
                  (List.map
                     (fun row ->
                       "["
                       ^ String.concat ", " (List.map string_of_float row)
                       ^ "]" )
                     m )
        in
        print_endline s;
        env

and eval_block env stmts = List.fold_left eval_stmt env stmts

let eval_prog (prog : program) = ignore (eval_block [] prog)
