open Ast

type env = (string * dsl_type) list

let rec type_of_expr env expr =
  match expr with
  | BoolConst _ -> Bool
  | IntConst _ -> Int
  | FloatConst _ -> Float
  | ConstVector_int(n, _) -> Vector_int n
  | ConstMatrix_int(a, b, _) -> Matrix_int(a, b)
  | ConstVector_float(n, _) -> Vector_float n
  | ConstMatrix_float(a, b, _) -> Matrix_float(a, b)
  | Var id -> (try List.assoc id env with Not_found -> failwith ("Undefined variable: " ^ id))
  | BinOp(op, e1, e2) ->
      let t1 = type_of_expr env e1 in
      let t2 = type_of_expr env e2 in
      (match (op, t1, t2) with
      (* Arithmetic Operations *)
      | ("+", Int, Int) | ("-", Int, Int) | ("*", Int, Int) | ("/", Int, Int) | ("%", Int, Int) -> Int
      | ("+", Float, Float) | ("-", Float, Float) | ("*", Float, Float) | ("/", Float, Float) -> Float
      | ("+", Float, Int) | ("-", Float, Int) | ("*", Float, Int) | ("/", Float, Int) -> Float
      | ("+", Int, Float) | ("-", Int, Float) | ("*", Int, Float) | ("/", Int, Float) -> Float
      | ("+", Vector_int n, Vector_int m) when n = m -> Vector_int n
      | ("+", Vector_float n, Vector_float m) when n = m -> Vector_float n
      | ("-", Vector_int n, Vector_int m) when n = m -> Vector_int n
      | ("-", Vector_float n, Vector_float m) when n = m -> Vector_float n
      | ("+", Matrix_int (a,b), Matrix_int (c,d)) when a = c && b = d -> Matrix_int (a,b)
      | ("+", Matrix_float (a,b), Matrix_float (c,d)) when a = c && b = d -> Matrix_float (a,b)
      | ("-", Matrix_int (a,b), Matrix_int (c,d)) when a = c && b = d -> Matrix_int (a,b)
      | ("-", Matrix_float (a,b), Matrix_float (c,d)) when a = c && b = d -> Matrix_float (a,b)
      (* Relational Operations *)
      | ("==", Int, Int) | ("!=", Int, Int) | ("<", Int, Int) | ("<=", Int, Int) | (">", Int, Int) | (">=", Int, Int) -> Bool
      | ("==", Float, Float) | ("!=", Float, Float) | ("<", Float, Float) | ("<=", Float, Float) | (">", Float, Float) | (">=", Float, Float) -> Bool
      | ("==", Float, Int) | ("!=", Float, Int) | ("<", Float, Int) | ("<=", Float, Int) | (">", Float, Int) | (">=", Float, Int) -> Bool
      | ("==", Int, Float) | ("!=", Int, Float) | ("<", Int, Float) | ("<=", Int, Float) | (">", Int, Float) | (">=", Int, Float) -> Bool
      (* Boolean Operations *)
      | ("&&", Bool, Bool) | ("||", Bool, Bool) | ("==", Bool, Bool) | ("!=", Bool, Bool) -> Bool
      | ("*", Int, Vector_int n) -> Vector_int n
      | ("*", Float, Vector_int n) -> Vector_float n
      | ("*", Int, Vector_float n) -> Vector_float n
      | ("*", Float, Vector_float n) -> Vector_float n
      | ("*", Int, Matrix_int (a,b)) -> Matrix_int (a,b)
      | ("*", Float, Matrix_int (a,b)) -> Matrix_float (a,b)
      | ("*", Int, Matrix_float (a,b)) -> Matrix_float (a,b)
      | ("*", Float, Matrix_float (a,b)) -> Matrix_float (a,b)
      | _ -> failwith ("Type error in binary operation: " ^ op))
    | Abs e ->
        (match type_of_expr env e with
        | Int -> Int
        | Float -> Float
        | _ -> failwith "Type error in absolute value")
    | Neg e->
      (match type_of_expr env e with
      | Int -> Int
      | Float -> Float
      | Bool -> Bool
      | _ -> failwith "Type error in negation")
  | DotProduct(e1, e2) ->
      (match (type_of_expr env e1, type_of_expr env e2) with
      | Vector_float n, Vector_float m when n = m -> Float
      | Vector_int n, Vector_int m when n = m -> Int
      | _ -> failwith "Type error in dot product")
    | Angle(e1, e2) ->
        (match (type_of_expr env e1, type_of_expr env e2) with
        | Vector_float n, Vector_float m when n = m -> Float
        | Vector_int n, Vector_int m when n = m -> Int
        | _ -> failwith "Type error in angle")
    | Dimension e ->
        (match type_of_expr env e with
        | Vector_int _ -> Int
        | Vector_float _ -> Int
        | _ -> failwith "Type error in dimension")
    | MatrixMultiply(e1, e2) ->
        (match (type_of_expr env e1, type_of_expr env e2) with
        | Matrix_float(a, b), Matrix_float(c, d) when b = c -> Matrix_float(a, d)
        | Matrix_int(a, b), Matrix_int(c, d) when b = c -> Matrix_int(a, d)
        | _ -> failwith "Type error in matrix multiplication")
  | Magnitude e ->
      (match type_of_expr env e with
      | Vector_float _ -> Float
    | Vector_int _ -> Float
      | _ -> failwith "Type error in magnitude")
  | Transpose e ->
      (match type_of_expr env e with
      | Matrix_int(a, b) -> Matrix_int(b, a) (* Transpose swaps dimensions *)
        | Matrix_float(a, b) -> Matrix_float(b, a) (* Transpose swaps dimensions *)
      | _ -> failwith "Type error in transpose")
  | Determinant e ->
      (match type_of_expr env e with
        | Matrix_int(a, b) when a = b -> Int
        | Matrix_float(a, b) when a = b -> Float
      | _ -> failwith "Type error in determinant")
  | IndexAccess(e1, e2) ->
        (match (type_of_expr env e1, type_of_expr env e2) with
        | Vector_int _, Int -> Int
        | Vector_float _, Int -> Float
        | Matrix_int (_,b), Int -> Vector_int b
        | Matrix_float (_,b), Int -> Vector_float b
        | _ -> failwith "Type error in index access")

let rec type_check_stmt env stmt =
    match stmt with
    | Assign(id, e) ->
        (try 
            let t_id = List.assoc id env in
            (* I have to update the env to have a different type for that variable *)
            let t = type_of_expr env e in
            if t_id = t then env else (id, t) :: List.remove_assoc id env
        with 
            Not_found -> (id, type_of_expr env e) :: env)
    | AssignIndex(index_expr, value_expr) ->
        let rec check_base_is_var x = match x with
            | IndexAccess(base, _) -> check_base_is_var base
            | Var id -> id (* Return the variable name if it's valid *)
            | _ -> failwith "Index assignment must target a variable, not a constant"
        in
        let _ = check_base_is_var index_expr in
        (* Check the type of the base variable and value *)
        let base_type = type_of_expr env index_expr in
        let value_type = type_of_expr env value_expr in
        if(base_type = value_type) then env else failwith "Type error in index assignment"
    | If(e, s1, s2_opt) ->
        let t = type_of_expr env e in
        if t = Bool then
            let env1 = List.fold_left type_check_stmt env s1 in
            (match s2_opt with
            | Some s2 -> List.fold_left type_check_stmt env1 s2
            | None -> env1)
        else failwith "Type error in if statement"
    | While(e, s) ->
        let t = type_of_expr env e in
        if t = Bool then List.fold_left type_check_stmt env s else failwith "Type error in while loop"
    | For(v, e1, e2, s) ->
        (match v with Assign(_, e3) ->
            (let env1 = type_check_stmt env v in
            let t1 = type_of_expr env1 e1 in
            let t2 = type_of_expr env1 e2 in
            let t3 = type_of_expr env1 e3 in
            if (t1 = Int && t2=Int && t3=Int) then List.fold_left type_check_stmt env1 s else failwith "Type error in for loop")
        | _ -> failwith "For loop statement should be an assignment")
    | Input id -> (match id with Some id -> (id, Int) :: env | None -> env)
    | Print id -> (if (List.mem_assoc id env) then env else failwith "Undefined variable in print statement")

let type_check_program program =
    match program with
    | stmts -> List.fold_left type_check_stmt [] stmts