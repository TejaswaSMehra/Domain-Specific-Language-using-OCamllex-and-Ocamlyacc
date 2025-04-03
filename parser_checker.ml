open Ast

(* Helper function to print expressions as strings for debugging *)
let rec string_of_expr = function
  | BoolConst b -> Printf.sprintf "Bool(%b)" b
  | IntConst i -> Printf.sprintf "Int(%d)" i
  | FloatConst f -> Printf.sprintf "Float(%f)" f
  | ConstVector_int (_, v) ->
      Printf.sprintf "ConstVector_int(%s)"
        (String.concat ", " (List.map string_of_int v))
  | ConstVector_float (_, v) ->
      Printf.sprintf "ConstVector_float(%s)"
        (String.concat ", " (List.map string_of_float v))
  | ConstMatrix_int (_, _, m) ->
      Printf.sprintf "ConstMatrix_int(%s)"
        (String.concat ", "
           (List.map
              (fun v ->
                "[" ^ String.concat ", " (List.map string_of_int v) ^ "]" )
              m ) )
  | ConstMatrix_float (_, _, m) ->
      Printf.sprintf "ConstMatrix_float(%s)"
        (String.concat ", "
           (List.map
              (fun v ->
                "[" ^ String.concat ", " (List.map string_of_float v) ^ "]" )
              m ) )
  | Var id -> Printf.sprintf "Var(%s)" id
  | BinOp (op, e1, e2) ->
      Printf.sprintf "BinOp(%s, %s, %s)" op (string_of_expr e1)
        (string_of_expr e2)
  | Neg e -> Printf.sprintf "Neg(%s)" (string_of_expr e)
  | Abs e -> Printf.sprintf "Abs(%s)" (string_of_expr e)
  | Angle (e1, e2) ->
      Printf.sprintf "Angle(%s, %s)" (string_of_expr e1) (string_of_expr e2)
  | Dimension e -> Printf.sprintf "Dimension(%s)" (string_of_expr e)
  | MatrixMultiply (e1, e2) ->
      Printf.sprintf "MatrixMultiply(%s, %s)" (string_of_expr e1)
        (string_of_expr e2)
  | DotProduct (e1, e2) ->
      Printf.sprintf "DotProduct(%s, %s)" (string_of_expr e1)
        (string_of_expr e2)
  | Magnitude e -> Printf.sprintf "Magnitude(%s)" (string_of_expr e)
  | Transpose e -> Printf.sprintf "Transpose(%s)" (string_of_expr e)
  | Determinant e -> Printf.sprintf "Determinant(%s)" (string_of_expr e)
  | IndexAccess (e1, e2) ->
      Printf.sprintf "IndexAccess(%s, %s)" (string_of_expr e1)
        (string_of_expr e2)
  | Input (Some filepath) -> Printf.sprintf "Input(Some(%s))" filepath
  | Input None -> Printf.sprintf "Input(None)"

(* Helper function to print statements as strings for debugging *)
let rec string_of_stmt = function
  | Assign (id, e) -> Printf.sprintf "Assign(%s, %s)" id (string_of_expr e)
  | AssignIndex (e1, e2) ->
      Printf.sprintf "AssignIndex(%s, %s)" (string_of_expr e1)
        (string_of_expr e2)
  | If (cond, then_stmt, Some else_stmt) ->
      let s1 =
          List.fold_left
            (fun acc stmt -> acc ^ string_of_stmt stmt ^ "\n")
            "" then_stmt
      in
      let s2 =
          List.fold_left
            (fun acc stmt -> acc ^ string_of_stmt stmt ^ "\n")
            "" else_stmt
      in
      Printf.sprintf "If(%s, %s, %s)" (string_of_expr cond) s1 s2
  | If (cond, then_stmt, None) ->
      let s1 =
          List.fold_left
            (fun acc stmt -> acc ^ string_of_stmt stmt ^ "\n")
            "" then_stmt
      in
      Printf.sprintf "If(%s, %s, None)" (string_of_expr cond) s1
  | While (cond, body) ->
      let s =
          List.fold_left
            (fun acc stmt -> acc ^ string_of_stmt stmt ^ "\n")
            "" body
      in
      Printf.sprintf "While(%s, %s)" (string_of_expr cond) s
  | Print s -> Printf.sprintf "Print(%s)" s
  | For (id, start, end_, body) ->
      let s =
          List.fold_left
            (fun acc stmt -> acc ^ string_of_stmt stmt ^ "\n")
            "" body
      in
      Printf.sprintf "For(%s, %s, %s, %s)" (string_of_stmt id)
        (string_of_expr start) (string_of_expr end_) s

(* Helper function to print the full program as a string *)
let string_of_program program =
    String.concat "\n" (List.map string_of_stmt program)

(* Parse and type-check a DSL program *)
let parse_and_type_check input =
    let lexbuf = input in
    try
      (* Parse the input program using the lexer and parser *)
      let program = Parser.program Lexer.token lexbuf in
      (* Type-check the program *)
      let _ = Type_checker.type_check_program program in

      (* Print the parsed and type-checked AST *)
      Printf.printf "AST:\n%s\n" (string_of_program program);
      Printf.printf "Type-checking successful!\n"
    with
    | Failure msg -> Printf.printf "Error: %s\n" msg
    | Parsing.Parse_error -> Printf.printf "Syntax error\n"

(* Main function to test the DSL *)
let () =
  let input =
    if Array.length Sys.argv > 1 then
      let filename = Sys.argv.(1) in
      Lexing.from_channel (open_in filename)
    else
      Lexing.from_channel stdin
  in
  parse_and_type_check input

