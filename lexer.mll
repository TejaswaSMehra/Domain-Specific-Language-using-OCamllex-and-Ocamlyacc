{
open Printf
open Parser
(* Define the token type *)

(* Helper function to remove quotes from a string *)
let remove_quotes s = String.sub s 1 (String.length s - 2);;

let input_taker s = String.sub s 6 (String.length s - 7)
let print_taker s = String.sub s 6 (String.length s - 7)

let parse_int_vector s =
  let dimension_list = String.split_on_char '\n' s in
  let dimension = List.hd dimension_list in
  let dimension = int_of_string dimension in
  let elements = List.tl dimension_list in
  let elements = List.hd elements in
  let elements = remove_quotes elements in
  let elements = String.split_on_char ',' elements in
  let elements = List.map int_of_string elements in
  if(dimension != List.length elements) then failwith "Dimension mismatch" else
  VECTOR_INT (dimension, elements)


let parse_float_vector s =
  let dimension_list = String.split_on_char '\n' s in
  let dimension = List.hd dimension_list in
  let dimension = int_of_string dimension in
  let elements = List.tl dimension_list in
  let elements = List.hd elements in
  let elements = remove_quotes elements in
  let elements = String.split_on_char ',' elements in
  let elements = List.map float_of_string elements in
  if(dimension != List.length elements) then failwith "Dimension mismatch" else
  VECTOR_FLOAT (dimension, elements)

let parse_int_matrix s = 
  let dimension_matrix = String.split_on_char '\n' s in
  let dimension = List.map int_of_string (String.split_on_char ',' (List.hd dimension_matrix)) in
  let vectors = List.tl dimension_matrix in
  let vectors = List.hd vectors in
  let vectors = remove_quotes vectors in
  let vectors = String.split_on_char ';' vectors in
  let vectors = List.map (fun x -> remove_quotes x) vectors in
  let vectors = List.map (fun x -> String.split_on_char ',' x) vectors in
  let vectors = List.map (fun x -> List.map int_of_string x) vectors in
  if(List.length vectors <> List.hd dimension) then failwith "Dimension mismatch"
  else if (List.hd (List.tl dimension )<> List.length (List.hd vectors)) then failwith "Dimension mismatch" else
  MATRIX_INT (List.hd dimension, List.hd (List.tl dimension), vectors)

let parse_float_matrix s =
  let dimension_matrix = String.split_on_char '\n' s in
  let dimension = List.map int_of_string (String.split_on_char ',' (List.hd dimension_matrix)) in
  let vectors = List.tl dimension_matrix in
  let vectors = List.hd vectors in
  let vectors = remove_quotes vectors in
  let vectors = String.split_on_char ';' vectors in
  let vectors = List.map (fun x -> remove_quotes x) vectors in
  let vectors = List.map (fun x -> String.split_on_char ',' x) vectors in
  let vectors = List.map (fun x -> List.map float_of_string x) vectors in
  if(List.length vectors <> List.hd dimension) then failwith "Dimension mismatch"
  else if (List.hd (List.tl dimension) <> List.length (List.hd vectors)) then failwith "Dimension mismatch" else
  MATRIX_FLOAT (List.hd dimension, List.hd (List.tl dimension), vectors)
}
(* Define the token rules *)


let dig_seq = ['0'-'9']+ 
let number = ['0'-'9']+ 
let sign_number = ['+' '-']? number
let float = number '.' (number ('e' ['+' '-']? number)? | number 'e' sign_number)?
let sign_float = ['+' '-']? float
let identifier = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '_' '0'-'9' '\'']* 
let mini_whitespace = [' ' '\t'] 
let whitespace = [' ' '\t' '\n']
let print_identifier = "Print(" identifier ')' 
let int_vector_list = '[' (sign_number) (',' (sign_number))* ']' 
let int_vector = dig_seq '\n' int_vector_list 
let float_vector_list = '[' (sign_float) (',' (sign_float))* ']' 
let float_vector = dig_seq '\n' float_vector_list 
let int_matrix_list = '[' int_vector_list (';' int_vector_list)* ']' 
let int_matrix = dig_seq ',' dig_seq '\n' int_matrix_list 
let float_matrix_list = '[' float_vector_list (';' float_vector_list)* ']' 
let float_matrix = dig_seq ',' dig_seq '\n' float_matrix_list 
(* Helper functions to extract the input and print strings *)

rule token = parse
  (* Whitespace *)
| whitespace { token lexbuf }

  (* Comments *)
| "(*" { comment lexbuf }

  (* Input and Print commands *)
| "Input()" { INPUT None }
| "Input(" [^ ')' '(']+ ")" as s { INPUT (Some (input_taker s)) }
| print_identifier as s { PRINT (print_taker s) }

  (* Keywords and control constructs *)
| "if" { IF }
| "then" { THEN }
| "else" { ELSE }
| "for" { FOR }
| "while" { WHILE }

  (* Boolean constants and operators *)
| "true" { BOOLEAN true }
| "false" { BOOLEAN false }
| "!" { NEGATION }
| "&&" { CONJUNCTION }
| "||" { DISJUNCTION }

  (* Arithmetic operators *)
| "+" { PLUS }
| "-" { MINUS }
| "*" { MULTIPLY }
| "/" { DIVIDE }
| "%" { REM }
| "abs" { ABS }

  (* Comparison operators *)
| "==" { EQ }
| "!=" { NEQ }
| "<" { LT }
| ">" { GT }
| "<=" { LEQ }
| ">=" { GEQ }

  (* Vectors *)
| int_vector as int_vec {parse_int_vector int_vec}
| float_vector as fl_vec {parse_float_vector fl_vec}

  (* Matrices *)
| int_matrix as int_mat {parse_int_matrix int_mat}
| float_matrix as fl_mat {parse_float_matrix fl_mat}

  (* Vector and Matrix operations *)
| "." { DOT }
| "angle" { ANGLE }
| "magnitude" { MAGNITUDE }
| "dimension" { DIMENSION }
| "transpose" { TRANSPOSE }
| "matrix_multiply" { MATRIX_MULTIPLY }
| "determinant" { DETERMINANT }

  (* Parentheses and brackets *)
| "(" { LPAREN }
| ")" { RPAREN }
| "[" { LBRACKET }
| "]" { RBRACKET }
| "{" { LCURLY }
| "}" { RCURLY }

  (* Assignment and sequencing *)
| ":=" { ASSIGN }
| ";" { SEMICOLON }

  (* Identifiers *)
| identifier as id { IDENTIFIER id }

  (* Integers *)
| number as int { INTEGER (int_of_string int) }

  (* Floats *)
| float as fl { FLOAT (float_of_string fl) }

  (* EOF *)
| eof { EOF }

  (* Fallback for unrecognized input *)
| _ as c {failwith (sprintf "Unrecognized character '%c'. " c)}


and comment = parse
  | "*)" { token lexbuf }
  | _ { comment lexbuf }