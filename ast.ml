type dsl_type =
  | Bool
  | Int
  | Float
  | Vector_int of int
  | Matrix_int of int * int
  | Vector_float of int
  | Matrix_float of int * int

type expr =
  | BoolConst of bool
  | IntConst of int
  | FloatConst of float
  | Var of string
  | ConstVector_int of int * int list
  | ConstMatrix_int of int * int * int list list
  | ConstVector_float of int * float list
  | ConstMatrix_float of int * int * float list list
  | BinOp of
      string * expr * expr (* Binary operations: +, -, *, /, &&, ||, etc. *)
  | Neg of expr (* Unary negation: - for numbers, ! for booleans *)
  | Abs of expr
  | DotProduct of expr * expr
  | Angle of expr * expr
  | Dimension of expr
  | Magnitude of expr
  | Transpose of expr
  | MatrixMultiply of expr * expr
  | Determinant of expr
  | IndexAccess of expr * expr (* Accessing an element of a vector or matrix *)
  | Input of string option

type stmt =
  | Assign of string * expr
  | AssignIndex of expr * expr
  | If of expr * stmt list * stmt list option
  | While of expr * stmt list
  | For of stmt * expr * expr * stmt list
  | Print of string

type program = stmt list
