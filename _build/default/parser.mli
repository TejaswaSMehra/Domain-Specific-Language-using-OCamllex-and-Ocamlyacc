type token =
  | IDENTIFIER of (
# 5 "parser.mly"
        string
# 6 "parser.mli"
)
  | INPUT of (
# 6 "parser.mly"
        string option
# 11 "parser.mli"
)
  | PRINT of (
# 7 "parser.mly"
        string
# 16 "parser.mli"
)
  | BOOLEAN of (
# 8 "parser.mly"
        bool
# 21 "parser.mli"
)
  | NEGATION
  | CONJUNCTION
  | DISJUNCTION
  | INTEGER of (
# 10 "parser.mly"
        int
# 29 "parser.mli"
)
  | FLOAT of (
# 11 "parser.mly"
        float
# 34 "parser.mli"
)
  | PLUS
  | MINUS
  | MULTIPLY
  | DIVIDE
  | REM
  | ABS
  | EQ
  | NEQ
  | LT
  | GT
  | LEQ
  | GEQ
  | VECTOR_FLOAT of (
# 14 "parser.mly"
        int * float list
# 51 "parser.mli"
)
  | VECTOR_INT of (
# 15 "parser.mly"
        int * int list
# 56 "parser.mli"
)
  | DOT
  | ANGLE
  | MAGNITUDE
  | DIMENSION
  | MATRIX_FLOAT of (
# 17 "parser.mly"
        int * int * float list list
# 65 "parser.mli"
)
  | MATRIX_INT of (
# 18 "parser.mly"
        int * int * int list list
# 70 "parser.mli"
)
  | TRANSPOSE
  | MATRIX_MULTIPLY
  | DETERMINANT
  | LPAREN
  | RPAREN
  | LBRACKET
  | RBRACKET
  | LCURLY
  | RCURLY
  | ASSIGN
  | SEMICOLON
  | IF
  | THEN
  | ELSE
  | FOR
  | WHILE
  | EOF

val program :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Ast.program
