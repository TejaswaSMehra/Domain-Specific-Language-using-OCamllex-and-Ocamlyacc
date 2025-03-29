%{
open Ast
%}

%token <string> IDENTIFIER
%token <string option> INPUT
%token <string> PRINT
%token <bool> BOOLEAN
%token NEGATION CONJUNCTION DISJUNCTION
%token <int> INTEGER
%token <float> FLOAT
%token PLUS MINUS MULTIPLY DIVIDE REM ABS
%token EQ NEQ LT GT LEQ GEQ
%token <int * float list> VECTOR_FLOAT
%token <int * int list> VECTOR_INT
%token DOT ANGLE MAGNITUDE DIMENSION
%token <int * int * float list list> MATRIX_FLOAT
%token <int * int * int list list> MATRIX_INT
%token TRANSPOSE MATRIX_MULTIPLY DETERMINANT
%token LPAREN RPAREN LBRACKET RBRACKET LCURLY RCURLY
%token ASSIGN SEMICOLON IF THEN ELSE FOR WHILE
%token EOF

%start program
%type <Ast.program> program

(* Precedence declarations to resolve shift/reduce conflicts *)
%left DISJUNCTION
%left CONJUNCTION
%nonassoc EQ NEQ LT LEQ GT GEQ
%left PLUS MINUS
%left MULTIPLY DIVIDE REM
%left DOT 
%left ANGLE 
%left MATRIX_MULTIPLY
%nonassoc MAGNITUDE DIMENSION TRANSPOSE DETERMINANT
%right UPLUS UMINUS

%%

program:
    stmt_list EOF { $1 }

stmt_list:
    stmt SEMICOLON stmt_list { $1 :: $3 }
  | stmt SEMICOLON { [$1] }

stmt:
    lvalue ASSIGN expr {
      match $1 with
      | Var(v) -> Assign(v, $3)
      | _      -> AssignIndex($1, $3)
    }
  | INPUT { Input($1) }
  | PRINT { Print($1) }
  | FOR LPAREN stmt SEMICOLON expr SEMICOLON expr RPAREN LCURLY stmt_list RCURLY { For($3, $5, $7, $10) }
  | IF LPAREN expr RPAREN THEN LCURLY stmt_list RCURLY ELSE LCURLY stmt_list RCURLY { If($3, $7, Some $11) }
  | IF LPAREN expr RPAREN THEN LCURLY stmt_list RCURLY { If($3, $7, None) }
  | WHILE LPAREN expr RPAREN LCURLY stmt_list RCURLY { While($3, $6) }

(* New nonterminal for assignment targets *)
lvalue:
    IDENTIFIER { Var($1) }
  | lvalue LBRACKET expr RBRACKET { IndexAccess($1, $3) }

expr:
    bool_expr { $1 }

bool_expr:
    bool_expr DISJUNCTION rel_expr { BinOp("||", $1, $3) }
  | bool_expr CONJUNCTION rel_expr { BinOp("&&", $1, $3) }
  | rel_expr { $1 }

rel_expr:
    arith_expr { $1 }
  | arith_expr EQ arith_expr { BinOp("==", $1, $3) }
  | arith_expr NEQ arith_expr { BinOp("!=", $1, $3) }
  | arith_expr LT arith_expr { BinOp("<", $1, $3) }
  | arith_expr LEQ arith_expr { BinOp("<=", $1, $3) }
  | arith_expr GT arith_expr { BinOp(">", $1, $3) }
  | arith_expr GEQ arith_expr { BinOp(">=", $1, $3) }

arith_expr:
    arith_expr PLUS term { BinOp("+", $1, $3) }
  | arith_expr MINUS term { BinOp("-", $1, $3) }
  | term { $1 }

term:
    term MULTIPLY factor { BinOp("*", $1, $3) }
  | term DIVIDE factor { BinOp("/", $1, $3) }
  | term REM factor { BinOp("%", $1, $3) }
  | factor { $1 }

factor:
    MINUS factor %prec UMINUS { Neg($2) }
  | NEGATION factor %prec UMINUS { Neg($2) }
  | PLUS factor %prec UPLUS { $2 }
  | ABS factor { Abs($2) }
  | postfix_expr { $1 }

postfix_expr:
    prefix_expr { $1 }
  | postfix_expr DOT prefix_expr { DotProduct($1, $3) }
  | postfix_expr MATRIX_MULTIPLY prefix_expr { MatrixMultiply($1, $3) }

prefix_expr:
    primary { $1 }
  | angle_expr { $1 }
  | unary_prefix_expr { $1 }

angle_expr:
    ANGLE primary primary { Angle($2, $3) }

unary_prefix_expr:
    MAGNITUDE primary { Magnitude($2) }
  | DIMENSION primary { Dimension($2) }
  | TRANSPOSE primary { Transpose($2) }
  | DETERMINANT primary { Determinant($2) }

primary:
    INTEGER { IntConst($1) }
  | FLOAT { FloatConst($1) }
  | BOOLEAN { BoolConst($1) }
  | IDENTIFIER { Var($1) }
  | VECTOR_FLOAT { let (n, l) = $1 in ConstVector_float(n, l) }
  | VECTOR_INT { let (n, l) = $1 in ConstVector_int(n, l) }
  | MATRIX_FLOAT { let (m, n, l) = $1 in ConstMatrix_float(m, n, l) }
  | MATRIX_INT { let (m, n, l) = $1 in ConstMatrix_int(m, n, l) }
  | primary LBRACKET expr RBRACKET { IndexAccess($1, $3) }
  | LPAREN expr RPAREN { $2 }
