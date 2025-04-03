open Ast
open Eval

let () =
    let input = Lexing.from_channel stdin in
    try
      let program = Parser.program Lexer.token input in
      eval_prog program
    with
    | Parser.Error -> Printf.printf "Syntax error\n"
    | Lexer.Lexing_error msg -> Printf.printf "Lexing error: %s\n" msg
    | Eval.RuntimeError msg -> Printf.printf "Runtime error: %s\n" msg
