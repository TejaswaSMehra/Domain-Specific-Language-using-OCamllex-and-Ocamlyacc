open Eval

let () =
    let input =
        if Array.length Sys.argv > 1 then
          let filename = Sys.argv.(1) in
          Lexing.from_channel (open_in filename)
        else Lexing.from_channel stdin
    in
    try
      let program = Parser.program Lexer.token input in
      eval_prog program
    with
    | Parsing.Parse_error ->
        Printf.printf "Parse error at %s\n"
          (Lexing.lexeme_start_p input).pos_fname
    | Eval.RuntimeError msg -> Printf.printf "Runtime error: %s\n" msg
    | Failure msg -> Printf.printf "Failure: %s\n" msg
