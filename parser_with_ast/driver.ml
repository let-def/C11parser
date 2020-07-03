module I = Parser.MenhirInterpreter

let rec normalize = function
  | I.Shifting _ | I.AboutToReduce _ as cp ->
    normalize (I.resume cp)
  | other -> other

let rec loop lexer lexbuf parser token =
  match
    normalize (I.offer parser
                 (token, lexbuf.Lexing.lex_start_p, lexbuf.Lexing.lex_curr_p))
  with
  | (I.Rejected | I.Shifting _ | I.AboutToReduce _) -> assert false
  | I.InputNeeded _ as parser' ->
    loop lexer lexbuf parser' (lexer lexbuf)
  | I.Accepted ok -> Ok ok
  | I.HandlingError env ->
    (* FIXME: we should remove this hack and either gracefully handle the
       situation when a type is unknown or just make it easy to specify
       as set of predefined types. *)
    match token with
    | Tokens.VARIABLE ->
      Format.eprintf "%S should be a type\n%!" !Lexer.last_id;
      loop lexer lexbuf parser Tokens.TYPE
    | _ -> Error (token, parser, env)

let parser lexer lexbuf =
  loop
    lexer lexbuf
    (Parser.Incremental.translation_unit_file lexbuf.Lexing.lex_curr_p)
    (lexer lexbuf)
