(* 2002-11-08 -- Time-stamp: <2003-01-06 14:04:13 pes20>    -*-SML-*- *)
(* Main.sml *)

open Parser Lexer Semantics PrettyPrint;;
     
exception MyFail;;
          
val language = "L2" ;;


(* parse string s, using entrypoint parser, printing parse and lex
error messages as appropriate and raising 'MyFail' *)

fun parse s parser err_msg_prefix = 
    let val lexbuf = Lexing.createLexerString s
        val result = 
            (parser Lexer.token lexbuf)
            handle
	    Parsing.ParseError f =>
	    let val pos1 = Lexing.getLexemeStart lexbuf
		val pos2 = Lexing.getLexemeEnd lexbuf
	    in
		Location.errMsg ("", BasicIO.std_in, lexbuf) 
		                (Location.Loc(pos1, pos2))
		                (err_msg_prefix ^ " parsing error.")
                                handle (Fail s) => raise MyFail;
                raise MyFail
	    end
	  | Lexer.LexicalError(msg, pos1, pos2) =>
	    if pos1 >= 0 andalso pos2 >= 0 then
		Location.errMsg ("", BasicIO.std_in, lexbuf)
		                (Location.Loc(pos1, pos2))
		                (err_msg_prefix ^ " lexical error: " ^ msg)
                                handle (Fail s) => raise MyFail
	    else 
		(Location.errPrompt 
                     (err_msg_prefix ^" lexical error: " ^ msg ^ "\n\n");
		     raise MyFail
                           )
        val _ = Parsing.clearParser() 
    in
        result
    end


fun main () = (
    TextIO.print("\n" ^ language^" implementation\n(NB: parentheses may be needed to make an expression parse the way you intend)\n(type ctrl-C to exit)\n");
    (while true do 
         let 
             (* read input expression*)
             val _ = TextIO.print( "\n\nEnter an "^language^" expression: " )
             val e_ascii = TextIO.inputLine TextIO.stdIn 
                           
             (* lex and parse the expression *)
             val e_raw = parse e_ascii Parser.main language
                         
             (* resolve scopes *)
             val e = resolve_scopes e_raw 
                 handle (Resolve err) => 
                        (TextIO.print 
                             (language ^ " scope resolution error: " ^ err);
                             raise MyFail )
                        


             (* read input initial store*)
             val _ = TextIO.print
                         ("Enter an initial store (eg " 
                          ^ (pp_store (zero_store e)) ^ "): " )
             val store_ascii = TextIO.inputLine TextIO.stdIn 
                               
             (* lex and parse the initial store*)
             val store = parse store_ascii Parser.store "store"

             val _ = TextIO.print "\n"

             (* type inference *)
             val _ = prettytype e store



             (* reduction *)
             val _ = prettyreduce (e,store) 
         in
             ()
         end
             handle MyFail => ()
                              ));;
val _ = main ();
    




