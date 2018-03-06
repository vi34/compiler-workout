open GT       
open Language
open List
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                         
let evalInstruction (stack, cfg) inst = 
    let (state, input, output) = cfg in 
    match inst with
        | CONST n -> (n :: stack, cfg)
        | READ -> ((hd input) :: stack, (state, tl input, output))
        | WRITE -> (tl stack, (state, input, output @ [hd stack]))
        | LD var -> ((state var)::stack, cfg)
        | ST var -> (tl stack, (Expr.update var (hd stack) state, input, output))
        | BINOP op -> 
            let x :: y :: tail = stack in 
            ((Expr.eval state (Expr.Binop (op, Expr.Const y, Expr.Const x)))::tail, cfg)


let rec eval config prg = match prg with
    | [] -> config
    | inst :: t -> eval (evalInstruction config inst) t  


(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)
let rec compileExpr expr = match expr with
    | Expr.Var x -> [LD x]  
    | Expr.Const n -> [CONST n]
    | Expr.Binop (op, x, y) -> (compileExpr x) @ (compileExpr y) @ [BINOP op]


let rec compile stmt = match stmt with
    | Stmt.Assign (var, expr) -> (compileExpr expr) @ [ST var]
    | Stmt.Read x -> [READ; ST x]
    | Stmt.Write expr -> (compileExpr expr) @ [WRITE]
    | Stmt.Seq (s1, s2) -> (compile s1) @ (compile s2)

                         
