(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators
open List
                         
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let undef x = failwith (Printf.sprintf "Variable %s is undefined" x)
    let empty = {g = undef; l = undef; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)

    let update x v s = 
      let update' x v stateFun = fun q -> if q = x then v else stateFun q in 
      if mem x s.scope then {g = s.g; l = update' x v s.l; scope = s.scope} else {g = update' x v s.g; l = s.l; scope = s.scope}                   
    
    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = if mem x s.scope then s.l x else s.g x 

    (* Creates a new scope, based on a given state *)
    let enter st xs = {g = st.g; l = undef; scope = xs}

    (* Drops a scope *)
    let leave st st' = {g = st.g; l = st'.l; scope = st'.scope}

  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t
    (* function call    *) | Call  of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * int option
                                                            
    (* Expression evaluator


          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)                                                       
    let to_func op =
      let bti   = function true -> 1 | _ -> 0 in
      let itb b = b <> 0 in
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> bti |> (< )
      | "<=" -> bti |> (<=)
      | ">"  -> bti |> (> )
      | ">=" -> bti |> (>=)
      | "==" -> bti |> (= )
      | "!=" -> bti |> (<>)
      | "&&" -> fun x y -> bti (itb x && itb y)
      | "!!" -> fun x y -> bti (itb x || itb y)
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op)    
    
    let rec eval st expr =      
      match expr with
      | Const n -> n
      | Var   x -> State.eval st x
      | Binop (op, x, y) -> to_func op (eval st x) (eval st y)



(*)    let rec eval env ((st, i, o, r) as conf) expr = failwith "Not implemented" *)
         
    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string                                                                                                                  
    *)
    ostap (                                      
      parse:
      !(Ostap.Util.expr 
             (fun x -> x)
         (Array.map (fun (a, s) -> a, 
                           List.map  (fun s -> ostap(- $(s)), (fun x y -> Binop (s, x, y))) s
                        ) 
              [|                
                  `Lefta, ["!!"];
                  `Lefta, ["&&"];
                  `Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
                  `Lefta, ["+" ; "-"];
                  `Lefta, ["*" ; "/"; "%"];
              |] 
         )
         primary);
      
      primary:
        n:DECIMAL {Const n}
      | x:IDENT   {Var x}
      | -"(" parse -")"
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)

     let rec eval env ((st, i, o, r) as conf) k stmt =
      match stmt with
        | Read    x       -> (match i with z::i' -> (State.update x z st, i', o) | _ -> failwith "Unexpected end of input")
        | Write   e       -> (st, i, o @ [Expr.eval st e])
        | Assign (x, e)   -> (State.update x (Expr.eval st e) st, i, o)
        | Seq    (s1, s2) -> eval env (eval env conf s1) s2
        | Skip            -> conf 
        | If (cond, t, e) -> eval env conf (if (Expr.eval st cond) <> 0 then t else e)
        | While (cond, body) -> (if (Expr.eval st cond) = 0 then conf else eval env (eval env conf body) stmt)
        | Repeat (body, cond) -> 
          let (st, i, o)  = eval env conf stmt in 
            if (Expr.eval st cond) = 0 then eval env (st, i, o) stmt else (st, i, o)
        | Call (f, args) -> 
          let params, locals, body = env#definition f in
          let evaluatedArgs = combine params (map (Expr.eval st) args) in 
          let initState = State.enter st (params @ locals) in 
          let state = fold_left (fun st (x, v) -> State.update x v st) initState evaluatedArgs in
          let resST, resI, resO = eval env (state, i, o) body in
          (State.leave resST st, resI, resO)
                          

    let rec parseElifs elifs els =  match elifs with
      | [] -> els
      | (cond, body)::elifs' -> If (cond, body, parseElifs elifs' els)

    (* Statement parser *)
    ostap (
      parse:
        s:stmt ";" ss:parse {Seq (s, ss)}
      | stmt;
      stmt:
        %"read" "(" x:IDENT ")"          {Read x}
      | %"write" "(" e:!(Expr.parse) ")" {Write e}
      | x:IDENT ":=" e:!(Expr.parse)    {Assign (x, e)}
      | %"skip" {Skip}
      | %"if" cond:!(Expr.parse) %"then" th:parse 
        elif:(%"elif" !(Expr.parse) %"then" parse)*
        els:(%"else" parse)?
        %"fi" { 
        If (
            cond,
            th, 
            match els with
              | None -> parseElifs elif Skip
              | Some body -> parseElifs elif body
          )}
      | %"while" cond: !(Expr.parse) %"do" body:parse %"od"  { While (cond, body) }
      | %"repeat" body:parse %"until" cond: !(Expr.parse)    { Repeat (body, cond) }
      | %"for" init:parse "," cond:!(Expr.parse) "," inc:parse %"do" body:parse %"od" { Seq (init, While (cond, Seq (body, inc))) }       
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      arg: IDENT;

      parse: %"fun" name:IDENT "(" args: !(Util.list0 arg) ")"
        locals: (%"local" !(Util.list arg))?
        "{" body: !(Stmt.parse) "}" 
        { (name, (args, (match locals with None -> [] | Some l -> l), body))}
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)

let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args (st, i, o, r) =
           let xs, locs, s      = snd @@ M.find f m in
           let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
           let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
           (State.leave st'' st, i', o', r')
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
