exception Error of string

(* modified while language

   - Control-related statements(while,if) are converted to
   control-flow edges.

   - http://www.program-analysis.com/while.html
*)

type id = string

type const = int

type bop = 
| Bop_plus
| Bop_minus
| Bop_mult
| Bop_div

type uop = 
| Uop_minus

type cmp = 
| Cmp_le
| Cmp_lt
| Cmp_ge
| Cmp_gt
| Cmp_eq
| Cmp_neq

type aexp = 
| Aexp_id of id
| Aexp_const of const
| Aexp_bop of bop * aexp * aexp
| Aexp_uop of uop * aexp

type bexp = 
| Bexp_true
| Bexp_false
| Bexp_cmp of cmp * aexp * aexp
| Bexp_not of bexp

type stmt = 
| Stmt_skip
| Stmt_assign of id * aexp
| Stmt_assert of bexp
| Stmt_call of id * aexp

type blk = stmt list

(* function name * argument * basic blocks in function *)
type func = id * id * blk list

(* from-function name * nth BB * to-function name * nth BB *)
type ctrl_edge = (id * int) * (id * int)

type ctrl_edges = ctrl_edge list

(* function definition * main program * control-flow edges *)
type pgm = func list * blk list * ctrl_edges

let rec get_arg_funcs (fs:func list) : id -> id =
  match fs with
  | [] -> (fun _ -> raise (Error "get_arg_funcs: not found"))
  | (f,a,_)::tl -> (fun x -> if x = f then a else (get_arg_funcs tl) x)

let get_arg (p:pgm) : id -> id = match p with (fs,_,_) -> get_arg_funcs fs

let get_fids_funcs (fs:func list) : id list = List.map (fun (f,_,_) -> f) fs
let get_fids (p:pgm) : id list = match p with (fs,_,_) -> ""::(get_fids_funcs fs)
