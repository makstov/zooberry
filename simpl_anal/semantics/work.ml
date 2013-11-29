exception Error of string

(* Partition is the same to Work. *)
module type Work =
sig
  type t
  val compare : t -> t -> int
  val to_string : t -> string
  val init : t
  val get_blks : t -> Syn.pgm -> Syn.blk list
  val get_childs : t -> Syn.pgm -> t list

  type lst
  val empty_lst : lst
  val is_empty : lst -> bool
  val choose_work : lst -> t * lst
  val works_add : t list -> lst -> lst
end

module FlowInsenWork = 
struct
  type t = unit
  let compare = compare 
  let to_string (x:t) : string = "unit"
  let init : t = ()
  let get_blks_funcs (fs:Syn.func list) : Syn.blk list = 
    List.fold_left (fun acc f -> acc@(match f with (_,_,bs) -> bs)) [] fs
  let get_blks (x:t) (p:Syn.pgm) : Syn.blk list = 
    match p with (fs,bs,_) -> (get_blks_funcs fs)@bs
  let get_childs (x:t) (p:Syn.pgm) : t list = [x]

  type lst = t list
  let empty_lst : lst = []
  let is_empty (x:lst) : bool = x = []
  let choose_work (x:lst) : t * lst = 
    match x with
    | [] -> raise (Error "choose_work: no work")
    | hd::tl -> (hd,tl)
  let rec works_add (ws:t list) (x:lst) : lst = 
    match ws with
    | [] -> x
    | hd::tl -> if List.mem hd x then works_add tl x else works_add tl (hd::x)
end

module FlowSenWork = 
struct
  type t = Syn.id * int
  let compare = compare 
  let to_string (x:t) : string = 
    match x with (f,i) -> "("^f^","^(string_of_int i)^")"
  let init : t = ("",0)
  let rec get_blks_funcs (w:t) (fs:Syn.func list) : Syn.blk list = 
    match fs with 
    | [] -> raise (Error "get_blks_funcs: not found")
    | (f,_,bs)::tl -> 
      if fst w = f
      then [List.nth bs (snd w)]
      else get_blks_funcs w tl
  let get_blks (w:t) (p:Syn.pgm) : Syn.blk list = 
    match p with (fs,bs,_) ->
      if fst w = ""
      then [List.nth bs (snd w)]
      else get_blks_funcs w fs
  let get_childs (w:t) (p:Syn.pgm) : t list = 
    match p with (_,_,ctrl_edges) ->
      let edges_from_w = List.filter (fun e -> fst e = w) ctrl_edges in
      let dest_ws = List.map snd edges_from_w in
      dest_ws

  type lst = t list
  let empty_lst : lst = []
  let is_empty (x:lst) : bool = x = []
  let choose_work (x:lst) : t * lst = 
    match x with
    | [] -> raise (Error "choose_work: no work")
    | hd::tl -> (hd,tl)
  let rec works_add (ws:t list) (x:lst) : lst = 
    match ws with
    | [] -> x
    | hd::tl -> if List.mem hd x then works_add tl x else works_add tl (hd::x)
end

module FuncSenWork = 
struct
  type t = Syn.id
  let compare = compare
  let to_string (w:t) : string = w
  let init : t = ""
  let rec get_blks_funcs (w:t) (fs:Syn.func list) : Syn.blk list = 
    match fs with
    | [] -> raise (Error "get_blks_funcs: not found")
    | (f,_,bs)::tl -> 
      if w = f then bs else get_blks_funcs w tl
  let get_blks (w:t) (p:Syn.pgm) : Syn.blk list = 
    match p with (fs,bs,_) -> 
      if w = ""
      then bs
      else get_blks_funcs w fs
  let get_childs (w:t) (p:Syn.pgm) : t list = 
    match p with (_,_,ctrl_edges) ->
      let edges_from_w = List.filter (fun e -> fst (fst e) = w) ctrl_edges in
      let dest_ws = List.map (fun e -> fst (snd e)) edges_from_w in
      dest_ws

  type lst = t list
  let empty_lst : lst = []
  let is_empty (x:lst) : bool = x = []
  let choose_work (x:lst) : t * lst = 
    match x with
    | [] -> raise (Error "choose_work: no work")
    | hd::tl -> (hd,tl)
  let rec works_add (ws:t list) (x:lst) : lst = 
    match ws with
    | [] -> x
    | hd::tl -> if List.mem hd x then works_add tl x else works_add tl (hd::x)
end
