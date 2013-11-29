exception Error of string

module type Eval = 
sig
  module Mem : Dom.Dom
  val init_mem : Mem.t
  val eval_blk : Syn.pgm -> Syn.blk -> Mem.t -> Mem.t
end

module ValueEval = 
struct 
  module Value = Dom.Pair (Itvl.Itvl) (Bool.Bool)
  module Id = 
  struct
    type t = string
    let compare = compare
    let to_string (x:t) : string = x
  end

(* The memory domain is optional: when a program point is unreachable,
   the abstract value on the point is None. *)
  module CoreMem = Dom.FinMap (Id) (Value)
  module Mem = Dom.Option (CoreMem)
  let init_mem : Mem.t = Some CoreMem.bot

  let rec eval_aexp (a:Syn.aexp) (m:CoreMem.t) : Value.t =
    match a with
    | Syn.Aexp_id x -> CoreMem.find x m
    | Syn.Aexp_const c -> ((Itvl.Z_inf_int c, Itvl.Z_inf_int c),
                           Bool.Bool.bot)
    | Syn.Aexp_bop (b,x,y) -> 
      let (vx,_) = eval_aexp x m in
      let (vy,_) = eval_aexp y m in
      (match b with
      | Syn.Bop_plus -> (Itvl.Itvl.plus vx vy,Bool.Bool.bot)
      | Syn.Bop_minus -> (Itvl.Itvl.minus vx vy,Bool.Bool.bot)
      | Syn.Bop_mult -> (Itvl.Itvl.mult vx vy,Bool.Bool.bot)
      | Syn.Bop_div -> (Itvl.Itvl.div vx vy,Bool.Bool.bot)
      )
    | Syn.Aexp_uop (u,x) ->
      let (vx,_) = eval_aexp x m in
      (match u with
      | Syn.Uop_minus -> (Itvl.Itvl.u_minus vx,Bool.Bool.bot)
      )

  let rec eval_bexp (b:Syn.bexp) (m:CoreMem.t) : Value.t = 
    match b with
    | Syn.Bexp_true -> (Itvl.Itvl.bot,Bool.Bool.Bool_true)
    | Syn.Bexp_false -> (Itvl.Itvl.bot,Bool.Bool.Bool_false)
    | Syn.Bexp_cmp (c,x,y) -> 
      let (vx,_) = eval_aexp x m in
      let (vy,_) = eval_aexp y m in
      (match c with
      | Syn.Cmp_le -> (Itvl.Itvl.bot,Itvl.Itvl.cmp_le vx vy)
      | Syn.Cmp_lt -> (Itvl.Itvl.bot,Itvl.Itvl.cmp_lt vx vy)
      | Syn.Cmp_ge -> (Itvl.Itvl.bot,Itvl.Itvl.cmp_ge vx vy)
      | Syn.Cmp_gt -> (Itvl.Itvl.bot,Itvl.Itvl.cmp_gt vx vy)
      | Syn.Cmp_eq -> (Itvl.Itvl.bot,Itvl.Itvl.cmp_eq vx vy)
      | Syn.Cmp_neq -> (Itvl.Itvl.bot,Itvl.Itvl.cmp_neq vx vy)
      )
    | Syn.Bexp_not x ->
      let (_,vx) = eval_bexp x m in
      (Itvl.Itvl.bot,Bool.Bool.sem_not vx)

  let eval_stmt (arg:Syn.id->Syn.id) (s:Syn.stmt) (om:Mem.t) : Mem.t = 
    match om with
    | None -> None
    | Some m -> 
      (match s with
      | Syn.Stmt_skip -> Some m
      | Syn.Stmt_assign (x,a) ->
        let v = eval_aexp a m in
        Some (CoreMem.add x v m)
      | Syn.Stmt_assert b ->
        let (_,v) = eval_bexp b m in
        if Bool.Bool.le v Bool.Bool.Bool_false
        then None
        else Some m
      | Syn.Stmt_call (f,e) ->
        let v = eval_aexp e m in
        let a = arg f in
        Some (CoreMem.add a v m)
      )

  let rec eval_blk_rec (arg:Syn.id->Syn.id) (b:Syn.blk) (om:Mem.t) : Mem.t = 
    match b with
    | [] -> om
    | hd::tl -> eval_blk_rec arg tl (eval_stmt arg hd om)

  let eval_blk (p:Syn.pgm) (b:Syn.blk) (om:Mem.t) : Mem.t = 
    let arg = Syn.get_arg p in
    eval_blk_rec arg b om
end

module AccessEval = 
struct
  module CoreMem = Dom.FinSet (ValueEval.Id)
  module Mem = Dom.Option (CoreMem)
  let init_mem : Mem.t = Some CoreMem.bot

  let rec eval_aexp (a:Syn.aexp) : CoreMem.t =
    match a with
    | Syn.Aexp_id x -> CoreMem.add x CoreMem.bot
    | Syn.Aexp_const c -> CoreMem.bot
    | Syn.Aexp_bop (b,x,y) -> CoreMem.join (eval_aexp x) (eval_aexp y)
    | Syn.Aexp_uop (u,x) -> eval_aexp x

  let rec eval_bexp (b:Syn.bexp) : CoreMem.t = 
    match b with
    | Syn.Bexp_true -> CoreMem.bot
    | Syn.Bexp_false -> CoreMem.bot
    | Syn.Bexp_cmp (c,x,y) ->  CoreMem.join (eval_aexp x) (eval_aexp y)
    | Syn.Bexp_not x -> eval_bexp x

  let eval_stmt 
      (arg:Syn.id->Syn.id) (s:Syn.stmt) : CoreMem.t = 
    match s with
    | Syn.Stmt_skip -> CoreMem.bot
    | Syn.Stmt_assign (x,a) -> CoreMem.add x (eval_aexp a)
    | Syn.Stmt_assert b -> eval_bexp b
    | Syn.Stmt_call (f,e) -> CoreMem.add (arg f) (eval_aexp e)

  let rec eval_blk_rec (arg:Syn.id->Syn.id) (b:Syn.blk) : CoreMem.t = 
    match b with
    | [] -> CoreMem.bot
    | hd::tl -> CoreMem.join (eval_blk_rec arg tl) (eval_stmt arg hd)

  let eval_blk (p:Syn.pgm) (b:Syn.blk) (om:Mem.t) : Mem.t = 
    let arg = Syn.get_arg p in
    Mem.join om (Some (eval_blk_rec arg b))
end

module CallEval = 
struct
  module CoreMem = Dom.FinSet (ValueEval.Id)
  module Mem = Dom.Option (CoreMem)
  let init_mem : Mem.t = Some CoreMem.bot

  let eval_stmt (s:Syn.stmt) : CoreMem.t = 
    match s with
    | Syn.Stmt_skip -> CoreMem.bot
    | Syn.Stmt_assign (x,a) -> CoreMem.bot
    | Syn.Stmt_assert b -> CoreMem.bot
    | Syn.Stmt_call (f,e) -> CoreMem.add f CoreMem.bot

  let rec eval_blk_rec (b:Syn.blk) : CoreMem.t = 
    match b with
    | [] -> CoreMem.bot
    | hd::tl -> CoreMem.join (eval_blk_rec tl) (eval_stmt hd)

  let eval_blk (p:Syn.pgm) (b:Syn.blk) (om:Mem.t) : Mem.t = 
    Mem.join om (Some (eval_blk_rec b))
end

