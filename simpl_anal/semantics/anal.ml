exception Error of string

module Anal (W:Work.Work) (E:Eval.Eval) =
struct 
  module State = Dom.FinMap (W) (E.Mem)

  let anal_step_mem (w:W.t) (om:E.Mem.t) (p:Syn.pgm) : E.Mem.t =
    let blks = W.get_blks w p in
    let new_oms = List.map (fun b -> E.eval_blk p b om) blks in
    let new_om = 
      List.fold_left 
        (fun acc om -> E.Mem.join acc om)
        E.Mem.bot new_oms
    in
    new_om

  let anal_step
      (w:W.t) (s:State.t) (p:Syn.pgm) (restrict_mem:W.t->W.t->E.Mem.t->E.Mem.t)
      : (State.t * W.t list) =
    let om = State.find w s in
    let new_om = anal_step_mem w om p in
    let next_ws = W.get_childs w p in
    let (new_s,updated_ws) = 
      List.fold_left
        (fun (new_s,updated_ws) next_w ->
          let restricted_mem = restrict_mem w next_w new_om in
          let next_w_mem = State.find next_w new_s in
          if E.Mem.le restricted_mem next_w_mem
          then (new_s,updated_ws)
          else (State.add 
                  next_w 
                  (E.Mem.widen next_w_mem restricted_mem)
                  new_s,
                next_w::updated_ws)
        )
        (s,[]) next_ws
    in
    (new_s,updated_ws)

  let rec anal_steps
      (wl:W.lst) (s:State.t) (p:Syn.pgm) 
      (restrict_mem:W.t->W.t->E.Mem.t->E.Mem.t)
      : State.t =
    if W.is_empty wl
    then s
    else 
      let (w,left_wl) = W.choose_work wl in
      let (new_s,updated_ws) = anal_step w s p restrict_mem in
      let new_wl = W.works_add updated_ws left_wl in
      anal_steps new_wl new_s p restrict_mem

  (* anal_i returns input memory of analysis result *)
  let anal_i (p:Syn.pgm) (restrict_mem:W.t->W.t->E.Mem.t->E.Mem.t) : State.t =
    let init_worklist = W.works_add [W.init] W.empty_lst in
    let init_state = State.add W.init E.init_mem State.bot in
    let anal_result = anal_steps init_worklist init_state p restrict_mem in
    anal_result

  (* anal_o returns output memory of analysis result *)
  let anal_o (p:Syn.pgm) (restrict_mem:W.t->W.t->E.Mem.t->E.Mem.t) 
      : State.t =
    let s = anal_i p restrict_mem in
    State.mapi (fun w om -> anal_step_mem w om p) s
end
