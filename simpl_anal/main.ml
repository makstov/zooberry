exception Error of string

let main (p:Syn.pgm) : unit = 

  let module PreAnal = Anal.Anal (Work.FlowInsenWork) (Eval.ValueEval) in
  let pre_restrict_mem
      (x:Work.FlowInsenWork.t) (y:Work.FlowInsenWork.t) (m:Eval.ValueEval.Mem.t)
      : Eval.ValueEval.Mem.t = 
    m 
  in
  let pre_result = PreAnal.anal_i p pre_restrict_mem in

  let module AccessAnal = Anal.Anal (Work.FuncSenWork) (Eval.AccessEval) in
  let access_restrict_mem 
      (x:Work.FuncSenWork.t) (y:Work.FuncSenWork.t) (m:Eval.AccessEval.Mem.t)
      : Eval.AccessEval.Mem.t = 
    if x = y then m else Some Eval.AccessEval.CoreMem.bot
  in
  let access_result = AccessAnal.anal_o p access_restrict_mem in

  let module CallAnal = Anal.Anal (Work.FuncSenWork) (Eval.CallEval) in
  let call_restrict_mem 
      (x:Work.FuncSenWork.t) (y:Work.FuncSenWork.t) (m:Eval.CallEval.Mem.t)
      : Eval.CallEval.Mem.t = 
    if x = y then m else Some Eval.AccessEval.CoreMem.bot
  in
  let call_result = CallAnal.anal_o p call_restrict_mem in

  let trans_callees (f:Syn.id) : Eval.CallEval.CoreMem.t = 
    let rec trans_callees_rec (callees:Eval.CallEval.CoreMem.t) 
        : Eval.CallEval.CoreMem.t = 
      let new_callees = 
        Eval.CallEval.CoreMem.fold
          (fun f acc -> 
            match CallAnal.State.find f call_result with
            | None -> acc
            | Some f_callees -> Eval.CallEval.CoreMem.join acc f_callees
          )
          callees callees
      in
      if Eval.CallEval.CoreMem.le new_callees callees
      then callees 
      else trans_callees_rec new_callees
    in
    trans_callees_rec (Eval.CallEval.CoreMem.add f Eval.CallEval.CoreMem.bot)
  in
  let trans_access (f:Syn.id) : Eval.AccessEval.CoreMem.t = 
    Eval.CallEval.CoreMem.fold
      (fun f acc ->
        match AccessAnal.State.find f access_result with
        | None -> acc
        | Some f_access -> Eval.AccessEval.CoreMem.join acc f_access
      )
      (trans_callees f) Eval.AccessEval.CoreMem.bot
  in

  let module MainAnal = Anal.Anal (Work.FlowSenWork) (Eval.ValueEval) in
  let main_restrict_mem 
      (x:Work.FlowSenWork.t) (y:Work.FlowSenWork.t) (om:Eval.ValueEval.Mem.t)
      : Eval.ValueEval.Mem.t = 
    if fst x = fst y then om
    else 
      let access_y : Eval.AccessEval.CoreMem.t = trans_access (fst y) in
      match om with 
      | None -> None
      | Some m -> 
        Some 
          (Eval.ValueEval.CoreMem.filter
             (fun x _ -> Eval.AccessEval.CoreMem.mem x access_y)
             m
          )
  in
  let main_result = MainAnal.anal_i p main_restrict_mem in
  ()
