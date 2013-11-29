(*
  Shape Analysis as a Generalized Path Problem
  Thomas Reps' PEPM '95 paper
  Sukyoung Ryu 7/16/2001
*)

analysis Shape =
 ana

   set PgmPoint = /Ast.exp/
   set Var = /Ast.var/
   set Shape = /Ast.shape/
   set Dfv = (PgmPoint * Var)            (* data flow variable *)
   set Dff = /Ast.dff/                   (* data flow function *)
   set Rhs = Shape + Dfv + Dff
   set Eqn = Dfv -> Rhs
   set Node = /Ast.node/ + Dfv
   set Label = /Ast.label/
   set Edge = Node * Node * Label
   set EdG = Node * Edge

   fun others (q,x) = { (q,z) => (q,z) | z from /Ast.vars/, not(z=x) }

   (* Setup: PgmPoint * PgmPoint -> Setup *)
   eqn Setup (/Ast.Ass(x,Atm _)/, q) = { (q,/x/) => /Ast.at/ } + others(q,/x/)
     | Setup (/Ast.Read(x)/, q) = { (q,/x/) => /Ast.at/ } + others(q,/x/)
     | Setup (/Ast.Ass(x,Nil)/, q) = { (q,/x/) => /Ast.nil/ } + others(q,/x/)
     | Setup (p as /Ast.Ass(x,y)/, q) = { (q,/x/) => (p,/y/) } + others(q,/x/)
     | Setup (p as /Ast.Ass(x,Car(y))/, q) =
       { (q,/x/) => /Ast.CarF(p,y)/ } + others(q,/x/)
     | Setup (p as /Ast.Ass(x,Cdr(y))/, q) =
       { (q,/x/) => /Ast.CdrF(p,y)/ } + others(q,/x/)
     | Setup (p as /Ast.Ass(x,Cons(y,z))/, q) =
       { (q,/x/) => /Ast.ConsF((p,y),(p,z))/ } + others(q,/x/)

   (* Edg: (Dfv * Rhs) -> power Edge *)
   eqn Edg ((q,x), /([], Ast.At)/) = {(/Ast.Atom/, (q,x), /Ast.Id/)}
     | Edg ((q,x), /([], Ast.Nil)/) = {(/Ast.Empty/, (q,x), /Ast.Id/)}
     | Edg ((q,x), (p,y)) = {((p,y), (q,x), /Ast.Id/)}
     | Edg ((q,x), /Ast.ConsF((p,y),(p,z))/) =
       { ((p,y),(q,x),/Ast.Hd/), ((p,z),(q,x),/Ast.Tl/) }
     | Edg ((q,x), /Ast.CarF(p,y)/) = {((p,y), (q,x), /Ast.HdI/)}
     | Edg ((q,x), /Ast.CdrF(p,y)/) = {((p,y), (q,x), /Ast.TlI/)}

 end
