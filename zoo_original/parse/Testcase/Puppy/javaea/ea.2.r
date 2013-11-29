(*
   Exception analysis for ML's core.
   Sukyoung Ryu 7/25/2001
*)

signature CFA =
 sig
  set Fns = power /Ast.exp/
  eqn Eqn: /Ast.exp/:index -> Fns
 end

analysis Ea (Cfa:CFA) =
 ana
   set Var = /Ast.var/
   set Con = /Ast.con/
   set Exp = /Ast.exp/
   set Edges = power Exn
               constraint
                 var = {X, P} index Var + Exp
                 rhs = var
                   | con(Con) : atomic
                   | cap(var, Exp, Con)
                   | min(var, Exp, power Con)

   eqn Eqn (/Ast.Var(x)/, f) = { X@f <- X@/owner(x)/ }
     | Eqn (/Ast.Lam(x,body)/, f) = Eqn (/body/, /nameLam Ast.Lam(x,body)/)
     | Eqn (/Ast.App(e1,e2)/, f) =
       let val lams = post Cfa.Eqn@/e1/
       in  { X@f <- X@/nameLam lam/ | lam from lams }
           + { P@f <- P@/nameLam lam/ | lam from lams }
           + { X@/nameLam lam/ <- X@f | lam from lams }
           + Eqn (/e1/, f) + Eqn (/e2/, f)
       end
     | Eqn (/Ast.Exn(k,e)/, f) = { X@f <- con(/k/) } + Eqn (/e/, f)
     | Eqn (/Ast.Dcn(e)/, f) = Eqn (/e/, f)
     | Eqn (/Ast.Case(e1,k,e2,e3)/, f) =
       Eqn (/e1/, f) + Eqn (/e2/, f) + Eqn (/e3/, f)
     | Eqn (/Ast.Fix(g,x,e1,e2)/, f) = Eqn (/e1/, /g/) + Eqn (/e2/, f)
     | Eqn (/Ast.Rais(e)/, f) = { P@f <- X@f } + Eqn (/e/, f)
     | Eqn (/Ast.Prais(e,k)/, f) =
       { P@f <- cap(X@f,/e/,/k/) } + Eqn (/e/, f)
     | Eqn (/Ast.Mrais(e,ks)/, f) =
       let val K = /Ast.list2set ks/
       in  { P@f <- minus(X@f,/e/,K) } + Eqn (/e/, f)
       end
     | Eqn (/Ast.Hndl(e1,x,e2)/, f) =
       let val (hndlee, hndler) = /nameHndl Ast.Hndl(e1,x,e2)/
       in  { X@f <- X@hndler, P@f <- P@hndler, X@hndler <- X@f,
             X@f <- X@hndlee } + Eqn (/e1/, hndlee) + Eqn (/e2/, hndler)
       end
     | Eqn (/Ast.Unit/, f) = {}

   cim con(k) = {k}
   cim cap(X,/e/,k) = if /Ast.exnArg(e)/ then X else { x | x from X, x = k }
   cim minus(X,/e/,K) = if /Ast.exnArg(e)/ then X
                        else { x | x from X, not (x in K) }

 end
