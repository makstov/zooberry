(*
   Control flow analysis for ML's core.
   Sukyoung Ryu 6/28/2001
*)

analysis Cfa =
 ana
   set Var = /Ast.var/
   set Exp = /Ast.exp/
   set Edges = power Exp
               constraint
                 var = {X} index Var + Exp
                 rhs = var
                   | app(X, X)
                   | lam(Var, Exp):atomic

   fun exps /Ast.Var(x) as e/ = { /e/ }
     | exps /Ast.Lam(x,body) as e/ = { /e/ } + exps /body/
     | exps /Ast.App(e1,e2) as e/ =
       { /e/ } + exps /e1/ + exps /e2/
     | exps /Ast.Exn(k,e') as e/ = { /e/ } + exps /e'/
     | exps /Ast.Dcn(e') as e/ = { /e/ } + exps /e'/
     | exps /Ast.Case(e1,k,e2,e3) as e/ =
       { /e/ } + exps /e1/ + exps /e2/ + exps /e3/
     | exps /Ast.Fix(f,x,e1,e2) as e/ =
       { /e/ } + exps /e1/ + exps /e2/
     | exps /Ast.Rais(e') as e/ = { /e/ } + exps /e'/
     | exps /Ast.Prais(e',k) as e/ = { /e/ } + exps /e'/
     | exps /Ast.Mrais(e',ks) as e/ = { /e/ } + exps /e'/
     | exps /Ast.Hndl(e1,x,e2) as e/ = { /e/ } + exps /e1/ + exps /e2/
     | exps /Ast.Unit as e/ = { /e/ }

   eqn Eqn /Ast.Var(x)/ = {}
     | Eqn /Ast.Lam(x,body) as e/ =
       { X@/e/ <- lam(/x/,/body/) } + Eqn /body/
     | Eqn /Ast.App(e1,e2) as e/ =
       { X@/e/ <- app(X@/e1/, X@/e2/) } + Eqn /e1/ + Eqn /e2/
     | Eqn /Ast.Exn(k,e)/ = Eqn /e/
     | Eqn /Ast.Dcn(e'') as e/ =
       { X@/e/ <- X@/e'/ | e' from exps(/program/), /type(e')/ = /type(e)/ }
       + Eqn /e''/
     | Eqn /Ast.Case(e1,k,e2,e3) as e/ =
       { X@/e/ <- X@/e2/, X@/e/ <- X@/e3/ } + Eqn /e1/ + Eqn /e2/ + Eqn /e3/
     | Eqn /Ast.Fix(f,x,e1,e2) as e/ =
       { X@/f/ <- lam(/x/,/e1/), X@/e/ <- X@/e2/ } + Eqn /e1/ + Eqn /e2/
     | Eqn /Ast.Rais(e)/ = Eqn /e/
     | Eqn /Ast.Prais(e,k)/ = Eqn /e/
     | Eqn /Ast.Mrais(e,ks)/ = Eqn /e/
     | Eqn /Ast.Hndl(e1,x,e2) as e/ =
       { X@/e/ <- X@/e1/, X@/e/ <- X@/e2/ } + Eqn /e1/ + Eqn /e2/
     | Eqn /Ast.Unit/ = {}

   ccr   X@a <- app(X@b, X@c), X@b <- lam(x, body)
         -----------------------------------------
         X@a <- X@body, X@x <- X@c
 end
