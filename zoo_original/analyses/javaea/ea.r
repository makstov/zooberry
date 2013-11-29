(*
  Exception Analysis for multithreaded Java's core
  Sukyoung Ryu 7/3/2001
*)

signature CLASS =
 sig
  set Cls = power /Ast.cls/
  eqn Sol: /Ast.exp/:index -> Cls
 end

signature CONCUR =
 sig
  eqn Sol: /Ast.cls * Ast.exp * Ast.cls/: index -> power /Ast.exp/
 end

analysis Ea (Class: CLASS, Concur: CONCUR) =
 ana
   set Exp = /Ast.exp/
   set Var = /Ast.var/
   set Exn = /Ast.cls/
   set Solution = power Exn
                  constraint
		    var = X index Var + Exp
		    rhs = var
                      | class(/Ast.exp/)
                      | exn(Exn)
                      | app(/Ast.exp/, Var)
                      | minus(var, Exn) : atomic

   eqn Col /Ast.Var(x)/ = {}
     | Col /Ast.Ass(x,e') as e/ = { X@/e/ <- X@/e'/ } + Col /e'/
     | Col /Ast.New(c)/ = {}
     | Col /Ast.This/ = {}
     | Col /Ast.Seq(e1,e2) as e/ =
       { X@/e/ <- X@/e1/, X@/e/ <- X@/e2/ } + Col /e1/ + Col /e2/
     | Col /Ast.Cond(e1,e2,e3) as e/ =
       { X@/e/ <- X@/e1/, X@/e/ <- X@/e2/, X@/e/ <- X@/e3/ }
       + Col /e1/ + Col /e2/ + Col /e3/
     | Col /Ast.Thrw(e') as e/ =
       { X@/e/ <- class(e'), X@/e/ <- X@/e'/ } + Col /e'/
     | Col /Ast.Try(e1,c,x,e2) as e/ =
       { X@/e/ <- minus(X@/e1/, /c/), X@/e/ <- X@/e2/ }
       + Col /e1/ + Col /e2/
     | Col /Ast.App(e1,m,e2)/ =
       { X@/e/ <- app(/e1/, /m/), X@/e/ <- X@/e1/, X@/e/ <- X@/e2/ }
       + Col /e1/ + Col /e2/
     | Col /Ast.Start(e') as e/ = { X@/e/ <- X@/e'/ } + Col /e'/
     | Col /Ast.Wait(e') as e/ = { X@/e/ <- X@/e'/ } + Col /e'/
     | Col /Ast.Notif(e') as e/ = { X@/e/ <- X@/e'/ } + Col /e'/
     | Col /Ast.Xthrw(e1,e2) as e/ =
       { X@e' <- class(e1) | /c/ from /Ast.owner(e)/,
                             /c'/ from post Class.Sol@/e2/,
                             e' from post Concur.Sol@/(c,e,c')/ }
       + { X@/e/ <- X@/e1/, X@/e/ <- X@/e2/ }
       + Col /e1/ + Col /e2/

   ccr  X@a <- class(/e/), /c/ in post Class.Sol@/e/
       ----------------------------------------------
            X@a <- exn(/c/)

   ccr  X@a <- app(/e/, /m/), /c/ in post Class.Sol@/e/,
                              /m/ in /Ast.methods(c)/
       --------------------------------------------------
            X@a <- X@/Ast.mkName(c,m)/

   cim minus(X,k) = { x | x from X, not (x in (/Ast.clos(k)/)) }

 end 
