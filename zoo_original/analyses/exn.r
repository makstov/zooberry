(*
  Exception Analysis form ML's core
  Kwangkeun Yi 6/30/2001
*)

signature CFA =
 sig
  lattice Env
  lattice Fns = power /Ast.exp/
  eqn Lam: /Ast.exp/:index * Env -> Fns
 end

analysis ExnAnal(Cfa: CFA) =
 ana
   set Exp = /Ast.exp/
   set Var = /Ast.var/
   set Exn = /Ast.exn/
   set Solution = power Exn
                  constraint
		    var = {X, P} index Var + Exp
		    rhs = var
                      | app_x(/Ast.exp/, var)
                      | app_p(/Ast.exp/, var)
                      | exn(Exn) 			 : atomic
                      | minus(var, /Ast.exp/, power Exn) : atomic
                      | cap(var, /Ast.exp/, Exn)	 : atomic

   eqn Col /Ast.Var(x)/ = {}
     | Col /Ast.Const/ = {}
     | Col /Ast.Lam(x,e)/ = Col /e/
     | Col /e as Ast.Fix(f,x,e',e'')/ = Col /e'/ + Col /e''/
                                 + { X@/e/ <- X@/e''/, P@/e/ <- P@/e''/ }
     | Col /e as Ast.Con(e',k)/ = Col /e'/
				+ { X@/e/ <- exn(/k/), P@/e/ <- P@/e'/ }
     | Col /e as Ast.Decon(e')/ = Col /e'/
				+ { X@/e/ <- X@/e'/, P@/e/ <- P@/e'/ }
     | Col /e as Ast.Exn(k,e')/ = Col /e'/
				+ { X@/e/ <- exn /k/, X@/e/ <- X@/e'/ }
     | Col /e as Ast.App(e',e'')/ = Col /e'/ + Col /e''/
				+ { X@/e/ <- app_x(/e'/, X@/e''/),
				    P@/e/ <- app_p(/e'/, X@/e''/),
				    P@/e/ <- P@/e'/, P@/e/ <- P@/e''/ }
     | Col /e as Ast.Case(e',k,e'',e''')/ =
		Col /e'/ + Col /e''/ + Col /e'''/
		+ { X@/e/ <- X@/e''/, X@/e/ <- X@/e'''/ }
		+ { P@/e/ <- P@/e'/, P@/e/ <- P@/e''/, P@/e/ <- P@/e'''/ }
     | Col /e as Ast.Raise(e')/ = Col /e'/ + { P@e <- X@/e'/ }
     | Col /e as Ast.Mraise(e',Ks)/ =
		let
		  val K = /Ast.list2set Ks/
		in
		  Col /e'/ + { P@e <- minus(X@/e'/,/e'/, K) }
		end
     | Col /e as Ast.Praise(e', k)/ =
		Col /e'/ + { P@/e/ <- cap(X@/e'/,/e'/,/k/) }
     | Col /e as Ast.Handle(e', f as Ast.Lam(x,e''))/ =
		Col /e'/ + Col /e''/
		+ { X@/e/ <- X@/e'/, X@/e/ <- app_x(/f/, P@/e'/) }
		+ { X@/x/ <- P@/e'/, P@/e/ <- app_p(/f/, P@/e'/) }

   (* constraint closure rule *)

   ccr  X@a <- app_x(/e/,X@b), /Ast.Lam(x,e')/ in post Cfa.Lam@/e/
       -----------------------------------------
            X@a <- X@/e'/, X@/x/ <- X@b

   ccr  X@a <- app_x(/e/,P@b), /Ast.Lam(x,e')/ in post Cfa.Lam@/e/
       -----------------------------------------
            X@a <- X@/e'/, X@/x/ <- P@b

   ccr  P@a <- app_p(/e/,X@b), /Ast.Lam(x,e')/ in post Cfa.Lam@/e/
       -----------------------------------------
            P@a <- P@/e'/, X@/x/ <- X@b

   ccr  P@a <- app_p(/e/,P@b), /Ast.Lam(x,e')/ in post Cfa.Lam@/e/
       -----------------------------------------
            P@a <- P@/e'/, X@/x/ <- P@b

   (* constraint image definition *)

   cim exn(k) = {k}
   cim minus(X,/e/,K) = if /Ast.exncarryexn(e)/ then X
                        else { x | x from X, not (x in K) }
   cim cap(X,/e/,k) = if /Ast.exncarryexn(e)/ then X
		      else { x | x from X, x = k }

 end 
