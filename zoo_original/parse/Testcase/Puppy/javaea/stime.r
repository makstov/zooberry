(*
  Time Analysis among Synchronizing Expressions for multithreaded Java's core
  Sukyoung Ryu 7/3/2001
*)

analysis Time =
 ana
   set Exp = /Ast.exp/
   set Sc = power Exp
            constraint
	      var = {P, S} index Exp
	      rhs = var
                  | p(Exp)
                  | s(Exp)
                  | exp(Exp) : atomic

   eqn Col /Ast.Var(x)/ = {}
     | Col /Ast.Ass(x,e') as e/ =
       { P@/e/ <- p(/e'/), S@/e'/ <- S@/e/ } + Col /e'/
     | Col /Ast.New(c)/ = {}
     | Col /Ast.This/ = {}
     | Col /Ast.Seq(e1,e2) as e/ =
       { P@(x = /hd(e2)/) <- p(/e1/), P@/e/ <- p(/e2/),
         S@/e1/ <- s(/hd(e2)/), S@/e2/ <- S@/e/ }
       + Col /e1/ + Col /e2/
     | Col /Ast.Cond(e1,e2,e3) as e/ =
       { P@(x = /hd(e2)/) <- p(/e1/), P@(x = /hd(e3)/) <- p(/e1/),
         P@/e/ <- p(/e1/), S@/e1/ <- S@/e/, S@/e2/ <- S@/e/, S@/e3/ <- S@/e/ }
       + Col /e1/ + Col /e2/ + Col /e3/
     | Col /Ast.Thrw(e') as e/ =
       { P@/e/ <- p(/e1/), S@/e1/ <- S@/e/ } + Col /e'/
     | Col /Ast.Try(e1,c,x,e2) as e/ =
       { P@(x = /hd(e2)/) <- p(/e1/), P@/e/ <- p(/e1/),
         S@/e1/ <- S@/e/, S@/e2/ <- S@/e/ }
       + Col /e1/ + Col /e2/
     | Col /Ast.App(e1,m,e2)/ =
       let val /em/ = /Ast.body(m)/
       in  { P@(x = /hd(e2)/) <- p(/e1/), P@(x = /hd(em)/) <- p(/e2/),
             P@/e/ <- p(/em/), S@/e1/ <- s(/hd(e2)/), S@/e2/ <- s(/hd(em)/),
             S@/em/ <- S@/e/ }
           + Col /e1/ + Col /e2/
       end
     | Col /Ast.Start(e') as e/ =
       { P@/e/ <- p(/e1/), S@/e1/ <- S@/e/ } + Col /e'/
     | Col /Ast.Wait(e') as e/ =
       { P@/e/ <- p(/e1/), S@/e1/ <- exp(/e/) } + Col /e'/
     | Col /Ast.Notif(e') as e/ =
       { P@/e/ <- p(/e1/), S@/e1/ <- exp(/e/) } + Col /e'/
     | Col /Ast.Xthrw(e1,e2) as e/ =
       { P@(x = /hd(e2)/) <- p(/e1/), P@/e/ <- p(/e2/),
         S@/e1/ <- s(/hd(e2)/), S@/e2/ <- S@/e/ }
       + Col /e1/ + Col /e2/

   ccr  P@a <- p(/e/), /Ast.synch(e)/ = true
       -----------------------------------------
            P@a <- exp(/e/)

   ccr  P@a <- p(/e/), /Ast.synch(e)/ = false
       -----------------------------------------
            P@a <- P@/e/

   ccr  S@a <- s(/e/), /Ast.synch(e)/ = true
       -----------------------------------------
            S@a <- exp(/e/)

   ccr  S@a <- s(/e/), /Ast.synch(e)/ = false
       -----------------------------------------
            S@a <- S@/e/

 end
