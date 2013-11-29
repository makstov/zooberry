(*
  Time Analysis among Expressions for multithreaded Java's core
  Sukyoung Ryu 7/3/2001
*)

analysis Time =
 ana
   set Exp = /Ast.exp/
   set Sc = power Exp
            constraint
              var = {P, S} index Exp
	      rhs = var
                  | exp(Exp) : atomic

   eqn Col /Ast.Var(x)/ = {}
     | Col /Ast.Ass(x,e') as e/ =
       { P@/e/ <- exp(/e'/), S@/e'/ <- exp(/e/) } + Col /e'/
     | Col /Ast.New(c)/ = {}
     | Col /Ast.This/ = {}
     | Col /Ast.Seq(e1,e2) as e/ =
       { P@(x = /hd(e2)/) <- exp(/e1/), P@/e/ <- exp(/e2/),
         S@/e1/ <- exp(/hd(e2)/), S@/e2/ <- exp(/e/) }
       + Col /e1/ + Col /e2/
     | Col /Ast.Cond(e1,e2,e3) as e/ =
       { P@(x = /hd(e2)/) <- exp(/e1/), P@(x = /hd(e3)/) <- exp(/e1/),
         P@/e/ <- exp(/e2/), P@/e/ <- exp(/e3/),
         S@/e1/ <- /hd(e2)/, S@/e1/ <- /hd(e3)/,
         S@/e2/ <- exp(/e/), S@/e3/ <- exp(/e/) }
       + Col /e1/ + Col /e2/ + Col /e3/
     | Col /Ast.Thrw(e') as e/ =
       { P@/e/ <- exp(/e1/), S@/e1/ <- exp(/e/) } + Col /e'/
     | Col /Ast.Try(e1,c,x,e2) as e/ =
       { P@(x = /hd(e2)/) <- exp(/e1/), P@/e/ <- exp(/e1/), P@/e/ <- exp(/e2/),
         S@/e1/ <- /hd(e2)/, S@/e1/ <- exp(/e/), S@/e2/ <- exp(/e/) }
       + Col /e1/ + Col /e2/
     | Col /Ast.App(e1,m,e2)/ =
       let val /em/ = /Ast.body(m)/
       in  { P@(x = /hd(e2)/) <- exp(/e1/), P@(x = /hd(em)/) <- exp(/e2/),
             P@/e/ <- exp(/em/), S@/e1/ <- /hd(e2)/, S@/e2/ <- /hd(em)/,
             S@/em/ <- exp(/e/) }
           + Col /e1/ + Col /e2/
       end
     | Col /Ast.Start(e') as e/ =
       { P@/e/ <- exp(/e'/), S@/e'/ <- exp(/e/) } + Col /e'/
     | Col /Ast.Wait(e') as e/ =
       { P@/e/ <- exp(/e'/), S@/e'/ <- exp(/e/) } + Col /e'/
     | Col /Ast.Notif(e') as e/ =
       { P@/e/ <- exp(/e'/), S@/e'/ <- exp(/e/) } + Col /e'/
     | Col /Ast.Xthrw(e1,e2) as e/ =
       { P@(x = /hd(e2)/) <- exp(/e1/), P@/e/ <- exp(/e2/),
         S@/e1/ <- exp(/hd(e2)/), S@/e2/ <- exp(/e/) }
       + Col /e1/ + Col /e2/

 end
