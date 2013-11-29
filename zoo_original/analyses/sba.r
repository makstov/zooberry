(*
   Set-based analysis for Lambda Calculus
   Kwangkeun Yi 6/20/2001
*)

analysis Sba = 
 ana
   set Var = /Ast.id/
   set Exp = /Ast.exp/
   set Val = power Exp
             constraint
               var = {X} index Var + Exp
               rhs = var
                   | app(var, var)
                   | lam(Var, Exp) : atomic

   eqn Col /Ast.Var(x)/ = {}
     | Col /Ast.Lam(x,body) as e/ = { X@/e/ <- lam(/x/,/body/) }
                                  + Col /body/
     | Col /Ast.App(e,e') as e/ = { X@/e/ <- app(X@/e/, X@/e'/) }
                                  + Col /e/ + Col /e'/

   ccr   X@a <- app(X@b, X@c), X@b <- lam(/x/, /body/)
         -----------------------------------------
         X@a <- X@/body/, X@/x/ <- X@c 

 end
