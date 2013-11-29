(*
  Concurrency Analysis for multithreaded Java's core
  Sukyoung Ryu 7/4/2001
*)

signature CLASS =
 sig
   set Cls = power /Ast.cls/
   eqn Sol: /Ast.exp/:index -> Cls
 end

signature TIME =
 sig
   set Exp = /Ast.exp/
   set Sc = power Exp
            constraint
              var = {P, S} index Exp
              rhs = var
                  | exp(Exp) : atomic
   eqn Col: Exp:index -> power Exp
 end

signature STIME =
 sig
   set Exp = /Ast.exp/
   set Sc = power Exp
            constraint
	      var = {P, S} index Exp
	      rhs = var
                  | p(Exp)
                  | s(Exp)
                  | exp(Exp) : atomic
 end

analysis Concur (Class: CLASS, Time: TIME, Stime: STIME) =
 ana
   set Exp = /Ast.exp/
   set Sc = power Exp
            constraint
              var = {U, D} index /Ast.cls * Ast.exp * Ast.cls/
              rhs = var
                  | exp(Exp) : atomic

   fun clos (ftn, e) =
     let fun nth 0 = { e }
           | nth n = + { post ftn@e' | e' from (nth (n-1)) }
     in  + { nth n | n from {0 ... /Ast.numExps()/} }
     end

   eqn Sol /(c,e,c')/ =
       { e' | /e1/ from post Stime.P@/e/, /e2/ from post Stime.S@/e/,
              /e1'/ from post U@/(c,e1,c')/,
              /e2'/ from post D@/(c,e2,c')/,
              e' from (clos(Time.S, /e1'/) * clos(Time.P, /e2'/)) }

   eqn Dup /(c,Ast.Ass(_,e),c')/ = Dup /c,e,c'/
     | Dup /(c,Ast.Seq(e1,e2),c')/ = Dup /c,e1,c'/ + Dup /c,e2,c'/
     | Dup /(c,Ast.Cond(e1,e2,e3),c')/ =
       Dup /c,e1,c'/ + Dup /c,e2,c'/ + Dup /c,e3,c'/
     | Dup /(c,Ast.Thrw(e),c')/ = Dup /c,e,c'/
     | Dup /(c,Ast.Try(e1,_,_,e2),c')/ = Dup /c,e1,c'/ + Dup /c,e2,c'/
     | Dup /(c,Ast.App(e1,_,e2),c')/ = Dup /c,e1,c'/ + Dup /c,e2,c'/
     | Dup /(c,Ast.Start(e),c')/ = Dup /c,e,c'/
     | Dup /(c,Ast.Wait(e') as e,c')/ =
       { U@/(c,e,c')/ <- exp(e2) | /Ast.Notif(e1) as e2/ from /Ast.exps(c')/,
                                   /c/ in /Ast.owner(e)/,
                                   not ((Class.Sol@/e'/*Class.Sol@/e1/)={}) }
     | Dup /(c,Ast.Notif(e') as e,c')/ =
       { U@/(c,e,c')/ <- exp(e2) | /Ast.Wait(e1) as e2/ from /Ast.exps(c')/,
                                   /c/ in /Ast.owner(e)/,
                                   not ((Class.Sol@/e'/*Class.Sol@/e1/)={}) }
     | Dup /(c,Ast.Xthrw(e1,e2),c')/ = Dup /c,e1,c'/ + Dup /c,e2,c'/
     | Dup /(c,_,c')/ = {}

   eqn Ddw /(c,Ast.Ass(_,e),c')/ = Ddw /c,e,c'/
     | Ddw /(c,Ast.Seq(e1,e2),c')/ = Ddw /c,e1,c'/ + Ddw /c,e2,c'/
     | Ddw /(c,Ast.Cond(e1,e2,e3),c')/ =
       Ddw /c,e1,c'/ + Ddw /c,e2,c'/ + Ddw /c,e3,c'/
     | Ddw /(c,Ast.Thrw(e),c')/ = Ddw /c,e,c'/
     | Ddw /(c,Ast.Try(e1,_,_,e2),c')/ = Ddw /c,e1,c'/ + Ddw /c,e2,c'/
     | Ddw /(c,Ast.App(e1,_,e2),c')/ = Ddw /c,e1,c'/ + Ddw /c,e2,c'/
     | Ddw /(c,Ast.Start(e),c')/ = Ddw /c,e,c'/
     | Ddw /(c,Ast.Wait(e') as e,c')/ =
       { D@/(c,e,c')/ <- exp(e2) | /Ast.Notif(e1) as e2/ from /Ast.exps(c')/,
                                   /c/ in /Ast.owner(e)/,
                                   not ((Class.Sol@/e'/*Class.Sol@/e1/)={}) }
     | Ddw /(c,Ast.Notif(e') as e,c')/ =
       { D@/(c,e,c')/ <- exp(e2) | /Ast.Wait(e1) as e2/ from /Ast.exps(c')/,
                                   /c/ in /Ast.owner(e)/,
                                   not ((Class.Sol@/e'/*Class.Sol@/e1/)={}) }
     | Ddw /(c,Ast.Xthrw(e1,e2),c')/ = Ddw /c,e1,c'/ + Ddw /c,e2,c'/
     | Ddw /(c,_,c')/ = {}

   ccr  U@/c'',e2,c'/ <- exp(/e3/), not(c'' = c'),
        /Ast.Notif(e1)/ in /Ast.exps(c'')/, /c/ in /Ast.classes()/,
        /Ast.Wait(e)/ in /Ast.exps(c)/, /e2/ in post Stime.P@/Ast.Notif(e1)/,
        not ((Class.Sol@/e/*Class.Sol@/e1/)={})
       -------------------------------------------------------------
            U@/c,Ast.Wait(e),c'/ <- exp(/e3/)

   ccr  U@/c'',e2,c'/ <- exp(/e3/), not(c'' = c'),
        /Ast.Wait(e1)/ in /Ast.exps(c'')/, /c/ in /Ast.classes()/,
        /Ast.Notif(e)/ in /Ast.exps(c)/, /e2/ in post Stime.P@/Ast.Wait(e1)/,
        not ((Class.Sol@/e/*Class.Sol@/e1/)={})
       -------------------------------------------------------------
            U@/c,Ast.Notif(e),c'/ <- exp(/e3/)

   ccr  D@/c'',e2,c'/ <- exp(/e3/), not(c'' = c'),
        /Ast.Notif(e1)/ in /Ast.exps(c'')/, /c/ in /Ast.classes()/,
        /Ast.Wait(e)/ in /Ast.exps(c)/, /e2/ in post Stime.P@/Ast.Notif(e1)/,
        not ((Class.Sol@/e/*Class.Sol@/e1/)={})
       -------------------------------------------------------------
            D@/c,Ast.Wait(e),c'/ <- exp(/e3/)

   ccr  D@/c'',e2,c'/ <- exp(/e3/), not(c'' = c'),
        /Ast.Wait(e1)/ in /Ast.exps(c'')/, /c/ in /Ast.classes()/,
        /Ast.Notif(e)/ in /Ast.exps(c)/, /e2/ in post Stime.P@/Ast.Wait(e1)/,
        not ((Class.Sol@/e/*Class.Sol@/e1/)={})
       -------------------------------------------------------------
            D@/c,Ast.Notif(e),c'/ <- exp(/e3/)

 end
