(*
  Context Analysis for LISP's core
  Sukyoung Ryu 7/6/2001
*)

analysis Context =
 ana
   set Exp = /Ast.exp/
   set Var = /Ast.var/
   set Rtg = /Ast.rtg/

   lattice Context = Exp -> Rtg
   lattice ContextEnv = Var -> Rtg

   (* Col: Exp * (Context * ContextEnv) -> Contex * ContextEnv *)
   eqn Col (/Ast.Var(x)/, (ct, ce)) = (ct, ce)
     | Col (/Ast.QUOTE(c)/, (ct, ce)) = (ct, ce)
     | Col (/Ast.CAR(e') as e/, (ct, ce)) = 
       let val /ertg/ = ct /e/
           val ertg' = if /Ast.isBot(ertg)/ then /Ast.bot/
                       else /Ast.expBot(e)/
           val prev = (ct + { /e'/ => ertg' }, ce)
       in  Col (/e'/, prev)
       end
     | Col (/Ast.CDR(e') as e/, (ct, ce)) = 
       let val /ertg/ = ct /e/
           val ertg' = if /Ast.isBot(ertg)/ then /Ast.bot/
                       else /Ast.botExp(e)/
           val prev = (ct + { /e'/ => ertg' }, ce)
       in  Col (/e'/, prev)
       end
     | Col (/Ast.ATOM(e') as e/, (ct, ce)) = 
       let val /ertg/ = ct /e/
           val ertg' = if /Ast.isBot(ertg)/ then /Ast.bot/ else /Ast.orBot/
           val prev = (ct + { /e'/ => ertg' }, ce)
       in  Col (/e'/, prev)
       end
     | Col (/Ast.NULL(e') as e/, (ct, ce)) = 
       let val /ertg/ = ct /e/
           val ertg' = if /Ast.isBot(ertg)/ then /Ast.bot/ else /Ast.orBot/
           val prev = (ct + { /e'/ => ertg' }, ce)
       in  Col (/e'/, prev)
       end
     | Col (/Ast.EQUAL(e1,e2) as e/, (ct, ce)) =
       let val /ertg/ = ct /e/
           val ertg' = if /Ast.isBot(ertg)/ then /Ast.bot/ else /Ast.top/
           val prev = (ct + { /e1/ => ertg', /e2/ => ertg' }, ce)
           val p1 = Col (/e1/, prev)
       in  Col (/e2/, p1)
       end
     | Col (/Ast.CONS(e1,e2) as e/, (ct, ce)) =
       let val /ertg/ = ct /e/
           val e1rtg = if /Ast.isTop(ertg) || Ast.isOrTopSome(ertg) ||
                           Ast.isTopSome(ertg)/
                       then /Ast.top/
                       else if /Ast.isBot(ertg) || Ast.isOr(ertg) ||
                                Ast.isOrBotSome(ertg) || Ast.isBotSome(ertg)/
                       then /Ast.bot/
                       else (case /ertg/
                               of /Ast.Or(a,_)/ or /Ast.Pair(a,_)/ =>
                                  let val esrtg =
                                          { ct e | e from /Ast.rtg2set(a)/ }
                                  in  /Ast.join(esrtg)/
                                  end)
           val e2rtg = if /Ast.isTop(ertg) || Ast.isOrSomeTop(ertg) ||
                           Ast.isSomeTop(ertg)/
                       then /Ast.top/
                       else if /Ast.isBot(ertg) || Ast.isOr(ertg) ||
                                Ast.isOrSomeBot(ertg) || Ast.isSomeBot(ertg)/
                       then /Ast.bot/
                       else (case /ertg/
                               of /Ast.Or(_,a)/ or /Ast.Pair(_,a)/ =>
                                  let val esrtg =
                                          { ct e | e from /Ast.rtg2set(a)/ }
                                  in  /Ast.join(esrtg)/
                                  end)
           val prev = (ct + { /e1/ => e1rtg, /e2/ => e2rtg }, ce)
           val p1 = Col (/e1/, prev)
       in  Col (/e2/, p1)
       end
     | Col (/Ast.IF(e1,e2,e3) as e/, (ct, ce)) =
       let val /ertg/ = ct /e/
           val e1rtg = if /Ast.isBot(ertg)/ then /Ast.bot/
                       else /Ast.Or(Ast.Bot,Ast.Bot)/
           val prev = (ct + { /e1/ => e1rtg, /e2/ => /ertg/, /e3/ => /ertg/ },
                      ce)
           val p1 = Col (/e1/, prev)
           val p2 = Col (/e2/, p1)
       in  Col (/e3/, p2)
       end
     | Col (/Ast.CALL(f,es) as e/, (ct, ce)) =
       let val /ertg/ = ct /e/
	   val xeset = /Ast.args(f,es)/
           fun ect x = if /Ast.isBot(ertg)/ then /Ast.bot/ else ce x
           val esmap = { e' => ect(x) | (x,e') from xeset }
           val prev = (ct + esmap, ce)
           val range = {2 ... /Ast.len(es)/}
           fun postv 1 = Col (/Ast.nth(es,1)/, prev)
             | postv (i in range) = Col (/Ast.nth(es,i)/, postv (i-1))
       in  postv /Ast.len(es)/
       end
     | Col (/Ast.OP(op,e1,e2) as e/, (ct, ce)) =
       let val /ertg/ = ct /e/
           val ertg' = if /Ast.isBot(ertg)/ then /Ast.bot/ else /Ast.Any/
	   val prev = (ct + { /e1/ => ertg', /e2/ => ertg' }, ce)
	   val p1 = Col (/e1/, prev)
       in  Col (/e2/, p1)
       end
     | Col (/Ast.DEFINEm(xs,e')/, (ct, ce)) =
       let fun xce /x/ =
             let val esrtg = { ct e | e from /Ast.useOf(x)/ }
             in  /Ast.join(esrtg)/
             end
           val xsmap = { x => xce(x) | x from /Ast.list2set(xs)/ }
       in  Col (e', (ct + { /e'/ => ce /Ast.main/ },
                     (ce + { /Ast.main/ => /Ast.piMain/ }) + xsmap))
       end
     | Col (/Ast.DEFINE(f,xs,e')/, (ct, ce)) =
       let val esrtg = { ct e | e from /Ast.callsTo(f)/ }
           val fce = /Ast.join(esrtg)/
           fun xce /x/ =
             let val esrtg = { ct e | e from /Ast.useOf(x)/ }
             in  /Ast.join(esrtg)/
             end
           val xsmap = { x => xce(x) | x from /Ast.list2set(xs)/ }
       in  Col (e', (ct + { /e'/ => ce /f/ }, (ce + { /f/ => fce }) + xsmap))
       end
     | Col (_, (ct, ce)) = (ct, ce)

 end
