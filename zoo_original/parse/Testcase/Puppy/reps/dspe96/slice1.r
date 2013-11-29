(*
  Type I Slicing
  Sukyoung Ryu 7/7/2001
*)

signature CONTEXT =
 sig
  lattice Context = /Ast.exp/ -> /Ast.rtg/
  lattice ContextEnv = /Ast.var/ -> /Ast.rtg/
  eqn Col: /Ast.exp/:index * (Context * ContextEnv) -> Contex * ContextEnv
 end

analysis Slice (Context: CONTEXT) =
 ana
   set Exp = /Ast.exp/

   (* Col: Exp -> Exp *)
   eqn Col e =
       let val ertg = post Context.Ctxt@e
       in  if /Ast.isBot(ertg)/ then /Ast.QUOTE(Ast.question)/
           else (case e
                  of /Ast.Var(x)/ => e
                   | /Ast.QUOTE(c)/ =>
                     let fun pi /Ast.Atm(Ast.Top)/ = /c/
                           | pi /Ast.Atm(Ast.Bot)/ = /Ast.question/
                           | pi /Ast.Any/ =
                             if /Ast.isAtom(c)/ then /c/ else /Ast.question/
                           | pi /Ast.Pair(a,b)/ =
                             if /Ast.isAtom(c)/ then /Ast.question/
                             else let val /a'/ = pi /Ast.Atm(a)/
                                      val /b'/ = pi /Ast.Atm(b)/
                                  in  /Ast.cons(a',b')/
                                  end
                           | pi /Ast.Or(a,b)/ =
                             if /Ast.isAtom(c)/ then /c/
                             else let val /a'/ = pi /Ast.Atm(a)/
                                      val /b'/ = pi /Ast.Atm(b)/
                                  in  /Ast.cons(a',b')/
                                  end
                         val /newc/ = pi /Ast.normal(ertg)/
                     in  /Ast.QUOTE(newc)/
                     end
                   | /Ast.CAR(e')/ =>
                     let val /newe'/ = Col /e'/ in /Ast.CAR(newe')/ end
                   | /Ast.CDR(e')/ =>
                     let val /newe'/ = Col /e'/ in /Ast.CDR(newe')/ end
                   | /Ast.ATOM(e')/ =>
                     let val /newe'/ = Col /e'/ in /Ast.ATOM(newe')/ end
                   | /Ast.NULL(e')/ =>
                     let val /newe'/ = Col /e'/ in /Ast.NULL(newe')/ end
                   | /Ast.EQUAL(e1,e2)/ =>
                     let val /newe1/ = Col /e1/ val /newe2/ = Col /e2/
                     in  /Ast.EQUAL(newe1,newe2)/
                     end
                   | /Ast.CONS(e1,e2)/ =>
                     let val /newe1/ = Col /e1/ val /newe2/ = Col /e2/
                     in  /Ast.CONS(newe1,newe2)/
                     end
                   | /Ast.IF(e1,e2,e3)/ =>
                     let val /newe1/ = Col /e1/ val /newe2/ = Col /e2/
                         val /newe3/ = Col /e3/
                     in  /Ast.IF(newe1,newe2,newe3)/
                     end
                   | /Ast.CALL(f,es)/ =>
                     let val range = {2 ... /Ast.len(es)/}
                         fun postv 1 = { 1 => Col (/Ast.nth(es,1)/) }
                           | postv (i in range) =
                             { i => Col (/Ast.nth(es,i)/) } + postv (i-1)
                         val newes = postv /Ast.len(es)/
                     in  /Ast.CALL(f,Ast.map2list(newes))/
                     end
                   | /Ast.OP(op,e1,e2)/ =>
                     let val /newe1/ = Col /e1/ val /newe2/ = Col /e2/
                     in  /Ast.OP(newe1,newe2)/
                     end
                   | /Ast.DEFINEm(xs,e')/ =>
                     let val /newe'/ = Col /e'/ in /Ast.DEFINEm(xs,newe')/ end
                   | /Ast.DEFINE(f,xs,e')/ =>
                     let val /newe'/ = Col /e'/ in /Ast.DEFINE(f,xs,newe')/ end
                   | e => e)
       end

 end
