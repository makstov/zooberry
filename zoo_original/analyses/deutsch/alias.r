(*
  May-Alias Analysis in Alain Deutsch's PLDI '94 paper
  Sukyoung Ryu 7/9/2001
*)

(**** Not yet   ************************************************************)
(**** from here ************************************************************
signature VSH =
 sig
  val Bot: K
  eqn Meet: 
  eqn Join: K * K -> K
 end

analysis Alias (VSh: VSH) =
 ana
   set Exp = /Ast.exp/
   set ExpL = /Ast.exp list/
   set Ap = /Ast.ap/   (* access path *)
   set Sel = /Ast.sel/ (* selectors *)
   set Ty = /Ast.ty/
   set Pvar = power /Ast.var/ (* a set of coefficient variables *)
   set K =
   set Sap = Ap + ...
   set Ali = (Ap * Ap) * K
   set Seq = (* system of equations *)
   set Rho = power Ali (* symbolic alias relation *)
   set SPS = (* symbolic path set *)

   val GlobalVariables

   (* The operator MakeGenericName(f) returns a symbolic access path f'
      consisting of a generic object U[k1,...,kn],
      where n is the number of coefficient variables occurring in f.
      The name U is determined uniquely from f, ignoring coefficient names
      and the k1, ..., kn are fresh variables. *)
   (* Figure 21 in page 241 *)
   (* MakeGenericName: Sap -> Sap *)
   fun MakeGenericName

   (* sel2sps: Sel -> SPS *)
   fun sel2sps sigma = (* ap2sps(pi) = {(pi,\top)} *)

   fun not true = false
     | not false = true
   (* isIn: 'a * 'a set -> bool *)
   fun isIn
   (* fv: Sap -> Pvar *)
   fun fv

   (* rename P s.t. coeffs. of P and rho are disjoint *)
   (* rename1: SPS * SPS -> SPS *)
   fun rename1 (P, Q) =

   (* rename P so that the coefficients appearing in P and Q are distinct *)
   (* rename2: SPS * Rho -> SPS *)
   fun rename2 (P, rho) =

   (* Rename: Rho -> Rho *)
   eqn Rename

**** till here *************************************************************)
(**** Not yet   ************************************************************)

(**** not defined *****
 The binary operator Match determines if a symbolic access path f can
 generate (contain) a particular access path, or a prefix of it.

   (* Figure 4 in page 233 *)
   (* Match: /Ast.matchKind/ * Ap * Sap -> Seq * Sap *)
   eqn Match (kind, pi, f) =
***** not defined ****)

(**** not defined *****
 The operator Compl takes a system of linear equations S and a set of
 variables U, and returns Compl(S,U), a set of elements of V#
 whose union upper approximates the complement of the system S with respect to
 the positive integers. Variables of U occurring in the system S are assumed
 to be arbitrary positive integers which are eliminated.

   (* Figure 4 in page 233 *)
   (* Compl: Seq * Pvar -> power K *)
   eqn Compl (S, U) =
***** not defined ****)

(**** not defined *****
 The operator StarClosureSh(P,t) computes a symbolic path set
 denoting the star closure of the set of access paths denoted by P,
 where t is the recursive type to which paths of P can be applied.

   (* Figure 4 in page 233 *)
   (* StarClosureSh: SPS * Ty -> SPS *)
   eqn StarClosureSh (P, t) =
***** not defined ****)

   (* Figure 3 in page 233 *)
   (* Join: Rho * Rho -> Rho *)
   eqn Join (rho1, rho2) =
       let fun loop rho =
	     let val set1 = { (f1,f2,K,K') | ((f1,f2),K) from rho,
					     ((f3,f4),K') from rho,
					     f1 = f3, f2 = f4, not(K = K') }
		 val set2 = { ((f1,f2),K), ((f1,f2),K') |
			      (f1,f2,K,K') from set1 }
	     in  case set1
		   of {} => rho
		    | _ =>
		      let val rho' = { r | r from rho, not(r in set2) }
			  val rho'' = rho' + {((f1,f2), VSh.Join({K,K'})) |
					      (f1,f2,K,K') from set1}
		      in  loop rho''
		      end
	     end
       in  loop (rho1 + rho2)
       end

   (* Figure 17 in page 241 *)
   (* EquivalenceClassSh: Ap * Rho -> SPS *)
   eqn EquivalenceClassSh (pi, rho) =
       let val /rhoL/ = /Ast.set2list(rho)/
           val range = {2 ... /Ast.len(rhoL)/}
           fun doit (f, K, P) =
               let val set = Match (/Ast.In/,pi,f)
                   val list = /Ast.set2list(set)/
                   val range = {2 ... /Ast.len(list)/}
                   fun doit' ((S,D), P') =
                       let val K' = VSh.ProjSh(VSh.CSh(K,S),
                                               fv(/Ast.mkAp''(f,D)/))
                       in  if VSh.isBot(K') then P'
                           else P' + {(/Ast.mkAp''(f,D)/,K')}
                       end
                   fun post 1 = doit' (/Ast.nth(list,1)/, P)
                     | post (i in range) =
                       doit' (/Ast.nth(list,i)/, post (i-1))
               in  post /Ast.len(list)/
               end
           fun rewrite (((f1,f2),K), P) =
               doit (f2, K, doit (f1, K, P))
           fun post 1 = equiv (/Ast.nth(rhoL,1)/, {})
             | post (i in range) = equiv (/Ast.nth(rhoL,i)/, post (i-1))
       in  (post /Ast.len(rhoL)/) + {(pi,VSh.Top)}
       end

   (* Figure 18 in page 241 *)
   (* StripPrefixSh: Ap * SPS -> SPS *)
   eqn StripPrefixSh (pi, P) =
       let val set = { (f,K,S,D) | (f,K) from P,
                                   (S,D) from Match (/Ast.Ni/,f,pi) }
           val list = /Ast.set2list(set)/
           val range = {2 ... /Ast.len(list)/}
           fun strip ((f,K,S,D), P') =
               let val K' = VSh.ProjSh(VSh.CSh(K,S), fv(D))
               in  if VSh.isBot(K') then P' else P' + {(D,K')}
               end
           fun post 1 = strip (/Ast.nth(list,1)/, {})
             | post (i in range) = strip (/Ast.nth(list,i)/, post (i-1))
       in  post /Ast.len(list)/
       end

   (* Figure 19 in page 241 *)
   (* Concat: SPS * SPS = SPS *)
   eqn Concat (P, Q) =
       let val P' = rename1 (P, Q)
       in  { (/Ast.mkAp''(f1,f2)/, VSh.MeetH(K1,K2)) |
             (f1,K1) from P', (f2,K2) from P' }
       end

   (* Figure 20 in page 241 *)
   (* RewriteShL: Ap * SPS * Rho -> Rho *)
   eqn RewriteShL (pi, P, rho) =
       let val P' = rename2 (P, rho)
           val /rhoL/ = /Ast.set2list(rho)/
           val range = {2 ... /Ast.len(rhoL)/}
           fun matchIn (f1,f2,K,rho') =
               let val set = { (S,D,g,K') | (S,D) from Match (/Ast.In/,pi,f1),
                                            (g,K') from P }
                   val list = /Ast.set2list(set)/
                   val range = {2 ... /Ast.len(list)/}
                   fun doit ((S,D,g,K'), rho'') =
                       let val K'' = VSh.ProjSh(VSh.CSh(VSh.MeetH(K,K'),S),
                                                fv(g)+fv(/Ast.mkAp''(f2,D)/))
                       in  if VSh.isBot(K'') then rho''
                           else rho'' + Rename {((g,/Ast.mkAp''(f2,D)/),K'')}
                       end
                   fun post 1 = doit (/Ast.nth(list,1)/, rho')
                     | post (i in range) = doit (/Ast.nth(list,i)/, post(i-1))
               in  post /Ast.len(list)/
               end
           fun matchNi (f1,f2,K,rho') =
               let val set = { (S,D,g,K') | (S,D) from Match (/Ast.Ni/,f1,pi),
                                            (g,K') from P }
                   val list = /Ast.set2list(set)/
                   val range = {2 ... /Ast.len(list)/}
                   fun doit ((S,D,g,K'), rho'') =
                       let val K'' = VSh.ProjSh(VSh.CSh(VSh.MeetH(K,K'),S),
                                                fv(/Ast.mkAp''(g,D)/)+fv(f2))
                       in  if VSh.isBot(K'') then rho''
                           else rho'' + Rename {((/Ast.mkAp''(g,D)/,f2),K'')}
                       end
                   fun post 1 = doit (/Ast.nth(list,1)/, rho')
                     | post (i in range) = doit (/Ast.nth(list,i)/, post(i-1))
               in  post /Ast.len(list)/
               end
           fun rewrite (((f1,f2),K), rho') =
               matchNi (f1, f2, K, matchIn (f1,f2,K,rho'))
           fun post 1 = rewrite (/Ast.nth(rhoL,1)/, {})
             | post (i in range) = rewrite (/Ast.nth(rhoL,i)/, post (i-1))
       in  post /Ast.len(rhoL)/
       end

(**** not defined *****
 RewriteShR is defined similarly.

   (* Figure 20 in page 241 *)
   (* RewriteShR: Ap * SPS * Rho -> Rho *)
   eqn RewriteShR (pi, P, rho) =
***** not defined ****)

   (* Figure 20 in page 241 *)
   (* RewriteSh: Ap * SPS * Rho -> Rho *)
   eqn RewriteSh (pi, P, rho) =
       let val rho1 = RewriteShL (pi, P, rho)
	   val rho2 = Join (rho1, RewriteShR (pi, P, Join (rho, rho1)))
       in  Join (rho2, Rename { ((f,pi),K) | (f,K) from P } )
       end

   (* Figure 5 in page 234 *)
   (* KillPath: Ap * Sap * K -> K *)
   eqn KillPath (pi, f, K) =
       let val A = { Compl (S,fv(D)) | (S,D) from Match (/Ast.Equiv/,pi,f) }
	   fun meetH B = { VSh.MeetH(K,K') | K' from B }
	   val joinA = { VSh.Join(meetH B) | B from A }
       in  VSh.Meet({K, VSh.Meet(joinA)})
       end

   (* Figure 5 in page 234 *)
   (* KillSh: Ap * Rho -> Rho *)
   eqn KillSh (pi, rho) =
       let fun killPaths (f1, f2, K) = KillPath(pi,f2,KillPath(pi,f1,K))
       in  { (f1,f2,killPaths (f1,f2,K)) | ((f1,f2),K) from rho,
				           not(killPaths(f1,f2,K) = VSh.Bot) }
       end

   (* Figure 6 in page 234 *)
   (* GenSh: Ap * Sel * Ap * Rho -> Rho *)
   eqn GenSh (lhs, sigma, rhs, rho) =
       let val E = EquivalenceClassSh (lhs, rho) (* aliases of lhs *)
	   val B = StripPrefixSh (rhs, E)
	   val C = StarClosureSh (Concat(B,sel2sps(sigma)), /Ast.typeof(rhs)/)
	   val P = Concat (Concat (E, sel2sps(sigma)), C)
       in  Join (rho, RewriteSh (rhs, P, rho)) 
       end

   (* Figure 21 in page 241 *)
   (* GeneraliseSh: Sap * Rho * Rho -> Rho * Rho *)
   eqn GeneraliseSh (((f1,f2),K), rhoE, theta) =
       let val f1' = MakeGenericName(f2)
           val S = { /Ast.Eq(u,v)/ | u from fv(f2), v from fv(f1') }
           val rhoE' = Join (rhoE, Rename {((f1',f2),VSh.SSh(S))})
           val K' = VSh.ProjSh(VSh.CSh(K,S), fv(f1')+fv(f1))
       in  (rhoE', theta + Rename {((f1',f1),K')})
       end

   (* Figure 9 in page 235 *)
   (* CallSh: Var * ExpL * Rho -> Rho * Rho * Rho *)
   eqn CallSh (/F/, /es/, rho) =
       let val /xs/ = /Ast.getArgs(F)/
           val range = {2 ... /Ast.len(es)/}
           fun post 1 =
               let val actual = /Ast.mkStar(Ast.nth(es,1))/
               in  KillSh (actual,
                           GenSh (/Ast.nth(xs,1)/,/Ast.Star/,actual,rho))
               end
             | post (i in range) =
               let val actual = /Ast.mkStar(Ast.nth(es,i))/
               in  KillSh (actual,
                           GenSh(/Ast.nth(xs,i)/,/Ast.Star/,actual,post(i-1)))
               end
           val rho' = post /Ast.len(es)/
           val support = /Ast.list2set(xs)/ + GlobalVariables
           val /rhoL/ = /Ast.set2list(rho')/
           val range = {2 ... /Ast.len(rhoL)/}
           fun call (alias as ((g1, g2), K), (rhoEntry, rhoThrough, theta)) =
               case (isIn(g1,support), isIn(g2,support))
                 of (true, true) =>
                    (rhoEntry + {alias}, rhoThrough, theta)
                  | (false, false) =>
                    (rhoEntry, rhoThrough + {alias}, theta)
                  | (false, true) =>
                     let val (rhoE, theta') =
                             GeneraliseSh (((g1,g2),K), rhoEntry, theta)
                     in  (rhoE, rhoThrough, theta')
                     end
                  | (true, false) =>
                     let val (rhoE, theta') =
                             GeneraliseSh (((g2,g1),K), rhoEntry, theta)
                     in  (rhoE, rhoThrough, theta')
                     end
           fun post 1 = call (/Ast.nth(rhoL,1)/, ({},{},{}))
             | post (i in range) = call (/Ast.nth(rhoL,i)/, post (i-1))
       in  post /Ast.len(rhoL)/
       end

(**** not defined *****
 InstantiateSh (u,K,Theta) returns a set of pairs (u',K') obtained
 by replacing u by the symbolic access paths associated with u in Theta
 and adjusting accordingly K.

   (* page 235 *)
   (* InstantiateSh: Sel * SPS * Rho -> power (Sel * SPS) *)
   eqn InstantiateSh (u,K,Theta) =
***** not defined ****)

   (* Figure 10 in page 236 *)
   (* ReturnSh: Rho * Rho * Rho -> Rho *)
   eqn ReturnSh (rhoExit, rhoT, theta) =
       let val theta' = theta + { (g,g) | g from GlobalVariables }
           val /rhoEL/ = /Ast.set2list(rhoExit)/
           val range = {2 ... /Ast.len(rhoEL)/}
           fun doit (u,M,v,N,K,rho) =
               let val us' = InstantiateSh (u, K, theta')
                   val vs' = InstantiateSh (v, K, theta')
                   val set = { (u',K1,v',K2) | (u',K1) from us',
                                               (v',K2) from vs'}
                   val list = /Ast.set2list(set)/
                   val range = {2 ... /Ast.len(list)/}
                   fun doit' ((u',K1,v',K2), rho') =
                       let val K' = VSh.MeetH(K1,K2)
                       in  if VSh.isBot(K') then rho'
                           else rho' + Rename {((/Ast.mkAp'(u',M)/,
                                                 /Ast.mkAp'(v',N)/),K')}
                       end
                   fun post 1 = doit' (/Ast.nth(list,1)/, rho)
                     | post (i in range) =
                       doit' (/Ast.nth(list,i)/, post (i-1))
               in  post /Ast.len(list)/
               end
           fun return (((g1, g2),K), rho) =
               let val (u, M) = /Ast.splitAp(g1)/
                   val (v, N) = /Ast.splitAp(g2)/
                   fun chk x =
                       if /Ast.isGlobal(x)/ then true else /Ast.isGeneric(x)/
               in  if chk u
                   then if chk v then doit (u,M,v,N,K,rho) else rho
                   else rho
               end
           fun post 1 = return (/Ast.nth(rhoEL,1)/, {})
             | post (i in range) = return (/Ast.nth(rhoEL,i)/, (post (i-1)))
           val rhoR = post /Ast.len(rhoEL)/
       in  Join (rhoR, rhoT)
       end

   (* Col: Exp * Rho -> Rho *)
   eqn Col (/Ast.Ass(l,r)/, rho) = (* Figure 7 in page 234 *)
       let val (lhs,sigma,rhs) = /Ast.mkAssIn(l,r)/
           (* where 'lhs.sigma \not(<=) rhs' and 'lhs.sigma \not(>=) rhs' *)
	   val pi = /Ast.mkAp(lhs,sigma)/
	   val rho' = KillSh (pi, rho)
       in  GenSh (lhs, sigma, rhs, rho')
       end
     | Col (/Ast.Ftn(F,xs,e)/, rho) = rho
     | Col (/Ast.App(F,es)/, rho) =
       let val (rhoEnt, rhoT, thet) = CallSh (/F/, /es/, rho)
           val rhoExit = Col (/Ast.getBody(F)/, rhoEnt)
       in  ReturnSh (rhoExit, rhoT, thet)
       end

 end
