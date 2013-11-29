(*
  Precise Interprocedural Dataflow Analysis via Graph Reachability
  Thomas Reps' POPL '95 paper
  Sukyoung Ryu 7/13/2001
*)

signature IP =
 sig
   set V = /Ast.var/
   set D                      (* dataflow facts *)
   set NStar                  (* nodes *)
   set EStar = NStar * NStar  (* edges *)
   set F = power D -> power D (* a set of distributive functions *)
   set M = EStar -> F         (* a map from Estar to dataflow functions *)
   val Start: V -> NStar
   val Exit: V -> NStar

   val isStart: NStar -> /Ast.bool/
   val isCall: V * NStar -> /Ast.bool/ (* isCall(p,n) = n \in Call_p *)
   val isExit: V * NStar -> /Ast.bool/ (* isExit(p,n) = n = e_p *)
   val isSameN: NStar * NStar -> /Ast.bool/
   val getName: NStar -> V
   val getStart: V -> NStar
 end

analysis Reachability (IP: IFDS) =
 ana

   set D = IP.D
   set DZ = D + {0 ... 0}
   set Node = IP.NStar
   set Edge = IP.EStar
   set Edges = power Edge
   set NSh = Node * DZ
   set ESh = (Node * DZ) * (Node * DZ)
   set GSh = NSh * ESh
   set Result = Node -> power D

   val init = ((IP.Start(/Ast.main/), 0), (IP.Start(/Ast.main/), 0))

(* Section 4. ***********************************************************)
(* not defined **********************************************************
   (* maps a call node to its corresponding return-site node *)
   (* returnSite: Node -> Node *)
   fun returnSite n =
   (* maps a node to the name of its enclosing procedure *)
   (* procOf: Node -> Var *)
   fun procOf n =
   (* maps a call node to the name of the called procedure *)
   (* calledProc: Node -> Var *)
   fun calledProc n =
   (* maps a procedure name to the set of call nodes
      that represent calls to that procedure *)
   (* callers: Var -> power Node *)
   fun callers v =
 * not defined **********************************************************)
   
   (* isSameNSh: NSh * NSh -> /Ast.bool/ *)
   fun isSameNSh ((n1,0), (n2,0)) = isSameN(n1,n2)
     | isSameNSh ((n1,d1), (n2,d2)) =
       if isSameN(n1,n2) then isSameD(d1,d2) else false

   (* Propagate: Edge * (Edges * Edges * Edges) -> Edges * Edges * Edges *)
   eqn Propagate (edg, (PathEdge, WorkList, SummaryEdge)) =
       if /Ast.isIn(edg, PathEdge)/
       then (PathEdge, WorkList, SummaryEdge)
       else (PathEdge + {edg}, WorkList + {edg}, SummaryEdge)

   (* ForwardTabulateSLRPs: ESh * (Edges * Edges * Edges) ->
                            Edges * Edges * Edges *)
   eqn ForwardTabulateSLRPs (ESh, (PathEdge, WorkList, SummaryEdge)) =
       let val EShL = /Ast.set2list(ESh)/
           val range = {2 ... /Ast.len(EShL)/}
           fun forward (edg as ((sp,d1),(n,d2)), (PE,WL,SE)) =
             let fun doit1sub1 ((n1,n3' as (n3,d3)), edgeSets) =
                     if isSameNSh (n1,(n,d2))
                     then if IP.isStart(n3)
                          then let val p = IP.getName(n3)
                                   val p' = CalledProc(n)
                               in  if /Ast.isSameV(p,p')/
                                   then Propagate ((n3',n3'), edgeSets)
                                   else edgeSets
                               end
                          else edgeSets
                     else edgeSets
                 fun doit1main1 1 = doit1sub1 (/Ast.nth(EShL,1)/, (PE,WL,SE))
                   | doit1main1 (i in range) =
                     doit1sub1 (/Ast.nth(EShL,i)/, doit1main1 (i-1))
                 fun doit1sub2 ((n1,(n3,d3)), edgeSets) =
                     if isSameNSh (n1,(n,d2))
                     then if isSameN (n3, returnSite(n))
                          then Propagate (((sp,d1),(n3,d3)), edgeSets)
                          else edgeSets
                     else edgeSets
                 fun doit1main2 (1, L, edgS) = doit1sub2 (/Ast.nth(L,1)/,edgS)
                   | doit1main2 (i in range, L, edgS) =
                     doit1sub2 (/Ast.nth(L,i)/, doit1main2 (i-1))
                 fun doit1 _ =
                   let val (PE',WL',SE') = doit1main1 (/Ast.len(EShL)/)
                       val EShSE = EShL + SE'
                       val EShSEL = /Ast.set2list(EShSE)/
                   in  doit1main2 (/Ast.len(EShSEL)/, EShSEL, (PE',WL',SE'))
                   end
                 fun doit2sub (edg as ((c,d4), ns), (PE',WL',SE')) =
                   if /Ast.isIn(edg, SE')/ then (PE',WL',SE')
                   else let val SE'' = SE' + {edg}
                            val list = /Ast.set2list(PE')/
                            val range = {2 ... /Ast.len(list)/}
                            fun doit' ((ns' as (nn,d3),ns2), edgeSets) =
                              if isSameNSh (ns2,(c,d4))
                              then if IP.isStart(nn)
                                   then let val p = IP.getName(nn)
                                            val p' = procOf(c)
                                        in  if /Ast.isSameV(p,p')/
                                            then Propagate ((ns',ns),edgeSets)
                                            else edgeSets
                                        end
                                   else edgeSets
                              else edgeSets
                            fun postv 1 =
                                doit' (/Ast.nth(list,1)/, (PE',WL',SE''))
                              | postv (i in range) =
                                doit' (/Ast.nth(list,i)/, postv (i-1))
                        in  postv (/Ast.len(list)/)
                        end
                 fun doit2main (c, edgeSets) =
                   let val set' = { ((na,d4), (nb,d5)) |
                                    ((na,d4),ns1) from ESh,
                                    (ns2,(nb,d5)) from ESh,
                                    na = c, ns1 = (sp,d1), ns2 = (n,d2),
                                    nb = returnSite(c) }
                       val list = /Ast.set2list(set')/
                       fun postv 1 = doit2sub (/Ast.nth(list,1)/, edgeSets)
                         | postv (i in range) =
                           doit2sub (/Ast.nth(list,i)/, postv (i-1))
                   in  postv (/Ast.len(list)/)
                   end
                 fun doit2 p =
                   let val set' = callers (p)
                       val list = /Ast.set2list(set')/
                       val range = {2 ... /Ast.len(list)/}
                       fun postv 1 = doit2main (/Ast.nth(list,1)/, (PE,WL,SE))
                         | postv (i in rage) =
                           doit2main (/Ast.nth(list,i)/, postv (i-1))
                   in  postv (/Ast.len(list)/)
                   end
                 fun doit3sub ((n1,n2), edgeSets) =
                     if isSameNSh ((n,d2),n1)
                     then Propagate (((sp,d1),n2), edgeSets) else edgeSets
                 fun doit3main 1 = doit3sub (/Ast.nth(EShL,1)/, (PE,WL,SE))
                   | doit3main (i in range) = 
                     doit3sub (/Ast.nth(EShL,i)/, doit3main (i-1))
             in  if IP.isStart(sp)
                 then let val WL' = WL - {edg}
                          val p = IP.getName(sp)
                      in  if IP.isCall(p,n) then doit1 {}
                          else if IP.isExit(p,n) then doit2 (p)
                               else doit3main (/Ast.len(EShL)/)
                      end
                 else (PE,WL,SE)
             end
       in  if /Ast.isEmpty(WorkList)/ then (PathEdge, WorkList, SummaryEdge)
           else let val list = /Ast.set2list(WorkList)/
                    val range = {2 ... /Ast.len(list)/}
                    fun postv 1 = forward (/Ast.nth(list,1)/,
                                           (PathEdge, WorkList, SummaryEdge))
                      | postv (i in range) =
                        forward (/Ast.nth(list,i)/, postv (i-1))
                in  ForwardTabulateSLRPs (postv (/Ast.len(list)/))
                end
       end

   (* Tabulate: GSh * D -> Result *)
   eqn Tabulate ((NSh, ESh), D) =
       let val (PathEdge, WorkList, SummaryEdge) =
               ForwardTabulateSLRPs (ESh, ({init}, {init}, {}))
           val list = /Ast.set2list(NSh)/
           val range = {2 ... /Ast.len(list)/}
           fun tab (n, res) =
             let val set' =
                     { d2 | d1 from (D + {0}), d2 from D,
                            ((IP.getStart(procOf(n)),d1),(n,d2)) in PathEdge }
             in  res + { n => set' }
             end
           fun postv 1 = tab (/Ast.nth(list,1)/, {})
             | postv (i in range) = tab (/Ast.nth(list,i)/, postv (i-1))
       in  postv (/Ast.len(list)/)
       end

 end
