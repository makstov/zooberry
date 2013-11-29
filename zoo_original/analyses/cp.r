(*
   Constant propagation analysis for ML's core.
   Derived from /home/kwang/Z1/zin/kir/cp.z
   Kwangkeun Yi 6/20/2001
*)

analysis ConstantProp = 
 ana
   set FnExp = /Ast.expr/
   set Id = /Ast.id/
   set I = {0 ... /Ast.maxRecArgs/}
   set Int = {/Ast.int-low/ ... /Ast.int-high/}

   lattice C = power FnExp
   lattice L = power Id
   lattice K = L
   lattice Z = power Int
   lattice V = C * L * K * Z
   lattice A = I -> V
   lattice S = Id -> A

   fun valueFetch (s,id) = s id 0
   fun valueA v = {0 => v}
   fun numToZ (n with n < -99999) = top
     | numToZ (n with n >= 99999) = top
     | numToZ n = n

   eqn Eval(/Ast.Const(n)/, s)  = ((__, __, __, numToZ n), s)
     | Eval(/Ast.Var(id)/, s)   = (valueFetch(s,/id/), s)
     | Eval(/Ast.String(r)/, s) = (__, s)
     | Eval(/Ast.Fn(f) as e/, s)= (({/e/}, __, __, __), s)
     | Eval(/Ast.Op(o) as e/, s)= (({/e/}, __, __, __), s)
     | Eval(/Ast.Con(k,e)/, s)  = Eval(/e/, s)
     | Eval(/Ast.Decon(e)/, s)  =
        let 
          val (s, v) = Eval(/e/,s)
          val v' = +{(fn x => s x 0) l | l from v.K} 
        in
          (v', s)
        end
     | Eval(/Ast.Apply(e,e')/, s) =
        let
          val (v', s') = Eval(/e/, s)
          val (v'', s'') = Eval(/e'/, s')
        in
          case v'.C
            of __ => (__,s'') 
             | ftns =>
                 let
                   fun scall /Ast.Primop(_)/= ((__,__,__,top), s'')
                     | scall /Ast.Fn(x,e)/ = Eval(/e/, s[x => (s x)+v''])
                 in
                   +{ scall fexp | fexp from ftns}
                 end
        end
     | Eval(/Ast.Fix(es)/, s) =
        let
          val range = {2 ... /Ast.len(es)/}
          fun post 1 = Eval(/Ast.nth(es,1)/, s)
            | post (i in range) = Eval(/Ast.nth(es,i-1)/, post (i-1))
          fun s 1 = ((post n).S)[/Ast.nthId(es,1)/ => (post 1).V]
            | s (i in range) = (s (i-1))[/Ast.nthId(es,i)/ => (post (i-1)).V]
        in
          Eval(/Ast.Body(es)/, s /Ast.len(es)/)
        end
     | Eval(/Ast.Case(e,match)/, s) =
        let
          val range = {1 ... /Ast.len(match)/}
          fun post 0 = Eval(/e/, s)
            | post (i in range) = Eval(/Ast.nth(match,i)/, (post 0).S)
        in
          +{post i | i from range}
        end
     | Eval(/Ast.Record(id,e)/, s) =
        (case /Ast.len(e)/
          of 0 => ((__, __, /id/, __), s)
           | n => let
                   fun post 1 = Eval(/Ast.nth(e, 1)/, s)
                     | post (k in {2 ... n})
                       = Eval(/Ast.nth(e, n)/, (post (k-1)).S)
                  in
                   ((__, __, /id/, __),
                    ((post n).S)[id => {i=> (post i).V | i from {1 ... n}}]
                   )
                  end
        )
     | Eval(/Ast.Select(e,k)/, s) = 
        let
          val post = Eval(/e/, s)
          fun asel id = post.S id (+ /k/ 1)
        in
          (+{asel id | id from post.V.K}, post.S)
        end
     | Eval(/Ast.Ref(e,id)/, s) =
        let
          val post = Eval(/e/, s)
        in
          ((__, /id/, __, __),
           (post.S)[/id/ => post.V])
        end
     | Eval(/Ast.Bang(e)/, s) =
        let
          val post = Eval(/e/, s)
          fun abang id = valueFetch(post.S, id)
        in
          (+{abang id | id from post.V.L}, post.S)
        end
     | Eval(/Ast.Assign(e)/, s) =
        let
          val post = Eval(/e/, s)
          val record = +{ (fn id => post.S id) id | id from post.V.K }
          val loc = (record 1).L
          fun assi id = (post.S)[id=> record 3]
        in
          case loc
          of __ => (__, post.S)
           | _ => (__, +{ assi id | id from loc })
        end
     | Eval(/Ast.Exn(e)/, s) = Eval(/e/, s)
     | Eval(/Ast.Raise(e)/, s) = Eval(/e/, s)
     | Eval(/Ast.Handle(e,x,e')/, s) = Eval(/e'/, (Eval(/e/, s)).S)
     | Eval(/Ast.Else/, s) = (__, s)
 end
