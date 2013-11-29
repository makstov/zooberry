(*
   Constant propagation analysis for ML's core.
   Derived from /home/kwang/Z1/zin/kir/cp.z
   Kwangkeun Yi 6/20/2001
*)

analysis ConstantProp = 
 ana
   set FnExp = /Ast.expr/
   set Id = /Ast.id/

   lattice C = power FnExp
   lattice L = power Id
   lattice V = C * L * K * Z
   lattice A = I -> V

   eqn Eval(s) = __ (* map ((__, __, __, numToZ n), s) __ *)
     | Eval(s) = 
        let
          val range = {1 ... /Ast.len(match)/}
          fun post' 0 = Eval(/e/, s)
            | post' (i in range) = Eval(/Ast.nth(match,i)/, (post' 0).S)
        in
          +{post' i | i from range}
        end
     | Eval(/Ast.Raise(e)/, s) = Eval(/e/, s)
     | Eval(/Ast.Handle(e,x,e')/, s) = Eval(/e'/, (Eval(/e/, s)).S)
     | Eval(/Ast.Else/, s) = (__, s)
 end
