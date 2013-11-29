(*
    짝수인 값을 계산하는 식이 있는가를 확인하는 프로그램 분석
*)

analysis EvenAnalysis =
  ana
    set Fn = /Ast.exp/
    set Id = /Ast.id/
    
    lattice V = flat {yes, no} + flat Fn
    lattice S = Id -> V

    fun numToV

    fun abs_add (top, _)   = top
      | abs_add (_, top)   = top
      | abs_add (yes, yes) = yes
      | abs_add (yes, no)  = no
      | abs_add (no, yes)  = no
      | abs_add (no, no)   = yes

    fun abs_sub (top, _)   = top
      | abs_sub (_, top)   = top
      | abs_sub (yes, yes) = yes
      | abs_sub (yes, no)  = no
      | abs_sub (no, yes)  = no
      | abs_sub (no, no)   = yes

    fun abs_mul (yes, _) = yes
      | abs_mul (_, yes) = yes
      | abs_mul (top, _) = top
      | abs_mul (_, top) = top
      | abs_mul (no, no) = no

    fun abs_div _ = top

    fun abs_eq (yes, no) = no
      | abs_eq (no, yes) = no
      | abs_eq _         = top

    fun abs_lt _ = top

    fun abs_gt _ = top

    fun abs_and (no, no) = no
      | abs_and _        = top

    fun abs_or  _ = top
      | abs_or

    eqn Eval(/Ast.INT(n)/, s)         = numToV /n/
      | Eval(/Ast.VAR(x)/, s)         = s /x/
      | Eval(/Ast.FN(x,e) as f/, s)   = /f/
      | Eval(/Ast.FX(x,e) as f/, s)   = /f/
      | Eval(/Ast.APP(e1,e2)/, s)     =
      | Eval(/Ast.LET((x,e1),e2)/, s) =
          let
            val s' = fn x' => if x = x' then e1 else s x'
          in
            eval(/e2/, s')
          end
      | Eval(/Ast.IF(e1,e2,e3)/, s)   =
          let
            val (v1, s1) = eval(/e1/, s)
            val (v2, s2) = eval(/e2/, s)
            val (v3, s3) = eval(/e3/, s)
          in
            case v1
              of top  => (v2 + v3, s)
               | even => (v3, s)
               | odd  => (v2 + v3, s)
          end
      | Eval(/Ast.BOP(bop,e1,e2)/, s) =
          let
            val (v1, s1) = eval(/e1/, s)
            val (v2, s2) = eval(/e2/, s)
          in
            case /bop/
              of /Ast.ADD/ => abs_add(v1,v2)
               | /Ast.SUB/ => abs_sub(v1,v2)
               | /Ast.MUL/ => abs_mul(v1,v2)
               | /Ast.DIV/ => abs_div(v1,v2)
               | /Ast.EQ/  => abs_eq(v1,v2)
               | /Ast.LT/  => abs_lt(v1,v2)
               | /Ast.GT/  => abs_gt(v1,v2)
               | /Ast.AND/ => abs_and(v1,v2)
               | /Ast.OR/  => abs_or(v1,v2)
          end
      | Eval(/Ast.READ/, s)           = (top, s)
      | Eval(/Ast.WRITE(e)/, s)       = Eval(/e/, s)
  end
