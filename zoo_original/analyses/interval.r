analysis IntervalAnal =
ana
 set Int = /int/ + {--,++}
 lattice Z = Int * Int
             with join((a,b),(a',b')) =>
                  let
                    fun min(--,_) = --
                      | min(_,--) = --
                      | min(++,x) = x
                      | min(x,++) = x
                      | min(x,y) = if x<=y then x else y
                    fun max(--,x) = x
                      | max(x,--) = x
                      | max(++,x) = ++
                      | max(x,++) = ++
                      | max(x,y) = if x<=y then x else y
                  in
                    (min(a,a'), max(b,b'))
                  end
 widen Z with ((a,b),(a',b')) =>
              (if a'<=a then -- else a,if b'>=b then ++ else b)

end
