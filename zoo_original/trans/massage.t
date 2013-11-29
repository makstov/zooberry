(*
 Kwangkeun Yi, The LET Project, KAIST

 Copyright(c) 2000-2004 Research On Program Analysis System
 National Creative Research Initiative Center
 Korea Advanced Institute of Science & Technology
 http://ropas.kaist.ac.kr

 All rights reserved. This file is distributed under the terms of
 an Open Source License.
*)

(*
 Massage of Rabbit program for efficient computation of the generated analysis.
 We apply the transformation that functional language compilers routinely use.
 We assume that program to analyze is available.
*)

[Notation]

 X -> Y		= Rabbit code X becomes Y
 X -> Y1 //guard1
   -> Y2 //guard2
		= X becomes YN if the guardN is the first that holds.
[Massage Rules]
todo: the transformations used inside the GHC compiler
- inlining: be careful not to duplicate works.
- beta reductions.
- 

