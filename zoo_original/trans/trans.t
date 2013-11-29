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
 * Translation of Rabbit program into nML program
 *)

[Notation]

 X -> Y		= X is a Rabbit code (a production rule) and Y is its
		  compiled nML code.
 X -> Y1 //guard1
   -> Y2 //guard2
		= X is compiled into YN if the guardN is the first that holds.
 X -> Y1 & Y2	= Rabbit code X is compiled into two nML codes: Y1 and Y2,
                  where Y1 is branched from X in the current translation tree
		  and Y2 is the beginning of a new tree.
 X -> Y1 & Y1' //guard1
   -> Y2       //guard2
		= combination of the guarded and multiple translation.
 _X_	   = X is a Rabbit code and _X_ represents its compiled nML code.
 _X/Z_	   = the same as _X_ but under context Z. Z can be anything.
 _X/Z1,Z2_ = the same as _X/Z_ but with multiple contexts Z1 and Z2.
 _Xrow_	   = _X1_, ..., _XN_ where Xrow = X1, ..., XN.
 _X_[A/B]   = the same as _X_ but A substitutes for B in _X_.
 <Z	   = <Z is the most recent Z in the current translation tree.
 <ty       = the Rabbit type of the translatee (ie, X in X -> Y).
 <tynom	   = the unique type name for Rabbit type <ty.
 <ty(X)	   = the Rabbit type of Rabbit object X.
 <tynom(X) = the unique type name for the Rabbit type <ty(X).
 Xlong     = Y if Xlongid = Y.a
 X#	   = a unique name with prefix X. The # can be indexed. 
	     X#'s scope is each trans rule.
 ><	   = not well-formed Rabbit; must have been rejected by tycheck.
 (*...*)   = comment 

[Notes/Invariants]
- Rabbit's type system follows the structural equivalence.
  i.e. 'Rabbit type' means the type contents not names.
- Every Rabbit term has a unique type.
- For each Rabbit type ty there is a unique name tynom.
- One implementation per Rabbit type.
- Minimize the intermediate data structures: deforest as much as possible at nml level
- Utilize Rabbit's sugars for economic translation

[Translation Rules]

_topdec_
	anadec -> _anadec_
	sigdec -> _sigdec_
	temdec -> _temdec_
	topdec1 topdec2 -> _topdec1_ _topdec2_

_anadec_
	analysis anaid = anaexp	-> structure anaid = _anaexp_
_sigdec_
	signature sigid = sigexp -> signature sigid = _sigexp_
_temdec_
	analysis temid(anaid1:sigexp1, anaid2:sigexp2) = anaexp
	-> functor temid(anaid1:_sigexp1_, anaid2:_sigexp2_) = _anaexp_

_anaexp_
	ana adec end	-> struct _adec_ end
	temid(anaexprow)-> temid(_anaexprow_)	(* functor app *)
	anaid		-> anaid
_sigexp_
	sig adesc end	-> sig _adesc_ end
	sigid		-> sigid

_adec_
	domdec		-> _domdec_
	semdec		-> _semdec_
	querydec	-> _querydec_
	adec1 adec2	-> _adec1_ _adec2_

_adesc_
	set setid	   -> structure Setid: SET (* generic sig SET  *)
	set setid:kind	   -> structure Setid: _kind/setsig_
	set setid = setexp -> structure Setid = _setexp_
	lattice latid	   -> structure Latid: LATTICE (* generic sig LATTICE *)
	lattice latid:kind -> structure Latid: _kind/latsig_
	lattice latid = latexp -> structure Latid = _latexp_
	val varid: ty	-> val varid: _ty_
	eqn varid: ty	-> val varid: _ty_
	query varid: ty	-> val varid: _ty_
	adesc1 adesc2	-> _adesc1_ _adesc2_

_kind/setsig_
	syntree	-> SYNTREE_SET
	index	-> INDEX_SET
	integer	-> INTEGER_SET
	power	-> POWER_SET
	sum	-> SUM_SET
	product	-> PROD_SET
	arrow	-> ARROW_SET
_kind/latsig_
	syntree	-> ><
	index	-> ><
	integer	-> ><
	power	-> POWER_LAT
	sum	-> SUM_LAT
	product	-> PROD_LAT
	arrow	-> ARROW_LAT

_domdec_
	setdec -> _setdec_
	latdec -> _latdec_
	widendec -> _widendec_
_setdec_ 
	set setid = setexp	-> structure Setid = _setexp_

_setexp_ (* compiled into a structure *)
	/tylongid/ 	-> AtomicSetFun(struct type elmt = tylongid  type index = tylongid val index = fn x => x)
	/strlongid/	-> strlongid
	setlongid	-> setlongid
	{e1 ... e2}	-> IntervalSetFun(struct type elmt = int ... end)
	{elmtidrow}	-> AtomicSetFun(struct type elmt =_elmtidrow_... end)
	power setexp 	-> PowerSetFun(_setexp_)
	setexp1 * setexp2	-> ProdSetFun(_setexp1_, _setexp2_)
	setexp1 + setexp2	-> SumSetFun(_setexp1_, _setexp2_)
	setexp1 -> setexp2	-> FunSetFun(_setexp1_, _setexp2_)
	(setexp)		-> _setexp_
	setexp constraint cnstdec	-> _setexp_
					& _constdec_
_cnstdec_
	var = {cvar1, cvar2} rhs = rhs
	-> structure Cnst<setid =
           struct
            type constraint = var<setid * rhs<setid
   	    and var = CVAR1 | CVAR2
            and rhs = _rhs_
           end

	var = {cvar1, cvar2} index setexp rhs = rhs
	-> structure Cnst<setid =
	   struct
	    type constraint = var<setid * rhs<setid
 	    and var = CVAR1 of _setexp/index_
		    | CVAR2 of _setexp/index_
            and rhs = _rhs_
	   end

_setexp/index_ (* index type for setexp *)
	/tylongid/ 	-> tylongid		(* tylongid is the index *)
	/strlongid/	-> strlongid.index
	setlongid	-> setlongid.index
	{e1 ... e2}	-> int
	{id1,id2}	-> S.index 	//if setexp is a defined set S 
			-> elmt_index#  //else
		        &  type elmt_index# = ID1 | ID2
	power setexp 	-> S.index 		//if setexp is a defined set S
			-> IndexSet#.index	//else 
			&  structure IndexSet#
			   = IndexPowerSetFun(_setexp_)
	setexp1 * setexp2	-> S.index 	//if setexp is a defined set S
				-> IndexSet#.index //else
				&  structure IndexSet#
				   = IndexProdSetFun(_setexp1_,_setexp2_)
	setexp1 + setexp2	-> S.index	//if setexp is a defined set S
				-> IndexSet#.index //else
				&  structure IndexSet#
				   = IndexSumSetFun(_setexp1_,_setexp2_)
	setexp1 -> setexp2	-> S.index	//if setexp is a defined set S
				-> IndexSet#.index //else
				&  structure IndexSet#
				   = IndexFunSetFun(_setexp1_,_setexp2_)
	(setexp)	-> _setexp/index_
	setexp constraint cnstdec	-> _setexp/index_

_rhs_
	var		-> RHSVAR of var
	var setlongid	-> RHSVAR# of setlong.Cnst<id.var (* must record which RHSVAR# is for which set *)
	conid		-> CONID
	conid carg	-> CONID of _carg_
	conid (carg1,carg2) -> CONID of _carg1_ * _carg2_
	rhs1 | rhs2	-> _rhs1_ | _rhs2_

_carg_ (* type of constraint conid's arguments *)
	var	-> var
	var setlongid -> setlong.Cnst<id.var
	setexp	-> S.elmt	// if setexp is a defined set S
		-> Set#.elmt	// else
		&  structure Set# = _setexp_
	(cargrow) -> (_cargrow_)

_latdec_
	lattice latid = latexp	-> structure Latid = _latexp_
_latexp_
	/strlongid/	-> strlongid
	latlongid	-> latlongid
	flat setexp	-> FlatLatFun(_setexp_)
	power setexp	-> PowerLatFun(_setexp_)
	latexp1 * latexp2	-> ProdLatFun(_latexp1_,_latexp2_)
	latexp1 -> latexp2	-> AtomFnLatFun(_latexp1_,_latexp2_)
	setexp -> latexp	-> DepFnLatFun(_setexp_,_latexp_)
	setexp order order	-> CustomLatFun(_setexp_,_order_) (* must share the elmt types of the setexp and the order structures *)
	(latexp)	-> _latexp_

_widendec_
	widen latid with match	->
				& fun widen _match_ (* add this to structure Latid *)
_semdec_
	valdec -> _valdec_
	eqndec -> _eqndec_
	ccrdec -> _ccrdec_
	cimdec -> _cimdec_
_valdec_
	val vbind     -> val _vbind_
	val rec vbind -> val rec _vbind_
_vbind_
	pat = e		  -> _pat_ = _e_
	pat = e and vbind -> _pat_ = _e_ and _vbind_

_pat_	(* case when the pat is inside a binding (not inside switch) *)
	/npat/	-> npat
	_	-> _
	varid	-> varid
	{patrow ...} 	-> >< (* no binding possible: why? *)
	{pat1 ... pat2} -> x# (* x# is an interval *)
 			&  val _pat1_ = <tynom.min x# (* x#: power int, <tynom is the set structure that implements power int as intervals *)
	                   val _pat2_ = <tynom.max x# (* x#: power int, <tynom is the set structure that implements power int as intervals *)
	{varid => const ...}	-> x# & val _ = if not (<tynom.constant x# _const_) then raise MatchFailture
        {_ => const ...}	-> x# & val _ = if not (<tynom.constant x# _const_) then raise MatchFailture
	{const1 => pat, (varid|_) => const ...}	-> x# & val y# as _pat_ = <tynom(pat).image x# _const1_
							val _ = if not(<tynom(pat).constant (<tynom(pat).shadow x# _const1_ y#) _const_)
								then raise MatchFailure 
	{const1 => pat1, const2 => pat2 ...}	-> x# &  val _pat1_ = <tynom.image x# _const1_
							 val _pat2_ = <tynom.image x# _const2_
	in (1|2) ty pat -> (_pat_:_ty_)		(* is the type hint needed? *)
	(pat1, pat2)    -> (_pat1_, _pat2_)
	pat with guard  -> _pat_ 
		        & val _ = if _guard_ then 0 else raise GuardFailure
	pat1 or pat2 -> ><
	varid as pat -> varid as _pat_ 
	pat: ty -> (_pat_:_ty_)
	(pat)   -> (_pat_)
	(* sweet sugar *)
	const   	-> _const_

_guard_
	e1 rop e2	-> (<tynom(e1).rop _e1_ _e2_)	// tynom(e1) = lattice (see for other cases)
			-> (_e1_ intform(rop) _e2_)	// tynom(e1) = int
	e1 in e2	-> (<tynom(e2).in _e1_ _e2_)
	not guard	-> (not _guard_)
	(guard)		-> (_guard_)
	guard1 and guard2 -> (_guard1_ andalso _guard2_)
	guard1 or guard2  -> (_guard1_ orelse _guard2_)
	! pat from e . guard 		-> (<tynom(e).fold (fn _pat_ _ => if (not _guard_) then raise FalseForall else true) true _e_)
					   handle FalseForall => false
	! pat=>pat' from e . guard 	-> (<tynom(e).fold (fn (_pat_,_pat'_) _ => if (not _guard_) then raise FalseForall else true) true _e_)
					   handle FalseForall => false
	? pat from e . guard 		-> (<tynom(e).fold (fn _pat_ _ => if _guard_ then raise TrueForsome else false) false _e_)
					   handle TrueForsome => true
	? pat=>pat' from e . guard 	-> (<tynom(e).fold (fn (_pat_,_pat'_) _ => if _guard_ then raise TrueForsome else false) false _e_)
					   handle TrueForsome => true
(* eqn a 1 = f1
     | a 2 = f2
   and b 1 = g1
     | b 2 = g2
 ->
   fun F a1 f = f1[f a/a, f b/b]
     | F a2 f = f2[f a/a, f b/b]
     | F b1 f = g1[f a/a, f b/b]
     | F b2 f = g2[f a/a, f b/b]

 This F is used inside the fixpoint engine as follows:
       \forall x in {a1, a2, b}.T[x] <- bottom
       repeat
         \forall x.T[x] <- F x f
       until T stable
 where
   fun f x i = T["xi"]
*)
  
_eqndec_
	eqn ebind -> fun F# _ebind_	(* F# is the name of the functional to be called from the fixpoint engine *)
_ebind_
	varid = e 	    -> varid = _e_	(* remember this varid (equation name); it will be passed to the fixpoint engine *)
	varid = e and ebind -> varid = _e_ | F# _ebind_ (* F# is the name that prefixes the _ebind_ *)

(*
_ccrdec_
	ccr cnstguard1 -- constraintrow1 | cnstguard2 -- constraintrow2
	-> (* TODO: a function to close constraints, needs bird's eye view (nbev) *)
_cnstguard_
	constraint	-> _constraint_
	guard		-> _guard_
	cnstguard1 , cnstguard2 -> _cnstguard1_ ... _cnstguard2_ ... (* TODO: nbev *)
*)

_constraint_
	cvarexp <- rhsexp	-> ((_cvarexp_, _rhsexp_): Cnst<tynom(constraint).constraint)
_cvarexp_
	cvarlongid	 -> cvarlong.Cnst<tynom.id	
	cvarlongid @ pat -> cvarlong.Cnst<tynom.id(_pat_)	// pat must consist of constants and variables
_rhsexp_
	cvarexp		-> Cnst<tynom.RHSVAR#(_cvarexp_)   (* the RHSVAR# is determined by the cvarexp and corresponding Cnst<tynom's rhs *)
	conlongid	-> conlong.Cnst<tynom.Id
	conlongid cargexp -> (conlong.Cnst<tynom.Id _cargexp_)

_cargexp_
	cvarexp		-> _cvarexp_
	pat		-> _pat_	(* pat must consists of constants and variables *)
	(cargexprow)	-> (_cargexprow_)

(*
_cimdec_
	cim conlongid = e	-> &  conlongid = _e_       (* substitute _e_ for conlongid in the semantic eqn *)
	cim conlongid pat = e	-> &  conlongid _pat_ = _e_ (* substitute _e_ for conlongid e in the semantic eqn *)
*)

_e_
	/nmlexp/	-> (nmlexp)
	setlongid	-> <tynom.top	
	const		-> (_const_)
	varlongid	-> varlongid		// varlongid is not an equation variable
	constraint	-> _constraint_ 
	e1 + e2	-> (<tynom.join _e1_ _e2_)	
	e1 * e2 -> (<tynom.meet _e1_ _e2_)
	e1 - e2 -> (<tynom.minus _e1_ _e2_)	// ty is a set
		-> (_e1_-_e2_)			// ty is int
	e1 < e2 -> not(<tynom.leq _e2_ _e1_)	// ty is a lattice
	e1 > e2 -> not(<tynom.leq _e1_ _e2_)	// ty is a lattice
	e1 = e2 -> (<tynom.eq _e1_ _e2_)
	e1 <= e2 -> (<tynom.leq _e1_ _e2_)
	e1 >= e2 -> (<tynom.leq _e2_ _e1_)
	{e1...e2} 	-> (<tynom.make_interval _e1_ _e2_)
	{e1,e2}		-> (<tynom.make2 _e1_ _e2_)
	{e1,e2|qual}	-> (_qual/e1,e2_)
	{pat1=>e1,pat2=>e2}	-> (<tynom.make2 (_pat_,_e1_) (_pat2_,_e2_)) 	// patN consists of constant and var
	{pat1=>e1,pat2=>e2|qual}-> (_qual/patN=>eN_)	// patN consist of constant and var
	{}		-> (<tynom.bottom)
	+ (map e1 e2)	-> (<tynom(e2).mapfold _e1_ _e2_ (fn x y => <tynom(map-exp).join x y) <tynom(map-exp).bottom)	// not ty(e1) = .-> int
			-> (<tynom(e2).mapfold _e1_ _e2_ (fn x y => x+y) 0)	// ty(e1) = .->int
	+ e		-> (<tynom(e).joinN _e_)
	* (map e1 e2)	-> (<tynom(e2).mapfold _e1_ _e2_ (fn x y => <tynom(map-exp).meet x y) <tynom(map-exp).bottom)	// not ty(e1) = .-> int
			-> (<tynom(e2).mapfold _e1_ _e2_ (fn x y => x*y) 0)	// ty(e1) = .->int
	* e		-> (<tynom(e).meetN _e_)
	(e1, e2)	-> (_e1_, _e2_)
	e.N		-> (_e_.N)
	in (1) ty e	-> (<tynom.First _e_)
	in (2) ty e 	-> (<tynom.Second _e_)
	let valdec in e end	-> (let _valdec_ in _e_ end)
	fn match	-> fn _match_
	e1 e2		-> (_e1_ _e2_)			// ty(e1) is a computational ftn
			-> (<tynom(e1).image _e1_ _e2_)	// ty(e1) is a ftn domain element
	(e)	-> (_e_)
	e:ty	-> (_e_:_ty_)
	varlongid	-> varlong.Fixpoint.T (string_index id)		// varlongid is an equation variable 
	varlongid @ e	-> varlong.Fixpoint.T (stringintpair_index id (<tynom(e).index _e_))		(* varlongid is the eqn variable/function id *)
	pre (varlongid @ e)  -> varlong.Fixpoint.Tx (index id (<tynom(e).index _e_))	
	post (varlongid @ e) -> varlong.Fixpoint.Ty (index id (<tynom(e).index _e_))
(*	cvarlongid @ e	-> 		 (* the result of applying the ccr and cim *) *)

	(* sweet sugars: sugars that can be translated into more efficient nML codes than being macro-expanded *)
	e [pat=>e']	-> (<tynom.shadow _e_ _pat_ _e'_)	// pat must consists of constant or varaible 
	case e of match	-> (case _e_ of _match_)
	if e1 then e2 else e3 	-> (if _e1_ then _e2_ else _e3_)
	map e1 e2	-> (<tynom(e2).map _e1_ _e2_)
	

_qual/e1,e2_	(* todo: if patterns are not exhaustive, then bottom *)
	pat from e -> <tynom(power eN).joinN
		      (<tynom(e).map (fn _pat_ => <tynom.make2 _e1_ _e2_) _e_)	
	pat from e, guard -> <tynom.joinN
			     (<tynom(e).map (fn _pat_ => if _guard_ then <tynom.make2 _e1_ _e2_ else <tynom.bottom)
					    _e_)
	pat=>pat' from e-> <tynom.joinN
		            (<tynom(e).map (fn (_pat_,_pat'_) => <tynom.make2 _e1_ _e2_) _e_)
	pat=>pat' from e, guard -> <tynom.joinN
			           (<tynom(e).map (fn (_pat_,_pat'_) => if _guard_ then <tynom.make2 _e1_ _e2_
									else <tynom.bottom)
						  _e_)
	pat1 from e1, pat2=>pat2' from e2, guard
		-> <tynom.joinN (<tynom(e1).map
			          (fn _pat1_ =>
				    <tynom(e2).map
				     (fn (_pat2_,_pat2'_) => if _guard_ then <tynom.make2 _e1_ _e2_ else <tynom.bottom)
				     _e2_)
				  _e1_)

_qual/patN=>eN_		// pat' must consist of constant and var so that patN=>eN be expressions
	pat from e -> <tynom.joinN (<tynom(e).map (fn _pat_ => <tynom.make (_patN_, _eN_)) _e_)
	pat from e, guard -> <tynom.joinN
			     (<tynom(e).map (fn _pat_ => if _guard_ then <tynom.make (_patN_, _eN_) else <tynom.bottom)
					    _e_)
	pat1=>pat2 from e-> <tynom.joinN
		            (<tynom(e).map (fn (_pat1_,_pat2_) => <tynom.make (_patN_, _eN_))
					   _e_)
	pat1=>pat2 from e, guard -> <tynom.joinN
			            (<tynom(e).map (fn (_pat1_,_pat2_) => if _guard_ then <tynom.make (_patN_, _eN_) else <tynom.bottom)
						   _e_)
	pat1 from e1, pat2=>pat2' from e2, guard
		-> <tynom.joinN (<tynom(e1).map
				  (fn _pat1_ => 
				    <tynom(e2).map
				      (fn (_pat2_,_pat2'_) => if _guard_ then <tynom.make (_patN_,_eN_) else <tynom.bottom)
				      _e2_)
				  _e1_)
_const_
	integer		-> integer
	elmtlongid	-> <tynom.elmtlongid
	top		-> <tynom.top
	^		-> <tynom.top
	bottom		-> <tynom.bottom
	__		-> <tynom.bottom
	true		-> true
	false		-> false
	
_match_
	/npat/ => e 	-> npat => _e_
        _ => e		->    _ => _e_
	{const ...} => e 	-> x# => if <tynom(pat).in _const_ x# then _e_ else raise MatchFailure
        {pat1 ... pat2} => e	-> x# => let val _pat1_ = <tynom(pat).interval_min x#
					     val _pat2_ = <tynom(pat).interval_max x#
					 in _e_ end
	{varid => const ...} => e -> x# => if <tynom(pat).constant x# _const_ then _e_ else raise MatchFailure 
        {_ => const ...} => e	  -> x# => if <tynom(pat).constant x# _const_ then _e_ else raise MatchFailure
	{const1 => pat, (varid|_) => const ...} => e	-> x# => let val y# as _pat_ = <tynom(pat).image x# _const1_
								 in if <tynom(pat).constant (<tynom(pat).shadow x# _const1_ y#) _const_
								    then _e_ else raise MatchFailure end
	{const1 => pat1, const2 => pat2 ...} => e	-> x# => let val _pat1_ = <tynom(pat).image x# _const1_
								     val _pat2_ = <tynom(pat).image x# _const2_
								 in _e_ end
	in (1|2) ty pat => e	-> _pat:ty=>e_  (* match object *)
	(pat1, pat2) => e	-> (x#, y#) => (case x# of _pat1_ => (case y# of _pat2=>e_)) handle _ => raise MatchFailure
	pat with guard => e 	-> _pat_ => if _guard_ then _e_ else raise MatchFailure
	pat1 or pat2 => e	-> _pat1=>e_ | _pat2=>e_
	varid as pat => e	-> varid as _pat=>e_
	pat: ty => e	-> _pat=>e_ & _ty_
        (pat) => e	-> _pat=>e_
	const => e	-> const => _e_

	pat1 => e1 | match	-> _pat1=>e1_[(case x# of _match_)/raise MatchFailure] | _match_

_ty_
	int	-> int
	domlongid	-> (paramtype) domlongid.elmt	// paramtype is the parameter type of domlongid's element type
	/tylongid/	-> tylongid
	ty1 * ty2	-> _ty1_ * _ty2_
	ty1 + ty2	-> (paramtype) <tynom.elmt	// paramtype is the parameter type of domlongid's element type
	ty1 -> ty2	-> _ty1_ -> _ty2_	(* type for computation function, not ftn set or lattice *)
	(ty)	-> (_ty_)
	ty:kind	-> _ty_ & (* record that ty is the kind *)

(*
_querydec_
	query ctlbind	-> fun _ctlbind_ 
_ctlbind_ 
	ctlid = ctl	-> ctlid = _ctl_ 
	ctlid = ctl and ctlbind	-> ctlid = _ctl_ and _ctlbind_ 
_ctl_ 
	varid: varlongid . form		-> 
	varid: pre varlongid . form 	->
	(ctl)	-> (_ctl_) 
*)
