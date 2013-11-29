/*====================================================================*/
/*  You-il Kim, The LET Project, KAIST                                */
/*--------------------------------------------------------------------*/
/*  Copyright(c) 2001 Research On Program Analysis System             */
/*  National Creative Research Initiative Center                      */
/*  Korea Advanced Institute of Science & Technology                  */
/*  http://ropas.kaist.ac.kr                                          */
/*--------------------------------------------------------------------*/
/*  All rights reserved. This file is distributed under the terms of  */
/*  an Open Source License.                                           */
/*====================================================================*/

/*--------------------------------------------------------------------*/
/*  Rabbit parser for nyacc                                           */
/*--------------------------------------------------------------------*/

%{

open RabbitAst
open ErrorInfo
open Print


(* Default YACC error handler *)

fun parse_error msg = 
    let
        val error_line = FileInfo.get_current_line_number ()
        val error_pos1 = FileInfo.get_current_token_start ()
        val error_pos2 = error_pos1 - FileInfo.get_current_line_start () + 1
    in
        print_int error_line;
        print_string ".";
        print_int error_pos2;
        print_string ": ";

        print_string msg;
        print_newline ()
    end


(* Get the region structure *)

fun region () =
    let
        val start_loc = FileInfo.get_loc (Parsing.symbol_start ())
        val end_loc   = FileInfo.get_loc (Parsing.symbol_end ())
    in
        Region.make_region start_loc end_loc
    end

fun region_of n =
    let
        val start_loc = FileInfo.get_loc (Parsing.rhs_start n)
        val end_loc   = FileInfo.get_loc (Parsing.rhs_end n)
    in
        Region.make_region start_loc end_loc
    end

fun merged_region_of s e =
    let
        val start_region = region_of s
        val end_region   = region_of e
    in
        Region.merge_region start_region end_region
    end


(* Keep information of variables *)

val check_ctlid = ref false
val check_anaid = ref false

exception InternalError;

val anaid_env = ref [([]:string list)]
val setid_env = ref [([]:string list)]
val latid_env = ref [([]:string list)]
val ctlid_env = ref [([]:string list)]
val cvarid_env = ref [([]:string list)]

fun general_push [] = raise InternalError
  | general_push ll = ([]::ll)

fun push_anaid_env () = (anaid_env := general_push (!anaid_env))
fun push_setid_env () = (setid_env := general_push (!setid_env))
fun push_latid_env () = (latid_env := general_push (!latid_env))
fun push_ctlid_env () = (ctlid_env := general_push (!ctlid_env))
fun push_cvarid_env () = (cvarid_env := general_push (!cvarid_env))

fun general_pop []      = raise InternalError
  | general_pop (_::[]) = raise InternalError
  | general_pop (_::ll) = ll

fun pop_anaid_env () = (anaid_env := general_pop (!anaid_env))
fun pop_setid_env () = (setid_env := general_pop (!setid_env))
fun pop_latid_env () = (latid_env := general_pop (!latid_env))
fun pop_ctlid_env () = (ctlid_env := general_pop (!ctlid_env))
fun pop_cvarid_env () = (cvarid_env := general_pop (!cvarid_env))

fun general_store s []      = raise InternalError
  | general_store s (l::ll) = ((s::l)::ll)

fun store_anaid s = (anaid_env := general_store s (!anaid_env))
fun store_setid s = (setid_env := general_store s (!setid_env))
fun store_latid s = (latid_env := general_store s (!latid_env))
fun store_ctlid s = (ctlid_env := general_store s (!ctlid_env))
fun store_cvarid s = (cvarid_env := general_store s (!cvarid_env))

fun general_lookup s [] = raise InternalError
  | general_lookup s ll = 
        (List.exists (fn l => List.exists (fn x => x = s) l) ll)

fun is_anaid s = general_lookup s (!anaid_env)
fun is_setid s = general_lookup s (!setid_env)
fun is_latid s = general_lookup s (!setid_env)
fun is_ctlid s = general_lookup s (!ctlid_env)
fun is_cvarid s = general_lookup s (!cvarid_env)


(* Intermediate parse tree *)

type domexp = NmlTyDom of string                * Region.region
            | IdDom of domlongid                * Region.region
            | IntervalDom of exp * exp          * Region.region
            | EnumDom of elmtid list            * Region.region
            | FlatDom of setexp                 * Region.region
            | PowerDom of setexp                * Region.region
            | ProductDom of domexp list         * Region.region
            | SumDom of domexp list             * Region.region
            | ArrowDom of domexp * domexp       * Region.region
            | OrderDom of setexp * order        * Region.region
            | ConstraintDom of setexp * cnstdec * Region.region

fun is_setexp (NmlTyDom _)         = True
  | is_setexp (IdDom _)            = True
  | is_setexp (IntervalDom _)      = True
  | is_setexp (EnumDom _)          = True
  | is_setexp (FlatDom _)          = False
  | is_setexp (PowerDom _)         = True
  | is_setexp (ProductDom (l,_))   = is_setexp_list l
  | is_setexp (SumDom (l,_))       = is_setexp_list l
  | is_setexp (ArrowDom (d1,d2,_)) = (is_setexp d1) andalso (is_setexp d2)
  | is_setexp (OrderDom _)         = False
  | is_setexp (ConstraintDom _)    = True

and is_setexp_list []     = True
  | is_setexp_list (d::l) = (is_setexp d) andalso (is_setexp_list l)

fun is_latexp (NmlTyDom _)         = True
  | is_latexp (IdDom _)            = True
  | is_latexp (IntervalDom _)      = False
  | is_latexp (EnumDom _)          = False
  | is_latexp (FlatDom _)          = True
  | is_latexp (PowerDom _)         = True
  | is_latexp (ProductDom (l,_) )  = is_latexp_list l
  | is_latexp (SumDom (l,_))       = is_latexp_list l
  | is_latexp (ArrowDom (d1,d2,_)) = is_latexp d2
  | is_latexp (OrderDom _)         = True
  | is_latexp (ConstraintDom _)    = False

and is_latexp_list []     = True
  | is_latexp_list (d::l) = (is_latexp d) andalso (is_latexp_list l)

val rec print_domexp = fn
    (NmlTyDom _) => print_string "NmlTyDom()"
  | (IdDom _) => print_string "IdDom()"
  | (IntervalDom _) => print_string "IntervalDom()"
  | (EnumDom _) => print_string "EnumDom()"
  | (FlatDom _) => print_string "FlatDom()"
  | (PowerDom _) => print_string "PowerDom()"
  | (ProductDom _) => print_string "ProductDom()"
  | (SumDom _) => print_string "SumDom()"
  | (ArrowDom _) => print_string "ArrowDom()"
  | (OrderDom _) => print_string "OrderDom()"
  | (ConstraintDom _) => print_string "ConstraintDom()"

fun setexp_of (NmlTyDom (s,r))        = NmlTySet (s,r)
  | setexp_of (IdDom (s,r))           = IdSet (s,r)
  | setexp_of (IntervalDom (e1,e2,r)) = IntervalSet (e1,e2,r)
  | setexp_of (EnumDom (l,r))         = EnumSet (l,r)
  | setexp_of (FlatDom (_,r))         = raise Error (Invalid_setexp,r)
  | setexp_of (PowerDom (d,r))        = PowerSet (d,r)
  | setexp_of (ProductDom (l,r))      = ProductSet (List.map setexp_of l,r)
  | setexp_of (SumDom (l,r))          = SumSet (List.map setexp_of l,r)
  | setexp_of (ArrowDom (d1,d2,r))    = FunSet (setexp_of d1,setexp_of d2,r)
  | setexp_of (OrderDom (_,_,r))      = raise Error (Invalid_setexp,r)
  | setexp_of (ConstraintDom (d,c,r)) = CnstSet (d,c,r)

fun latexp_of (NmlTyDom (s,r))        = NmlStrLat (s,r)
  | latexp_of (IdDom (s,r))           = IdLat (s,r)
  | latexp_of (IntervalDom (_,_,r))   = raise Error (Invalid_latexp,r)
  | latexp_of (EnumDom (_,r))         = raise Error (Invalid_latexp,r)
  | latexp_of (FlatDom (d,r))         = FlatLat (d,r)
  | latexp_of (PowerDom (d,r))        = PowerLat (d,r)
  | latexp_of (ProductDom (l,r))      = ProductLat (List.map latexp_of l,r)
  | latexp_of (SumDom (l,r))          = SumLat (List.map latexp_of l,r)
  | latexp_of (ArrowDom (d1,d2,r))    = 
        if is_latexp d1 then AtomicLat (latexp_of d1,latexp_of d2,r)
                        else DependLat (setexp_of d1,latexp_of d2,r)
  | latexp_of (OrderDom (d,o,r))      = OrderLat (d,o,r)
  | latexp_of (ConstraintDom (_,_,r)) = raise Error (Invalid_latexp,r)

type common = Nml of string                 * Region.region
            | Id of id                      * Region.region
            | LongId of id list             * Region.region
            | Const of const                * Region.region
            | Set of common list            * Region.region
            | Map of map list               * Region.region
            | Tuple of common list          * Region.region
            | Interval of common * common   * Region.region
            | Join of common * common       * Region.region
            | Meet of common * common       * Region.region
            | Coercion of common * ty       * Region.region
            | Index of common * common      * Region.region
            | Exp of exp                    * Region.region
            | Pat of pat                    * Region.region
            (*
            | Cargexp of cargexp            * Region.region
            *)
            | Ty of ty                      * Region.region
            | Rop of common * rop * exp     * Region.region

and map     = common * common               * Region.region

fun get_region (Nml (_,r))        = r
  | get_region (Id (_,r))         = r
  | get_region (LongId (_,r))     = r
  | get_region (Const (_,r))      = r
  | get_region (Set (_,r))        = r
  | get_region (Tuple (_,r))      = r
  | get_region (Interval (_,_,r)) = r
  | get_region (Join (_,_,r))     = r
  | get_region (Meet (_,_,r))     = r
  | get_region (Map (_,r))        = r
  | get_region (Coercion (_,_,r)) = r
  | get_region (Index (_,_,r))    = r
  | get_region (Exp (_,r))        = r
  | get_region (Pat (_,r))        = r
  (*
  | get_region (Cargexp (_,r))    = r
  *)
  | get_region (Ty (_,r))         = r
  | get_region (Rop (_,_,_,r))    = r

fun is_id (Id _) = True
  | is_id _ = False

fun is_longid (Id _) = True
  | is_longid (LongId _) = True
  | is_longid _ = False

fun is_pat (Nml _)            = True
  | is_pat (Id _)             = True
  | is_pat (Const _)          = True
  | is_pat (Set (l,_))        = is_pat_list l
  | is_pat (Map (l,_))        = is_mpat_list l
  | is_pat (Tuple (l,_))      = is_pat_list l
  | is_pat (Interval (x,y,_)) = (is_pat x) andalso (is_pat y)
  | is_pat (Pat _)            = True
  | is_pat (Rop (x,_,_,_))    = is_pat x
  | is_pat _ = False

and is_pat_list []            = True
  | is_pat_list (first::rest) = (is_pat first) andalso (is_pat_list rest)

and is_mpat (p1,p2,_) = (is_pat p1) andalso (is_pat p2)

and is_mpat_list []            = True
  | is_mpat_list (first::rest) = (is_mpat first) andalso (is_mpat_list rest)


fun id_of (Id (i,r)) = (i,r)
  | id_of c = raise Error (Invalid_id, get_region c)

fun longid_of (Id (i,r)) = (i::[],r)
  | longid_of (LongId (l,r)) = (l,r)
  | longid_of c = raise Error (Invalid_longid, get_region c)

fun exp_of (Nml (e,r))     = NmlExp (e,r)
  | exp_of (Id (e,r))      = if is_setid e 
                             then SetIdExp ((e::[],r),r)
                             else IdExp ((e::[],r),r)
  | exp_of (LongId (n1::n2::[],r)) = if is_setid n2 
                                     then SetIdExp ((n1::n2::[],r),r)
                                     else IdExp ((n1::n2::[],r),r)
  | exp_of (Const (e,r))  = ConstExp (e,r)
  | exp_of (Set (l,r))    = EnumSetExp ((exp_list_of l), r)
  | exp_of (Map (l,r))    = MapExp ((mrule_list_of l), r)
  | exp_of (Tuple (l,r))  = TupleExp ((exp_list_of l), r)
  | exp_of (Interval (e1,e2,r)) = IntervalSetExp (exp_of e1, exp_of e2, r)
  | exp_of (Join (e1,e2,r)) = BopExp (exp_of e1, PlusOp, exp_of e2, r)
  | exp_of (Meet (e1,e2,r)) = BopExp (exp_of e1, MultiOp, exp_of e2, r)
  | exp_of (Coercion (e,ty,r)) = CoerceExp (exp_of e, ty, r)
  | exp_of (Index (longid,exp,r)) = IndexExp ({tag=None, eqnid=(longid_of longid), index=(exp_of exp)},r)
  | exp_of (Exp (e,r))      = e
  | exp_of (Rop (e1,rop,e2,r)) = BopExp (exp_of e1, RelOp rop, e2, r)
  | exp_of c = raise Error (Invalid_exp, get_region c)

and exp_list_of [] = []
  | exp_list_of (first::rest) = (exp_of first)::(exp_list_of rest)

and pat_of (Nml (p,r))   = NmlPat (p)
  | pat_of (Id (p,r))    = VarPat (p,r)
  | pat_of (LongId ([anaid,elmtid],r)) = ConstPat (ElmtIdConst ([anaid,elmtid],r))
  | pat_of (Const (p,r)) = ConstPat (p)
  | pat_of (Set (l,r))   = SetPat (pat_list_of l)
  | pat_of (Map (l,r))   = MapPat (mpat_list_of l)
  | pat_of (Tuple (l,r)) = TuplePat (pat_list_of l)
  | pat_of (Interval (p1,p2,r)) = IntervalSetPat (pat_of p1, pat_of p2)
  | pat_of (Coercion (p,ty,r)) = TyPat (pat_of p, ty)
  | pat_of (Pat (p,r))   = p
  | pat_of (Rop (p,rop,e,r)) = RopPat (pat_of p, rop, e)
  | pat_of c = raise Error (Invalid_pat, get_region c)

and pat_list_of [] = []
  | pat_list_of (first::rest) = (pat_of first)::(pat_list_of rest)


and mrule_of (p,e,r) = (pat_of p, exp_of e, r)

and mpat_of (p1,p2,r) = (pat_of p1, pat_of p2)

and mrule_list_of l = List.map mrule_of l

and mpat_list_of l = List.map mpat_of l


fun ty_of (Nml (t,r))      = NmlTy (t,r)
  | ty_of (Id (t,r))       = DomTy ((t::[],r),r)
  | ty_of (LongId (l,r))   = DomTy ((l,r),r)
  | ty_of (Join (t1,t2,r)) = SumTy ((ty_of t1)::(ty_of t2)::[], r)
  | ty_of (Meet (t1,t2,r)) = TupleTy ((ty_of t1)::(ty_of t2)::[], r)
  | ty_of (Ty (t,r))       = t
  | ty_of c = raise Error (Invalid_ty, get_region c)

and ty_list_of [] = []
  | ty_list_of (first::rest) = (ty_of first)::(ty_list_of rest)


fun cvarexp_of (Id (n,r)) = {cvarid=([n],r), index=None}
  | cvarexp_of (LongId (l,r)) = {cvarid=(l,r), index=None}
  | cvarexp_of (Index (c1,c2,r)) = {cvarid=(longid_of c1), index=(Some (pat_of c2))}
  (*
  | cvarexp_of (Cargexp (CargexpCvar e,r)) = e
  *)
  | cvarexp_of c = raise Error (Invalid_cvarexp, get_region c)

fun cargexp_of (Tuple (l,r)) = CargexpTuple (cargexp_list_of l)
  | cargexp_of (Index (c1,c2,r)) = CargexpCvar (cvarexp_of (Index (c1,c2,r)))
  (*
  | cargexp_of (Cargexp (c,r)) = c
  *)
  | cargexp_of c = if is_pat c then CargexpPat (pat_of c) 
                               else raise Error (Invalid_cargexp, get_region c)

and cargexp_list_of [] = []
  | cargexp_list_of (first::rest) = (cargexp_of first)::(cargexp_list_of rest)



fun dissolve_sugared_order _ [] = []
  | dissolve_sugared_order pat1 ((po,pat2)::rest) =
        (po,TuplePat [pat1,pat2])::(dissolve_sugared_order pat2 rest)
%}


/*--------------------------------------------------------------------*/
/*  Tokens                                                            */
/*--------------------------------------------------------------------*/

%token ANA
%token ANALYSIS
%token AND
%token ARROW
%token AS
%token ATOMIC
%token BOTTOM
%token CASE
%token CCR
%token CIM
%token CONSTRAINT
%token ELSE
%token END
%token EQN
%token FALSE
%token FLAT
%token FN
%token FROM
%token FUN
%token IF
%token IN
%token INDEX
%token INT
%token LATTICE
%token LET
%token MAP
%token MP
%token NOT
%token OF
%token OR
%token ORDER
%token POST
%token POWER
%token PRE
%token PRODUCT
%token REC
%token RHS
%token QUERY
%token SET
%token SIG
%token SIGNATURE
%token SUM
%token SYNTREE
%token THEN
%token TOP
%token TRUE
%token VAL
%token VAR
%token WIDEN
%token WITH

%token AF
%token AG
%token AU
%token AX
%token EF
%token EG
%token EU
%token EX

%token UNDER        /* "_"      */
%token UNDERUNDER   /* "__"     */
%token LPAREN       /* "("      */
%token RPAREN       /* ")"      */
%token LBRACE       /* "{"      */
%token RBRACE       /* "}"      */
%token LBRACKET     /* "["      */
%token RBRACKET     /* "]"      */
%token COLON        /* ":"      */
%token COMMA        /* ","      */
%token STAR         /* "*"      */
%token PLUS         /* "+"      */
%token MINUS        /* "-"      */
%token LEFTARROW    /* "<-"     */
%token RIGHTARROW   /* "->"     */
%token BOTHARROW    /* "<->"    */
%token DOUBLEARROW  /* "=>"     */
%token AT           /* "@"      */
%token HAT          /* "^"      */
%token BAR          /* "|"      */
%token DOT          /* "."      */
%token DOTDOTDOT    /* "..."    */
%token BANG         /* "!"      */
%token QUESTION     /* "?"      */
%token LT           /*  "<"     */
%token GT           /*  ">"     */
%token EQ           /*  "="     */
%token LE           /*  "<="    */
%token GE           /*  ">="    */
%token LINE
%token EOF

%token <string> LID
%token <string> UID
%token <string> SID
%token <int>    INTNUM
%token <string> NMLEXP

%token <string> CTLID
%token <string> ANAID


/*--------------------------------------------------------------------*/
/*  Precedences and Associativities (lower precedences come first)    */
/*--------------------------------------------------------------------*/


/*--------------------------------------------------------------------*/
/*  Entry points                                                      */
/*--------------------------------------------------------------------*/

%start rabbit
%type <RabbitAst.topdec> rabbit


%%

/*--------------------------------------------------------------------*/
/*  Rules                                                             */
/*--------------------------------------------------------------------*/

rabbit
    : topdec_list EOF
      { $1 }
    ;

id
    : LID
      { ($1, region ()) }
    | UID
      { ($1, region ()) }
    | SID
      { ($1, region ()) }
    ;

id_row
    : id
      { $1::[] }
    | id COMMA id_row
      { $1::$3 }
    ;

topdec
/*
    : adec
      {
        ADec ($1::[])
      }
*/
    : anadec
      {
        AnaDec $1
      }
    | sigdec
      {
        SigDec $1
      }
    | temdec
      {
        TemDec $1
      }
    ;

topdec_list
    : topdec
      {
        ($1: topdec)::[]
      }
    | topdec topdec_list
      {
        ($1: topdec)::($2: topdec list)
      }
    ;

adec
    : domdec
      {
        DomDec $1
      }
    | semdec
      {
        SemDec $1
      }
    | querydec
      {
        QueryDec $1
      }
    ;

adec_list
    : adec
      { $1::[] }
    | adec adec_list
      { $1::$2 }
    ;

anadec
    : ANALYSIS id EQ anaexp
      {
        let
            val anaid  = $2
            val anaexp = $4
        in
            store_anaid (anaid.0);
            {anaid=anaid, anaexp=anaexp}
        end
      }
    ;

ana_begin
    : ANA
      {
        push_setid_env ();
        push_latid_env ();
        push_ctlid_env ();
        push_cvarid_env ();

        ()
      }
    ;

anaexp
    : ana_begin adec_list END
      {
        pop_setid_env ();
        pop_latid_env ();
        pop_ctlid_env ();
        pop_cvarid_env ();

        AnaExpEnd $2
      }
    | id LPAREN anaexp_row RPAREN
      {
        AnaExpApp {temid=$1, params=$3}
      }
    | id
      {
        AnaExpId $1
      }
    ;

anaexp_row
    : anaexp
      {
        $1::[]
      }
    | anaexp COMMA anaexp_row
      {
        $1::$3
      }
    ;

sigdec
    : SIGNATURE id EQ SIG adesc_list END
      {
        let
            val sigid  = $2
            val sigexp = SigExp $5
        in
            {sigid=sigid, sigexp=sigexp}
        end
      }
    | SIGNATURE id EQ id
      {
        let
            val sigid  = $2
            val sigexp = SigId $4
        in
            {sigid=sigid, sigexp=sigexp}
        end
      }
    ;

tem_begin
    : ANALYSIS id
      {
        push_anaid_env ();

        $2
      }
    ;

temdec
    : tem_begin LPAREN param_row RPAREN EQ ana_begin adec_list END
      {
        let
            val temid = $1
        in
            pop_anaid_env ();
            pop_setid_env ();
            pop_latid_env ();
            pop_ctlid_env ();
            pop_cvarid_env ();

            {temid=temid, params=$3, body=$7} 
        end
      }
    ;

param
    : id COLON SIG adesc_list END
      {
        let
            val anaid  = $1
            val sigexp = SigExp $4
        in
            store_anaid (anaid.0);
            {anaid=anaid, sigexp=sigexp}
        end
      }
    | id COLON id
      {
        let
            val anaid  = $1
            val sigexp = SigId $3
        in
            store_anaid (anaid.0);
            {anaid=anaid, sigexp=sigexp}
        end
      }
    ;

param_row
    : param
      {
        $1::[]
      }
    | param COMMA param_row
      {
        $1::$3 
      }
    ;

adesc
    : SET setdesc_row
      {
        $2
      }
    | LATTICE latdesc_row
      {
        $2
      }
    | VAL id COLON common11
      {
        let
            val varid = $2
            val ty    = ty_of $4
        in
            (VarDesc (varid, ty))::[]
        end
      }
    | EQN id COLON common11
      {
        let
            val varid = $2
            val ty    = ty_of $4
        in
            (EqnDesc (varid, ty))::[]
        end
      }
    | QUERY id COLON common11
      {
        let
            val ctlid = $2
            val ty    = ty_of $4
        in
            (QueryDesc (ctlid, ty))::[]
        end
      }
    ;

adesc_list
    : adesc
      {
        $1
      }
    | adesc adesc_list
      {
        $1 @ $2 
      }
    ;

setdesc
    : UID
      {
        let
            val setid = ($1, region ())
        in
            SDescId setid
        end
      }
    | UID COLON kind
      {
        let
            val setid = ($1, region_of 1)
        in
            SDescKind (setid, $3)
        end
      }
    | setbind
      {
        SDescBind $1
      }
    ;

setdesc_row
    : setdesc
      {
        $1::[]
      }
    | setdesc COMMA setdesc_row
      {
        $1::$3
      }
    ;

latdesc
    : UID
      {
        let
            val latid = ($1, region ())
        in
            LDescId latid
        end
      }
    | UID COLON kind
      {
        let
            val latid = ($1, region_of 1)
        in
            LDescKind (latid, $3)
        end
      }
    | latbind
      {
        LDescBind $1
      }
    ;

latdesc_row
    : latdesc
      {
        $1::[]
      }
    | latdesc COMMA latdesc_row
      {
        $1::$3
      }
    ; 

domdec
    : setdec
      {
        SetDec $1
      }
    | latdec
      {
        LatDec $1
      }
    | widendec
      {
        WidenDec $1
      }
    ;

setdec
    : SET setbind
      {
        let
            val (setid, setexp) = $2
        in
            store_setid (setid.0);
            (setid, setexp)
        end
      }
    ;

setbind
    : UID EQ domexp6
      {
        let
            val setid  = ($1, region_of 1)
            val setexp = setexp_of $3
        in
            (setid, setexp)
        end
      }
    ;

latdec
    : LATTICE latbind
      {
        let
            val (latid, latexp) = $2
        in
            store_latid (latid.0);
            (latid, latexp)
        end
      }
    ;

latbind
    : UID EQ domexp6
      {
        let
            val latid  = ($1, region_of 1)
            val latexp = latexp_of $3
        in
            (latid, latexp)
        end
      }
    ;

domexp1
    : NMLEXP
      {
        NmlTyDom ($1, region ()) 
      }
    | UID
      {
        let
            val longid = ($1::[], region ())
        in
            IdDom (longid, region ())
        end
      }
    | id DOT UID
      {
        let
            val longid = (($1.0)::$3::[], region ())
        in
            IdDom (longid, region ())
        end
      }
    /*
    | ANAID DOT UID
      {
        let
            val longid = ($1::$3::[], region ())
        in
            IdDom (longid, region ())
        end
      }
    */
    | LBRACE common12 DOTDOTDOT common12 RBRACE
      {
        let
            val exp1 = exp_of $2
            val exp2 = exp_of $4
        in
            IntervalDom (exp1, exp2, region ())
        end
      }
    | LBRACE id_row RBRACE
      {
        EnumDom ($2, region ())
      }
    | LPAREN domexp6 RPAREN
      {
        $2
      }
    ;

domexp2
    : domexp1
      {
        $1 
      }
    | domexp2 CONSTRAINT cnstdec
      {
        let
            val setexp = setexp_of $1
        in
            ConstraintDom (setexp, $3, region ())
        end
      }
    | domexp2 ORDER order_group
      {
        let
            val setexp = setexp_of $1
        in
            OrderDom (setexp, $3, region ()) 
        end
      }
    ;

domexp3
    : domexp2
      {
        $1
      }
    | POWER domexp3
      {
        let
            val setexp = setexp_of $2
        in
            PowerDom (setexp, region ()) 
        end
      }
    | FLAT domexp3
      {
        let
            val setexp = setexp_of $2
        in
            FlatDom (setexp, region ()) 
        end
      }
    ;

domexp4
    : domexp3
      {
        $1
      }
    | domexp4 STAR domexp3
      {
        ProductDom ($1::$3::[], region ()) 
      }
    ;

domexp5
    : domexp4
      {
        $1 
      }
    | domexp5 PLUS domexp4
      { 
        SumDom ($1::$3::[], region ()) 
      }
    ;

domexp6
    : domexp5
      {
        $1 
      }
    | domexp5 RIGHTARROW domexp6
      {
        ArrowDom ($1, $3, region ()) 
      }
    ;

cnstdec
    : VAR EQ LBRACE id_row RBRACE RHS EQ rhs_group
      {
        let
            val cvarid_list  = $4
            val index_option = None
            val rhs_list     = $8
        in
            List.iter (fn x => store_cvarid (x.0)) cvarid_list;
            {cvar=cvarid_list, index=index_option, rhs=rhs_list}::[]
        end
      }
    | VAR EQ LBRACE id_row RBRACE INDEX domexp6 RHS EQ rhs_group
      {
        let
            val cvarid_list  = $4
            val index_option = Some (setexp_of $7)
            val rhs_list     = $10
        in
            List.iter (fn x => store_cvarid (x.0)) cvarid_list;
            {cvar=cvarid_list, index=index_option, rhs=rhs_list}::[]
        end
      }
    ;

rhs
    : VAR
      {
        RhsVar
      }
    | VAR UID
      {
        let
            val setlongid = ([$2], region_of 2)
        in
            RhsVarr setlongid
        end
      }
    | VAR id DOT UID
      {
        let
            val setlongid = ([$2.1,$4], merged_region_of 2 4)
        in
            RhsVarr setlongid
        end
      }
    | id
      {
        let
            val conid = $1
            val carg  = CargEmpty
            val flag  = NonAtomic
        in
            RhsConid {conid=conid, carg=carg, flag=flag}
        end
      }
    | id domexp1
      {
        let
            val conid = $1
            val carg  = CargSet (setexp_of $2)
            val flag  = NonAtomic
        in
            RhsConid {conid=conid, carg=carg, flag=flag}
        end
      }
    | id carg
      {
        let
            val conid = $1
            val carg  = $2
            val flag  = NonAtomic
        in
            RhsConid {conid=conid, carg=carg, flag=flag}
        end
      }
    | id COLON ATOMIC
      {
        let
            val conid = $1
            val carg  = CargEmpty
            val flag  = Atomic
        in
            RhsConid {conid=conid, carg=carg, flag=flag}
        end
      }
    | id domexp1 COLON ATOMIC
      {
        let
            val conid = $1
            val carg  = CargSet (setexp_of $2)
            val flag  = Atomic
        in
            RhsConid {conid=conid, carg=carg, flag=flag}
        end
      }
    | id carg COLON ATOMIC
      {
        let
            val conid = $1
            val carg  = $2
            val flag  = Atomic
        in
            RhsConid {conid=conid, carg=carg, flag=flag}
        end
      }
    ;

rhs_group
    : rhs
      {
        $1::[] 
      }
    | rhs BAR rhs_group
      {
        $1::$3
      }

carg
    : VAR
      {
        CargVar
      }
    | VAR UID
      {
        let
            val setlongid = ([$2], region_of 2)
        in
            CargVarr setlongid
        end
      }
    | VAR id DOT UID
      {
        let
            val setlongid = ([$2.1,$4], merged_region_of 2 4)
        in
            CargVarr setlongid
        end
      }
    | LPAREN carg RPAREN
      {
        let
            val carg_list = $2::[]
        in
            CargTuple carg_list
        end
      }
    | LPAREN domexp6 COMMA carg_row RPAREN
      {
        let
            val setexp    = setexp_of $2
            val carg      = CargSet setexp
            val carg_list = carg::$4
        in
            CargTuple carg_list
        end
      }
    | LPAREN carg COMMA carg_row RPAREN
      {
        let
            val carg_list = $2::$4
        in
            CargTuple carg_list
        end
      }
    ;

carg_row
    : domexp6
      {
        let
            val setexp    = setexp_of $1
            val carg      = CargSet setexp
        in
            carg::[]
        end
      }
    | domexp6 COMMA carg_row
      {
        let
            val setexp   = setexp_of $1
            val carg     = CargSet setexp
        in
            carg::$3
        end
      }
    | carg
      {
        $1::[] 
      }
    | carg COMMA carg_row
      {
        $1::$3 
      }
    ;

order
    : LT common01
      {
        let
            val po  = LTrop
            val pat = pat_of $2
        in
            ((po, pat)::[], region ())
        end
      }
    | GT common01
      {
        let
            val po  = GTrop
            val pat = pat_of $2
        in
            ((po, pat)::[], region ())
        end
      }
    | common01 po_pat_list
      {
        let
            val pat = pat_of $1
        in
            (dissolve_sugared_order pat $2, region ())
        end
      }
    ;

order_group
    : order
      {
        $1
      }
    | order BAR order_group
      {
        let
            val (orders1, _) = $1
            val (orders2, _) = $3
        in
            (orders1 @ orders2, region ())
        end
      }
    ;

po_pat_list
    : LT common01
      {
        let
            val po  = LTrop
            val pat = pat_of $2
        in
            (po, pat)::[]
        end
      }
    | GT common01
      {
        let
            val po  = GTrop
            val pat = pat_of $2
        in
            (po, pat)::[]
        end
      }
    | LT common01 po_pat_list
      {
        let
            val po  = LTrop
            val pat = pat_of $2
        in
            (po, pat)::$3
        end
      }
    | GT common01 po_pat_list
      {
        let
            val po  = GTrop
            val pat = pat_of $2
        in
            (po, pat)::$3
        end
      }
    ;

widendec
    : WIDEN UID WITH match
      {
        let
            val latid = ($2, region_of 2)
        in
            (latid, $4)
        end
      }
    ;

kind
    : SYNTREE
      {
        SyntreeKind 
      }
    | INDEX
      {
        IndexKind 
      }
    | POWER
      {
        PowerKind 
      }
    | SUM
      {
        SumKind 
      }
    | PRODUCT
      {
        ProductKind 
      }
    | ARROW
      {
        ArrowKind 
      }
    | CONSTRAINT
      {
        ConstraintKind 
      }
    ;

semdec
    : valdec
      {
        ValDec $1 
      }
    | eqndec
      {
        EqnDec $1 
      }
    | ccrdec
      {
        CcrDec $1 
      }
    | cimdec
      {
        CimDec $1 
      }
    ;

valdec
    : VAL vbind_list
      {
        ValBind ($2, region ()) 
      }
    | VAL REC vbind_list
      {
        RecValBind ($3, region ()) 
      }
    | FUN fbind_list
      {
        FunBind ($2, region ()) 
      }
    | MAP fbind_list
      {
        MapBind ($2, region ()) 
      }
    ; 

valdec_list
    : valdec
      {
        $1::[]
      }
    | valdec valdec_list
      {
        $1::$2
      }
    ;

vbind
    : common06 EQ common11a
      {
        let
            val pat = pat_of $1
            val exp = exp_of $3
        in
            (pat, exp)
        end
      }
    ;

vbind_list
    : vbind
      {
        $1::[] 
      }
    | vbind AND vbind_list
      {
        $1::$3 
      }
    ;

fbind
    : id common06 EQ common11a
      {
        let
            val varid = $1
            val pat   = pat_of $2
            val exp   = exp_of $4
        in
            {varid=$1, pat=pat, exp=exp}::[]
        end
      }
    | id common06 EQ common11a BAR fbind
      {
        let
            val varid = $1
            val pat   = pat_of $2
            val exp   = exp_of $4
        in
            {varid=$1, pat=pat, exp=exp}::$6
        end
      }
    ;

fbind_list
    : fbind
      { 
        ($1, region_of 1)::[] 
      }
    | fbind AND fbind_list
      {
        ($1, region_of 1)::$3 
      }
    ;

eqndec
    : EQN ebind_list
      {
        EqnBind ($2, region ()) 
      }
    | EQN REC ebind_list
      {
        RecEqnBind ($3, region ()) 
      }
    | EQN fbind_list
      {
        FunEqnBind ($2, region ()) 
      }
    ;

ebind
    : id EQ common16
      {
        let
            val varid = $1
            val exp   = exp_of $3
        in
            (varid, exp, region ())
        end
      }
    ;

ebind_list
    : ebind
      {
        $1::[] 
      }
    | ebind AND ebind_list
      {
        $1::$3 
      }
    ;


ccrdec
    : CCR cnstguard_row LINE constraint_row
      {
        let
            val premise = $2
            val conseq  = $4
        in
            ({premise=premise, conseq=conseq}, region ())
        end
      }
    ;

cnstguard
    : constraint
      {
        CcrCnst $1 
      }
    | guard5
      {
        CcrGuard $1 
      }
    ;

cnstguard_row
    : cnstguard
      { 
        $1::[] 
      }
    | cnstguard COMMA cnstguard_row
      {
        $1::$3 
      }
    ;

constraint
    : common03 LEFTARROW rhsexp_group
      {
        let
            val cvarexp     = cvarexp_of $1
            val rhsexp_list = $3
        in
            (cvarexp, rhsexp_list)
        end
      }
    ;

rhsexp
    : id
      {
        let
            val cvarlongid = ([$1.1], region ())
            val cvarexp    = {cvarid=cvarlongid, index=None}
        in
            RhsexpCvar cvarexp
        end
      }
    | id DOT id
      {
        let
            val cvarlongid = ([$1.1,$3.1], region ())
            val cvarexp    = {cvarid=cvarlongid, index=None}
        in
            RhsexpCvar cvarexp
        end
      }
    | id AT common07
      {
        let
            val cvarlongid = ([$1.1], region_of 1)
            val pat        = pat_of $3
            val cvarexp    = {cvarid=cvarlongid, index=(Some pat)}
        in
            RhsexpCvar cvarexp
        end
      }
    | id DOT id AT common07
      {
        let
            val cvarlongid = ([$1.1,$3.1], merged_region_of 1 3)
            val pat        = pat_of $5
            val cvarexp    = {cvarid=cvarlongid, index=(Some pat)}
        in
            RhsexpCvar cvarexp
        end
      }
    | id common07
      {
        let
            val conlongid = ([$1.1], region_of 1)
            val cargexp   = cargexp_of $2
        in
            RhsexpConid (conlongid, cargexp)
        end
      }
    | id DOT id common07
      {
        let
            val conlongid = ([$1.1,$3.1], merged_region_of 1 3)
            val cargexp   = cargexp_of $4
        in
            RhsexpConid (conlongid, cargexp)
        end
      }
    ;

rhsexp_group
    : rhsexp
      {
        $1::[]
      }
    | rhsexp PLUS rhsexp_group
      {
        $1::$3
      }
    ;
      

constraint_row
    : constraint
      {
        $1::[] 
      }
    | constraint COMMA constraint_row
      {
        $1::$3 
      }
    ;

cimdec
    : CIM id EQ common16
      {
        let
            val conlongid = ([$2.1], region_of 2)
            val exp       = exp_of $4
        in
            (conlongid, None, exp, region ())
        end
      }
    | CIM id DOT id EQ common16
      {
        let
            val conlongid = ([$2.1,$4.1], merged_region_of 2 4)
            val exp       = exp_of $6
        in
            (conlongid, None, exp, region ())
        end
      }
    | CIM id common06 EQ common16
      {
        let
            val conlongid = ([$2.1], region_of 2)
            val pat       = pat_of $3
            val exp       = exp_of $5
        in
            (conlongid, Some pat, exp, region ()) 
        end
      }
    | CIM id DOT id common06 EQ common16
      {
        let
            val conlongid = ([$2.1,$4.1], merged_region_of 2 4)
            val pat       = pat_of $5
            val exp       = exp_of $7
        in
            (conlongid, Some pat, exp, region ()) 
        end
      }
    ;

const
    : INTNUM
      {
        IntConst $1 
      }
    | TOP
      {
        TopConst 
      }
    | BOTTOM
      {
        BottomConst
      }
    | HAT
      {
        TopConst 
      }
    | UNDERUNDER
      {
        BottomConst 
      }
    | TRUE
      {
        TrueConst
      }
    | FALSE
      {
        FalseConst
      }
    ;

common01
    : NMLEXP
      {
        Nml ($1, region ())
      }
    | id
      {
        Id $1
      }
    /*
    | ANAID DOT id
      {
        LongId (($1)::($3.0)::[], region ())
      }
    */
    | const
      {
        Const ($1, region ())
      }
    | UNDER
      {
        (* pat: wild pattern *)
        Pat (WildPat, region ())
      }
    | INT
      {
        (* ty: integer type *)
        Ty (IntTy, region ())
      }
    | LBRACE common15 DOTDOTDOT common16 RBRACE
      {
        Interval ($2, $4, region ())
      }
    | LBRACE common_row RBRACE
      {
        Set ($2, region ())
      }
    | LBRACE map_row RBRACE
      {
        Map ($2, region ())
      }
    | LBRACE common_row BAR qual RBRACE
      {
        (* e: set comprehension *)
        let
            val exp_list = exp_list_of $2
            val qual = $4
            val exp = SetCompExp (exp_list, qual, region ())
        in
            Exp (exp, region ())
        end
      }
    | LBRACE map_row BAR qual RBRACE
      {
        (* e: map comprehension *)
        let
            val exp_list = mrule_list_of $2
            val qual = $4
            val exp = MapCompExp (exp_list, qual, region ()) 
        in
            Exp (exp, region ())
        end
      }
    | LBRACE common15 DOTDOTDOT RBRACE
      {
        (* pat: set pattern *)
        let
            val pat_list = (pat_of $2)::[]
            val pat = SetDotsPat pat_list
        in
            Pat (pat, region ())
        end
      }
    | LBRACE common15 COMMA common_row DOTDOTDOT RBRACE
      {
        (* pat: set pattern *)
        let
            val pat_list = (pat_of $2)::(pat_list_of $4)
            val pat = SetDotsPat pat_list
        in
            Pat (pat, region ())
        end
      }
    | LBRACE map_row DOTDOTDOT RBRACE
      {
        (* pat: map pattern *)
        Pat (MapDotsPat (mpat_list_of $2), region ())
      }
    /*
    | LBRACE constraint_row RBRACE
      {
        let
            val r   = region ()
            val exp = EnumSetExp (List.map (fn x => CnstExp x) $2, r)
        in
            Exp (exp, r)
        end
      }
    | LBRACE constraint_row BAR qual RBRACE
      {
        let
            val r   = region ()
            val exp = SetCompExp (List.map (fn x => CnstExp x) $2, $4, r)
        in
            Exp (exp, r)
        end
      }
    */
    | LBRACE RBRACE
      {
        (* e: empty set/map *)
        Exp (EmptySetExp (region ()), region ())
      }
    | LPAREN common16 RPAREN
      {
        $2 
      }
    | LPAREN common15 COMMA common_row RPAREN
      {
        Tuple ($2::$4, region ()) 
      }
    | LET valdec_list IN common16 END
      {
        let
            val exp = exp_of $4
            val r   = region ()
        in
            Exp (LetExp ($2, exp, r), r)
        end
      }
    ;

intprojtag
    : DOT INTNUM
      {
        (IntProjTag $2, region ())
      }
    ;

idprojtag
    : DOT id
      {
        let
            val longid = (($2.0)::[], $2.1)
        in
            (IdProjTag longid, region ())
        end
      }
    ;

projtag_list
    : intprojtag
      {
        $1::[]
      }
    | idprojtag
      {
        $1::[]
      }
    | intprojtag projtag_list
      {
        $1::$2
      }
    | idprojtag projtag_list
      {
        let
            fun is_idprojtag (IdProjTag _,_) = true
              | is_idprojtag _ = false
        in
            if (is_idprojtag (List.hd $2)) then
                let
                    val (IdProjTag (s1::_, r1), r2) = $1
                    val (IdProjTag (s2::_, r3), r4) = List.hd $2
                in
                    if (is_anaid s1) then
                        let
                            val r5 = Region.merge_region r1 r3
                            val r6 = Region.merge_region r2 r4
                            val longid = (s1::s2::[], r5)
                        in
                            ((IdProjTag longid), r6)::(List.tl $2)
                        end
                    else
                        $1::$2
                end
            else
               $1::$2
        end
      }
    ;

common02
    : common01
      {
        $1
      }
    | common01 projtag_list
      {
        let
            fun is_idprojtag (IdProjTag _,_) = true
              | is_idprojtag _ = false

            fun make_exp exp (projtag,r) = 
                let
                    val r' = Region.merge_region (region_of 1) r
                in
                    ProjectExp (exp, projtag, r')
                end
        in
            if (is_id $1) andalso (is_anaid (id_of $1).0) then
                let
                    val (s1,r1) = (id_of $1)
                    (* TODO: *)
                    val (IdProjTag (s2::_,_),r2) = List.hd $2
                    val longid = (s1::s2::[], Region.merge_region r1 r2)
                    val exp = exp_of (LongId longid)
                in
                    if ((List.length (List.tl $2)) = 0) then
                        LongId longid
                    else
                        Exp (List.fold_left make_exp exp (List.tl $2), region ())
                end
            else
                Exp (List.fold_left make_exp (exp_of $1) $2, region ())
        end
      }
    /*
    | common01 DOT INTNUM
      {
        let
            val e = exp_of $1
            val r = region ()
        in
            Exp (ProjectExp (e, IntProjTag $3, r), r)
        end
      }
    | common02 DOT id
      {
        let
            val exp = exp_of $1
            val tag = (($3.0)::[], $3.1)
            val r   = region ()
        in
            Exp (ProjectExp (exp, IdProjTag tag, r), r)
        end
      }
    | common02 DOT ANAID DOT id
      {
        let
            val exp = exp_of $1
            val tag = (($3)::($5.0), Region.merge_region (region_of 3) ($5.1))
            val r   = region ()
        in
            Exp (ProjectExp (exp, IdProjTag tag, r), r)
        end
      }
    */
    ;

common03
    : common02
      {
        $1
      }
    | common02 AT common03
      {
        Index ($1, $3, region ())
      }
    /*
    | common02 AT common03
      {
        if (is_id $1) andalso (is_cvarid (id_of $1)) then
            let
                val cvarid = id_of $1
                val pat    = pat_of $3
                val r      = region ()
            in
                (*
                print_string "<common03>\n";
                print_string "CargexpCvar returns\n";
                print_cvarid cvarid;
                print_newline ();
                *)
                Cargexp (CargexpCvar {cvarid=cvarid, index=(Some pat)}, r)
            end
        else
            let
                val varlongid = longid_of $1
                val exp       = exp_of $3
                val r         = region ()
            in
                (*
                print_string "<common03>\n";
                print_string "IndexExp returns\n";
                print_varlongid varlongid;
                print_newline ();
                *)
                Exp (IndexExp ({tag=None, eqnid=varlongid, index=exp}, r), r)
            end
      }
    */
    | PRE id AT common03
      {
        let
            val tag   = Pre
            val eqnid = (($2.0)::[], $2.1)
            val exp   = exp_of $4
            val r     = region ()
        in
            Exp (IndexExp ({tag=(Some tag), eqnid=eqnid, index=exp}, r), r)
        end
      }
    | PRE id DOT id AT common03
      {
        let
            val tag_option = Some Pre
            val eqnid      = (($2.0)::($4.0)::[], merged_region_of 2 4)
            val exp        = exp_of $6
            val r          = region ()
        in
            Exp (IndexExp ({tag=tag_option, eqnid=eqnid, index=exp}, r), r)
        end
      }
    | POST id AT common03
      {
        let
            val tag_option = Some Post
            val eqnid      = (($2.0)::[], $2.1)
            val exp        = exp_of $4
            val r          = region ()
        in
            Exp (IndexExp ({tag=tag_option, eqnid=eqnid, index=exp}, r), r)
        end
      }
    | POST id DOT id AT common03
      {
        let
            val tag_option = Some Post
            val eqnid      = (($2.0)::($4.0)::[], merged_region_of 2 4)
            val exp        = exp_of $6
            val r          = region ()
        in
            Exp (IndexExp ({tag=tag_option, eqnid=eqnid, index=exp}, r), r)
        end
      }
    /*
    | id AT common03
      {
        if (is_cvarid ($1.0)) then
            let
                val pat = pat_of $3
                val r   = region ()
            in
                (*
                print_string "<common03>\n";
                print_string "CargexpCvar returns\n";
                print_cvarid $1;
                print_newline ();
                *)
                Cargexp (CargexpCvar {cvarid=$1, index=(Some pat)}, r)
            end
        else
            let
                val longid = (($1.0)::[], $1.1)
                val exp    = exp_of $3
                val r      = region ()
            in
                (*
                print_string "<common03>\n";
                print_string "IndexExp returns\n";
                print_varlongid longid;
                print_newline ();
                *)
                Exp (IndexExp ({tag=None, eqnid=longid, index=exp}, r), r)
            end
      }
    | ANAID DOT id AT common03
      {
        let 
            val longid = ($1::($3.0)::[], $3.1)
            val exp    = exp_of $5
            val r      = region ()
        in
            Exp (IndexExp ({tag=None, eqnid=longid, index=exp}, r), r)
        end
      }
    | PRE id AT common03
      {
        let
           val longid = (($2.0)::[], $2.1)
           val exp    = exp_of $4
           val r      = region ()
        in
           Exp (IndexExp ({tag=Some Pre, eqnid=longid, index=exp}, r), r)
        end
      }
    | PRE ANAID DOT id AT common03
      {
        let
           val longid = ($2::($4.0)::[], $4.1)
           val exp    = exp_of $6
           val r      = region ()
        in
           Exp (IndexExp ({tag=Some Pre, eqnid=longid, index=exp}, r), r)
        end
      }
    | POST id AT common03
      {
        let
           val longid = (($2.0)::[], $2.1)
           val exp    = exp_of $4
           val r      = region ()
        in
           Exp (IndexExp ({tag=Some Post, eqnid=longid, index=exp}, r), r)
        end
      }
    | POST ANAID DOT id AT common03
      {
        let
           val longid = ($2::($4.0)::[], $4.1)
           val exp    = exp_of $6
           val r      = region ()
        in
           Exp (IndexExp ({tag=Some Post, eqnid=longid, index=exp}, r), r)
        end
      }
    */
    ;

common04
    : common03
      {
        $1
      }
    | POWER common04
      {
        let
            val ty = ty_of $2
            val r  = region ()
        in
            Ty (PowerTy (ty, r), r)
        end
      }
    ;

common05
    : common04
      {
        $1
      }
    | common05 LBRACKET map RBRACKET
      {
        let
            val exp   = exp_of $1
            val mrule = mrule_of $3
            val r     = region ()
        in
            Exp (MapModExp (exp, mrule, r), r)
        end
      }
    ;

common06
    : common05
      {
        $1
      }
    | common06 COLON common01
      {
        let
            val ty = ty_of $3
        in
            Coercion ($1, ty, region ())
        end
      }
    | common06 COLON kind
      {
        let
            val ty = ty_of $1
            val r  = region ()
        in
            Ty (KindTy (ty, $3, r), r)
        end
      }
    ;

common07
    : common06
      { 
        $1 
      }
    | common07 common06
      {
        let
            val exp1 = exp_of $1
            val exp2 = exp_of $2
            val r    = region ()
        in
            Exp (AppExp (exp1, exp2, r), r)
        end
      }
    ;

common07a
    : common07
      {
        $1
      }
    | constraint
      {
        Exp (CnstExp ($1, region ()), region ())
      }
    ;

common08
    : common07a
      { 
        $1 
      }
    | STAR common08
      {
        let
            val exp = exp_of $2
            val r   = region ()
        in
            Exp (FoldMeetExp (exp, r), r)
        end
      }
    | PLUS common08
      {
        let
            val exp = exp_of $2
            val r   = region ()
        in
            Exp (FoldJoinExp (exp, r), r)
        end
      }
    ;

common09
    : common08
      {
        $1
      }
    | common09 STAR common08
      {
        Meet ($1, $3, region ()) 
      }
    ;

common10
    : common09
      {
        $1
      }
    | common10 PLUS common09
      {
        Join ($1, $3, region ()) 
      }
    | common10 MINUS common09
      {
        let
            val exp1 = exp_of $1
            val exp2 = exp_of $3
            val r    = region ()
        in
            Exp (BopExp (exp1, MinusOp, exp2, r), r)
        end
      }
    ;

common11
    : common10
      {
        $1
      }
    | common11 RIGHTARROW common10
      {
        let
            val ty1 = ty_of $1
            val ty2 = ty_of $3
            val r   = region ()
        in
            Ty (ArrowTy (ty1, ty2, r), r)
        end
      }
    ;

common11a
    : common11
      {
        $1
      }
    | IF common16 THEN common16 ELSE common11a
      {
        let
            val exp1 = exp_of $2
            val exp2 = exp_of $4
            val exp3 = exp_of $6
            val r    = region ()
        in
            Exp (IfExp (exp1, exp2, exp3, r), r)
        end
      }
    ;

common11b
    : common11a
      {
        $1
      }
    | common11b rop common11a
      {
        let
            val exp = exp_of $3
        in
            Rop ($1, $2, exp, region ())
        end
      }
    ;

common11c
    : common11b
      {
        $1
      }
    | common11c IN common11a
      {
        let
            val pat = pat_of $1
            val exp = exp_of $3
        in
            Pat (InPat (pat, exp), region ())
        end
      }
    ;

common12
    : common11c
      {
        $1
      }
    | IN LPAREN INTNUM RPAREN common01
      {
        (* pat: injection pattern *)
        let
            val injtag = $3
            val pat    = pat_of $5
        in
            Pat (InjectPat (injtag, pat), region ())
        end
      }
    | IN LPAREN INTNUM RPAREN common01 common12
      {
        (* e: injection *)
        let
            val injtag = $3
            val ty     = ty_of $5
            val exp    = exp_of $6
            val r      = region ()
        in
            Exp (InjectExp (injtag, ty, exp, r), r)
        end
      }
    ;

common13
    : common12
      {
        $1
      }
    | id AS common13
      {
        (* pat: as pattern *)
        let
            val varid = $1
            val pat   = pat_of $3
        in
            Pat (AsPat (varid, pat), region ())
        end
      }
    ;

common14
    : common13
      {
        $1 
      }
    | common14 WITH guard2
      {
        (* pat: guarded pattern *)
        let
            val pat   = pat_of $1
            val guard = $3
        in
            Pat (GuardedPat (pat, guard), region ())
        end
      }
    ;

common15
    : common14
      {
        $1
      }
    | common15 OR common14
      {
        (* pat: or pattern *)
        let
            val pat1 = pat_of $1
            val pat2 = pat_of $3
        in
            Pat (OrPat (pat1::pat2::[]), region ())
        end
      }
    ;

common16
    : common15
      {
        $1
      }
    | FN match
      {
        let
            val exp = FnExp ($2, region ())
        in
            Exp (exp, region ())
        end
      }
    | MP match
      {
        let
            val exp = MpExp ($2, region ())
        in
            Exp (exp, region ())
        end
      }
    | CASE common16 OF match
      {
        let
            val exp   = exp_of $2
            val match = $4
        in
            Exp (CaseExp (exp, match, region ()), region ())
        end
      }
    | MAP common02 common15
      {
          let
              val exp1 = exp_of $2
              val exp2 = exp_of $3
          in
              Exp (MappingExp (exp1, exp2, region ()), region ())
          end
      }
    ;

common_row
    : common15
      {
        $1::[]
      }
    | common15 COMMA common_row
      {
        $1::$3
      }
    ;


map
    : common15 DOUBLEARROW common15
      {
        ($1, $3, region ())
      }
    ;

map_row
    : map
      {
        $1::[]
      }
    | map COMMA map_row
      {
        $1::$3
      }
    ;

match
    : map
      {
        let
            val mrule = mrule_of $1
        in
            mrule::[]
        end
      }
    | map BAR match
      {
        let
            val mrule = mrule_of $1
        in
            mrule::$3
        end
      }
    ;

qual
    : common15 FROM common16
      {
        let
            val pat = pat_of $1
            val exp = exp_of $3
            val ge  = SetElmtGen (pat, exp, region ())
            val gen = (ge::[], region ())
        in
            (gen, None)
        end
      }
    | map FROM common16
      {
        let
            val mpat = mpat_of $1
            val exp  = exp_of $3
            val ge   = MapElmtGen (mpat, exp, region ())
            val gen  = (ge::[], region ())
        in
            (gen, None)
        end
      }
    | common15 FROM common12 COMMA guard_row
      {
        let
            val pat = pat_of $1
            val exp = exp_of $3
            val r1  = merged_region_of 1 3
            val r2  = region_of 5
            val ge  = SetElmtGen (pat, exp, r1)
            val gen = (ge::[], r1)
            val guard_option = Some (AndGuard ($5, r2))
        in
            (gen, guard_option)
        end
      
      }
    | map FROM common12 COMMA guard_row
      {
        let
            val mpat = mpat_of $1
            val exp  = exp_of $3
            val r1   = merged_region_of 1 3
            val r2   = region_of 5
            val ge   = MapElmtGen (mpat, exp, r1)
            val gen  = (ge::[], r1)
            val guard_option = Some (AndGuard ($5, r2))
        in
            (gen, guard_option)
        end
      }
    | common15 FROM common12 COMMA qual
      {
        let
            val pat = pat_of $1
            val exp = exp_of $3
            val ge  = SetElmtGen (pat, exp, region ())
            val ((ge_list,r), guard_option) = $5
            val gen = (ge::ge_list, Region.merge_region (region_of 1) r)
        in
            (gen, guard_option)
        end
      }
    | map FROM common12 COMMA qual
      {
        let
            val mpat = mpat_of $1
            val exp  = exp_of $3
            val ge   = MapElmtGen (mpat, exp, region ())
            val ((ge_list,r), guard_option) = $5
            val gen  = (ge::ge_list, Region.merge_region (region_of 1), r)
        in
            (gen, guard_option)
        end
      }
    /*
    : gen
      {
        let
            val gen   = $1::[]
            val guard = None
        in
            (gen, guard)
        end
      }
    | gen COMMA guard5
      {
        let
            val gen   = $1::[]
            val guard = Some $3
        in
            (gen, guard)
        end
      }
    | gen COMMA qual
      {
        let
            val (gen2,guard) = $3
            val gen          = $1::gen2
        in
            (gen, guard)
        end
      }
    */
    ;

/* Use common01: !gen.guard / ?gen.guard */
gen
    : common15 FROM common01
      {
        let
            val pat = pat_of $1
            val exp = exp_of $3
        in
            SetElmtGen (pat, exp, region ()) 
        end
      }
    | map FROM common01
      {
        let
            val mpat = mpat_of $1
            val exp  = exp_of $3
        in
            MapElmtGen (mpat, exp, region ()) 
        end
      }
    ;

gen_row
    : gen
      {
        $1::[] 
      }
    | gen COMMA gen_row
      {
        $1::$3
      }
    ;

rop
    : LT
      {
        LTrop 
      }
    | GT
      {
        GTrop 
      }
    | EQ
      {
        EQrop
      }
    | LE
      {
        LErop
      }
    | GE
      {
        GErop 
      }
    ;

guard1
    : common10 rop common10
      {
        let
            val exp1 = exp_of $1
            val exp2 = exp_of $3
        in
            RopGuard (LTrop, exp1::exp2::[], region ()) 
        end
      }
    | common10 IN common10
      {
        let
            val exp1 = exp_of $1
            val exp2 = exp_of $3
        in
            MemberGuard (exp1, exp2, region ())
        end
      }
    | LPAREN guard_row RPAREN
      {
        AndGuard ($2, region ())
      }
    ; 

guard2
    : guard1
      {
        $1
      }
    | NOT guard2
      {
        NotGuard ($2, region ())
      }
    ;

guard3
    : guard2
      {
        $1
      }
    | guard2 AND guard3
      {
        AndGuard ($1::$3::[], region ())
      }
    ;

guard4
    : guard3
      {
        $1
      }
    | guard3 OR guard4
      {
        OrGuard ($1::$3::[], region ())
      }
    ;

guard5
    : guard4
      {
        $1
      }
    | BANG gen_row DOT guard5
      {
        UnivGuard ($2, $4, region ())
      }
    | QUESTION gen_row DOT guard5
      {
        ExisGuard ($2, $4, region ())
      }
    ;

guard_row
    : guard5
      {
        $1::[]
      }
    | guard5 COMMA guard_row
      {
        $1::$3
      }
    ;

querydec
    : QUERY ctlbind_group
      {
        QueryDec $2
      }
    ;

ctlbind
    : id EQ ctl
      {
        let
            val ctlid = $1
            val ctl   = $3
        in
            store_ctlid (ctlid.0);
            (ctlid, ctl, region ())
        end
      }
    ;

ctlbind_group
    : ctlbind
      {
        $1::[]
      }
    | ctlbind AND ctlbind_group
      {
        $1::$3
      }
    ;

ctl_begin
    : id COLON id DOT
      {
        let
            val varid      = $1
            val tag_option = None
            val eqnid      = ([$3.1], region_of 3)
        in
            check_ctlid := true;
            (varid, tag_option, eqnid)
        end
      }
    | id COLON LPAREN id DOT id RPAREN DOT
      {
        let
            val varid      = $1
            val tag_option = None
            val eqnid      = ([$4.1,$6.1], merged_region_of 4 6)
        in
            check_ctlid := true;
            (varid, tag_option, eqnid)
        end
      }
    | id COLON PRE id DOT
      {
        let
            val varid      = $1
            val tag_option = Some Pre
            val eqnid      = ([$4.1], region_of 4)
        in
            check_ctlid := true;
            (varid, tag_option, eqnid)
        end
      }
    | id COLON PRE LPAREN id DOT id RPAREN DOT
      {
        let
            val varid      = $1
            val tag_option = Some Pre
            val eqnid      = ([$5.1,$7.1], merged_region_of 5 7)
        in
            check_ctlid := true;
            (varid, tag_option, eqnid)
        end
      }
    | id COLON POST id DOT
      {
        let
            val varid      = $1
            val tag_option = Some Post
            val eqnid      = ([$4.1], region_of 4)
        in
            check_ctlid := true;
            (varid, tag_option, eqnid)
        end
      }
    | id COLON POST LPAREN id DOT id RPAREN DOT
      {
        let
            val varid      = $1
            val tag_option = Some Post
            val eqnid      = ([$5.1,$7.1], merged_region_of 5 7)
        in
            check_ctlid := true;
            (varid, tag_option, eqnid)
        end
      }
    ;

ctl
    : ctl_begin form3
      {
        let
            val (varid, tag_option, eqnid) = $1
        in
            check_ctlid := false;
            FormulaCtl {id=varid, tag=tag_option, eqnid=eqnid, formula=$2}
        end
      }
    | ctl_begin guard2
      {
        let
            val (varid, tag_option, eqnid) = $1
        in
            check_ctlid := false;
            GuardCtl {id=varid, tag=tag_option, eqnid=eqnid, guard=$2}
        end
      }
    /*
    : id COLON id DOT form3
      {
        let
            val varid = $1
            val eqnid = $3
        in
            FormulaCtl {id=varid, tag=None, eqnid=eqnid, formula=$5}
        end
      }
    | id COLON PRE id DOT form3
      {
        let
            val varid = $1
            val eqnid = $4
        in
            FormulaCtl {id=varid, tag=(Some Pre), eqnid=eqnid, formula=$6}
        end
      }
    | id COLON POST id DOT form3
      {
        let
            val varid = $1
            val eqnid = $4
        in
            FormulaCtl {id=varid, tag=(Some Post), eqnid=eqnid, formula=$6}
        end
      }
    | id COLON id DOT guard2
      {
        let
            val varid = $1
            val eqnid = $3
        in
            GuardCtl {id=varid, tag=None, eqnid=eqnid, guard=$5}
        end
      }
    | id COLON PRE id DOT guard2
      {
        let
            val varid = $1
            val eqnid = $4
        in
            GuardCtl {id=varid, tag=(Some Pre), eqnid=eqnid, guard=$6}
        end
      }
    | id COLON POST id DOT guard2
      {
        let
            val varid = $1
            val eqnid = $4
        in
            GuardCtl {id=varid, tag=(Some Post), eqnid=eqnid, guard=$6}
        end
      }
    */
    ;

form1
    : CTLID id
      {
        let
            val ctlid = ($1, region_of 1)
            val varid = $2
        in
            AppForm (ctlid, varid, region ())
        end
      }
    | LPAREN form6 RPAREN
      {
        $2
      }
    ;

form2
    : form1
      {
        $1
      }
    | AX ctl
      {
        AXForm ($2, region ())
      }
    | AF ctl
      {
        AFForm ($2, region ())
      }
    | AG ctl
      {
        AGForm ($2, region ())
      }
    | EX ctl
      {
        EXForm ($2, region ())
      }
    | EF ctl
      {
        EFForm ($2, region ())
      }
    | EG ctl
      {
        EGForm ($2, region ()) 
      }
    | AU LPAREN ctl COMMA ctl RPAREN
      {
        AUForm ($3, $5, region ())
      }
    | EU LPAREN ctl COMMA ctl RPAREN
      {
        EUForm ($3, $5, region ())
      }
    ; 

form3
    : form2
      {
        $1
      }
    | NOT form3
      {
        NotForm ($2, region ())
      }
    ;

form4
    : form3
      {
        $1
      }
    | form3 form_and form4
      {
        AndForm ($1::$3::[], region ())
      }
    /*
    | form3 AND form4
      {
        AndForm ($1::$3::[], region ())
      }
    */
    ;

form5
    : form4
      {
        $1
      }
    | form4 form_or form5
      {
        OrForm ($1::$3::[], region ())
      }
    /*
    | form4 OR form5
      {
        OrForm ($1::$3::[], region ())
      }
    */
    ;

form6
    : form5
      {
        $1
      }
    | form5 form_implication form6
      {
        ImplyForm ($1, $3, region ())
      }
    | form5 form_equivalence form6
      {
        EquivForm ($1, $3, region ())
      }
    /*
    | form5 RIGHTARROW form6
      {
        ImplyForm ($1, $3, region ())
      }
    | form5 BOTHARROW form6
      {
        EquivForm ($1, $3, region ())
      }
    */
    ;

form_and
    : AND
      {
        check_ctlid := true
      }
    ;

form_or
    : OR
      {
        check_ctlid := true
      }
    ;

form_implication
    : RIGHTARROW
      {
        check_ctlid := true
      }
    ;

form_equivalence
    : BOTHARROW
      {
        check_ctlid := true
      }
    ;
