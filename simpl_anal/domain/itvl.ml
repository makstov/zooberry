exception Error of string

type z_inf = 
| Z_inf_int of int
| Z_inf_pos
| Z_inf_neg

let z_inf_le (x:z_inf) (y:z_inf) : bool = 
  match x,y with
  | Z_inf_neg,_ -> true
  | _,Z_inf_pos -> true
  | Z_inf_int i,Z_inf_int j -> i <= j
  | _,_ -> false
let z_inf_lt (x:z_inf) (y:z_inf) : bool = not (z_inf_le y x)

let z_inf_min (x:z_inf) (y:z_inf) : z_inf = 
  if z_inf_le x y then x else y
let z_inf_max (x:z_inf) (y:z_inf) : z_inf = 
  if z_inf_le x y then y else x

let z_inf_widen_low (x:z_inf) (y:z_inf) : z_inf = 
  match x,y with
  | Z_inf_neg,_ -> Z_inf_neg
  | Z_inf_pos,_ -> y
  | _,Z_inf_neg -> Z_inf_neg
  | _,Z_inf_pos -> x
  | Z_inf_int i,Z_inf_int j -> if i <= j then x else Z_inf_neg
let z_inf_widen_high (x:z_inf) (y:z_inf) : z_inf = 
  match x,y with
  | Z_inf_neg,_ -> y
  | Z_inf_pos,_ -> Z_inf_pos
  | _,Z_inf_neg -> x
  | _,Z_inf_pos -> Z_inf_pos
  | Z_inf_int i,Z_inf_int j -> if i >= j then x else Z_inf_pos

let z_inf_to_string (x:z_inf) : string = 
  match x with
  | Z_inf_int i -> string_of_int i
  | Z_inf_pos -> "+oo"
  | Z_inf_neg -> "-oo"

let z_inf_u_minus (x:z_inf) : z_inf = 
  match x with
  | Z_inf_int i -> Z_inf_int (i * -1)
  | Z_inf_pos -> Z_inf_neg
  | Z_inf_neg -> Z_inf_pos

let z_inf_plus (x:z_inf) (y:z_inf) : z_inf = 
  match x,y with
  | Z_inf_neg,Z_inf_neg 
  | Z_inf_neg,Z_inf_int _
  | Z_inf_int _,Z_inf_neg -> Z_inf_neg
  | Z_inf_pos,Z_inf_pos
  | Z_inf_pos,Z_inf_int _
  | Z_inf_int _,Z_inf_pos -> Z_inf_pos
  | Z_inf_int i,Z_inf_int j -> Z_inf_int (i+j)
  | _,_ -> raise (Error "z_inf_plus: invalid plus")

module Itvl = 
struct
  type t = z_inf * z_inf
  let low (x:t) : z_inf = fst x
  let high (x:t) : z_inf = snd x

  let bot : t = (Z_inf_pos,Z_inf_neg)
  let is_bot (x:t) : bool = 
    match x with
    | (Z_inf_pos,_) -> true
    | (_,Z_inf_neg) -> true
    | (Z_inf_int i,Z_inf_int j) -> i > j
    | _ -> false

  let top : t = (Z_inf_neg,Z_inf_pos)

  let le (x:t) (y:t) : bool = 
    if is_bot x then true
    else if is_bot y then false
    else z_inf_le (low y) (low x) && z_inf_le (high x) (high y)

  let join (x:t) (y:t) : t =
    if is_bot x then y
    else if is_bot y then x
    else (z_inf_min (low x) (low y),z_inf_max (high x) (high y))
      
  let widen (x:t) (y:t) : t =
    if is_bot x then y
    else if is_bot y then x
    else (z_inf_widen_low (low x) (low y),z_inf_widen_high (high x) (high y))

  let to_string (x:t) : string = 
    "["^(z_inf_to_string (low x))^","^(z_inf_to_string (high x))^"]"

  let u_minus (x:t) : t = 
    if is_bot x then bot
    else (z_inf_u_minus (high x),z_inf_u_minus (low x))

  let plus (x:t) (y:t) : t = 
    if is_bot x || is_bot y then bot
    else (z_inf_plus (low x) (low y),z_inf_plus (high x) (high y))

  let minus (x:t) (y:t) : t = plus x (u_minus y)

  let mult (x:t) (y:t) : t = 
    if is_bot x || is_bot y then bot
    else top

  let div (x:t) (y:t) : t = 
    if is_bot x || is_bot y then bot
    else top

  let cmp_le (x:t) (y:t) : Bool.Bool.t = 
    if is_bot x || is_bot y then Bool.Bool.Bool_bot
    else if z_inf_le (high x) (low y) then Bool.Bool.Bool_true
    else if z_inf_lt (high y) (low x) then Bool.Bool.Bool_false
    else Bool.Bool.Bool_top
  let cmp_lt (x:t) (y:t) : Bool.Bool.t = 
    if is_bot x || is_bot y then Bool.Bool.Bool_bot
    else if z_inf_lt (high x) (low y) then Bool.Bool.Bool_true
    else if z_inf_le (high y) (low x) then Bool.Bool.Bool_false
    else Bool.Bool.Bool_top
  let cmp_ge (x:t) (y:t) : Bool.Bool.t = cmp_le y x
  let cmp_gt (x:t) (y:t) : Bool.Bool.t = cmp_lt y x
  let cmp_eq (x:t) (y:t) : Bool.Bool.t = 
    if is_bot x || is_bot y then Bool.Bool.Bool_bot
    else if low x = high x && high x = low y && low y = high y
    then Bool.Bool.Bool_true
    else if z_inf_lt (high x) (low y) || z_inf_lt (high y) (low x)
    then Bool.Bool.Bool_false
    else Bool.Bool.Bool_top
  let cmp_neq (x:t) (y:t) : Bool.Bool.t = 
    if is_bot x || is_bot y then Bool.Bool.Bool_bot
    else if low x = high x && high x = low y && low y = high y
    then Bool.Bool.Bool_false
    else if z_inf_lt (high x) (low y) || z_inf_lt (high y) (low x)
    then Bool.Bool.Bool_true
    else Bool.Bool.Bool_top

end
