module Bool = 
struct 
  type t = 
  | Bool_bot
  | Bool_true
  | Bool_false
  | Bool_top
    
  let bot : t = Bool_bot
  let le (x:t) (y:t) : bool = 
    match x,y with
    | Bool_bot,_ -> true
    | _,Bool_top -> true
    | Bool_true,Bool_true -> true
    | Bool_false,Bool_false -> true
    | _,_ -> false
  let join (x:t) (y:t) : t = 
    match x,y with
    | Bool_bot,_ -> y
    | _,Bool_bot -> x
    | Bool_true,Bool_true -> Bool_true
    | Bool_false,Bool_false -> Bool_false
    | Bool_true,Bool_false -> Bool_top
    | Bool_false,Bool_true -> Bool_top
    | Bool_top,_ -> Bool_top
    | _,Bool_top -> Bool_top
  let widen (x:t) (y:t) : t = join x y
  let to_string (x:t) : string = 
    match x with
    | Bool_bot -> "bBot"
    | Bool_true -> "bTrue"
    | Bool_false -> "bFalse"
    | Bool_top -> "bTop"

  let sem_not (x:t) : t =
    match x with 
    | Bool_bot -> Bool_bot
    | Bool_true -> Bool_false
    | Bool_false -> Bool_true
    | Bool_top -> Bool_top
end
