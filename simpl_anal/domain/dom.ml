module type Dom = 
sig
  type t

  val bot : t
  val le : t -> t -> bool
  val join : t -> t -> t
  val widen : t -> t -> t
  val to_string : t -> string
end

module type FinDom = 
sig 
  type t 
  val compare : t -> t -> int
  val to_string : t -> string
end

module Pair (M:Dom) (N:Dom) = 
struct 
  type t = M.t * N.t

  let bot : t = (M.bot,N.bot)
  let le (x:t) (y:t) : bool = M.le (fst x) (fst y) && N.le (snd x) (snd y)
  let join (x:t) (y:t) : t = (M.join (fst x) (fst y),N.join (snd x) (snd y))
  let widen (x:t) (y:t) : t = (M.widen (fst x) (fst y),N.widen (snd x) (snd y))
  let to_string (x:t) : string =
    "("^(M.to_string (fst x))^","^(N.to_string (snd x))^")"
end

module FinSet (M:FinDom) =
struct
  module MSet = Set.Make (M)
  type t = MSet.t
  let mem (k:M.t) (x:t) : bool = MSet.mem k x
  let add (k:M.t) (x:t) : t = MSet.add k x
  let fold (f:M.t -> 'a -> 'a) (x:t) (init:'a) : 'a = MSet.fold f x init

  let bot : t = MSet.empty
  let le (x:t) (y:t) : bool = MSet.subset x y
  let join (x:t) (y:t) : t = MSet.union x y
  let widen (x:t) (y:t) : t = join x y
  let to_string (x:t) : string = 
    "{"^
      (MSet.fold
         (fun v acc -> 
           if acc="" then (M.to_string v) else acc^","^(M.to_string v)
         )
         x "")^
      "}"
end

module FinMap (M:FinDom) (N:Dom) = 
struct 
  module MMap = Map.Make (M)
  type t = N.t MMap.t
  let add (k:M.t) (v:N.t) (x:t) : t = MMap.add k v x 
  let remove (k:M.t) (x:t) : t = MMap.remove k x 
  let find (k:M.t) (x:t) : N.t = 
    try MMap.find k x
    with Not_found -> N.bot
  let mapi (f:M.t -> N.t -> 'a) (x:t) : 'a MMap.t = MMap.mapi f x
  let fold (f:M.t -> N.t -> 'a -> 'a) (x:t) (init:'a) : 'a = MMap.fold f x init
  let filter (f:M.t -> N.t -> bool) (x:t) : t = 
    fold (fun k v acc -> if f k v then acc else remove k acc) x x

  let bot : t = MMap.empty
  let le (x:t) (y:t) : bool = 
    MMap.fold (fun k v acc -> acc && N.le v (find k y)) x true
  let join (x:t) (y:t) : t = 
    MMap.fold (fun k v acc -> add k (N.join (find k acc) v) acc) y x
  let widen (x:t) (y:t) : t = 
    MMap.fold (fun k v acc -> add k (N.widen (find k acc) v) acc) y x
  let to_string (x:t) : string = 
    "{"^
      (MMap.fold 
         (fun k v acc -> 
           if acc=""
           then (M.to_string k)^"->"^(N.to_string v)
           else acc^","^(M.to_string k)^"->"^(N.to_string v)
         )
         x "")^
      "}"
end

module Option (M:Dom) = 
struct
  type t = M.t option

  let bot : t = None
  let le (x:t) (y:t) : bool =
    match x,y with
    | None,_ -> true
    | _,None -> false
    | Some a,Some b -> M.le a b
  let join (x:t) (y:t) : t = 
    match x,y with
    | None,_ -> y
    | _,None -> x
    | Some a,Some b -> Some (M.join a b)
  let widen (x:t) (y:t) : t = 
    match x,y with
    | None,_ -> y
    | _,None -> x
    | Some a,Some b -> Some (M.widen a b)
  let to_string (x:t) : string = 
    match x with
    | None -> "None"
    | Some a -> "Some "^(M.to_string a)
end
