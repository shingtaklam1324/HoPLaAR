/-
Copyright (c) 2003-2007, John Harrison
Copyright (c) 2021, Shing Tak Lam
(See "LICENSE" for details)
-/

-- # Misc library functions to set up a nice environment.

-- `identity` replaced with `id`

-- `**` replaced with `∘`

-- ## GCD and LCM on arbitrary-precision numbers.

-- `gcd_num` replaced with `Nat.gcd`

-- `lcm_num`
def Nat.lcm (a b : Nat) := a * b / a.gcd b

-- ## A useful idiom for "non contradictory" etc.

def non (p : α → Bool) (x : α) : Bool := !p x

-- # Kind of assertion checking.

def check {α : Type} [Inhabited α] (p : α → Bool) (x : α) := 
  if p x then x else panic! "check"

-- ## Repetition of a function.

-- `funpow` replaced with `Nat.repeat`

-- let can f x = try f x; true with Failure _ -> false;;

-- let rec repeat f x = try repeat f (f x) with Failure _ -> x;;

-- ## Handy list operations.

def List.range' (lb : Nat) : Nat → List Nat
| 0 => []
| n + 1 => range' lb n ++ [lb + n]

syntax "[" term ".." term "]" : term
macro_rules
| `([$m .. $n]) => `(List.range' $m ($n - $m + 1))

#eval [2 .. 3]

-- `(---)` has been removed

-- `map2` has been replaced by `List.map₂`

-- `rev` has been replaced by `List.reverse`

-- `hd` has been replaced by `List.head!`

-- `tl` has been replaced by `List.tail!`

-- `it_list` has been replaced by `List.foldr`

-- `end_itlist`
def List.reducer {α} [Inhabited α] (f : α → α → α) : List α → α
| [] => panic! ""
| [x] => x
| h :: t => f h (reducer f t)

-- #check List.foldr
def List.foldr₂ {β} [Inhabited β] (f : α → α → β → β) : List α → List α → β → β
| [], [], b => b
| h₁::t₁, h₂::t₂, b => f h₁ h₂ <| foldr₂ f t₁ t₂ b
| _, _, _ => panic! ""

-- `zip` has been replaced by `List.zip` 

-- `forall` has been replaced by `List.all`

-- `exists` has been replaced by `List.any`

-- `partition` has been replaced by `List.partition`

-- `filter` has been replaced by `List.filter`

-- `length` has been replaced by `List.length`

-- `last` has been replaced by `List.getLast!`

-- `butlast` has been replaced by `List.init`

-- `find` has been replaced by `List.find?`

-- `el` has been replaced by `List.get!`

-- `map` has been replaced by `List.map`

def allPairs (f : α → α → β) (l₁ l₂ : List α) : List β :=
match l₁ with
| [] => []
| h₁ :: t₁ => List.foldr (λ x a => f h₁ x :: a) (allPairs f t₁ l₂) l₂

def distinctPairs (l : List α) : List (α × α) :=
match l with
| [] => []
| x :: t => List.foldr (λ y a => (x, y) :: a) (distinctPairs t) t

-- let rec chop_list n l =
--   if n = 0 then [],l else
--   try let m,l' = chop_list (n-1) (tl l) in (hd l)::m,l'
--   with Failure _ -> failwith "chop_list";;

-- let replicate n a = map (fun x -> a) (1--n);;

-- let rec insertat i x l =
--   if i = 0 then x::l else
--   match l with
--     [] -> failwith "insertat: list too short for position to exist"
--   | h::t -> h::(insertat (i-1) x t);;

-- let rec forall2 p l1 l2 =
--   match (l1,l2) with
--     [],[] -> true
--   | (h1::t1,h2::t2) -> p h1 h2 & forall2 p t1 t2
--   | _ -> false;;

-- let index x =
--   let rec ind n l =
--     match l with
--       [] -> failwith "index"
--     | (h::t) -> if Pervasives.compare x h = 0 then n else ind (n + 1) t in
--   ind 0;;

-- let rec unzip l =
--   match l with
--     [] -> [],[]
--   | (x,y)::t ->
--       let xs,ys = unzip t in x::xs,y::ys;;

-- (* ------------------------------------------------------------------------- *)
-- (* Whether the first of two items comes earlier in the list.                 *)
-- (* ------------------------------------------------------------------------- *)

-- let rec earlier l x y =
--   match l with
--     h::t -> (Pervasives.compare h y <> 0) &
--             (Pervasives.compare h x = 0 or earlier t x y)
--   | [] -> false;;

-- (* ------------------------------------------------------------------------- *)
-- (* Application of (presumably imperative) function over a list.              *)
-- (* ------------------------------------------------------------------------- *)

-- let rec do_list f l =
--   match l with
--     [] -> ()
--   | h::t -> f(h); do_list f t;;

-- (* ------------------------------------------------------------------------- *)
-- (* Association lists.                                                        *)
-- (* ------------------------------------------------------------------------- *)

-- let rec assoc a l =
--   match l with
--     (x,y)::t -> if Pervasives.compare x a = 0 then y else assoc a t
--   | [] -> failwith "find";;

-- let rec rev_assoc a l =
--   match l with
--     (x,y)::t -> if Pervasives.compare y a = 0 then x else rev_assoc a t
--   | [] -> failwith "find";;

-- (* ------------------------------------------------------------------------- *)
-- (* Merging of sorted lists (maintaining repetitions).                        *)
-- (* ------------------------------------------------------------------------- *)

-- let rec merge ord l1 l2 =
--   match l1 with
--     [] -> l2
--   | h1::t1 -> match l2 with
--                 [] -> l1
--               | h2::t2 -> if ord h1 h2 then h1::(merge ord t1 l2)
--                           else h2::(merge ord l1 t2);;

-- (* ------------------------------------------------------------------------- *)
-- (* Bottom-up mergesort.                                                      *)
-- (* ------------------------------------------------------------------------- *)

-- let sort ord =
--   let rec mergepairs l1 l2 =
--     match (l1,l2) with
--         ([s],[]) -> s
--       | (l,[]) -> mergepairs [] l
--       | (l,[s1]) -> mergepairs (s1::l) []
--       | (l,(s1::s2::ss)) -> mergepairs ((merge ord s1 s2)::l) ss in
--   fun l -> if l = [] then [] else mergepairs [] (map (fun x -> [x]) l);;

-- (* ------------------------------------------------------------------------- *)
-- (* Common measure predicates to use with "sort".                             *)
-- (* ------------------------------------------------------------------------- *)

-- let increasing f x y = Pervasives.compare (f x) (f y) < 0;;

-- let decreasing f x y = Pervasives.compare (f x) (f y) > 0;;

-- (* ------------------------------------------------------------------------- *)
-- (* Eliminate repetitions of adjacent elements, with and without counting.    *)
-- (* ------------------------------------------------------------------------- *)

-- let rec uniq l =
--   match l with
--     x::(y::_ as t) -> let t' = uniq t in
--                       if Pervasives.compare x y = 0 then t' else
--                       if t'==t then l else x::t'
--  | _ -> l;;

-- let repetitions =
--   let rec repcount n l =
--     match l with
--       x::(y::_ as ys) -> if Pervasives.compare y x = 0 then repcount (n + 1) ys
--                   else (x,n)::(repcount 1 ys)
--     | [x] -> [x,n]
--     | [] -> failwith "repcount" in
--   fun l -> if l = [] then [] else repcount 1 l;;

-- let rec tryfind f l =
--   match l with
--       [] -> failwith "tryfind"
--     | (h::t) -> try f h with Failure _ -> tryfind f t;;

-- let rec mapfilter f l =
--   match l with
--     [] -> []
--   | (h::t) -> let rest = mapfilter f t in
--               try (f h)::rest with Failure _ -> rest;;

-- (* ------------------------------------------------------------------------- *)
-- (* Find list member that maximizes or minimizes a function.                  *)
-- (* ------------------------------------------------------------------------- *)

-- let optimize ord f l =
--   fst(end_itlist (fun (x,y as p) (x',y' as p') -> if ord y y' then p else p')
--                  (map (fun x -> x,f x) l));;

-- let maximize f l = optimize (>) f l and minimize f l = optimize (<) f l;;

-- (* ------------------------------------------------------------------------- *)
-- (* Set operations on ordered lists.                                          *)
-- (* ------------------------------------------------------------------------- *)

-- let setify =
--   let rec canonical lis =
--      match lis with
--        x::(y::_ as rest) -> Pervasives.compare x y < 0 & canonical rest
--      | _ -> true in
--   fun l -> if canonical l then l
--            else uniq (sort (fun x y -> Pervasives.compare x y <= 0) l);;

def List.sort [Inhabited α] [LT α] [DecidableRel (· < · : α → α → Prop)] (l : List α) : List α :=
  l.toArray.qsort (· < ·) |>.toList

def setify [Inhabited α] [LT α] [BEq α] [DecidableRel (· < · : α → α → Prop)] (l : List α) : List α 
  := l.sort.eraseDups

private partial def unionAux [BEq α] [LT α] [DecidableRel (· < · : α → α → Prop)] : List α → List α → List α
| [], l₂ => l₂
| l₁, [] => l₁
| l₁@(h₁ :: t₁), l₂@(h₂ :: t₂) =>
  if h₁ == h₂ then
    h₁ :: unionAux t₁ t₂ 
  else if h₁ < h₂ then
    h₁ :: unionAux t₁ l₂
  else
    h₂ :: unionAux l₁ t₂

def union [BEq α] [LT α] [DecidableRel (· < · : α → α → Prop)] [Inhabited α] (s₁ s₂ : List α) : List α :=
  unionAux (setify s₁) (setify s₂)

private partial def intersectAux [BEq α] [LT α] [DecidableRel (· < · : α → α → Prop)] : List α → List α → List α
| [], l₂ => []
| l₁, [] => []
| l₁@(h₁ :: t₁), l₂@(h₂ :: t₂) =>
  if h₁ == h₂ then
    h₁ :: intersectAux t₁ t₂ 
  else if h₁ < h₂ then
    intersectAux t₁ l₂
  else
    intersectAux l₁ t₂

def intersect [BEq α] [LT α] [DecidableRel (· < · : α → α → Prop)] [Inhabited α] (s₁ s₂ : List α) : List α :=
  intersectAux (setify s₁) (setify s₂)

-- let subtract =
--   let rec subtract l1 l2 =
--     match (l1,l2) with
--         ([],l2) -> []
--       | (l1,[]) -> l1
--       | ((h1::t1 as l1),(h2::t2 as l2)) ->
--           if h1 = h2 then subtract t1 t2
--           else if h1 < h2 then h1::(subtract t1 l2)
--           else subtract l1 t2 in
--   fun s1 s2 -> subtract (setify s1) (setify s2);;

def subsetAux [BEq α] [LT α] [DecidableRel (· < · : α → α → Prop)] (l₁ l₂ : List α) : Bool :=
  match l₁, l₂ with
  | [], _ => true
  | _, [] => false
  | h₁ :: t₁, h₂ :: t₂ =>
    if h₁ == h₂ then
      subsetAux t₁ t₂
    else if h₁ < h₂ then
      false
    else
      subsetAux l₁ t₂ 

def psubsetAux [BEq α] [LT α] [DecidableRel (· < · : α → α → Prop)] (l₁ l₂ : List α) : Bool :=
  match l₁, l₂ with
  | _, [] => false
  | [], _ => true
  | h₁ :: t₁, h₂ :: t₂ =>
    if h₁ == h₂ then
      psubsetAux t₁ t₂
    else if h₁ < h₂ then
      false
    else
      subsetAux l₁ t₂ 
  
def subset [BEq α] [LT α] [DecidableRel (· < · : α → α → Prop)] [Inhabited α] (l₁ l₂ : List α) : Bool :=
  subsetAux (setify l₁) (setify l₂)

def psubset [BEq α] [LT α] [DecidableRel (· < · : α → α → Prop)] [Inhabited α] (l₁ l₂ : List α) : Bool :=
  psubsetAux (setify l₁) (setify l₂)

-- let rec set_eq s1 s2 = (setify s1 = setify s2);;

-- let insert x s = union [x] s;;

def image [Inhabited β] [LT β] [BEq β] [DecidableRel (· < · : β → β → Prop)] (f : α → β) (s : List α) : List β := s.map f |> setify
-- let image f s = setify (map f s);;

-- (* ------------------------------------------------------------------------- *)
-- (* Union of a family of sets.                                                *)
-- (* ------------------------------------------------------------------------- *)

-- let unions s = setify(itlist (@) s []);;

-- (* ------------------------------------------------------------------------- *)
-- (* List membership. This does *not* assume the list is a set.                *)
-- (* ------------------------------------------------------------------------- *)

-- let rec mem x lis =
--   match lis with
--     [] -> false
--   | (h::t) -> Pervasives.compare x h = 0 or mem x t;;

-- (* ------------------------------------------------------------------------- *)
-- (* Finding all subsets or all subsets of a given size.                       *)
-- (* ------------------------------------------------------------------------- *)

-- let rec allsets m l =
--   if m = 0 then [[]] else
--   match l with
--     [] -> []
--   | h::t -> union (image (fun g -> h::g) (allsets (m - 1) t)) (allsets m t);;

-- let rec allsubsets s =
--   match s with
--     [] -> [[]]
--   | (a::t) -> let res = allsubsets t in
--               union (image (fun b -> a::b) res) res;;

-- let allnonemptysubsets s = subtract (allsubsets s) [[]];;

-- (* ------------------------------------------------------------------------- *)
-- (* Explosion and implosion of strings.                                       *)
-- (* ------------------------------------------------------------------------- *)

def explode (s : String) : List String := s.data.map (λ x => ⟨[x]⟩)

def implode (l : List Char) : String := l.asString

-- (* ------------------------------------------------------------------------- *)
-- (* Timing; useful for documentation but not logically necessary.             *)
-- (* ------------------------------------------------------------------------- *)

-- let time f x =
--   let start_time = Sys.time() in
--   let result = f x in
--   let finish_time = Sys.time() in
--   print_string
--     ("CPU time (user): "^(string_of_float(finish_time -. start_time)));
--   print_newline();
--   result;;

-- (* ------------------------------------------------------------------------- *)
-- (* Polymorphic finite partial functions via Patricia trees.                  *)
-- (*                                                                           *)
-- (* The point of this strange representation is that it is canonical (equal   *)
-- (* functions have the same encoding) yet reasonably efficient on average.    *)
-- (*                                                                           *)
-- (* Idea due to Diego Olivier Fernandez Pons (OCaml list, 2003/11/10).        *)
-- (* ------------------------------------------------------------------------- *)

-- type ('a,'b)func =
--    Empty
--  | Leaf of int * ('a*'b)list
--  | Branch of int * int * ('a,'b)func * ('a,'b)func;;
inductive Func (α β : Type _)
| Empty
| Leaf (i : USize) (l : List (α × β)) -- TODO: Change to `Int`
| Branch (i j : USize) (k l : Func α β)
deriving Inhabited

-- (* ------------------------------------------------------------------------- *)
-- (* Undefined function.                                                       *)
-- (* ------------------------------------------------------------------------- *)

def Func.undefined {α β} : Func α β := Empty

-- (* ------------------------------------------------------------------------- *)
-- (* In case of equality comparison worries, better use this.                  *)
-- (* ------------------------------------------------------------------------- *)

def Func.isUndefined : Func α β → Bool
| Empty => true
| _ => false 

-- (* ------------------------------------------------------------------------- *)
-- (* Operation analogous to "map" for lists.                                   *)
-- (* ------------------------------------------------------------------------- *)

def Func.map (f : α → β) (t : Func γ α) : Func γ β :=
  let rec mapList : List (γ × α) → List (γ × β) := 
    fun
    | [] => []
    | (x, y) :: t => (x, f y) :: mapList t
  let rec mapf : Func γ α → Func γ β :=
    fun
    | Empty => Empty
    | Leaf h l => Leaf h (mapList l)
    | Branch p b l r => Branch p b (mapf l) (mapf r)
  mapf t

-- (* ------------------------------------------------------------------------- *)
-- (* Operations analogous to "fold" for lists.                                 *)
-- (* ------------------------------------------------------------------------- *)

-- let foldl =
--   let rec foldl_list f a l =
--     match l with
--       [] -> a
--     | (x,y)::t -> foldl_list f (f a x y) t in
--   let rec foldl f a t =
--     match t with
--       Empty -> a
--     | Leaf(h,l) -> foldl_list f a l
--     | Branch(p,b,l,r) -> foldl f (foldl f a l) r in
--   foldl;;

-- let foldr =
--   let rec foldr_list f l a =
--     match l with
--       [] -> a
--     | (x,y)::t -> f x y (foldr_list f t a) in
--   let rec foldr f t a =
--     match t with
--       Empty -> a
--     | Leaf(h,l) -> foldr_list f l a
--     | Branch(p,b,l,r) -> foldr f l (foldr f r a) in
--   foldr;;

-- (* ------------------------------------------------------------------------- *)
-- (* Mapping to sorted-list representation of the graph, domain and range.     *)
-- (* ------------------------------------------------------------------------- *)

-- let graph f = setify (foldl (fun a x y -> (x,y)::a) [] f);;

-- let dom f = setify(foldl (fun a x y -> x::a) [] f);;

-- let ran f = setify(foldl (fun a x y -> y::a) [] f);;

-- (* ------------------------------------------------------------------------- *)
-- (* Application.                                                              *)
-- (* ------------------------------------------------------------------------- *)

#check Ord

private def applyList [Ord α] (l : List (α × β)) (g : α → β) (y : α) : β :=
  match l with
  | (a, b) :: t => 
    match compare y a with
    | Ordering.lt => g y
    | Ordering.eq => b
    | Ordering.gt => applyList t g y
  | [] => g y

private partial def look [Ord α] [Inhabited β] (t : Func α β) (k : USize) (g : α → β) (x : α) : β :=
    match t with
    | Func.Leaf h l =>
      if h == k then
        applyList l g x
      else
        g x
    | Func.Branch p b l r =>
      if (k ^^^ p) &&& (b - 1) == 0 then
        look (if k &&& b == 0 then l else r) k g x
      else
        g x
    | _ => g x

partial def applyd [Inhabited β] [Ord α] [Hashable α] (f : Func α β) (g : α → β) (x : α) : β :=
  look f (hash x) g x

-- let applyd =
--   let rec apply_listd l d x =
--     match l with
--       (a,b)::t -> let c = Pervasives.compare x a in
--                   if c = 0 then b else if c > 0 then apply_listd t d x else d x
--     | [] -> d x in
--   fun f d x ->
--     let k = Hashtbl.hash x in
--     let rec look t =
--       match t with
--         Leaf(h,l) when h = k -> apply_listd l d x
--       | Branch(p,b,l,r) when (k lxor p) land (b - 1) = 0
--                 -> look (if k land b = 0 then l else r)
--       | _ -> d x in
--     look f;;

-- def apply (f) := applyd f (λ x => _)

-- let apply f = applyd f (fun x -> failwith "apply");;

-- let tryapplyd f a d = applyd f (fun x -> d) a;;

-- let tryapplyl f x = tryapplyd f x [];;

-- let defined f x = try apply f x; true with Failure _ -> false;;

-- (* ------------------------------------------------------------------------- *)
-- (* Undefinition.                                                             *)
-- (* ------------------------------------------------------------------------- *)

-- let undefine =
--   let rec undefine_list x l =
--     match l with
--       (a,b as ab)::t ->
--           let c = Pervasives.compare x a in
--           if c = 0 then t
--           else if c < 0 then l else
--           let t' = undefine_list x t in
--           if t' == t then l else ab::t'
--     | [] -> [] in
--   fun x ->
--     let k = Hashtbl.hash x in
--     let rec und t =
--       match t with
--         Leaf(h,l) when h = k ->
--           let l' = undefine_list x l in
--           if l' == l then t
--           else if l' = [] then Empty
--           else Leaf(h,l')
--       | Branch(p,b,l,r) when k land (b - 1) = p ->
--           if k land b = 0 then
--             let l' = und l in
--             if l' == l then t
--             else (match l' with Empty -> r | _ -> Branch(p,b,l',r))
--           else
--             let r' = und r in
--             if r' == r then t
--             else (match r' with Empty -> l | _ -> Branch(p,b,l,r'))
--       | _ -> t in
--     und;;

-- (* ------------------------------------------------------------------------- *)
-- (* Redefinition and combination.                                             *)
-- (* ------------------------------------------------------------------------- *)

-- let (|->),combine =
--   let newbranch p1 t1 p2 t2 =
--     let zp = p1 lxor p2 in
--     let b = zp land (-zp) in
--     let p = p1 land (b - 1) in
--     if p1 land b = 0 then Branch(p,b,t1,t2)
--     else Branch(p,b,t2,t1) in
--   let rec define_list (x,y as xy) l =
--     match l with
--       (a,b as ab)::t ->
--           let c = Pervasives.compare x a in
--           if c = 0 then xy::t
--           else if c < 0 then xy::l
--           else ab::(define_list xy t)
--     | [] -> [xy]
--   and combine_list op z l1 l2 =
--     match (l1,l2) with
--       [],_ -> l2
--     | _,[] -> l1
--     | ((x1,y1 as xy1)::t1,(x2,y2 as xy2)::t2) ->
--           let c = Pervasives.compare x1 x2 in
--           if c < 0 then xy1::(combine_list op z t1 l2)
--           else if c > 0 then xy2::(combine_list op z l1 t2) else
--           let y = op y1 y2 and l = combine_list op z t1 t2 in
--           if z(y) then l else (x1,y)::l in
--   let (|->) x y =
--     let k = Hashtbl.hash x in
--     let rec upd t =
--       match t with
--         Empty -> Leaf (k,[x,y])
--       | Leaf(h,l) ->
--            if h = k then Leaf(h,define_list (x,y) l)
--            else newbranch h t k (Leaf(k,[x,y]))
--       | Branch(p,b,l,r) ->
--           if k land (b - 1) <> p then newbranch p t k (Leaf(k,[x,y]))
--           else if k land b = 0 then Branch(p,b,upd l,r)
--           else Branch(p,b,l,upd r) in
--     upd in
--   let rec combine op z t1 t2 =
--     match (t1,t2) with
--       Empty,_ -> t2
--     | _,Empty -> t1
--     | Leaf(h1,l1),Leaf(h2,l2) ->
--           if h1 = h2 then
--             let l = combine_list op z l1 l2 in
--             if l = [] then Empty else Leaf(h1,l)
--           else newbranch h1 t1 h2 t2
--     | (Leaf(k,lis) as lf),(Branch(p,b,l,r) as br) ->
--           if k land (b - 1) = p then
--             if k land b = 0 then
--               (match combine op z lf l with
--                  Empty -> r | l' -> Branch(p,b,l',r))
--             else
--               (match combine op z lf r with
--                  Empty -> l | r' -> Branch(p,b,l,r'))
--           else
--             newbranch k lf p br
--     | (Branch(p,b,l,r) as br),(Leaf(k,lis) as lf) ->
--           if k land (b - 1) = p then
--             if k land b = 0 then
--               (match combine op z l lf with
--                 Empty -> r | l' -> Branch(p,b,l',r))
--             else
--               (match combine op z r lf with
--                  Empty -> l | r' -> Branch(p,b,l,r'))
--           else
--             newbranch p br k lf
--     | Branch(p1,b1,l1,r1),Branch(p2,b2,l2,r2) ->
--           if b1 < b2 then
--             if p2 land (b1 - 1) <> p1 then newbranch p1 t1 p2 t2
--             else if p2 land b1 = 0 then
--               (match combine op z l1 t2 with
--                  Empty -> r1 | l -> Branch(p1,b1,l,r1))
--             else
--               (match combine op z r1 t2 with
--                  Empty -> l1 | r -> Branch(p1,b1,l1,r))
--           else if b2 < b1 then
--             if p1 land (b2 - 1) <> p2 then newbranch p1 t1 p2 t2
--             else if p1 land b2 = 0 then
--               (match combine op z t1 l2 with
--                  Empty -> r2 | l -> Branch(p2,b2,l,r2))
--             else
--               (match combine op z t1 r2 with
--                  Empty -> l2 | r -> Branch(p2,b2,l2,r))
--           else if p1 = p2 then
--            (match (combine op z l1 l2,combine op z r1 r2) with
--               (Empty,r) -> r | (l,Empty) -> l | (l,r) -> Branch(p1,b1,l,r))
--           else
--             newbranch p1 t1 p2 t2 in
--   (|->),combine;;

-- (* ------------------------------------------------------------------------- *)
-- (* Special case of point function.                                           *)
-- (* ------------------------------------------------------------------------- *)

-- let (|=>) = fun x y -> (x |-> y) undefined;;

-- (* ------------------------------------------------------------------------- *)
-- (* Idiom for a mapping zipping domain and range lists.                       *)
-- (* ------------------------------------------------------------------------- *)

-- let fpf xs ys = itlist2 (|->) xs ys undefined;;

-- (* ------------------------------------------------------------------------- *)
-- (* Grab an arbitrary element.                                                *)
-- (* ------------------------------------------------------------------------- *)

-- let rec choose t =
--   match t with
--     Empty -> failwith "choose: completely undefined function"
--   | Leaf(h,l) -> hd l
--   | Branch(b,p,t1,t2) -> choose t1;;

-- (* ------------------------------------------------------------------------- *)
-- (* Install a (trivial) printer for finite partial functions.                 *)
-- (* ------------------------------------------------------------------------- *)

-- let print_fpf (f:('a,'b)func) = print_string "<func>";;

-- #install_printer print_fpf;;

-- (* ------------------------------------------------------------------------- *)
-- (* Related stuff for standard functions.                                     *)
-- (* ------------------------------------------------------------------------- *)

-- let valmod a y f x = if x = a then y else f(x);;

-- let undef x = failwith "undefined function";;

-- (* ------------------------------------------------------------------------- *)
-- (* Union-find algorithm.                                                     *)
-- (* ------------------------------------------------------------------------- *)

-- type ('a)pnode = Nonterminal of 'a | Terminal of 'a * int;;

-- type ('a)partition = Partition of ('a,('a)pnode)func;;

-- let rec terminus (Partition f as ptn) a =
--   match (apply f a) with
--     Nonterminal(b) -> terminus ptn b
--   | Terminal(p,q) -> (p,q);;

-- let tryterminus ptn a =
--   try terminus ptn a with Failure _ -> (a,1);;

-- let canonize ptn a = fst(tryterminus ptn a);;

-- let equivalent eqv a b = canonize eqv a = canonize eqv b;;

-- let equate (a,b) (Partition f as ptn) =
--   let (a',na) = tryterminus ptn a
--   and (b',nb) = tryterminus ptn b in
--   Partition
--    (if a' = b' then f else
--     if na <= nb then
--        itlist identity [a' |-> Nonterminal b'; b' |-> Terminal(b',na+nb)] f
--     else
--        itlist identity [b' |-> Nonterminal a'; a' |-> Terminal(a',na+nb)] f);;

-- let unequal = Partition undefined;;

-- let equated (Partition f) = dom f;;

-- (* ------------------------------------------------------------------------- *)
-- (* First number starting at n for which p succeeds.                          *)
-- (* ------------------------------------------------------------------------- *)

-- let rec first n p = if p(n) then n else first (n +/ Int 1) p;;
