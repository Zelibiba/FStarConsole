module Test.Float.Base

include Test.Float.Pair
open FStar.Printf
open FStar.Mul


new val float : eqtype

val to_string : float -> string

private let extension = MkExtension #float to_string
let float_extension : extension_parser = fun s ->
  match s with
  | 'f'::tl -> Some (extension, tl)
  | _ -> None

val to_pair (x: float) : pair
val of_pair (p: pair) : float

let base x : GTot (b: int{b = 0 \/ b % 10 <> 0}) = (to_pair x).base
let exp x : GTot int = (to_pair x).exp



val of_int (x: int) : (r: float{r = of_pair (norm_pair ({ base = x; exp = 0 }))})

val _0 : (z: float{z = of_pair ({ base = 0; exp = 0 })})
val _1  : (o: float{o = of_pair ({ base = 1; exp = 0 })})

type not_0 = (nz: float{nz <> _0})

let to_shared_exp (a b: float) : GTot (int & int & int) =
  let { base = base_a; exp = exp_a } = to_pair a in
  let { base = base_b; exp = exp_b } = to_pair b in
  let exp_min = min exp_a exp_b in
  let a' = base_a * pow10 (exp_a - exp_min) in
  let b' = base_b * pow10 (exp_b - exp_min) in
  a', b', exp_min

val add (a b: float) : Pure float (requires True)
  (ensures fun sum -> 
    let a', b', exp_min = to_shared_exp a b in
    sum = of_pair (norm_pair ({ base = a' + b'; exp = exp_min })))

val sub (a b: float) : Pure float (requires True)
  (ensures fun diff -> 
    let a', b', exp_min = to_shared_exp a b in
    to_pair diff = norm_pair ({ base = a' - b'; exp = exp_min }))

val neg (a: float) : Pure float (requires True)
  (ensures fun neg -> base neg = -(base a) /\ exp neg = exp a)

val mul (a b: float) : Pure float (requires True)
  (ensures fun prod -> prod = of_pair (norm_pair ({ base = base a * base b; exp = exp a + exp b })))

val eq (a b: float)  : Pure bool (requires True) (ensures fun c -> c = (base (a `sub` b) = 0) /\ c = (a = b))
val gt (a b: float)  : Pure bool (requires True) (ensures fun c -> c = (base (a `sub` b) > 0))
val lt (a b: float)  : Pure bool (requires True) (ensures fun c -> c = (base (a `sub` b) < 0))
val gte (a b: float) : Pure bool (requires True) (ensures fun c -> c = (base (a `sub` b) >= 0))
val lte (a b: float) : Pure bool (requires True) (ensures fun c -> c = (base (a `sub` b) <= 0))

unfold let ( +. ) a b = add a b
unfold let ( -. ) a b = sub a b
unfold let ( ~. ) a   = neg a
unfold let ( *. ) a b = mul a b
// unfold let ( /. ) a b = div a b
unfold let (=.) a b = eq a b
unfold let (>.) a b = gt a b
unfold let (<.) a b = lt a b
unfold let (>=.) a b = gte a b
unfold let (<=.) a b = lte a b

let sqr x = x *. x

val sqrt (a: float) : Pure float (requires a >=. _0)
  (ensures fun sqrt -> sqrt >=. _0 /\ sqrt *. sqrt = a /\ (sqrt = _0 <==> a = _0))