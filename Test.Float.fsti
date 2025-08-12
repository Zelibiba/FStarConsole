module Test.Float

open FStar.Printf
open FStar.Mul

new val float : eqtype

val to_string : float -> string

private let extension = MkExtension #float to_string
let float_extension : extension_parser = fun s ->
  match s with
  | 'f'::tl -> Some (extension, tl)
  | _ -> None

type mantType = int
type powerType = e: int{e <= 0}
type mant_pow' = mantType & powerType
type mant_pow = x: mant_pow'{x._1 % 10 = 0 ==> x._2 = 0}

val to_pair (x: float) : mant_pow
val of_pair (mant_power: mant_pow) : float
let of_int (x: int) : float = of_pair (x, 0)

val lemma_of_to_inv (x: float) : Lemma (of_pair (to_pair x) = x) [SMTPat (to_pair x)]
val lemma_to_of_inv (x: mant_pow) : Lemma (to_pair (of_pair x) = x) [SMTPat (of_pair x)]

val zero : (z: float{z = of_pair (0, 0)})
val one : (o: float{o = of_pair (1, 0)})

type not_zero = (nz: float{nz <> zero})

let mantissa (x: float) : GTot mantType = (to_pair x)._1
let power (x: float) : GTot powerType = (to_pair x)._2


let rec pow10 (x: nat) : GTot pos =
  match x with
  | 0 -> 1
  | _ -> 10 * pow10 (x - 1)
let rec incr_power (mp: mant_pow') : GTot (x: mant_pow'{x._1 % 10 = 0 ==> x._2 = 0}) (decreases (-mp._2)) =
    if mp._1 % 10 = 0 && mp._2 < 0
    then incr_power (mp._1 / 10, mp._2 + 1)
    else mp
let norm_pair (mant_pow: mant_pow') : GTot (x: mant_pow'{x._1 % 10 = 0 ==> x._2 = 0}) =
  let mantissa = mant_pow._1 in
  let exp = mant_pow._2 in
  match mantissa with
  | 0 -> 0, 0
  | _ -> incr_power mant_pow


val add (a b: float) : Pure float
  (requires True)
  (ensures fun c -> 
    let mant_a, pow_a = to_pair a in
    let mant_b, pow_b = to_pair b in
    let pow_min = min pow_a pow_b in
    let a' = (mantissa a) * pow10 (pow_a - pow_min) in
    let b' = (mantissa b) * pow10 (pow_b - pow_min) in
    to_pair c = (a' + b', pow_min))

val sub (a b: float) : Pure float
  (requires True)
  (ensures fun c -> 
    let mant_a, pow_a = to_pair a in
    let mant_b, pow_b = to_pair b in
    let pow_min = min pow_a pow_b in
    let a' = (mantissa a) * pow10 (pow_a - pow_min) in
    let b' = (mantissa b) * pow10 (pow_b - pow_min) in
    to_pair c = (a' - b', pow_min))

val neg (a: float) : Pure float
  (requires True)
  (ensures fun b -> mantissa a = -(mantissa b) /\ power a = power b)

val mul (a b: float) : Pure float
  (requires True)
  (ensures fun c -> to_pair c = norm_pair (mantissa a * mantissa b, power a + power b))

val div (a: float) (b: not_zero) : float

val gt (a b: float) : Pure bool (requires True) (ensures fun c -> c <==> mantissa (a `sub` b) > 0)
val lt (a b: float) : Pure bool (requires True) (ensures fun c -> c <==> mantissa (a `sub` b) < 0)
val gte (a b: float) : Pure bool (requires True) (ensures fun c -> c <==> mantissa (a `sub` b) >= 0)
val lte (a b: float) : Pure bool (requires True) (ensures fun c -> c <==> mantissa (a `sub` b) <= 0)

unfold let ( +. ) a b = add a b
unfold let ( -. ) a b = sub a b
unfold let ( ~. ) a   = neg a
unfold let ( *. ) a b = mul a b
unfold let ( /. ) a b = div a b

unfold let (>.) a b = gt a b
unfold let (<.) a b = lt a b
unfold let (>=.) a b = gte a b
unfold let (<=.) a b = lte a b


val abs (a: float) : Pure float
  (requires True)
  (ensures fun b -> (if a <. zero then b = ~.a else b = a) /\ b >=. zero)

let lemma_commut_add a b : Lemma (a +. b = b +. a) = ()
let lemma_commut_mul a b : Lemma (a *. b = b *. a) = ()

let lemma_add_zero a : Lemma (a +. zero = a) = ()
let lemma_mul_one  a : Lemma (a *. one  = a) = ()
let lemma_mul_zero a : Lemma (a *. zero = zero) = ()

let lemma_sub_neg a : Lemma (~.a = zero -. a) = ()
let lemma_neg_neg a : Lemma (~.(~.a) = a) = ()
let lemma_add_neg a : Lemma (a -. a = zero) = ()

let lemma_additive_add_left a b c : Lemma (a +. b +. c = (a +. b) +. c) = ()
let lemma_additive_add_right a b c : Lemma (a +. b +. c = a +. (b +. c)) [SMTPat (a +. b +. c)] =
  assume (a +. b +. c = a +. (b +. c))
let lemma_additive_mul_left a b c : Lemma (a *. b *. c = (a *. b) *. c) = ()
let lemma_additive_mul_right a b c : Lemma (a *. b *. c = a *. (b *. c)) = 
  assume (a *. b *. c = a *. (b *. c))

let lemma_add_perenos a b c : Lemma (requires a +. b = c) (ensures a = c -. b) =
  assert (a +. b -. b = c -. b);
  lemma_additive_add_right a b (~.b)

let lemma_distrib_add a b c : Lemma (a *. (b +. c) = a *. b +. a *. c) = assume (a *. (b +. c) = a *. b +. a *. c)

// let lemma_gt a b : Lemma (requires a >. b) (ensures a -. b >. zero) = ()


let ( .[] ) x (min, max) = min <=. x && x <=. max
let ( .() ) x (min, max) = min <. x && x <. max
let ( <.|> ) x (min, max) = min <=. x && x <. max
let ( <|.> ) x (min, max) = min <. x && x <=. max

let pi : float = of_int 180
let piHalf : float = of_int 90

val sin : float -> (r: float{r.[~.one, one]})
val cos : float -> (r: float{r.[~.one, one]})
val arctg (x y: float) : (r: float{r.[~.pi, pi]})
val hypot (x y: float) : (r: float{r *. r = x *. x +. y *. y /\ r >=. zero})

val lemma_sin_odd  (a: float) : Lemma (sin a = ~.(sin ~.a))
val lemma_cos_even (a: float) : Lemma (cos a = cos ~.a)
val lemma_arctg_x_pos x y : Lemma (requires x >=. zero) (ensures (arctg x y).(~.piHalf, piHalf)) [SMTPat (arctg x y)]

val lemma_sin_0 (a: float{a = zero}) : Lemma (sin a = zero)
val lemma_cos_0 (a: float{a = zero}) : Lemma (cos a = one)
let lemma_sin_cos_0 (a: float{a = zero}) : Lemma (sin a = zero /\ cos a = one) = lemma_sin_0 a; lemma_cos_0 a

val lemma_sin_90 (a: float{a = of_int 90}) : Lemma (sin a = one)
val lemma_cos_90 (a: float{a = of_int 90}) : Lemma (cos a = zero)
let lemma_sin_cos_90 (a: float{a = of_int 90}) : Lemma (sin a = one /\ cos a = zero) = lemma_sin_90 a; lemma_cos_90 a

val lemma_cos_add (a b: float) : Lemma (cos (a +. b) = cos a *. cos b -. sin a *. sin b)
val lemma_sin_add (a b: float) : Lemma (sin (a +. b) = sin a *. cos b +. cos a *. sin b)