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

val of_pair (mant_power: mant_pow) : float
val to_pair (x: float) : mant_pow

val lemma_of_to_inv (x: float) : Lemma (of_pair (to_pair x) = x) [SMTPat (to_pair x)]
val lemma_to_of_inv (x: mant_pow) : Lemma (to_pair (of_pair x) = x) [SMTPat (of_pair x)]

let zero : float = of_pair (0, 0)

let mantissa (x: float) : GTot mantType = (to_pair x)._1
let power (x: float) : GTot powerType = (to_pair x)._2


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

  
let rec pow10 (x: nat) : GTot pos =
  match x with
  | 0 -> 1
  | _ -> 10 * pow10 (x - 1)

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

val mul (a b: float) : Pure float
  (requires True)
  (ensures fun c -> to_pair c = norm_pair (mantissa a * mantissa b, power a + power b))

// val div (a b: float) : Pure float
//   (requires True)
//   (ensures fun c -> )

val gt (a b: float) : Pure bool (requires True) (ensures fun c -> c <==> mantissa (a `sub` b) > 0)
val lt (a b: float) : Pure bool (requires True) (ensures fun c -> c <==> mantissa (a `sub` b) < 0)
val gte (a b: float) : Pure bool (requires True) (ensures fun c -> c <==> mantissa (a `sub` b) >= 0)
val lte (a b: float) : Pure bool (requires True) (ensures fun c -> c <==> mantissa (a `sub` b) <= 0)