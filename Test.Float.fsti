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

type mant_pow' = int & int
type mant_pow = x: mant_pow'{x._1 % 10 = 0 ==> (x._1 = 0 /\ x._2 = 0)}

let rec pow10 (x: nat) : GTot pos =
  match x with
  | 0 -> 1
  | _ -> 10 * pow10 (x - 1)
let rec norm_pair (mp: mant_pow') : Tot mant_pow (decreases abs (fst mp)) =
  let mantissa = fst mp in
  let power = snd mp in
  if mantissa = 0
  then 0, 0
  else if mantissa % 10 = 0
       then norm_pair (mantissa / 10, power + 1)
       else mp

let rec lemma_norm_pow_add (n: int) (mp': mant_pow') (mp_': mant_pow') : Lemma 
  (requires fst mp' <> 0 /\ mp_' = (fst mp', snd mp' + n))
  (ensures (let mp = norm_pair mp' in norm_pair mp_' = (fst mp, snd mp + n)))
  (decreases abs (fst mp'))
  =
  match fst mp' % 10 with
  | 0 -> 
    let mp'' = (fst mp' / 10, snd mp' + 1) in
    let mp_'' = (fst mp_' / 10, snd mp_' + 1) in
    lemma_norm_pow_add n mp'' mp_''
  | _ -> ()

let rec lemma_norm_mant_mul' (n: nat) (mp: mant_pow) : Lemma 
  (requires fst mp <> 0)
  (ensures norm_pair (fst mp * pow10 n, snd mp) = (fst mp, snd mp + n))
  =
  match n with
  | 0 -> ()
  | _ ->
    lemma_norm_mant_mul' (n - 1) mp;
    let mant', pow' = fst mp * pow10 (n - 1), snd mp + n - 1 in
    assert (norm_pair (mant', snd mp) = (fst mp, pow'));
    lemma_norm_pow_add 1 (mant', snd mp) (mant', snd mp + 1);
    assert (norm_pair (mant', snd mp + 1) = (fst mp, pow' + 1));
    assert (norm_pair (mant' * 10, snd mp) = norm_pair (mant', snd mp + 1));
    assert (norm_pair (mant' * 10, snd mp) = (fst mp, pow' + 1))

let lemma_norm_mant_mul (n: nat) (mant: int) (pow: int) : Lemma
  (requires mant % 10 <> 0)
  (ensures norm_pair (mant * pow10 n, pow) = (mant, pow + n))
  [SMTPat (norm_pair (mant * pow10 n, pow))]
  = lemma_norm_mant_mul' n (mant, pow)

val to_pair (x: float) : mant_pow
val of_pair (mant_power: mant_pow) : float
let of_int (x: int) : float = of_pair (norm_pair (x, 0))

val lemma_of_to_inv (x: float) : Lemma (of_pair (to_pair x) = x) [SMTPat (to_pair x)]
val lemma_to_of_inv (x: mant_pow) : Lemma (to_pair (of_pair x) = x) [SMTPat (of_pair x)]

val zero : (z: float{z = of_pair (0, 0)})
val one : (o: float{o = of_pair (1, 0)})


type not_zero = (nz: float{nz <> zero})

let mantissa (x: float) : GTot int = (to_pair x)._1
let power (x: float) : GTot int = (to_pair x)._2


val add (a b: float) : Pure float
  (requires True)
  (ensures fun c -> 
    let mant_a, pow_a = to_pair a in
    let mant_b, pow_b = to_pair b in
    let pow_min = min pow_a pow_b in
    let a' = (mantissa a) * pow10 (pow_a - pow_min) in
    let b' = (mantissa b) * pow10 (pow_b - pow_min) in
    to_pair c = norm_pair (a' + b', pow_min))

val sub (a b: float) : Pure float
  (requires True)
  (ensures fun c -> 
    let mant_a, pow_a = to_pair a in
    let mant_b, pow_b = to_pair b in
    let pow_min = min pow_a pow_b in
    let a' = mant_a * pow10 (pow_a - pow_min) in
    let b' = mant_b * pow10 (pow_b - pow_min) in
    to_pair c = norm_pair (a' - b', pow_min))

val neg (a: float) : Pure float
  (requires True)
  (ensures fun b -> mantissa a = -(mantissa b) /\ power a = power b)

val mul (a b: float) : Pure float
  (requires True)
  (ensures fun c -> to_pair c = norm_pair (mantissa a * mantissa b, power a + power b))

val div (a: float) (b: not_zero) : Pure float
  (requires True)
  (ensures fun c -> c `mul` b = a)

val inv (a: not_zero) : Pure not_zero
  (requires True)
  (ensures fun b -> b = one `div` a)

val gt (a b: float) : Pure bool (requires True) (ensures fun c -> c <==> mantissa (a `sub` b) > 0)
val lt (a b: float) : Pure bool (requires True) (ensures fun c -> c <==> mantissa (a `sub` b) < 0)
val gte (a b: float) : Pure bool (requires True) (ensures fun c -> c <==> mantissa (a `sub` b) >= 0)
val lte (a b: float) : Pure bool (requires True) (ensures fun c -> c <==> mantissa (a `sub` b) <= 0)

val abs (a: float) : Pure float
  (requires True)
  (ensures fun b -> if a `lt` zero then b = neg a else b = a)

unfold let ( +. ) a b = add a b
unfold let ( -. ) a b = sub a b
unfold let ( ~. ) a   = neg a
unfold let ( *. ) a b = mul a b
unfold let ( /. ) a b = div a b

unfold let (>.) a b = gt a b
unfold let (<.) a b = lt a b
unfold let (>=.) a b = gte a b
unfold let (<=.) a b = lte a b

let lemma_commut_add a b : Lemma (a +. b = b +. a) = ()
let lemma_commut_mul a b : Lemma (a *. b = b *. a) = ()

let lemma_add_zero (a: float) : Lemma (a `add` zero = a) = ()
let lemma_mul_one  a : Lemma (a *. one  = a) = ()
let lemma_mul_zero a : Lemma (a *. zero = zero) = ()
let lemma_div_one  a : Lemma (a /. one = a) = ()

let test () = assert (zero = of_pair (0, 0))

let lemma_sub_neg (a: float) : Lemma (~.a = zero -. a) =
  match a = zero with
  | true -> ()
  | _ -> 
    let mant_z, pow_z = to_pair zero in
    let mant_a, pow_a = to_pair a in
    let pow_min = min pow_a pow_z in
    let z' = mant_z * pow10 (pow_z - pow_min) in
    let a' = mant_a * pow10 (pow_a - pow_min) in
    match pow_min with
    | 0 ->
      assert (z' - a' = - mant_a * pow10 pow_a);
      lemma_norm_mant_mul pow_a (-mant_a) pow_min
    | _ -> ()
  
let lemma_neg_neg a : Lemma (~.(~.a) = a) = ()
let lemma_add_neg a : Lemma (a -. a = zero) = ()
let lemma_sub_add a b : Lemma (a -. b = a +. ~.b) = ()
// let lemma_div_inv a : Lemma (a /. a = one) = ()
// let lemma_inv_inv a : Lemma (inv (inv a) = a) = ()

let lemma_additive_add_left a b c : Lemma (a +. b +. c = (a +. b) +. c) = ()
let lemma_additive_add_right a b c : Lemma (a +. b +. c = a +. (b +. c)) [SMTPat (a +. b +. c)] =
  assume (a +. b +. c = a +. (b +. c))
let lemma_additive_sub_right a b c : Lemma (a +. b -. c = a +. (b -. c)) [SMTPat (a +. b -. c)] =
  assume (a +. b -. c = a +. (b -. c))
let lemma_additive_mul_left a b c : Lemma (a *. b *. c = (a *. b) *. c) = ()
let lemma_additive_mul_right a b c : Lemma (a *. b *. c = a *. (b *. c)) [SMTPat (a *. b *. c)] = 
  assume (a *. b *. c = a *. (b *. c))

let lemma_add_perenos a b c : Lemma (requires a +. b = c) (ensures a = c -. b) =
  assert (a +. b -. b = c -. b);
  lemma_additive_sub_right a b b

let lemma_distrib_add a b c : Lemma (a *. (b +. c) = a *. b +. a *. c) =
  assume (a *. (b +. c) = a *. b +. a *. c)