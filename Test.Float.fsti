module Test.Float

open FStar.Printf
open FStar.Mul
module Lemmas = FStar.Math.Lemmas

new val float : eqtype

val to_string : float -> string

private let extension = MkExtension #float to_string
let float_extension : extension_parser = fun s ->
  match s with
  | 'f'::tl -> Some (extension, tl)
  | _ -> None

type mant_pow' = int & int
type mant_pow = x: mant_pow'{x._1 % 10 = 0 ==> (x._1 = 0 /\ x._2 = 0)}

private let ( +> ) (mp: mant_pow') (n: int) = (fst mp, snd mp + n)
private let ( *< ) (mp: mant_pow') (n: int) = (fst mp * n, snd mp)
private let ( /< ) (mp: mant_pow') (n: nonzero) = (fst mp / n, snd mp)
private let ( >=< ) (a b: int) =
  a > 0 && b > 0 ||
  a = 0 && b = 0 ||
  a < 0 && b < 0

let lemma_mant_mul (mp: mant_pow') (a b: int) : Lemma (mp *< a *< b = mp *< (a * b)) = ()


let rec pow10 (x: nat) : GTot pos =
  match x with
  | 0 -> 1
  | _ -> 10 * pow10 (x - 1)
let rec norm_pair (mp': mant_pow') : Pure mant_pow
  (requires True)
  (ensures fun mp ->
    (fst mp' >=< fst mp) /\
    (fst mp' <> 0 ==>
      snd mp' <= snd mp /\
      fst mp' = fst mp * pow10 (snd mp - snd mp') /\
      fst mp = fst mp' / pow10 (snd mp - snd mp')))
  (decreases abs (fst mp'))
  =
  let mantissa = fst mp' in
  let power = snd mp' in
  match mantissa, mantissa % 10 with
  | 0, _ -> 0, 0
  | _, 0 -> 
    let mp = norm_pair (mantissa / 10, power + 1) in
    Lemmas.cancel_mul_div (fst mp) (pow10 (snd mp - snd mp'));
    mp
  | _, _ -> mp'

let rec lemma_norm_pow_inj (n: int) (mp': mant_pow') : Lemma
  (requires fst mp' <> 0)
  (ensures norm_pair (mp' +> n) = norm_pair mp' +> n)
  (decreases abs (fst mp'))
  =
  match fst mp' % 10 with
  | 0 -> lemma_norm_pow_inj n (mp' /< 10 +> 1)
  | _ -> ()

let rec lemma_norm_neg_inj (mp' : mant_pow') : Lemma
  (requires True)
  (ensures norm_pair (mp' *< (-1)) = (norm_pair mp') *< (-1))
  (decreases abs (fst mp'))
  =
  match fst mp', fst mp' % 10 with
  | 0, _ -> ()
  | _, 0 -> lemma_norm_neg_inj (mp' /< 10 +> 1)
  | _, _ -> ()

let lemma_norm_mul10_inj (mp': mant_pow') : Lemma
  (requires fst mp' <> 0)
  (ensures norm_pair (mp' *< 10) = (norm_pair mp') +> 1)
  =
  assert (norm_pair (mp' *< 10 +> (-1)) = norm_pair mp');
  lemma_norm_pow_inj 1 (mp' *< 10 +> (-1))



let rec lemma_norm_pow10_inj' (n: nat) (mp': mant_pow') : Lemma 
  (requires fst mp' <> 0)
  (ensures norm_pair (mp' *< pow10 n) = (norm_pair mp') +> n)
  =
  match n with
  | 0 -> ()
  | _ ->
    lemma_norm_pow10_inj' (n - 1) mp';
    assert (norm_pair (mp' *< pow10 (n - 1)) = (norm_pair mp') +> (n - 1));
    lemma_norm_mul10_inj (mp' *< pow10 (n - 1));
    lemma_mant_mul mp' (pow10 (n - 1)) 10;
    assert (norm_pair (mp' *< pow10 (n - 1) *< 10) = norm_pair (mp' *< pow10 (n - 1)) +> 1);
    assert (norm_pair (mp' *< pow10 n) = norm_pair mp' +> n)

let lemma_norm_pow10_inj (n: nat) (mant: int) (pow: int) : Lemma
  (requires mant % 10 <> 0)
  (ensures norm_pair (mant * pow10 n, pow) = (mant, pow + n))
  [SMTPat (norm_pair (mant * pow10 n, pow))]
  = lemma_norm_pow10_inj' n (mant, pow)

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

val neg (a: float) : Pure float
  (requires True)
  (ensures fun b -> mantissa a = -(mantissa b) /\ power a = power b)

val sub (a b: float) : Pure float
  (requires True)
  (ensures fun c -> 
    (let mant_a, pow_a = to_pair a in
    let mant_b, pow_b = to_pair b in
    let pow_min = min pow_a pow_b in
    let a' = mant_a * pow10 (pow_a - pow_min) in
    let b' = mant_b * pow10 (pow_b - pow_min) in
    to_pair c = norm_pair (a' - b', pow_min))
    /\ (c = a `add` (neg b)))

val mul (a b: float) : Pure float
  (requires True)
  (ensures fun c -> to_pair c = norm_pair (mantissa a * mantissa b, power a + power b))

val div (a: float) (b: not_zero) : Pure float
  (requires True)
  (ensures fun c -> c `mul` b = a)

val inv (a: not_zero) : Pure not_zero
  (requires True)
  (ensures fun b -> b = one `div` a)

val eq (a b: float)  : Pure bool (requires True) (ensures fun c -> c = (mantissa (a `sub` b) = 0) /\ c = (a = b))
val gt (a b: float)  : Pure bool (requires True) (ensures fun c -> c = (mantissa (a `sub` b) > 0))
val lt (a b: float)  : Pure bool (requires True) (ensures fun c -> c = (mantissa (a `sub` b) < 0))
val gte (a b: float) : Pure bool (requires True) (ensures fun c -> c = (mantissa (a `sub` b) >= 0))
val lte (a b: float) : Pure bool (requires True) (ensures fun c -> c = (mantissa (a `sub` b) <= 0))

val abs (a: float) : Pure float
  (requires True)
  (ensures fun b -> if a `lt` zero then b = neg a else b = a)

unfold let ( +. ) a b = add a b
unfold let ( -. ) a b = sub a b
unfold let ( ~. ) a   = neg a
unfold let ( *. ) a b = mul a b
unfold let ( /. ) a b = div a b

unfold let (=.) a b = eq a b
unfold let (>.) a b = gt a b
unfold let (<.) a b = lt a b
unfold let (>=.) a b = gte a b
unfold let (<=.) a b = lte a b

let lemma_gt_zero a b  : Lemma (a  >. b <==> a -. b  >. zero) = ()
let lemma_lt_zero a b  : Lemma (a  <. b <==> a -. b  <. zero) = ()
let lemma_gte_zero a b : Lemma (a >=. b <==> a -. b >=. zero) = ()
let lemma_lte_zero a b : Lemma (a <=. b <==> a -. b <=. zero) = ()

let lemma_gt_lt a b : Lemma (a <. b <==> b >. a) = ()
let lemma_gte_lte a b : Lemma (a <=. b <==> b >=. a) = ()

let lemma_commut_add a b : Lemma (a +. b = b +. a) = ()
let lemma_commut_mul a b : Lemma (a *. b = b *. a) = ()

let lemma_add_zero a : Lemma (a +. zero = a) = ()
let lemma_mul_one  a : Lemma (a *. one  = a) = ()
let lemma_mul_zero a : Lemma (a *. zero = zero) = ()
let lemma_div_one  a : Lemma (a /. one = a) = ()

let lemma_sub_neg (a: float) : Lemma (~.a = zero -. a) = ()
let lemma_mul_neg_left (a b: float) : Lemma ((~.a) *. b = ~.(a *. b)) [SMTPat ((~.a) *. b)] =
  let mant_a, pow_a = to_pair a in
  let mant_b, pow_b = to_pair b in
  lemma_norm_neg_inj (mant_a * mant_b, pow_a + pow_b);
  Lemmas.neg_mul_left mant_a mant_b;
  assert (norm_pair ((-mant_a) * mant_b, pow_a + pow_b) = norm_pair (-(mant_a * mant_b), pow_a + pow_b));
  assert (norm_pair (-(mant_a * mant_b), pow_a + pow_b) = norm_pair (mant_a * mant_b, pow_a + pow_b) *< (-1))
let lemma_mul_neg_right (a b: float) : Lemma (a *. (~.b) = ~.(a *. b)) [SMTPat (a *. (~.b))] =
  lemma_commut_mul a (~.b)

let lemma_gt_neg  (a: float) : Lemma (a >.  zero <==> ~.a <. zero) = ()
let lemma_gte_neg (a: float) : Lemma (a >=. zero <==> ~.a <=. zero) = ()
let lemma_lt_neg  (a: float) : Lemma (a <.  zero <==> ~.a >. zero) = ()
let lemma_lte_neg (a: float) : Lemma (a <=. zero <==> ~.a >=. zero) = ()
  
let lemma_additive_add_left a b c : Lemma (a +. b +. c = (a +. b) +. c) = ()
let lemma_additive_add_right a b c : Lemma (a +. b +. c = a +. (b +. c)) [SMTPat (a +. b +. c)] = assume (a +. b +. c = a +. (b +. c))
let lemma_additive_mul_left a b c : Lemma (a *. b *. c = (a *. b) *. c) = ()
let lemma_additive_mul_right a b c : Lemma (a *. b *. c = a *. (b *. c)) [SMTPat (a *. b *. c)] = assume (a *. b *. c = a *. (b *. c))
let lemma_distrib_add a b c : Lemma (a *. (b +. c) = a *. b +. a *. c) [SMTPat (a *. (b +. c))] = assume (a *. (b +. c) = a *. b +. a *. c)
let lemma_distrib_sub a b c : Lemma (a *. (b -. c) = a *. b -. a *. c) [SMTPat (a *. (b -. c))] = ()

let lemma_neg_neg a : Lemma (~.(~.a) = a) = ()
let lemma_add_neg a : Lemma (a -. a = zero) = ()
let lemma_sub_add a b : Lemma (a -. b = a +. ~.b) = ()

let lemma_neg_mul a : Lemma (~.a = (~.one) *. a) = ()
let lemma_distrib_neg a b : Lemma (~.a +. ~.b = ~.(a +. b)) =
  lemma_neg_mul (a +. b);
  assert (~.(a +. b) = ~.one *. (a +. b));
  lemma_distrib_add (~.one) a b;
  lemma_neg_mul a;
  lemma_neg_mul b;
  assert (~.(a +. b) = ~.a +. ~.b)
let lemma_neg_sub a b : Lemma (a -. b = ~.(b -. a)) =
  lemma_sub_add b a;
  lemma_distrib_neg b (~.a);
  assert (~.(b -. a) = ~.b +. ~.(~.a));
  lemma_neg_neg a;
  lemma_commut_add (~.b) a;
  lemma_sub_add a b

// стоит переписать через обобщённую функцию бинарных отношений
let lemma_gt_additive a b c : Lemma (requires a >. b) (ensures a +. c >. b +. c) =
  lemma_gt_zero a b;
  assert (a -. b >. zero);
  lemma_add_zero a;
  lemma_commut_add a zero;
  assert (a -. b = zero +. a -. b);
  lemma_add_neg c;
  assert (a -. b = (c +. ~.c +. a) +. ~.b);
  lemma_additive_add_right c (~.c) a;
  lemma_commut_add (~.c) a;
  lemma_additive_add_right c a (~.c);
  assert (c +. ~.c +. a = c +. a +. ~.c);
  lemma_commut_add c a;
  assert (a -. b = a +. c +. ~.c +. ~.b);
  lemma_distrib_add (a +. c) (~.c) (~.b);
  lemma_distrib_neg c b;
  lemma_sub_add (a +. c) (c +. b);
  lemma_commut_add c b;
  assert (a -. b = (a +. c) -. (b +. c));
  lemma_gt_zero (a +. c) (b +. c)
let lemma_lt_additive a b c : Lemma (requires a <. b) (ensures a +. c <. b +. c) = lemma_gt_additive b a c

let lemma_gt_add a b c : Lemma (requires a >. c /\ b >. c) (ensures a +. b >. c) = ()

let lemma_commut_gt a b c : Lemma (requires a >. b /\ b >. c) (ensures a >. c) =
  lemma_gt_zero a b;
  assert (a -. b >. zero);
  
  assume (a >. c);
  ()

// let lemma_div_inv a : Lemma (a /. a = one) = ()
// let lemma_inv_inv a : Lemma (inv (inv a) = a) = ()

// let lemma_add_perenos a b c : Lemma (requires a +. b = c) (ensures a = c -. b) =
//   assert (a +. b -. b = c -. b);
//   lemma_sub_add (a +. b) b

let lemma_sqr_eq (a b: float) : Lemma
  (requires a *. a =. b *. b)
  (ensures (a =. b) \/ (a =. ~.b))
  =
  assume ((a = b) \/ (a = ~.b))