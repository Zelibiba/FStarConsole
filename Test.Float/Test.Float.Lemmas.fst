module Test.Float.Lemmas

open Test.Float.Pair
open Test.Float.Base
open FStar.Mul

let of_to_inj (x: float) : Lemma (of_pair (to_pair x) = x) [SMTPat (to_pair x)]
  = admit ()
let to_of_inj (p: pair) : Lemma (to_pair (of_pair p) = p) [SMTPat (of_pair p)]
  = admit ()

let commut_add a b : Lemma (a +. b = b +. a) = ()
let commut_mul a b : Lemma (a *. b = b *. a) = ()

let add_zero a : Lemma (a +. zero = a /\ zero +. a = a) = ()
let sub_zero a : Lemma (a -. zero = a) = ()
let sub_self a : Lemma (a -. a = zero) = ()
let mul_one  a : Lemma (a *. one = a /\ one *. a = a) = ()
let mul_zero a : Lemma (a *. zero = zero /\ zero *. a = zero) = ()

let sub_is_add_neg a b : Lemma (a -. b = a +. (~.b)) = 
  let a', b', exp_min = to_shared_exp a b in
  let _a', _b', _exp_min = to_shared_exp a (~.b) in
  assert (_a' = a');
  assert (_b' = -b');
  assert (exp_min = exp_min)
let neg_is_mul_neg_one a : Lemma (~.a = (~.one) *. a /\ ~.a = a *. (~.one)) = ()
let double_neg a : Lemma (~.(~.a) = a) = ()
let neg_is_zero_sub a : Lemma (~.a = zero -. a) =
  add_zero (~.a);
  sub_is_add_neg zero (~.a)

let additive_add_left a b c : 
  Lemma (a +. b +. c = (a +. b) +. c /\
         a +. b -. c = (a +. b) -. c /\
         a -. b +. c = (a -. b) +. c /\
         a -. b -. c = (a -. b) -. c)
  = ()
let additive_add_right a b c :
  Lemma (a +. b +. c = a +. (b +. c) /\
         a +. b -. c = a +. (b -. c) /\
         a -. b +. c = a +. (c -. b) /\
         a -. b -. c = a -. (b +. c))
  = admit ()
let additive_mul_left  a b c : Lemma (a *. b *. c = (a *. b) *. c) = ()
let additive_mul_right a b c : Lemma (a *. b *. c = a *. (b *. c)) = admit ()

let distrib_add a b c :
  Lemma (a *. (b +. c) = a *. b +. a *. c /\
         a *. (b -. c) = a *. b -. a *. c)
  = admit ()
let distrib_neg a b : Lemma (~.(a +. b) = ~.a +. ~.b) =
  neg_is_mul_neg_one (a +. b);
  distrib_add (~.one) a b;
  neg_is_mul_neg_one a;
  neg_is_mul_neg_one b

let revert_sub a b : Lemma (a -. b = ~.(b -. a)) =
  sub_is_add_neg a b;
  double_neg a;
  distrib_neg (~.a) b;
  sub_is_add_neg b a