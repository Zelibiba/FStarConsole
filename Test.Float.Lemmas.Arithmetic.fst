module Test.Float.Lemmas.Arithmetic

open Test.Float.Pair
open Test.Float.Base
open FStar.Mul

let of_to_inj (x: float) : Lemma (of_pair (to_pair x) = x) [SMTPat (to_pair x)]
  = admit ()
let to_of_inj (p: pair) : Lemma (to_pair (of_pair p) = p) [SMTPat (of_pair p)]
  = admit ()

let commut_add a b : Lemma (a +. b = b +. a) [SMTPat (a +. b)] = ()
let commut_mul a b : Lemma (a *. b = b *. a) [SMTPat (a *. b)] = ()

let add_zero a : Lemma (a +. _0 = a /\ _0 +. a = a) = ()
let sub_zero a : Lemma (a -. _0 = a) = ()
let sub_self a : Lemma (a -. a = _0) = ()
let mul_one  a : Lemma (a *. _1 = a /\ _1 *. a = a) = ()
let mul_zero a : Lemma (a *. _0 = _0 /\ _0 *. a = _0) = ()

let sub_is_add_neg a b : Lemma (a -. b = a +. (~.b)) = 
  let a', b', exp_min = to_shared_exp a b in
  let _a', _b', _exp_min = to_shared_exp a (~.b) in
  assert (_a' = a');
  assert (_b' = -b');
  assert (exp_min = exp_min)
let neg_is_mul_neg_one a : Lemma (~.a = (~._1) *. a /\ ~.a = a *. (~._1)) = ()
let double_neg a : Lemma (~.(~.a) = a) = ()
let neg_is_zero_sub a : Lemma (~.a = _0 -. a) =
  add_zero (~.a);
  sub_is_add_neg _0 (~.a)

let assoc_add_left a b c : 
  Lemma (a +. b +. c = (a +. b) +. c /\
         a +. b -. c = (a +. b) -. c /\
         a -. b +. c = (a -. b) +. c /\
         a -. b -. c = (a -. b) -. c)
  = ()
let assoc_add_right a b c :
  Lemma (a +. b +. c = a +. (b +. c) /\
         a +. b -. c = a +. (b -. c) /\
         a -. b +. c = a +. (c -. b) /\
         a -. b -. c = a -. (b +. c))
  = admit ()
let assoc_mul_left  a b c : Lemma (a *. b *. c = (a *. b) *. c) = ()
let assoc_mul_right a b c : Lemma (a *. b *. c = a *. (b *. c)) = admit ()
let commut_tri_mul a b c : 
  Lemma (a *. b *. c = b *. a *. c /\
         a *. b *. c = c *. a *. b /\
         a *. b *. c = b *. c *. a /\
         a *. b *. c = c *. b *. a /\
         a *. b *. c = a *. c *. b)
  = admit ()

let distrib_add a b c :
  Lemma (a *. (b +. c) = a *. b +. a *. c /\
         a *. (b -. c) = a *. b -. a *. c)
  = admit ()
let distrib_neg_add a b : Lemma (~.(a +. b) = ~.a +. ~.b /\
                                 ~.(a -. b) = ~.a -. ~.b)
  = 
  let aux a b : Lemma (~.(a +. b) = ~.a +. ~.b) =
    neg_is_mul_neg_one (a +. b);
    distrib_add (~._1) a b;
    neg_is_mul_neg_one a;
    neg_is_mul_neg_one b
  in
  aux a b;
  sub_is_add_neg a b;
  aux a (~.b);
  sub_is_add_neg (~.a) (~.b)

let revert_sub a b : Lemma (a -. b = ~.(b -. a)) =
  sub_is_add_neg a b;
  double_neg a;
  distrib_neg_add (~.a) b;
  sub_is_add_neg b a

let distrib_neg_mul a b : Lemma (~.(a *. b) = (~.a) *. b /\
                                 ~.(a *. b) = a *. (~.b)) =
  let aux a b : Lemma (~.(a *. b) = (~.a) *. b) =
    neg_is_mul_neg_one (a *. b); 
    assoc_mul_right ~._1 a b;
    neg_is_mul_neg_one a
  in aux a b; aux b a

let sqr_eq a b : Lemma (requires a *. a = b *. b) (ensures a = b \/ a = ~.b) = admit ()