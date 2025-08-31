module Test.Float.Lemmas.Inequality

open FStar.Mul
open Test.Float.Pair
open Test.Float.Base
open Test.Float.Lemmas.Arithmetic

module Lemmas = FStar.Math.Lemmas
module TC = FStar.Tactics.Typeclasses

let gt_lt   a b : Lemma (a  >. b <==> b  <. a) = revert_sub a b
let gte_lte a b : Lemma (a >=. b <==> b <=. a) = revert_sub a b

let gt_gte a b : Lemma (requires a >. b) (ensures a >=. b) = ()
let lt_lte a b : Lemma (requires a <. b) (ensures a <=. b) = ()

type binop (a: Type) = a -> a -> bool

class binrel (f: binop float) = {
  intop: binop int;
  [@@@TC.no_method]
  props : squash (forall a b. a `f` b <==> (base (a -. b) `intop` 0))
}

instance binrel_gt  : binrel ( >.) = { intop = ( >); props = () }
instance binrel_lt  : binrel ( <.) = { intop = ( <); props = () }
instance binrel_gte : binrel (>=.) = { intop = (>=); props = () }
instance binrel_lte : binrel (<=.) = { intop = (<=); props = () }

let binrel_neg f {| binrel f |} a b : Lemma (f a b <==> f (~.b) (~.a)) =
  distrib_neg_add b a;
  revert_sub a b

let gt_neg  a b : Lemma ((a  >. b <==> ~.b  >. ~.a) /\ (a  >. b <==> ~.a  <. ~.b)) = binrel_neg ( >.) a b; gt_lt   ~.b ~.a
let lt_neg  a b : Lemma ((a  <. b <==> ~.b  <. ~.a) /\ (a  <. b <==> ~.a  >. ~.b)) = binrel_neg ( <.) a b; gt_lt   ~.a ~.b
let gte_neg a b : Lemma ((a >=. b <==> ~.b >=. ~.a) /\ (a >=. b <==> ~.a <=. ~.b)) = binrel_neg (>=.) a b; gte_lte ~.b ~.a
let lte_neg a b : Lemma ((a <=. b <==> ~.b <=. ~.a) /\ (a <=. b <==> ~.a >=. ~.b)) = binrel_neg (<=.) a b; gte_lte ~.a ~.b


let binrel_additive f {| binrel f |} a b c : Lemma
  ((a `f` b <==> (a +. c) `f` (b +. c)) /\
   (a `f` b <==> (a -. c) `f` (b -. c)))
  =
  let aux f {| binrel f |} a b c : Lemma (a `f` b <==> (a +. c) `f` (b +. c)) =
    commut_add b c;
    assoc_add_right (a +. c) c b;
    assoc_add_right a c c;
    assert ((a +. c) -. (b +. c) = a +. (c -. c) -. b);
    sub_self c;
    add_zero a;
    assert ((a +. c) -. (b +. c) = a -. b)
  in
  aux f a b c;
  sub_is_add_neg a c;
  sub_is_add_neg b c;
  aux f a b (~.c)

let binrel_to_sub f {| binrel f |} a b : Lemma (a `f` b <==> (a -. b) `f` zero) =
  binrel_additive f a b b;
  sub_self b

let distrib_gt_zero a b : Lemma (requires a >. zero /\ b >=. zero) (ensures a +. b >. zero) =
  let a', b', exp_min = to_shared_exp a b in
  sub_zero a;
  sub_zero b;
  Lemmas.lemma_mult_lt_right (pow10 (exp a - exp_min)) 0 (base a);
  Lemmas.lemma_mult_le_right (pow10 (exp b - exp_min)) 0 (base b);
  assert (a' > 0 /\ b' >= 0);
  assert (a' + b' > 0);

  let c = a +. b in
  normalized_save_sign (to_pair c) { base = a' + b'; exp = exp_min };
  assert (base c > 0)

let distrib_lt_zero a b : Lemma (requires a <. zero /\ b <=. zero) (ensures a +. b <. zero) =
  lt_neg a zero;
  lte_neg b zero;
  assert (~.a >. zero /\ ~.b >=. zero);
  distrib_gt_zero (~.a) (~.b);
  distrib_neg_add a b;
  assert (~.(a +. b) >. zero);
  lt_neg (a +. b) zero

class weak_binrel (f: binop float) = {
  op: binop float;
  binrel_f : binrel f;
  binrel_w: binrel op;
  [@@@TC.no_method]
  props : squash (
    (forall a b. a `op` b <==> (a `f` b \/ a =. b)) /\
    (forall (a: float{a `f` zero}) (b: float{b `op` zero}). (a +. b) `f` zero))
}

instance weak_gt : weak_binrel (>.) = {
  op = (>=.);
  binrel_f = binrel_gt;
  binrel_w = binrel_gte;
  props = introduce forall (a: float{a >. zero}) (b: float{b >=. zero}). (a +. b) >. zero with distrib_gt_zero a b
}
instance weak_lt : weak_binrel (<.) = {
  op = (<=.);
  binrel_f = binrel_lt;
  binrel_w = binrel_lte;
  props = introduce forall (a: float{a <. zero}) (b: float{b <=. zero}). (a +. b) <. zero with distrib_lt_zero a b
}

let binrel_commut f {| wb: weak_binrel f |} a b c : Lemma (requires a `f` b /\ b `wb.op` c) (ensures a `f` c) =
  add_zero a;
  sub_self (~.b);
  sub_is_add_neg (~.b) (~.b);
  assert (a -. c = a +. (~.b +. b) -. c);
  assoc_add_right a (~.b) b;
  assoc_add_right (a +. ~.b) b c;
  sub_is_add_neg a b;
  assert (a -. c = (a -. b) +. (b -. c));
  binrel_to_sub f #wb.binrel_f a b;
  binrel_to_sub wb.op #wb.binrel_w b c;
  binrel_to_sub f #wb.binrel_f a c

let commut_gt_gte a b c : Lemma (requires a >. b /\ b >=. c) (ensures a >. c) = binrel_commut (>.) a b c
let commut_lt_lte a b c : Lemma (requires a <. b /\ b <=. c) (ensures a <. c) = binrel_commut (<.) a b c