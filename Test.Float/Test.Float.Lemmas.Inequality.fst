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

class binrel = {
  op : binop float;
  intop: binop int;
  [@@@TC.no_method]
  props : squash (forall a b. a `op` b <==> (base (a -. b) `intop` 0))
}

let (<?>) {| binrel |} a b = op a b

instance b_gt  : binrel = { op = ( >.); intop = ( >); props = () }
instance b_lt  : binrel = { op = ( <.); intop = ( <); props = () }
instance b_gte : binrel = { op = (>=.); intop = (>=); props = () }
instance b_lte : binrel = { op = (<=.); intop = (<=); props = () }

let binrel_neg {| binrel |} a b : Lemma (a <?> b <==> (~.b) <?> (~.a)) =
  distrib_neg_add b a;
  revert_sub a b

let gt_neg  a b : Lemma ((a  >. b <==> ~.b  >. ~.a) /\ (a  >. b <==> ~.a  <. ~.b)) = binrel_neg #b_gt  a b; gt_lt   ~.b ~.a
let lt_neg  a b : Lemma ((a  <. b <==> ~.b  <. ~.a) /\ (a  <. b <==> ~.a  >. ~.b)) = binrel_neg #b_lt  a b; gt_lt   ~.a ~.b
let gte_neg a b : Lemma ((a >=. b <==> ~.b >=. ~.a) /\ (a >=. b <==> ~.a <=. ~.b)) = binrel_neg #b_gte a b; gte_lte ~.b ~.a
let lte_neg a b : Lemma ((a <=. b <==> ~.b <=. ~.a) /\ (a <=. b <==> ~.a >=. ~.b)) = binrel_neg #b_lte a b; gte_lte ~.a ~.b


let binrel_additive {| binrel |} a b c : Lemma
  ((a <?> b <==> (a +. c) <?> (b +. c)) /\
   (a <?> b <==> (a -. c) <?> (b -. c)))
  =
  let aux {| binrel |} a b c : Lemma (a <?> b <==> (a +. c) <?> (b +. c)) =
    commut_add b c;
    assoc_add_right (a +. c) c b;
    assoc_add_right a c c;
    assert ((a +. c) -. (b +. c) = a +. (c -. c) -. b);
    sub_self c;
    add_zero a;
    assert ((a +. c) -. (b +. c) = a -. b)
  in
  aux a b c;
  sub_is_add_neg a c;
  sub_is_add_neg b c;
  aux a b (~.c)

let binrel_to_sub {| binrel |} a b : Lemma (a <?> b <==> (a -. b) <?> zero) =
  binrel_additive a b b;
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

class weak_pair = {
  strong : binrel;
  weak: binrel;
  [@@@TC.no_method]
  props : squash (
    (forall a b. weak.op a b <==> (strong.op a b \/ a =. b)) /\
    (forall (a: float{strong.op a zero}) (b: float{weak.op b zero}). strong.op (a +. b) zero)
  )
}

let (<??>) {| weak_pair |} a b = strong.op a b
let (<?=>) {| weak_pair |} a b = weak.op a b

instance weak_gt : weak_pair = {
  strong = b_gt;
  weak = b_gte;
  props = introduce forall (a: float{a `b_gt.op` zero}) (b: float{b `b_gte.op` zero}). (a +. b) `b_gt.op` zero with distrib_gt_zero a b
}
instance weak_lt : weak_pair = {
  strong = b_lt;
  weak = b_lte;
  props = introduce forall (a: float{a `b_lt.op` zero}) (b: float{b `b_lte.op` zero}). (a +. b) `b_lt.op` zero with distrib_lt_zero a b
}

let binrel_commut {| wp: weak_pair |} a b c : Lemma (requires a <??> b /\ b <?=> c) (ensures a <??> c) =
  add_zero a;
  sub_self (~.b);
  sub_is_add_neg (~.b) (~.b);
  assert (a -. c = a +. (~.b +. b) -. c);
  assoc_add_right a (~.b) b;
  assoc_add_right (a +. ~.b) b c;
  sub_is_add_neg a b;
  assert (a -. c = (a -. b) +. (b -. c));
  binrel_to_sub #wp.strong a b;
  binrel_to_sub #wp.weak b c;
  binrel_to_sub #wp.strong a c

let commut_gt_gte a b c : Lemma (requires a >. b /\ b >=. c) (ensures a >. c) = binrel_commut #weak_gt a b c
let commut_lt_lte a b c : Lemma (requires a <. b /\ b <=. c) (ensures a <. c) = binrel_commut #weak_lt a b c