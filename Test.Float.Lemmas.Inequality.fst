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

let neg_binrel {| binrel |} a b : Lemma (a <?> b <==> (~.b) <?> (~.a)) =
  distrib_neg_add b a;
  revert_sub a b

let gt_neg  a b : Lemma ((a  >. b <==> ~.b  >. ~.a) /\ (a  >. b <==> ~.a  <. ~.b)) = neg_binrel #b_gt  a b; gt_lt   ~.b ~.a
let lt_neg  a b : Lemma ((a  <. b <==> ~.b  <. ~.a) /\ (a  <. b <==> ~.a  >. ~.b)) = neg_binrel #b_lt  a b; gt_lt   ~.a ~.b
let gte_neg a b : Lemma ((a >=. b <==> ~.b >=. ~.a) /\ (a >=. b <==> ~.a <=. ~.b)) = neg_binrel #b_gte a b; gte_lte ~.b ~.a
let lte_neg a b : Lemma ((a <=. b <==> ~.b <=. ~.a) /\ (a <=. b <==> ~.a >=. ~.b)) = neg_binrel #b_lte a b; gte_lte ~.a ~.b


let additive_binrel {| binrel |} a b c : Lemma
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

let binrel_to_sub {| binrel |} a b : Lemma (a <?> b <==> (a -. b) <?> _0) =
  additive_binrel a b b;
  sub_self b

let distrib_gt_zero a b : Lemma (requires a >. _0 /\ b >=. _0) (ensures a +. b >. _0) =
  let a', b', exp_min = to_shared_exp a b in
  sub_zero a;
  sub_zero b;
  Lemmas.lemma_mult_lt_right (pow10 (exp a - exp_min)) 0 (base a);
  Lemmas.lemma_mult_le_right (pow10 (exp b - exp_min)) 0 (base b);
  assert (a' > 0 /\ b' >= 0);
  assert (a' + b' > 0);

  let c = a +. b in
  normalized_save_sign (to_pair c) ({ base = a' + b'; exp = exp_min });
  assert (base c > 0)

let distrib_lt_zero a b : Lemma (requires a <. _0 /\ b <=. _0) (ensures a +. b <. _0) =
  lt_neg a _0;
  lte_neg b _0;
  assert (~.a >. _0 /\ ~.b >=. _0);
  distrib_gt_zero (~.a) (~.b);
  distrib_neg_add a b;
  assert (~.(a +. b) >. _0);
  lt_neg (a +. b) _0

class binrel_pair = {
  strong : binrel;
  weak: binrel;
  [@@@TC.no_method]
  props : squash (
    (forall a b. weak.op a b <==> (strong.op a b \/ a =. b)) /\
    (forall (a: float{strong.op a _0}) (b: float{weak.op b _0}). strong.op (a +. b) _0)
  )
}

let (<??>) {| binrel_pair |} a b = strong.op a b
let (<?=>) {| binrel_pair |} a b = weak.op a b

instance weak_gt : binrel_pair = {
  strong = b_gt;
  weak = b_gte;
  props = introduce forall (a: float{a `b_gt.op` _0}) (b: float{b `b_gte.op` _0}). (a +. b) `b_gt.op` _0 with distrib_gt_zero a b
}
instance weak_lt : binrel_pair = {
  strong = b_lt;
  weak = b_lte;
  props = introduce forall (a: float{a `b_lt.op` _0}) (b: float{b `b_lte.op` _0}). (a +. b) `b_lt.op` _0 with distrib_lt_zero a b
}

let weak_to_strong {| binrel_pair |} a b : Lemma (requires a <?=> b /\ ~(a =. b)) (ensures a <??> b) = ()
let gte_to_gt a b : Lemma (requires a >=. b /\ ~(a =. b)) (ensures a >. b) = ()
let lte_to_lt a b : Lemma (requires a <=. b /\ ~(a =. b)) (ensures a <. b) = ()

let binrel_distrib_weak_0 {| binrel_pair |} a b : Lemma (requires a <?=> _0 /\ b <?=> _0) (ensures (a +. b) <?=> _0) = ()
let distrib_gte_0 a b : Lemma (requires a >=. _0 /\ b >=. _0) (ensures (a +. b) >=. _0) = binrel_distrib_weak_0 #weak_gt a b
let distrib_lte_0 a b : Lemma (requires a <=. _0 /\ b <=. _0) (ensures (a +. b) <=. _0) = binrel_distrib_weak_0 #weak_lt a b

let commut_binrel_left {| bp: binrel_pair |} a b c : Lemma (requires a <??> b /\ b <?=> c) (ensures a <??> c) =
  add_zero a;
  sub_self (~.b);
  sub_is_add_neg (~.b) (~.b);
  assert (a -. c = a +. (~.b +. b) -. c);
  assoc_add_right a (~.b) b;
  assoc_add_right (a +. ~.b) b c;
  sub_is_add_neg a b;
  assert (a -. c = (a -. b) +. (b -. c));
  binrel_to_sub #bp.strong a b;
  binrel_to_sub #bp.weak b c;
  binrel_to_sub #bp.strong a c

let commut_gt_gte a b c : Lemma (requires a >. b /\ b >=. c) (ensures a >. c) = commut_binrel_left #weak_gt a b c
let commut_lt_lte a b c : Lemma (requires a <. b /\ b <=. c) (ensures a <. c) = commut_binrel_left #weak_lt a b c

let commut_binrel_right {| bp: binrel_pair |} a b c : Lemma (requires a <?=> b /\ b <??> c) (ensures a <??> c) =
  neg_binrel #bp.weak a b;
  neg_binrel #bp.strong b c;
  commut_binrel_left (~.c) (~.b) (~.a);
  neg_binrel #bp.strong a c

let commut_gte_gt a b c : Lemma (requires a >=. b /\ b >. c) (ensures a >. c) = commut_binrel_right #weak_gt a b c
let commut_lte_lt a b c : Lemma (requires a <=. b /\ b <. c) (ensures a <. c) = commut_binrel_right #weak_lt a b c

let commut_binrel_weak {| binrel_pair |} a b c : Lemma (requires a <?=> b /\ b <?=> c) (ensures a <?=> c) =
  match a =. b with
  | true -> ()
  | false -> commut_binrel_left a b c

let commut_gte_gte a b c : Lemma (requires a >=. b /\ b >=. c) (ensures a >=. c) = commut_binrel_weak #weak_gt a b c
let commut_lte_lte a b c : Lemma (requires a <=. b /\ b <=. c) (ensures a <=. c) = commut_binrel_weak #weak_lt a b c

let sqr_gt_0' a : Lemma (requires a <> _0) (ensures a *. a >. _0) =
  assert (a <> _0);
  let p' = { base = base a * base a; exp = exp a + exp a } in
  normalized_save_sign (norm_pair p') p';
  assert (base (a *. a) > 0)
  
let sqr_gt_0 a : Lemma (a *. a >=. _0) [SMTPat (a *. a)] =
  match a =. _0 with
  | true -> sub_zero a; assert (base a = 0); assert (a *. a = _0)
  | false -> assert (a <> _0); sqr_gt_0' a

let sqr_eq a b : Lemma (requires a = sqrt (b *. b))
  (ensures (b >=. _0 <==> a = b) /\ (b <=. _0 <==> a = ~.b)) = admit ()

let is_sqrt s a : Lemma (requires a >=. _0 /\ s >=. _0 /\ s *. s = a) (ensures s = sqrt a) = admit ()