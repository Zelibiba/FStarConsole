module Test.Float.Trigonometry

include Test.Float.Ranges
open Test.Float.Lemmas.Arithmetic
open Test.Float.Lemmas.Inequality


val _180 : (x: float{x = of_int 180})
val _90  : (x: float{x = of_int 90})

val sin : float -> (r: float{r.[~._1, _1]})
val cos : float -> (r: float{r.[~._1, _1]})
val arctg (x y: float) : (r: float{r.[~._180, _180]})
val hypot2 (x y: float) : Pure float (requires True) (ensures fun h ->
  sqr_gt_0 x; sqr_gt_0 y;
  distrib_gte_0 (sqr x) (sqr y);
  (sqr x +. sqr y) >=. _0 /\ h = sqrt (sqr x +. sqr y))
val hypot3 (x y z: float) : Pure float (requires True) (ensures fun h ->
  sqr_gt_0 x; sqr_gt_0 y; sqr_gt_0 z;
  distrib_gte_0 (sqr x) (sqr y);
  distrib_gte_0 (sqr x +. sqr y) (sqr z);
  (sqr x +. sqr y +. sqr z) >=. _0 /\ h = sqrt (sqr x +. sqr y +. sqr z))


val lemma_sin_odd  (a: float) : Lemma (sin a = ~.(sin ~.a))
val lemma_cos_even (a: float) : Lemma (cos a = cos ~.a)
val lemma_arctg_x_pos (x y: float) : Lemma (requires x >=. _0) (ensures ~._90 <. _90 /\ (arctg x y).(~._90, _90))

val lemma_sin_0 (a: float{a = _0}) : Lemma (sin a = _0)
val lemma_cos_0 (a: float{a = _0}) : Lemma (cos a = _1)
let lemma_sin_cos_0 (a: float{a = _0}) : Lemma (sin a = _0 /\ cos a = _1) = lemma_sin_0 a; lemma_cos_0 a

val lemma_sin_90 (a: float{a = of_int 90}) : Lemma (sin a = _1)
val lemma_cos_90 (a: float{a = of_int 90}) : Lemma (cos a = _0)
let lemma_sin_cos_90 (a: float{a = of_int 90}) : Lemma (sin a = _1 /\ cos a = _0) = lemma_sin_90 a; lemma_cos_90 a

val lemma_osn_trig_todj (a: float) : Lemma (sqr (sin a) +. sqr (cos a) = _1)

val lemma_cos_add (a b: float) : Lemma (cos (a +. b) = cos a *. cos b -. sin a *. sin b)
val lemma_sin_add (a b: float) : Lemma (sin (a +. b) = sin a *. cos b +. cos a *. sin b)

val lemma_arctg (a: float{a.[~._180, _180]}) (b: not_0) : Lemma (arctg (cos a *. b) (sin a *. b) = a)

val lemma_cos_pos (a: float{a.(~._90, _90)}) : Lemma (cos a >. _0)

let simplification_sqr_cos_sin a b : Lemma (sqr (b *. cos a) +. sqr (b *. sin a) = sqr b) =
  let cos = cos a in
  let sin = sin a in
  let bb = sqr (b *. cos) +. sqr (b *. sin) in

  assoc_mul_right (b *. cos) b cos;
  commut_tri_mul b cos b;
  assoc_mul_right (b *. b) cos cos;
  assoc_mul_right (b *. sin) b sin;
  commut_tri_mul b sin b;
  assoc_mul_right (b *. b) sin sin;
  assert (bb = (b *. b) *. (cos *. cos) +. (b *. b) *. (sin *. sin));
  distrib_add (sqr b) (sqr cos) (sqr sin);
  lemma_osn_trig_todj a;
  mul_one (sqr b)