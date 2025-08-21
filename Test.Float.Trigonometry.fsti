module Test.Float.Trigonometry

open Test.Float

let ( .[] ) x (min, max)  = min <=. x /\ x <=. max
let ( .() ) x (min, max)  = min <.  x /\ x <.  max
let ( <.|> ) x (min, max) = min <=. x /\ x <.  max
let ( <|.> ) x (min, max) = min <.  x /\ x <=. max

let pi : float = of_int 180
let piHalf : float = of_int 90

let lemma_int_in_otr (a: float{a.(~.piHalf, piHalf)}) : Lemma (a.[~.pi, pi]) =
  assert (a >. ~.piHalf);
  assert (piHalf <=. pi);
  lemma_lte_neg piHalf pi;
  assert (~.piHalf >=. ~.pi);
  lemma_commut_gt_gte a (~.piHalf) (~.pi);
  assert (a >. ~.pi);
  assert (a >=. ~.pi);
  lemma_gte_lte (~.pi) a;
  assert (~.pi <=. a);

  assert (piHalf >. a);
  assert (pi >=. piHalf);
  lemma_commut_gte_gt pi piHalf a;
  assert (pi >. a);
  assert (pi >=. a);
  lemma_gte_lte a pi;
  assert (a <=. pi)


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

val lemma_osn_trig_todj a : Lemma ((sin a *. sin a) +. (cos a *. cos a) = one) 

val lemma_cos_add (a b: float) : Lemma (cos (a +. b) = cos a *. cos b -. sin a *. sin b)
val lemma_sin_add (a b: float) : Lemma (sin (a +. b) = sin a *. cos b +. cos a *. sin b)

val lemma_arctg (a: float{a.[~.pi, pi]}) (b: not_zero) : Lemma (arctg (b *. cos a) (b *. sin a) = a)

val lemma_cos_pos (a: float{a.(~.piHalf, piHalf)}) : Lemma (cos a >. zero)