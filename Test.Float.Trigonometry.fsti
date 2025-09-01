module Test.Float.Trigonometry

include Test.Float.Ranges
open Test.Float.Lemmas.Arithmetic
open Test.Float.Lemmas.Inequality


val _180 : (x: float{x = of_int 180})
val _90 : (x: float{x = of_int 90})

val sin : float -> (r: float{r.[~.one, one]})
val cos : float -> (r: float{r.[~.one, one]})
val arctg (x y: float) : (r: float{r.[~._180, _180]})
val hypot (x y: float) : (r: float{r *. r = x *. x +. y *. y /\ r >=. zero})

val sin_odd  (a: float) : Lemma (sin a = ~.(sin ~.a))
val cos_even (a: float) : Lemma (cos a = cos ~.a)
val arctg_x_pos (x y: float) : Lemma (requires x >=. zero) (ensures (arctg x y).(~._90, _90)) [SMTPat (arctg x y)]

val sin_0 (a: float{a = zero}) : Lemma (sin a = zero)
val cos_0 (a: float{a = zero}) : Lemma (cos a = one)
let sin_cos_0 (a: float{a = zero}) : Lemma (sin a = zero /\ cos a = one) = sin_0 a; cos_0 a

val sin_90 (a: float{a = of_int 90}) : Lemma (sin a = one)
val cos_90 (a: float{a = of_int 90}) : Lemma (cos a = zero)
let sin_cos_90 (a: float{a = of_int 90}) : Lemma (sin a = one /\ cos a = zero) = sin_90 a; cos_90 a

val osn_trig_todj (a: float) : Lemma ((sin a *. sin a) +. (cos a *. cos a) = one) 

val cos_add (a b: float) : Lemma (cos (a +. b) = cos a *. cos b -. sin a *. sin b)
val sin_add (a b: float) : Lemma (sin (a +. b) = sin a *. cos b +. cos a *. sin b)

val arctg_of_cos_sin (a: float{a.[~._180, _180]}) (b: notzero) : Lemma (arctg (b *. cos a) (b *. sin a) = a)

val cos_pos (a: float{a.(~._90, _90)}) : Lemma (cos a >. zero)