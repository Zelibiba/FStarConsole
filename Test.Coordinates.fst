module Test.Coordinates

open Test.Float
open Test.Float.Trigonometry

type azType = (az: float{az <.|> (~.pi, pi)})
type psk : eqtype =
  {
    az: azType;
    um: (um: float{um.(~.piHalf, piHalf)})
  }
type cart : eqtype = { x: float; y: float; z: float}

let psk2cart (coord: psk) = 
  let x = cos coord.az *. cos coord.um in
  let y = sin coord.az *. cos coord.um in
  let z = sin coord.um in
  { x = x; y = y; z = z }

let cart2psk (coord: cart) =
  let az = arctg coord.x coord.y in
  let um = arctg (hypot coord.x coord.y) coord.z in
  let az' = 
    match az =. pi with
    | true -> ~.pi
    | _ -> az
  in { az = az'; um = um }

let lemma_hypot_cos (h: float) (cos: float{cos >. zero}) : Lemma 
  (requires h *. h = cos *. cos /\ h >=. zero)
  (ensures h = cos)
  =
  lemma_sqr_eq h cos;
  lemma_lte_neg cos zero;
  assert (~.cos >=. zero <==> cos <=. zero);
  assert (h = cos)

let lemma_one_zero () : Lemma (one <> zero) = ()

let lemma_psk2cart (p: psk) : Lemma (cart2psk (psk2cart p) = p) [SMTPat (psk2cart p)] =
  let c = psk2cart p in
  let p' = cart2psk c in
  
  lemma_cos_pos p.um;
  lemma_arctg p.az (cos p.um);
  assert (p'.az = p.az);

  let h = hypot c.x c.y in
  assert (h *. h = cos p.az *. cos p.az *. cos p.um *. cos p.um +. sin p.az *. sin p.az *. cos p.um *. cos p.um);
  assert (h *. h = cos p.az *. cos p.az *. (cos p.um *. cos p.um) +. sin p.az *. sin p.az *. (cos p.um *. cos p.um));
  lemma_distrib_add (cos p.um *. cos p.um) (cos p.az *. cos p.az) (sin p.az *. sin p.az);
  assert (h *. h = (cos p.um *. cos p.um) *. ((cos p.az *. cos p.az) +. (sin p.az *. sin p.az)));
  lemma_commut_add (cos p.az *. cos p.az) (sin p.az *. sin p.az);
  lemma_osn_trig_todj p.az;
  assert (h *. h = one *. cos p.um *. cos p.um);
  lemma_mul_one (cos p.um);
  assert (h *. h = cos p.um *. cos p.um);
  lemma_hypot_cos h (cos p.um);
  assert (h = cos p.um);
  lemma_int_in_otr p.um;
  assert (p.um.[~.pi, pi]);
  lemma_one_zero ();
  lemma_mul_one (cos p.um);
  lemma_mul_one (sin p.um);
  lemma_arctg p.um one;
  assert (p'.um = p.um)