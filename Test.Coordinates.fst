module Test.Coordinates

open Test.Float

type azType = (az: float{az |-> (~._180 <.|> _180)})
type psk : eqtype =
  {
    az: azType;
    um: (um: float{um.(~._90, _90)})
  }
type cart : eqtype = { x: float; y: float; z: float}

let psk2cart (coord: psk) = 
  let x = cos coord.az *. cos coord.um in
  let y = sin coord.az *. cos coord.um in
  let z = sin coord.um in
  { x = x; y = y; z = z }

private let wrap (a: float) : Pure float (requires a.[~._180, _180]) 
  (ensures fun b -> b |-> (~._180 <.|> _180) /\ (a |-> (~._180 <.|> _180) ==> a = b))
  =
  match a = _180 with
  | true -> ~._180
  | false -> a

let cart2psk (coord: cart) =
  let az = arctg coord.x coord.y in
  let um = arctg (hypot coord.x coord.y) coord.z in
  lemma_arctg_x_pos (hypot coord.x coord.y) coord.z;
  assert (um.(~._90, _90));
  
  let az' = wrap az in
  { az = az'; um = um }

let lemma_psk2cart (p: psk) : Lemma (cart2psk (psk2cart p) = p) [SMTPat (psk2cart p)] =
  let lemma_range x : Lemma (requires x.(~._90, _90)) (ensures x.[~._180, _180]) =
    assert (_90 <=. _180);
    lte_neg _90 _180;
    assert (~._90 >=. ~._180);
    point_inj x (~._90 <|> _90) (~._180 <.|.> _180)
  in
  let lemma_hypot_cos (h az um: float) : Lemma
    (requires h = hypot (cos az *. cos um) (sin az *. cos um) /\ um.(~._90, _90))
    (ensures h = cos um)
    =
    let cos_az = cos az in
    let sin_az = sin az in
    let cos_um = cos um in
    lemma_cos_pos um;

    assert (h *. h = (cos_az *. cos_um) *. (cos_az *. cos_um) +. (sin_az *. cos_um) *. (sin_az *. cos_um));
    assert (h *. h = (cos_az *. cos_um) *. (cos_um *. cos_az) +. (sin_az *. cos_um) *. (cos_um *. sin_az));
    assoc_mul_right (cos_az *. cos_um) cos_um cos_az;
    commut_tri_mul cos_az cos_um cos_um;
    assoc_mul_right (cos_um *. cos_um) cos_az cos_az;

    assoc_mul_right (sin_az *. cos_um) cos_um sin_az;
    commut_tri_mul sin_az cos_um cos_um;
    assoc_mul_right (cos_um *. cos_um) sin_az sin_az;
    assert (h *. h = (cos_um *. cos_um) *. (cos_az *. cos_az) +. (cos_um *. cos_um) *. (sin_az *. sin_az));
    distrib_add (cos_um *. cos_um) (cos_az *. cos_az) (sin_az *. sin_az);
    lemma_osn_trig_todj az;
    mul_one (cos_um *. cos_um);
    assert (h *. h = cos_um *. cos_um);
    lemma_hypot_pos h cos_um
  in
  let lemma_one () : Lemma (_1 <> _0) = ()
  in
  let c = psk2cart p in
  let p' = cart2psk c in
  
  lemma_cos_pos p.um;
  lemma_arctg p.az (cos p.um);
  assert (p'.az = p.az);

  let h = hypot c.x c.y in
  lemma_hypot_cos h p.az p.um;

  mul_one (cos p.um);
  mul_one (sin p.um);
  assert (p'.um = arctg (cos p.um) (sin p.um));
  lemma_range p.um;
  assert (p.um.[~._180, _180]);
  lemma_one ();
  lemma_arctg p.um _1;
  assert (p'.um = p.um)