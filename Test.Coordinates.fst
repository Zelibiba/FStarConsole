module Test.Coordinates

open Test.Float

type azType = (az: float{az |-> (~._180 <.|> _180)})
type psk : eqtype =
  {
    az: azType;
    um: (um: float{um.(~._90, _90)});
  }
type cart' : eqtype = { x: float; y: float; z: float }
let radius (coord: cart') = hypot3 coord.x coord.y coord.z
type cart = coord: cart'{radius coord = _1}


let psk2cart (coord: psk) : cart = 
  let x = cos coord.az *. cos coord.um in
  let y = sin coord.az *. cos coord.um in
  let z = sin coord.um in
  let coord' = { x = x; y = y; z = z } in
  
  let _1_gt_0 () : Lemma (_1 >. _0) = () in
  simplification_sqr_cos_sin coord.az (cos coord.um);
  lemma_osn_trig_todj coord.um;
  assert (sqr x +. sqr y +. sqr z = _1);
  _1_gt_0 ();
  _1 `is_sqrt` _1;
  assert (radius coord' = _1);

  coord'

private let wrap (a: float) : Pure float (requires a.[~._180, _180]) 
  (ensures fun b -> b |-> (~._180 <.|> _180) /\ (a |-> (~._180 <.|> _180) ==> a = b))
  =
  match a = _180 with
  | true -> ~._180
  | false -> a

let cart2psk (coord: cart) =
  let az = arctg coord.x coord.y in
  let um = arctg (hypot2 coord.x coord.y) coord.z in
  lemma_arctg_x_pos (hypot2 coord.x coord.y) coord.z;
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
  let lemma_one () : Lemma (_1 <> _0) = ()
  in
  let c = psk2cart p in
  let p' = cart2psk c in
  
  lemma_cos_pos p.um;
  lemma_arctg p.az (cos p.um);
  assert (p'.az = p.az);

  let h = hypot2 c.x c.y in
  simplification_sqr_cos_sin p.az (cos p.um);
  assert (h = sqrt (sqr (cos p.um)));
  lemma_cos_pos p.um;
  sqr_eq h (cos p.um);
  assert (h = cos p.um);
  mul_one (cos p.um);
  mul_one (sin p.um);
  assert (p'.um = arctg (cos p.um) (sin p.um));
  lemma_range p.um;
  assert (p.um.[~._180, _180]);
  lemma_one ();
  lemma_arctg p.um _1;
  assert (p'.um = p.um)