module Test.Coordinates

open Test.Float

type azType = (az: float{az <.|> (~.pi, pi)})
type psk : eqtype =
  {
    az: (az: float{az <.|> (~.pi, pi)});
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
  let az' = if az = pi then ~.pi else az in
  { az = az'; um = um }

// let lemma_psk2cart (p: psk) : Lemma (cart2psk (psk2cart p) = p) [SMTPat (psk2cart p)] =
//   ()