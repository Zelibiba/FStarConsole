module Test.Program

open FStar.IO
open Test.Float

let f x =
  let rec g y = y + 1 in
  g x

#push-options "--warn_error -272"
let main =
  let x = of_pair (2, -1) in
  let y = of_pair (4, 0) in
  let z = x `sub` y in
  let b = z `gt` zero in

  let msg = Printf.ext_sprintf float_extension
    "%Xf * %Xf = %Xf %b\n"
    x y z b in
  print_string msg

#pop-options