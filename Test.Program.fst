module Test.Program

open FStar.IO
open Test.Float


#push-options "--warn_error -272"
let main =
  let x = of_pair (2, -1) in
  let y = of_pair (4, 0) in
  let z = x +. y in
  assert (z = of_pair (42, -1));

  let msg = Printf.ext_sprintf float_extension
    "%Xf * %Xf = %Xf\n"
    x y z in
  print_string msg

#pop-options