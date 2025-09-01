module Test.Program

open FStar.IO
open Test.Float


#push-options "--warn_error -272"
let main =
  let x = of_pair ({base = 2; exp = -1}) in
  let y = of_int 4 in
  let z = x +. y in
  assert (z = of_pair ({base = 42; exp = -1}));
  let c = sin ~._90 in

  let msg = Printf.ext_sprintf float_extension
    "%Xf + %Xf = %Xf\nsin -90 = %Xf\n"
    x y z c in
  print_string msg

#pop-options