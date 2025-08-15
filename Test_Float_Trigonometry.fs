module Test_Float_Trigonometry

open Test_Float

let pi: float = System.Single.Pi
let piHalf: float = System.Single.Pi / 2f

let inline sin (x: float) : float = float.Sin(x / 180f * pi)
let inline cos (x: float) : float = float.Cos(x / 180f * pi)
let inline sinCos (x: float) : struct (float * float) = float.SinCos(x / 180f * pi)
let inline arctg (x: float) (y: float) : float = float.Atan2(y, x) * 180f / pi
let inline hypot (x: float) (y: float) : float = float.Hypot(x, y)