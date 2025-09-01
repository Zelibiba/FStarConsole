module Test_Float_Trigonometry

open Test_Float_Base

let _180: float = 180f
let _90: float = 90f

let inline sin (x: float) : float = float.Sin(x / 180f * float.Pi)
let inline cos (x: float) : float = float.Cos(x / 180f * float.Pi)
// let inline sinCos (x: float) : struct (float * float) = float.SinCos(x / 180f * float.Pi)
let inline arctg (x: float) (y: float) : float = float.Atan2(y, x) * 180f / float.Pi
let inline hypot (x: float) (y: float) : float = float.Hypot(x, y)