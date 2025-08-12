module Test_Float
open System.Numerics

type float = System.Single


let to_string (x: float) : string = x.ToString()

let to_pair (x: float) : BigInteger * BigInteger =
    Seq.initInfinite (fun exp ->
        let x' = x * single (pown 10 exp)
        exp, x')
    |> Seq.pick (fun (exp, value) ->
        if System.Single.IsInteger value
        then Some (BigInteger value, BigInteger -exp)
        else None)
let of_pair (mant: BigInteger, exp: BigInteger) : float = System.Single.Parse $"{mant}e{exp}"
let of_int (x: BigInteger) : float = single x

let zero : float = 0f
let one : float = 1f

let add (a: float) (b: float) : float = a + b
let sub (a: float) (b: float) : float = a - b
let neg (a: float) : float = -a
let mul (a: float) (b: float) : float = a * b
let div (a: float) (b: float) : float = a / b

let gt (a: float) (b: float) = a > b
let lt (a: float) (b: float) = a < b
let gte (a: float) (b: float) = a >= b
let lte (a: float) (b: float) = a <= b

let abs (a: float) : float = abs a

let pi: float = System.Single.Pi
let piHalf: float = System.Single.Pi / 2f

let inline sin (x: float) : float = float.Sin(x / 180f * pi)
let inline cos (x: float) : float = float.Cos(x / 180f * pi)
let inline sinCos (x: float) : struct (float * float) = float.SinCos(x / 180f * pi)
let inline arctg (x: float) (y: float) : float = float.Atan2(y, x) * 180f / pi
let inline hypot (x: float) (y: float) : float = float.Hypot(x, y)