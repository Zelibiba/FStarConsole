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
let inv (a: float) : float = 1f / a

let gt (a: float) (b: float) = a > b
let lt (a: float) (b: float) = a < b
let gte (a: float) (b: float) = a >= b
let lte (a: float) (b: float) = a <= b

let abs (a: float) : float = abs a