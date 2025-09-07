module Test_Float_Base
open System.Numerics
open Test_Float_Pair

type float = System.Single


let to_string (x: float) : string = x.ToString()

let to_pair (x: float) : pair =
    Seq.initInfinite (fun exp ->
        let x' = x * single (pown 10 exp)
        exp, x')
    |> Seq.pick (fun (exp, value) ->
        if System.Single.IsInteger value
        then Some ({ base1 = BigInteger value; exp = BigInteger -exp })
        else None)
let of_pair (pair: pair') : float = System.Single.Parse $"{pair.base1}e{pair.exp}"
let of_int (x: BigInteger) : float = single x

let _0 : float = 0f
let _1 : float = 1f

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

let sqr (a: float) : float = a * a
let sqrt (a: float) : float = float.Sqrt a