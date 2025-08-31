module Test.Float.Pair

module Lemmas = FStar.Math.Lemmas
open FStar.Mul

type pair' = { base: int; exp: int }
type pair = p: pair'{p.base % 10 = 0 ==> (p.base = 0 /\ p.exp = 0)}

let ( |+ ) (pair: pair') (n: int) : GTot pair' = { pair with exp = pair.exp + n }
let ( |- ) (pair: pair') (n: int) : GTot pair' = { pair with exp = pair.exp - n }
let ( *| ) (pair: pair') (n: int) : GTot pair' = { pair with base = pair.base * n }
let ( /| ) (pair: pair') (n: nonzero) : GTot pair' = { pair with base = pair.base / n }

let rec pow10 (x: nat) : GTot pos =
  match x with
  | 0 -> 1
  | _ -> 10 * pow10 (x - 1)

let rec mod10 (x: nonzero) : GTot nat (decreases abs x) =
  match x % 10 with
  | 0 -> 1 + mod10 (x / 10)
  | _ -> 0

let normalized (p: pair) (p': pair'{p'.base <> 0}) : prop = 
  let count = mod10 p'.base in
  p'.base = p.base * pow10 count /\
  p.exp = p'.exp + count

let rec norm_pair (p': pair') : Ghost pair
  (requires True)
  (ensures fun p ->
    (p'.base = 0 ==> p.base = 0) /\
    (p'.base <> 0 ==> p `normalized` p'))
  (decreases abs p'.base)
  =
  match p'.base, p'.base % 10 with
  | 0, 0 -> { base = 0; exp = 0 }
  | _, 0 -> let _p = (p' /| 10 |+ 1) in norm_pair _p
  | _, _ -> p'


let normalized_save_sign (p: pair) (p': pair') : Lemma
  (requires p'.base <> 0 /\ p `normalized` p')
  (ensures p'.base > 0 <==> p.base > 0 /\ p'.base < 0 <==> p.base < 0)
  = ()

let pair_mul_left (p: pair') a b : Lemma (p *| a *| b = p *| (a * b)) = ()

let norm_pair_right_add (p': pair') : Lemma
  (requires p'.base <> 0)
  (ensures norm_pair (p' *| 10) = (norm_pair p' |+ 1))
  = 
  let p = norm_pair p' in
  let p'_10 = p' *| 10 in
  let p_10 = norm_pair p'_10 in
  let count = mod10 p'.base in

  assert (p'.base = p.base * pow10 count);
  assert (p'_10.base = p_10.base * pow10 (count + 1));
  Lemmas.lemma_cancel_mul p'.base (p_10.base * pow10 count) 10;
  assert (p'.base = p_10.base * pow10 count);
  Lemmas.lemma_cancel_mul p.base p_10.base (pow10 count);
  assert (p_10.base = p.base);

  assert (p_10.exp = p.exp + 1)

let rec norm_pair_pow10 (n: nat) (p': pair') : Lemma
  (requires p'.base <> 0)
  (ensures norm_pair (p' *| pow10 n) = (norm_pair p' |+ n))
  =
  match n with
  | 0 -> ()
  | _ -> 
    norm_pair_pow10 (n - 1) p';
    assert (norm_pair (p' *| pow10 (n - 1)) = (norm_pair p' |+ (n - 1)));
    pair_mul_left p' (pow10 (n - 1)) 10;
    assert (norm_pair (p' *| pow10 n) = norm_pair (p' *| pow10 (n - 1) *| 10));
    norm_pair_right_add (p' *| pow10 (n - 1));
    assert (norm_pair (p' *| pow10 (n - 1) *| 10) = (norm_pair (p' *| pow10 (n - 1)) |+ 1))

let norm_pow10 (n: nat) (base exp: int) : Lemma
  (requires base % 10 <> 0)
  (ensures norm_pair { base = base * pow10 n; exp = exp } =
                     { base = base; exp = exp + n })
  [SMTPat (norm_pair { base = base * pow10 n; exp = exp })]
  =
  norm_pair_pow10 n { base = base; exp = exp }
