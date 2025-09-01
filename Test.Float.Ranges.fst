module Test.Float.Ranges

include Test.Float.Base
open Test.Float.Lemmas.Arithmetic
open Test.Float.Lemmas.Inequality

type endpoint =
  | Opened: p:float -> endpoint
  | Closed: p:float -> endpoint

let v point =
  match point with
  | Opened p -> p
  | Closed p -> p

let satisfy {| binrel_pair |} x point =
  match point with
  | Opened p -> x <??> p
  | Closed p -> x <?=> p

let (>^) = satisfy #weak_gt
let (<^) = satisfy #weak_lt

let (>.<) {| binrel_pair |} p1 p2 =
  match p1, p2 with
  | Closed v1, Opened v2 -> v1 <??> v2
  | _, _ -> v p1 <?=> v p2

let (>>.<) = (>.<) #weak_gt
let (>.<<) = (>.<) #weak_lt

let commut_endpoint {| binrel_pair |} (a b c: endpoint) : Lemma
  (requires a >.< b /\ b >.< c)
  (ensures a >.< c)
  =
  match a, b, c with
  | Closed _, Opened _,        _ -> commut_binrel_left (v a) (v b) (v c)
  |        _, Closed _, Opened _ -> commut_binrel_right (v a) (v b) (v c)
  |        _,        _,        _ -> binrel_commut_weak (v a) (v b) (v c)



type range = { l: endpoint; r: endpoint }

let ( |-> ) x (rng: range) = x >^ rng.l /\ x <^ rng.r

let (<.|> ) x (left, right) = x |-> { l = (Closed left); r = (Opened right) }
let ( <|.>) x (left, right) = x |-> { l = (Opened left); r = (Closed right) }
let (<.|.>) x (left, right) = x |-> { l = (Closed left); r = (Closed right) }
let ( <|> ) x (left, right) = x |-> { l = (Opened left); r = (Opened right) }
let ( .[] ) = (<.|.>)
let ( .() ) = ( <|> )

let ( |=> ) (less more: range) =
  less.l >>.< more.l /\
  less.r >.<< more.r

let single (x: float) : Pure range (requires True) 
  (ensures fun range -> x |-> range /\ (forall (y: float{y |-> range}). y = x)) =
  { l = Closed x; r = Closed x }

let contains_is_closed_range range x : Lemma (x |-> range <==> single x |=> range) = ()

let range_inj (a b c: range) : Lemma (requires a |=> b /\ b |=> c) (ensures a |=> c) =
  commut_endpoint #weak_gt a.l b.l c.l;
  commut_endpoint #weak_lt a.r b.r c.r;
  assert (a.l >>.< c.l);
  assert (a.r >.<< c.r)

let point_inj x a b : Lemma (requires x |-> a /\ a |=> b) (ensures x |-> b) =
  range_inj (single x) a b