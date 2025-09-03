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
  | Closed _, Opened _,        _ -> commut_binrel_left  (v a) (v b) (v c)
  |        _, Closed _, Opened _ -> commut_binrel_right (v a) (v b) (v c)
  |        _,        _,        _ -> commut_binrel_weak  (v a) (v b) (v c)



type range = { l: endpoint; r: endpoint }
let not_empty range =
  match range.l, range.r with
  | Closed v1, Closed v2 -> v1 <=. v2
  | _, _ -> v range.l <. v range.r

let ( |-> ) x (range: range) = x >^ range.l /\ x <^ range.r

let lemma_not_empty_range x range : Lemma (requires x |-> range) (ensures not_empty range) [SMTPat (x |-> range)]=
  match range.l, range.r with
  | Opened _, _ -> gt_lt x (v range.l); commut_lt_lte (v range.l) x (v range.r)
  | _, Opened _ -> gt_lt x (v range.l); commut_lte_lt (v range.l) x (v range.r)
  | _, _ -> gt_lt x (v range.l); commut_lte_lte (v range.l) x (v range.r)

let (<.|> ) left right = { l = (Closed left); r = (Opened right) }
let ( <|.>) left right = { l = (Opened left); r = (Closed right) }
let (<.|.>) left right = { l = (Closed left); r = (Closed right) }
let ( <|> ) left right = { l = (Opened left); r = (Opened right) }
let ( .[] ) x (left, right) = x |-> (left <.|.> right)
let ( .() ) x (left, right) = x |-> (left  <|>  right)

let ( |=> ) (less more: range) = less.l >>.< more.l /\ less.r >.<< more.r /\ not_empty less

let lemma_not_empty_more less more : Lemma (requires less |=> more) (ensures not_empty more) [SMTPat (less |=> more)] =
  let l = v more.l in
  let r = v more.r in
  match more.l, less.l, less.r, more.r with
  | Closed _, _, _, Closed _ ->
    gte_lte (v less.l) l;
    commut_lte_lte l (v less.l) (v less.r);
    commut_lte_lte l (v less.r) r
  | _, Opened _, _, _ ->
    gte_lte (v less.l) l;
    commut_lte_lt l (v less.l) (v less.r);
    commut_lt_lte l (v less.r) r
  | Opened _, Closed _, _, _ ->
    gt_lt (v less.l) l;
    commut_lt_lte l (v less.l) (v less.r);
    commut_lt_lte l (v less.r) r
  | Closed _, Closed _, Closed _, Opened _ ->
    gte_lte (v less.l) l;
    commut_lte_lte l (v less.l) (v less.r);
    commut_lte_lt l (v less.r) r
  | Closed _, Closed _, Opened _, Opened _ ->
    gte_lte (v less.l) l;
    commut_lte_lt l (v less.l) (v less.r);
    commut_lt_lte l (v less.r) r


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