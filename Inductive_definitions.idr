module Inductive_definitions

data NNat = Zero | Succ NNat
data BBool = TTrue | FFalse

negate : BBool -> BBool
negate TTrue = TTrue
negate FFalse = FFalse

add : NNat -> NNat -> NNat
add Zero n = n
add (Succ m) n = Succ (add m n)

is_odd : NNat -> BBool
is_odd Zero = FFalse
is_odd (Succ n) = negate (is_odd n)

data TTree : (ty : Type) -> Type where
  Leaf : ty -> (TTree ty)
  Node : (TTree ty) -> (TTree ty) -> (TTree ty)

no_of_leaves : (TTree ty) -> NNat
no_of_leaves (Leaf a) = (Succ Zero)
no_of_leaves (Node left right) = add (no_of_leaves left) (no_of_leaves right)

tree1 : TTree BBool
tree1 = Node (Node (Leaf TTrue) (Leaf (TTrue))) (Leaf FFalse)