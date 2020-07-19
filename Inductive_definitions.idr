module Inductive_definitions

-- Inductive definition of data types ------------------------------
data NNat = Zero | Succ NNat
data BBool = TTrue | FFalse
--------------------------------------------------------------------

-- Inductive definition of functions -------------------------------
negate : BBool -> BBool
negate TTrue = TTrue
negate FFalse = FFalse

add : NNat -> NNat -> NNat
add Zero n = n
add (Succ m) n = Succ (add m n)

is_odd : NNat -> BBool
is_odd Zero = FFalse
is_odd (Succ n) = negate (is_odd n)
--------------------------------------------------------------------------

-- A slightly more complex example ---------------------------------------
data TTree : Type -> Type where 
  Leaf : ty -> (TTree ty)
  Node : (TTree ty) -> (TTree ty) -> (TTree ty)

no_of_leaves : (TTree ty) -> NNat
no_of_leaves (Leaf a) = (Succ Zero)
no_of_leaves (Node left right) = add (no_of_leaves left) (no_of_leaves right)

tree1 : TTree BBool
tree1 = Node (Node (Leaf TTrue) (Leaf (TTrue))) (Leaf FFalse)
----------------------------------------------------------------------------------
-- We can also use lambda to define functions. Although they won't be inductive --
collapse : (TTree BBool) -> (TTree BBool)
collapse = \tr => (Leaf TTrue)
----------------------------------------------------------------------------------
data SSum : Type -> Type -> Type where
  inl : left -> SSum left right
  inr : right -> SSum left right
-- Write "the (SSum NNat BBool) (inl Zero)" in case type inferance fails ---------

-- Universal property holds :P   ------------------------------------------------
----------------------------------------------------------------------------------
universal_fun : (left -> ty) -> (right -> ty) -> (SSum left right) -> ty
universal_fun lf rf (inl x) = lf x
universal_fun lf rf (inr y) = rf y
----------------------------------------------------------------------------------