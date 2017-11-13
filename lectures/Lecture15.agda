open import Lec1Done

data List (X : Set) : Set where
  []   : List X
  _,-_ : X -> List X -> List X

infixr 4 _,-_

-- Interpret `X` as the type of elements, and
--           `T` as the type of "sub structures" (or tail of a list)
ListF : Set -> Set -> Set
ListF X T = One + (X * T)

-- We can functorially switch out substructures
-- (I think the punchline is we can use listF to turn mkList into foldr?)
listF : {X T U : Set} -> (T -> U) -> ListF X T -> ListF X U
listF g (inl x)       = inl x
listF g (inr (x , t)) = inr (x , (g t))

-- For `mkList`, we are interpreting T as List X
mkList : (X : Set) -> One + (X * List X) -> List X
mkList z (inl x)        = []
mkList z (inr (x , xs)) = x ,- xs

-- `alg` for algebra
-- algebras are like : F T -> T, right?
-- The LHS of `alg`'s type somewhat reflects the structure of lists
-- Let us rewrite it using ListF
-- foldr : {X T : Set} -> ((One + (X * T)) -> T) -> List X -> T
foldr : {X T : Set} -> (ListF X T -> T) -> List X -> T
foldr alg []        = alg (inl <>)
foldr alg (x ,- xs) = alg (inr (x , foldr alg xs))

-- Get a type error for this one! Very concerned!
-- ex1 = foldr mkList (1 ,- 2 ,- 3 ,- [])

length : {X : Set} -> List X -> Nat
length = foldr \ { (inl <>) → zero ; (inr (x , n)) → suc n}

ex2 : (length (1 ,- 2 ,- 3 ,- 4 ,- []))  == four
ex2 = refl four
