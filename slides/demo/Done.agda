module Done where

open import Util

data BinOp : Set where
  add : BinOp
  sub : BinOp
  mul : BinOp

is-eq1 : BinOp → BinOp → Bool
is-eq1 add add = true
is-eq1 sub sub = true
is-eq1 mul mul = true
is-eq1 _ _ = false

is-eq-test1 : add ≡ add
is-eq-test1 = refl

is-eq-test2 : add ≢ sub
is-eq-test2 = λ ()

is-eq2 : (x : BinOp) → (y : BinOp) → Maybe (x ≡ y)
is-eq2 add add = just refl
is-eq2 sub sub = just refl
is-eq2 mul mul = just refl
is-eq2 _ _ = nothing

is-eq3 : (x : BinOp) → (y : BinOp) → Dec (x ≡ y)
is-eq3 add add = yes refl
is-eq3 add sub = no (λ ())
is-eq3 add mul = no (λ ())
is-eq3 sub add = no (λ ())
is-eq3 sub sub = yes refl
is-eq3 sub mul = no (λ ())
is-eq3 mul add = no (λ ())
is-eq3 mul sub = no (λ ())
is-eq3 mul mul = yes refl

binop-to-nat : BinOp → ℕ
binop-to-nat add = 0
binop-to-nat sub = 1
binop-to-nat mul = 2

nat-to-binop : ℕ → Maybe BinOp
nat-to-binop 0 = just add
nat-to-binop 1 = just sub
nat-to-binop 2 = just mul
nat-to-binop _ = nothing

is-inverse : IsInverse binop-to-nat nat-to-binop
is-inverse add = refl
is-inverse sub = refl
is-inverse mul = refl

is-eq-binop' : (x : BinOp) → (y : BinOp) → Dec (x ≡ y)
is-eq-binop' = IsInverse→DecEqFun binop-to-nat nat-to-binop is-inverse

instance
  binop-to-tree : ToTree BinOp
  binop-to-tree = tree⋆ from sur
    where from : Tree → Maybe BinOp
          from (node 0 _) = just add
          from (node 1 _) = just sub
          from (node 2 _) = just mul
          from _ = nothing

          sur : IsSurjective from
          sur add = node 0 [] , refl
          sur sub = node 1 [] , refl
          sur mul = node 2 [] , refl

is-eq-binop3 : (x : BinOp) → (y : BinOp) → Dec (x ≡ y)
is-eq-binop3 x y = x ≟ y

is-eq-same : (x : BinOp) → (y : BinOp) → is-eq1 x y ≡ true → x ≡ y
is-eq-same add add refl = refl
is-eq-same add sub ()
is-eq-same add mul ()
is-eq-same sub add ()
is-eq-same sub sub refl = refl
is-eq-same sub mul ()
is-eq-same mul add ()
is-eq-same mul sub ()
is-eq-same mul mul refl = refl

is-eq-same' : (x : BinOp) → (y : BinOp) → is-eq1 x y ≡ false → x ≢ y
is-eq-same' add .add () refl
is-eq-same' sub .sub () refl
is-eq-same' mul .mul () refl
