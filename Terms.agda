open import NonDependentTypes

module Terms where

term1-⊤ : ⊤
term1-⊤ = tt

term1-× : ℕ × ℕ
term1-× = zero , zero

term1-r : R ℕ ⊤ (ℕ × ℕ)
term1-r =  record{
  f₁ = zero
  ;f₂ = term1-⊤
  ;f₃ = term1-×
  }

term1-+ : ℕ + (ℕ × ℕ)
term1-+ = inj₁ zero

term2-+ : ℕ + (ℕ × ℕ)
term2-+ = inj₂ term1-×

term1-w : WeekDay
term1-w = monday

term2-w : WeekDay
term2-w = tuesday

term3-w : WeekDay
term3-w = wednesday

term4-w : WeekDay
term4-w = thursday

term5-w : WeekDay
term5-w = friday

add : ℕ -> ℕ -> ℕ
add n  zero = n
add n (m) = (add n m)

term1-mb : Maybe ℕ
term1-mb = just zero

term2-mb : Maybe ℕ
term2-mb = nothing

term1-li : List ℕ
term1-li = nil

term2-li : List ℕ
term2-li = zero ∷ (zero ∷ term1-li)

term1-tr : Tree ℕ
term1-tr = empty

term2-tr : Tree ℕ
term2-tr = leaf zero

term3-tr : Tree ℕ
term3-tr = node term1-tr term2-tr

term-tr4 : Tree ℕ
term-tr4 = node (leaf zero) (node (leaf zero) empty)
