-- Leanear Algebra: Linear Algebra Done Right in Lean

universe u

section chapter1

class Field (F : Type u) where
  zero : F
  one : F
  add : F → F → F
  mult : F → F → F
  add_id : ∀ x : F, add zero x = x
  mult_id : ∀ x : F, mult one x = x
  add_inv : F → F
  mult_inv : ∀ x : F, (x ≠ zero) → F
  add_comm : ∀ x y : F, add x y = add y x
  mult_comm : ∀ x y : F, mult x y = mult y x
  add_assoc : ∀ x y z : F, add (add x y) z = add x (add y z)
  mult_assoc : ∀ x y z : F, mult (mult x y) z = mult x (mult y z)
  distrib : ∀ x y z : F, mult x (add y z) = add (mult x y) (mult x z)

def xor (x y : Bool) := (x || y) && (¬ (x && y))
theorem false_xor_x : ∀ x : Bool, xor false x = x := by
  intro x
  induction x
  case false => simp
  case true => simp

theorem true_and_x : ∀ x : Bool, (true && x) = x := by
  intro x
  induction x
  case false => simp
  case true => simp

theorem false_and_x : ∀ x : Bool, (false && x) = false := by
  intro x
  simp

instance : Field Bool where
  zero := false
  one := true
  add x y := xor x y
  mult x y := x && y
  add_id x := by
    simp
    apply false_xor_x
  mult_id x := by simp
  add_inv x := x
  mult_inv x := by
    intro h
    exact true
  add_comm x y := by
    simp
    induction x
    case false =>
      induction y
      case false => simp
      case true => simp
    case true =>
      induction y
      case false => simp
      case true => simp
  -- surely there is a better way to do this.
  mult_comm x y := by
    simp
    induction x
    case false =>
      induction y
      case false => simp
      case true => simp
    case true =>
      induction y
      case false => simp
      case true => simp
  add_assoc x y z := by
    simp
    induction x
    case false => 
      repeat rw [false_xor_x]
    case true =>
      induction y
      case false => 
        rw [false_xor_x]
        rfl
      case true =>
        induction z
        case true =>
          rfl
        case false =>
          rfl
  -- This is incredibly dumb.
  mult_assoc x y z := by
    simp
    induction x
    case false =>
      repeat rw [false_and_x]
    case true =>
      repeat rw [true_and_x]
  distrib x y z := by
    simp
    induction x
    case false =>
      repeat rw [false_and_x]
      rfl
    case true =>
      repeat rw [true_and_x]
      

end chapter1