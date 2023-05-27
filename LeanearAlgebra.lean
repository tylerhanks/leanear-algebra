-- Leanear Algebra: Linear Algebra Done Right in Lean

universe u v

section chapter1

class Field (F : Type u) where
  zero : F
  one : F
  add : F → F → F
  mult : F → F → F
  add_id : ∀ x : F, add zero x = x
  mult_id : ∀ x : F, mult one x = x
  add_inv : F → F
  is_add_inv : ∀ x : F, add x (add_inv x) = zero
  mult_inv : ∀ x : F, (x ≠ zero) → F
  is_mult_inv : ∀ (x : F) (p : x ≠ zero), mult x (mult_inv x p) = one
  add_comm : ∀ x y : F, add x y = add y x
  mult_comm : ∀ x y : F, mult x y = mult y x
  add_assoc : ∀ x y z : F, add (add x y) z = add x (add y z)
  mult_assoc : ∀ x y z : F, mult (mult x y) z = mult x (mult y z)
  distrib : ∀ x y z : F, mult x (add y z) = add (mult x y) (mult x z)

export Field (zero one add mult add_inv mult_inv)

class VectorSpace (V : Type v) (F : Type u) [Field F] where
  add : V → V → V
  smult : F → V → V
  add_comm : ∀ u v : V, add u v = add v u
  add_assoc : ∀ u v w : V, add (add u v) w = add u (add v w)
  smult_assoc : ∀ (a b : F) (v : V), smult (Field.mult a b) v = smult a (smult b v)
  zero : V
  add_id : ∀ v : V, add v zero = v
  add_inv : V → V
  is_add_inv : ∀ v : V, add v (add_inv v) = zero
  smult_id : ∀ v : V, smult Field.one v = v
  smult_distrib : ∀ (a : F) (u v : V), smult a (add u v) = add (smult a u) (smult a v)
  add_distrib : ∀ (a b : F) (v : V), smult (Field.add a b) v = add (smult a v) (smult b v)

instance (S : Type v) (F : Type u) [Field F] : VectorSpace (S → F) F where
  add f g := fun x => Field.add (f x) (g x)
  smult c f := fun x => Field.mult c (f x)
  add_comm f g := by
    simp
    apply funext; intro x
    rw [Field.add_comm]
  add_assoc f g h := by
    simp
    apply funext; intro x
    rw [Field.add_assoc]
  smult_assoc c d f := by
    simp
    apply funext; intro x
    rw [Field.mult_assoc]
  zero := fun x => Field.zero
  add_id f := by
    simp
    apply funext; intro x
    rw [Field.add_comm, Field.add_id]
  add_inv f := fun x => Field.add_inv (f x)
  is_add_inv := by
    intro f; simp
    apply funext; intro x
    rw [Field.is_add_inv]
  smult_id := by
    intro f; simp
    apply funext; intro x
    rw [Field.mult_id]
  smult_distrib := by
    intro c f g; simp
    apply funext; intro x
    rw [Field.distrib]
  add_distrib := by
    intro c d f; simp
    apply funext; intro x
    rw [Field.mult_comm, Field.distrib, Field.mult_comm]
    conv in (mult (f x) d) => rw [Field.mult_comm]
    


  

    
  

#check funext
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
  is_add_inv x := by
    simp
    induction x
    case false => simp
    case true => simp
  mult_inv x := by
    intro
    exact true
  is_mult_inv x p := by
    simp
    induction x
    case false =>
      contradiction
    case true =>
      rfl 
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