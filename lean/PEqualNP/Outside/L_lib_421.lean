import Mathlib

namespace PEqualNP.Outside.L_lib_421_aux
abbrev Cube (n : ℕ) := Fin n → ZMod 2
def sgn (b : ZMod 2) : ℤ := if b=0 then 1 else -1
def ch {n : ℕ} (a x : Cube n) : ℤ := sgn (dotProduct a x)

theorem sign_add (a b : ZMod 2) : sgn (a+b) = sgn a * sgn b := by
  revert a b
  decide

theorem symm {n : ℕ} (a x : Cube n) : ch a x = ch x a := by
  simp only [ch,dotProduct,mul_comm (a _) (x _)]

theorem ortho {n : ℕ} (a b : Cube n) :
    (∑ x : Cube n, ch a x * ch b x) = if a=b then (2:ℤ)^n else 0 := by
  classical
  by_cases eq : a=b
  · subst b
    have square (t : ZMod 2) : sgn t * sgn t = 1 := by revert t; decide
    simp [ch,square,ZMod.card]
  · rw [if_neg eq]
    obtain ⟨i,hi⟩ : ∃ i, a i ≠ b i := by
      by_contra! h
      exact eq (funext h)
    let e : Cube n := fun j => if j=i then 1 else 0
    have shift (p x : Cube n) : ch p (x+e) = ch p x * sgn (p i) := by
      have unit : dotProduct p e = p i := by simp [dotProduct,e,mul_ite]
      rw [ch,dotProduct_add,unit,sign_add]
      rfl
    have opposite : ∀ u v : ZMod 2, u ≠ v → sgn u * sgn v = -1 := by decide
    let f (x : Cube n) := ch a x * ch b x
    have flip (x : Cube n) : f (x+e) = -f x := by
      dsimp only [f]
      rw [shift,shift]
      calc
        _ = (ch a x * ch b x) * (sgn (a i) * sgn (b i)) := by ring
        _ = _ := by rw [opposite _ _ hi]; ring
    have same := Equiv.sum_comp (Equiv.addRight e) f
    change (∑ x : Cube n, f (x+e)) = ∑ x : Cube n, f x at same
    simp_rw [flip] at same
    rw [Finset.sum_neg_distrib] at same
    change (∑ x : Cube n, f x) = 0
    omega

end PEqualNP.Outside.L_lib_421_aux

theorem PEqualNP.Outside.L_lib_421 : ∀ m n : ℕ,
  let X := Fin m → ZMod 2
  let Y := Fin n → ZMod 2
  let s := fun (bit : ZMod 2) => if bit = 0 then (1 : ℤ) else -1
  ∀ (π : Y → X) (g : Y → ZMod 2) (a : X) (b : Y),
    (∑ x : X, ∑ y : Y, s (dotProduct x (π y) + g y + dotProduct a x + dotProduct b y)) =
      (2:ℤ)^m * ∑ y : Y, if π y = a then s (g y + dotProduct b y) else 0 := by
  classical
  intro m n X Y s π g a b
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  let h := g y + dotProduct b y
  have term (x : X) :
      s (dotProduct x (π y) + g y + dotProduct a x + dotProduct b y) =
        (PEqualNP.Outside.L_lib_421_aux.ch (π y) x * PEqualNP.Outside.L_lib_421_aux.ch a x) * s h := by
    change PEqualNP.Outside.L_lib_421_aux.sgn _ = _
    rw [show dotProduct x (π y) + g y + dotProduct a x + dotProduct b y =
        dotProduct x (π y) + dotProduct a x + h by dsimp [h]; ring,
        PEqualNP.Outside.L_lib_421_aux.sign_add,PEqualNP.Outside.L_lib_421_aux.sign_add]
    exact congrArg (fun v => v * PEqualNP.Outside.L_lib_421_aux.ch a x * s h) (PEqualNP.Outside.L_lib_421_aux.symm x (π y))
  simp_rw [term]
  rw [← Finset.sum_mul,PEqualNP.Outside.L_lib_421_aux.ortho]
  by_cases eq : π y = a <;> simp [eq,h]
