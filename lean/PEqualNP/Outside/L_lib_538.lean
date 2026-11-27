import Mathlib

namespace PEqualNP.Outside.L_lib_538_aux

abbrev K := ZMod 2
def sg (a : K) : ℤ := if a=0 then 1 else -1
theorem sg_add (a b : K) : sg (a+b) = sg a * sg b := by revert a b; decide
theorem twice (a : K) : a+a=0 := by revert a; decide
theorem sg_sum {ι : Type*} (S : Finset ι) (f : ι → K) :
    sg (∑ i ∈ S, f i) = ∏ i ∈ S, sg (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [sg]
  | insert i S hi ih => simp [hi, sg_add, ih]
theorem localSum (c p q : K) :
    (∑ v : K × K, sg (c * (v.1*v.2) + p*v.1 + q*v.2)) =
      if c=0 then (if p=0 ∧ q=0 then 4 else 0) else 2*sg (p*q) := by
  revert c p q
  decide
theorem flipSum {s : ℕ} (f : Fin s → Fin s → K) :
    (∑ i, ∑ j ∈ Finset.Iio i, f i j) = ∑ j, ∑ i ∈ Finset.Ioi j, f i j := by
  classical
  have lo (i : Fin s) : Finset.Iio i = Finset.univ.filter (fun j => j < i) := by ext; simp
  have hi (j : Fin s) : Finset.Ioi j = Finset.univ.filter (fun i => j < i) := by ext; simp
  simp_rw [lo,hi,Finset.sum_filter]
  rw [Finset.sum_comm]
theorem transposeSum {s : ℕ} (p z : Fin s → K) (M : Fin s → Fin s → K) :
    (∑ i, p i * ∑ j ∈ Finset.Iio i, M i j * z j) =
    ∑ j, (∑ i ∈ Finset.Ioi j, p i * M i j) * z j := by
  simp_rw [Finset.mul_sum, Finset.sum_mul, ← mul_assoc]
  exact flipSum _

end PEqualNP.Outside.L_lib_538_aux

open PEqualNP.Outside.L_lib_538_aux in

theorem PEqualNP.Outside.L_lib_538 : ∀ s : ℕ,
  let V := Fin s → ZMod 2
  let dot := fun (u v : V) => ∑ i : Fin s, u i * v i
  let sign := fun (x : ZMod 2) => if x = 0 then (1 : ℤ) else -1
  ∀ (A B : Fin s → Fin s → ZMod 2) (γ : V) (Z : V → V → V),
  (∀ x y i, Z x y i =
    (x i + ∑ j ∈ Finset.Iio i, A i j * Z x y j) *
    (y i + ∑ j ∈ Finset.Iio i, B i j * Z x y j)) →
  ∀ p q : V,
    let c := fun (j : Fin s) =>
      γ j + ∑ i ∈ Finset.Ioi j, (p i * A i j + q i * B i j)
    (∑ x : V, ∑ y : V, sign (dot γ (Z x y) + dot p x + dot q y)) =
      ∏ j : Fin s,
        if c j = 0 then (if p j = 0 ∧ q j = 0 then 4 else 0)
        else 2 * sign (p j * q j) := by
  classical
  intro s V dot sign A B γ Z hz p q c
  let Pair := Fin s → K × K
  let z : Pair → V := fun e i => (e i).1 * (e i).2
  let h := fun (M : Fin s → Fin s → K) (v : V) (i : Fin s) => ∑ j ∈ Finset.Iio i, M i j * v j
  let decode : Pair → V × V := fun e =>
    (fun i => (e i).1 + h A (z e) i, fun i => (e i).2 + h B (z e) i)
  let encode : V × V → Pair := fun u i => (u.1 i + h A (Z u.1 u.2) i, u.2 i + h B (Z u.1 u.2) i)
  have after (e : Pair) : Z (decode e).1 (decode e).2 = z e := by
    funext i
    refine @WellFounded.induction (Fin s) (· < ·) wellFounded_lt (fun j => Z (decode e).1 (decode e).2 j = z e j) i ?_
    intro i ih
    have ht (M : Fin s → Fin s → K) : h M (Z (decode e).1 (decode e).2) i = h M (z e) i :=
      Finset.sum_congr rfl (fun j hj => congrArg (fun a : K => M i j * a) (ih j (Finset.mem_Iio.mp hj)))
    rw [hz]
    change (((e i).1 + h A (z e) i) + h A _ i) * (((e i).2 + h B (z e) i) + h B _ i) = _
    rw [ht A,ht B]
    simp [add_assoc,twice,z]
  let bij : Pair ≃ V × V := {
    toFun := decode
    invFun := encode
    left_inv := by intro e; funext i; simp [encode,after,decode,add_assoc,twice]
    right_inv := by
      intro u
      have eqz : z (encode u) = Z u.1 u.2 := funext (fun i => (hz u.1 u.2 i).symm)
      apply Prod.ext <;> funext i <;> simp [decode,eqz,encode,add_assoc,twice] }
  let phase := fun (u : V × V) => sg (dot γ (Z u.1 u.2) + dot p u.1 + dot q u.2)
  let term := fun i (v : K × K) => sg (c i * (v.1*v.2) + p i*v.1 + q i*v.2)
  have decomp (e : Pair) : phase (bij e) = ∏ i, term i (e i) := by
    change sg (dot γ (Z (decode e).1 (decode e).2) + dot p (decode e).1 + dot q (decode e).2) = _
    rw [after]
    unfold term
    rw [← sg_sum]
    congr 1
    change _ = ∑ i, (c i * z e i + p i * (e i).1 + q i * (e i).2)
    dsimp only [dot,decode,h,c]
    simp only [mul_add,add_mul,Finset.sum_add_distrib]
    rw [transposeSum,transposeSum]
    abel
  calc
    _ = ∑ u : V × V, phase u := (Fintype.sum_prod_type phase).symm
    _ = ∑ e : Pair, phase (bij e) := (Equiv.sum_comp bij phase).symm
    _ = ∑ e : Pair, ∏ i, term i (e i) := Finset.sum_congr rfl (fun e _ => decomp e)
    _ = ∏ i, ∑ v : K × K, term i v := (Fintype.prod_sum term).symm
    _ = _ := Finset.prod_congr rfl (fun i _ => localSum _ _ _)
