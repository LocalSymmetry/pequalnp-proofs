import Mathlib

theorem PEqualNP.Outside.L_lib_567 : ∀ (n k : ℕ) (m : Fin k → ℕ) (v : (j : Fin k) → Fin (m j) → Fin n → ℝ) (w : Fin k → ℝ),
  (∀ j, 0 < m j) →
  let dot := fun (x y : Fin n → ℝ) => ∑ i, x i * y i
  (∀ j, 0 ≤ w j) →
  (∀ j a b, dot (v j a) (v j b) = if a = b then 1 else 0) →
  (∀ x, (∑ j, w j * (∑ a, (dot x (v j a))^2)) = dot x x) →
  (∀ j, w j ≤ 1) ∧
    ∀ i j, i ≠ j → w i = 1 → 0 < w j → ∀ a b, dot (v i a) (v j b) = 0 := by
  classical
  intro n k m v w hm dot hw orth parseval
  let term := fun (i : Fin k) (a : Fin (m i)) (j : Fin k) =>
    w j * ∑ b, (dot (v i a) (v j b))^2
  have nn (i a j) : 0 ≤ term i a j := mul_nonneg (hw j) (Finset.sum_nonneg (fun b _ => sq_nonneg _))
  have energy (i a) : ∑ j, term i a j = 1 := by
    exact (parseval (v i a)).trans (by simp [orth])
  have own (i a) : term i a i = w i := by
    simp [term,orth]
  constructor
  · intro j
    let a : Fin (m j) := ⟨0,hm j⟩
    rw [← own j a,← energy j a]
    exact Finset.single_le_sum (fun l _ => nn j a l) (Finset.mem_univ j)
  · intro i j ne one pos a b
    have pair : term i a i + term i a j ≤ ∑ l, term i a l := by
      have h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ ({i,j} : Finset (Fin k)))
        (fun l _ _ => nn i a l)
      simpa [ne] using h
    rw [own,one,energy] at pair
    have z : term i a j = 0 := le_antisymm (by linarith) (nn _ _ _)
    have sz : (∑ c, (dot (v i a) (v j c))^2) = 0 := (mul_eq_zero.mp z).resolve_left pos.ne'
    have le := Finset.single_le_sum (fun c _ => sq_nonneg (dot (v i a) (v j c))) (Finset.mem_univ b)
    rw [sz] at le
    nlinarith
