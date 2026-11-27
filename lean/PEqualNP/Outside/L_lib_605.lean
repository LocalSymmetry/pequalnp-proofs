import Mathlib

theorem PEqualNP.Outside.L_lib_605 : ∀ (m r : Nat),
  let A := Fin (m+1)
  let W := Fin r → Bool
  ∀ label : Fin m → A → W,
    let ok := fun (x : Fin m → W) (a : A) => ∀ i, x i ≠ label i a
    let covers := ∀ x, ∃ a, ok x a
    (covers ↔ ∀ i, Function.Injective (label i)) ∧
    (covers → ∀ b : A, ∃ order : Fin m → A,
      Function.Injective order ∧ (∀ i, order i ≠ b) ∧
      ∀ (flags : Fin m → Bool) (v : A),
        ok (fun pos => label pos (if flags pos then b else order pos)) v ↔
          (v = b ∧ ∀ j, flags j = false) ∨ (∃ j, flags j = true ∧ v = order j)) := by
  classical
  intro m r
  dsimp only
  intro label
  let covers := ∀ x : Fin m → (Fin r → Bool), ∃ a : Fin (m+1), ∀ i, x i ≠ label i a
  have characterization : covers ↔ ∀ i, Function.Injective (label i) := by
    constructor
    · intro cov i a c same
      by_contra distinct
      obtain ⟨j,hj⟩ := Fin.exists_succAbove_eq (Ne.symm distinct)
      let e := Equiv.swap i j
      let x := fun k : Fin m => label k (a.succAbove (e k))
      obtain ⟨v,hv⟩ := cov x
      by_cases va : v = a
      · subst v
        apply hv i
        simpa [x,e,hj] using same.symm
      · obtain ⟨t,ht⟩ := Fin.exists_succAbove_eq va
        specialize hv (e.symm t)
        exact hv (by simp [x,ht])
    · intro inj x
      by_contra h
      have hit (a : Fin (m+1)) : ∃ i, x i = label i a := by
        by_contra! miss
        exact h ⟨a,miss⟩
      choose f hf using hit
      have hi : Function.Injective f := by
        intro a b eq
        apply inj (f b)
        have ha := hf a
        rw [eq] at ha
        exact ha.symm.trans (hf b)
      have bad := Fintype.card_le_of_injective f hi
      simp at bad
  refine ⟨characterization, ?_⟩
  intro cov b
  have inj := characterization.mp cov
  refine ⟨b.succAbove, b.succAbove_right_injective, Fin.succAbove_ne b, ?_⟩
  intro flags v
  change (∀ i, label i (if flags i then b else b.succAbove i) ≠ label i v) ↔ _
  have distinct (i : Fin m) (u w : Fin (m+1)) : (label i u ≠ label i w) ↔ u ≠ w :=
    not_congr (inj i).eq_iff
  simp only [distinct]
  constructor
  · intro ok
    by_cases hv : v = b
    · refine Or.inl ⟨hv, ?_⟩
      intro j
      cases h : flags j <;> simp_all
    · obtain ⟨j,hj⟩ := Fin.exists_succAbove_eq hv
      refine Or.inr ⟨j,?_,hj.symm⟩
      cases h : flags j
      · exact False.elim ((ok j) (by simpa [h] using hj))
      · rfl
  · rintro (⟨rfl,alloff⟩ | ⟨j,on,rfl⟩) i
    · simp [alloff,Fin.succAbove_ne]
    · cases hi : flags i
      · have : i ≠ j := by rintro rfl; simp [hi] at on
        simpa [hi] using b.succAbove_right_injective.ne this
      · simp [hi,Fin.ne_succAbove]
