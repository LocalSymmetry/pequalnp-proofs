import Mathlib

theorem PEqualNP.Outside.L_lib_554 : ∀ (m k p : ℕ) (need : Fin m → Finset (Fin p)) (view : Fin p → Finset (Fin k)),
  let common := fun i : Fin m => Finset.univ.filter
    (fun j : Fin k => ∀ o ∈ need i, j ∈ view o)
  let same := fun (S : Finset (Fin k)) (x y : Fin k → Bool) => ∀ j ∈ S, x j = y j
  let decodable := fun D : (Fin k → Bool) → Fin m → Bool =>
    ∀ (i : Fin m) (o : Fin p), o ∈ need i → ∀ x y, same (view o) x y → D x i = D y i
  (∀ D : (Fin k → Bool) → Fin m → Bool, Function.Surjective D → decodable D →
    (∀ (i : Fin m) (x y : Fin k → Bool), same (common i) x y → D x i = D y i) ∧
    ∀ S : Finset (Fin m), S.card ≤ (S.biUnion common).card) ∧
  ((∃ D : (Fin k → Bool) → Fin m → Bool, Function.Surjective D ∧ decodable D) ↔
    ∃ f : Fin m ↪ Fin k, ∀ i, f i ∈ common i) := by
  classical
  intro m k p need view common same decodable
  have allClaims (D : (Fin k → Bool) → Fin m → Bool) (onto : Function.Surjective D)
      (dec : decodable D) : (∀ i x y, same (common i) x y → D x i = D y i) ∧
        ∀ S : Finset (Fin m), S.card ≤ (S.biUnion common).card := by
    have localize (i : Fin m) (x y : Fin k → Bool) (agree : same (common i) x y) : D x i = D y i := by
      let blend := fun (T : Finset (Fin k)) j => if j ∈ T then y j else x j
      have preserved (T : Finset (Fin k)) : D (blend T) i = D x i := by
        induction T using Finset.induction_on with
        | empty => simp [blend]
        | insert z T hz ih =>
          rw [← ih]
          by_cases eqz : x z = y z
          · apply congrArg (fun f : Fin k → Bool => D f i)
            funext j
            by_cases h : j = z
            · subst j
              simp [blend,hz,eqz]
            · simp [blend,h]
          · have outside : z ∉ common i := fun h => eqz (agree z h)
            have existsO : ∃ o ∈ need i, z ∉ view o := by
              by_contra! h
              exact outside (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
            obtain ⟨o,ho,hno⟩ := existsO
            apply dec i o ho
            intro j hj
            have h : j ≠ z := fun eq => hno (eq ▸ hj)
            simp [blend,h]
      simpa [blend] using (preserved Finset.univ).symm
    refine ⟨localize,?_⟩
    intro S
    let U := S.biUnion common
    let extendU := fun (a : U → Bool) (j : Fin k) => if h : j ∈ U then a ⟨j,h⟩ else false
    let localD := fun (a : U → Bool) (i : S) => D (extendU a) i
    have ontoS : Function.Surjective localD := by
      intro y
      let y' := fun i : Fin m => if h : i ∈ S then y ⟨i,h⟩ else false
      obtain ⟨x,hx⟩ := onto y'
      refine ⟨fun j => x j,?_⟩
      funext i
      change D (extendU (fun j => x j)) i = y i
      calc
        _ = D x i := localize i _ x (by
          intro j hj
          have h : j ∈ U := Finset.mem_biUnion.mpr ⟨i,i.property,hj⟩
          simp [extendU,h])
        _ = _ := by rw [hx]; simp [y']
    have card := Fintype.card_le_of_surjective localD ontoS
    change S.card ≤ U.card
    simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_coe] at card
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp card
  refine ⟨allClaims,?_,?_⟩
  · rintro ⟨D,honto,hdec⟩
    obtain ⟨f,hf,hmem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective common).mp (allClaims D honto hdec).2
    exact ⟨⟨f,hf⟩,hmem⟩
  · rintro ⟨f,hf⟩
    refine ⟨fun x i => x (f i), ?_, ?_⟩
    · intro y
      refine ⟨Function.extend f y (fun _ => false),?_⟩
      funext i
      exact f.injective.extend_apply _ _ _
    · intro i o ho x y h
      exact h (f i) ((Finset.mem_filter.mp (hf i)).2 o ho)
