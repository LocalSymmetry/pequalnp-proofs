import Mathlib

theorem PEqualNP.Outside.L_lib_461 : ∀ (n k : ℕ) (G : SimpleGraph (Fin n)),
  (∃ C : Finset (Fin n), C.card ≤ k ∧ G.IsVertexCover (C : Set (Fin n))) ↔
  ∃ D : Finset (Fin n), D.card ≤ k ∧ ∀ x : Fin n,
    ¬ Relation.TransGen (fun a b : Fin n => a ∉ D ∧ b ∉ D ∧ G.Adj a b) x x := by
  intro n k G
  classical
  constructor
  · rintro ⟨C,hcard,hcov⟩
    refine ⟨C,hcard,fun x h => ?_⟩
    have noedge : ∀ a b : Fin n, ¬ (a ∉ C ∧ b ∉ C ∧ G.Adj a b) := by
      rintro a b ⟨ha,hb,e⟩
      exact (hcov e).elim ha hb
    cases h with
    | single h => exact noedge _ _ h
    | tail _ h => exact noedge _ _ h
  · rintro ⟨D,hcard,hd⟩
    refine ⟨D,hcard,?_⟩
    intro a b e
    by_contra! h
    apply hd a
    exact (Relation.TransGen.single (b := b) ⟨h.1,h.2,e⟩).tail ⟨h.2,h.1,e.symm⟩
