import Mathlib

namespace PEqualNP.Outside.L_lib_545_aux
variable {K V α : Type} [Field K] [AddCommGroup V] [Module K V]

theorem closed (run : List α → V) (A : α → V →ₗ[K] V)
    (step : ∀ w a, run (w++[a]) = A a (run w)) (P : Finset (List α))
    (start : run [] ∈ Submodule.span K (run '' (P : Set (List α))))
    (extend : ∀ w ∈ P, ∀ a, run (w++[a]) ∈ Submodule.span K (run '' (P : Set (List α)))) :
    ∀ w, run w ∈ Submodule.span K (run '' (P : Set (List α))) := by
  let U := Submodule.span K (run '' (P : Set (List α)))
  have stable (a : α) : U ≤ U.comap (A a) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w,hw,rfl⟩
    change A a (run w) ∈ U
    rw [← step]
    exact extend w hw a
  intro w
  induction w using List.reverseRecOn with
  | nil => exact start
  | append_singleton w a ih =>
    rw [step]
    exact stable a ih

theorem basis_words [Module.Finite K V] (run : List α → V) (A : α → V →ₗ[K] V)
    (step : ∀ w a, run (w++[a]) = A a (run w)) :
    ∃ P : Finset (List α), P.card ≤ Module.finrank K V ∧
      (∀ w ∈ P, w.length < Module.finrank K V) ∧ (∀ w a, w++[a] ∈ P → w ∈ P) ∧
      LinearIndependent K (fun w : P => run w.val) ∧
      ∀ w, run w ∈ Submodule.span K (run '' (P : Set (List α))) := by
  classical
  let dim := Module.finrank K V
  let Good := fun P : Finset (List α) =>
    LinearIndepOn K run (P : Set (List α)) ∧
    (∀ w ∈ P, w.length < P.card) ∧ (∀ w a, w++[a] ∈ P → w ∈ P)
  have bound (P : Finset (List α)) (h : Good P) : P.card ≤ dim := by
    have li : LinearIndependent K (fun w : P => run w.val) := h.1
    simpa using li.fintype_card_le_finrank
  let sizes := (Finset.range (dim+1)).filter (fun n => ∃ P, Good P ∧ P.card=n)
  have empty : Good ∅ := by simp [Good,linearIndepOn_empty]
  have inhabited : sizes.Nonempty :=
    ⟨0,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),∅,empty,rfl⟩⟩
  obtain ⟨n,hn,hmax⟩ := Finset.exists_max_image sizes id inhabited
  obtain ⟨P,ok,hcard⟩ := (Finset.mem_filter.mp hn).2
  have maximal (Q : Finset (List α)) (hq : Good Q) : Q.card ≤ P.card := by
    rw [hcard]
    exact hmax Q.card (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (bound Q hq)), Q,hq,rfl⟩)
  have localReach (v : List α) (hv : v=[] ∨ ∃ w ∈ P, ∃ a, v=w++[a]) :
      run v ∈ Submodule.span K (run '' (P : Set (List α))) := by
    by_contra outside
    have fresh : v ∉ P := fun h => outside (Submodule.subset_span ⟨v,h,rfl⟩)
    have more : Good (insert v P) := by
      refine ⟨?_,?_,?_⟩
      · rw [Finset.coe_insert]
        exact (linearIndepOn_insert (show v ∉ (P : Set (List α)) from fresh)).2 ⟨ok.1,outside⟩
      · intro b hb
        rw [Finset.card_insert_of_notMem fresh]
        rcases Finset.mem_insert.mp hb with rfl|h
        · rcases hv with rfl|⟨w,hw,a,rfl⟩
          · simp
          · simpa using Nat.succ_lt_succ (ok.2.1 _ hw)
        · exact Nat.lt_succ_of_lt (ok.2.1 _ h)
      · intro w a ha
        rcases Finset.mem_insert.mp ha with h|h
        · rcases hv with rfl|⟨z,hz,b,rfl⟩
          · simp at h
          · exact Finset.mem_insert_of_mem ((List.append_singleton_inj.mp h).1.symm ▸ hz)
        · exact Finset.mem_insert_of_mem (ok.2.2 w a h)
    have bad := maximal _ more
    rw [Finset.card_insert_of_notMem fresh] at bad
    omega
  refine ⟨P,bound P ok,fun w hw => lt_of_lt_of_le (ok.2.1 w hw) (bound P ok),ok.2.2,ok.1,?_⟩
  exact closed run A step P (localReach [] (Or.inl rfl))
    (fun w hw a => localReach _ (Or.inr ⟨w,hw,a,rfl⟩))

end PEqualNP.Outside.L_lib_545_aux

open PEqualNP.Outside.L_lib_545_aux in
theorem PEqualNP.Outside.L_lib_545 : ∀ (K : Type) [Field K] (q d e : ℕ),
  let V := Fin d → K
  let W := Fin e → K
  ∀ (s : V) (t : W) (A : Fin q → V →ₗ[K] V) (B : Fin q → W →ₗ[K] W)
    (f : V →ₗ[K] K) (g : W →ₗ[K] K),
    let X := fun (w : List (Fin q)) => w.foldl (fun x a => A a x) s
    let Y := fun (w : List (Fin q)) => w.foldl (fun y a => B a y) t
    (∃ w, f (X w) ≠ g (Y w)) →
      ∃ w, w.length < d + e ∧ f (X w) ≠ g (Y w) := by

  classical
  intro K inst q d e V W s t A B f g X Y
  let pairRun := fun w : List (Fin q) => (X w,Y w)
  let trans := fun a => (A a).prodMap (B a)
  let output : V × W →ₗ[K] K := f.coprod (-g)
  have step (w : List (Fin q)) (a : Fin q) : pairRun (w++[a]) = trans a (pairRun w) := by
    simp [pairRun,trans,X,Y,List.foldl_append,LinearMap.prodMap_apply]
  have dim : Module.finrank K (V × W) = d+e := by
    rw [Module.finrank_prod]
    simp [V,W]
  have same (w : List (Fin q)) : pairRun w ∈ LinearMap.ker output ↔ f (X w) = g (Y w) := by
    change f (X w) + -(g (Y w)) = 0 ↔ _
    rw [← sub_eq_add_neg,sub_eq_zero]

  rintro ⟨long,bad⟩
  obtain ⟨P,_,short,_,_,spans⟩ := basis_words pairRun trans step
  rw [dim] at short
  by_contra! noShort
  have vanishes : Submodule.span K (pairRun '' (P : Set (List (Fin q)))) ≤ LinearMap.ker output := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w,hw,rfl⟩
    exact (same w).2 (noShort w (short _ hw))
  exact bad ((same long).1 (vanishes (spans long)))
