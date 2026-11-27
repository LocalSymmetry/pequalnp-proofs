import Mathlib

namespace PEqualNP.Outside.L_lib_664_aux

abbrev K := ZMod 2
abbrev V (r : Nat) := Fin r → K
abbrev I (m r : Nat) := Fin m × Fin r

theorem twice (a : K) : a+a=0 := by fin_cases a <;> rfl

theorem cancel {r : Nat} (S : Finset (Fin r)) (small : S.card < r)
    (f : V r → K) (depends : ∀ x y : V r, (∀ j ∈ S, x j = y j) → f x = f y) :
    ∑ t, f t = 0 := by
  classical
  obtain ⟨j,hj⟩ : ∃ j, j ∉ S := by
    by_contra! h
    have he : S = Finset.univ := Finset.eq_univ_of_forall h
    simpa [he] using small
  let flip (t : V r) := Function.update t j (t j+1)
  have keep (t : V r) : f t = f (flip t) := by
    apply depends
    intro i hi
    have hn : i ≠ j := fun e => hj (e ▸ hi)
    simp [flip, Function.update_of_ne hn]
  apply Finset.sum_involution (fun t _ => flip t)
  · intro t _
    rw [← keep, twice]
  · intro t _ _ he
    have e := congrFun he j
    simpa [flip] using e
  · simp
  · intro t _
    funext i
    by_cases e : i=j
    · subst i
      simp [flip,add_assoc,show (1:K)+1=0 by decide]
    · simp [flip, Function.update_of_ne e]

def weight {r : Nat} (W : Finset (Fin r)) (t : V r) : K := ∏ j ∈ W, t j
def plain {m r : Nat} (A : Finset (I m r)) (W : Finset (Fin r)) : K :=
  ∑ t : V r, weight W t * ∏ j ∈ A, t j.2

theorem zeroPlain {m r : Nat} (A : Finset (I m r)) (W : Finset (Fin r))
    (h : W.card + A.card < r) : plain A W = 0 := by
  classical
  apply cancel (W ∪ A.image Prod.snd)
  · have := Finset.card_union_le W (A.image Prod.snd)
    have : (A.image Prod.snd).card ≤ A.card := Finset.card_image_le
    omega
  · intro x y e
    apply congrArg₂ (· * ·)
    · apply Finset.prod_congr rfl
      intro j hj
      exact e j (Finset.mem_union_left _ hj)
    · apply Finset.prod_congr rfl
      intro j hj
      exact e j.2 (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj))

theorem moment {m r : Nat} (M : Finset (I m r)) (W : Finset (Fin r))
    (hm : M.card < r) (hw : W.card ≤ 1) (base : Fin m → V r) :
    (∑ t : V r, weight W t * ∏ j ∈ M, (base j.1 j.2 + t j.2)) = plain M W := by
  classical
  have expand (t : V r) : (∏ j ∈ M, (base j.1 j.2 + t j.2)) =
      ∑ A ∈ M.powerset, (∏ j ∈ A, t j.2) * ∏ j ∈ M \ A, base j.1 j.2 := by
    simp_rw [add_comm (base _ _) _]
    exact Finset.prod_add _ _ _
  simp_rw [expand,Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ A ∈ M.powerset, plain A W * ∏ j ∈ M \ A, base j.1 j.2 := by
      apply Finset.sum_congr rfl
      intro A _
      simp only [plain,Finset.sum_mul,mul_assoc]
    _ = _ := by
      rw [Finset.sum_eq_single M]
      · simp
      · intro A hA hn
        have hcard := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.mem_powerset.mp hA,hn⟩)
        rw [zeroPlain A W (by omega),zero_mul]
      · simp

end PEqualNP.Outside.L_lib_664_aux

open PEqualNP.Outside.L_lib_664_aux in
theorem PEqualNP.Outside.L_lib_664 : ∀ (r m : Nat), 0 < r →
  let K := ZMod 2
  let V := Fin r → K
  let W := Fin m → V
  let I := Fin m × Fin r
  let low := fun (f : W → K) => ∃ T : Finset (Finset I),
    (∀ mon ∈ T, mon.card < r) ∧
    ∀ word, f word = ∑ mon ∈ T, ∏ j ∈ mon, word j.1 j.2
  ∀ (point : Fin m → V) (pred : Fin m → W → K), (∀ i, low (pred i)) →
    ∃ tag : Fin m → V, ∀ (base : W) (i : Fin m),
      let bad := (Finset.univ : Finset V).filter (fun t =>
        pred i (fun j => base j + t) ≠ (if base i + t = point i then 1 else 0))
      bad.card % 2 = 1 ∧ ∀ k : Fin r, (∑ t ∈ bad, t k) = base i k + tag i k := by
  classical
  intro r m hr K' V' W' I' low point pred hlow
  choose T hcard hrep using hlow
  let c (i : Fin m) (W : Finset (Fin r)) : K := ∑ M ∈ T i, plain M W
  have weighted (i : Fin m) (W : Finset (Fin r)) (hw : W.card ≤ 1) (base : W') :
      (∑ t : V', weight W t * pred i (fun j => base j + t)) = c i W := by
    simp_rw [hrep,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro M hM
    exact moment M W (hcard i M hM) hw base
  have cz (i : Fin m) : c i ∅ = 0 := by
    apply Finset.sum_eq_zero
    intro M hM
    apply zeroPlain
    simpa using hcard i M hM
  refine ⟨fun i k => point i k + c i {k}, ?_⟩
  intro base i bad
  have bs (g : V' → K) : (∑ t ∈ bad, g t) =
      (∑ t : V', g t * pred i (fun j => base j+t)) + g (point i-base i) := by
    have equiv (t : V') : base i + t = point i ↔ t = point i-base i := by
      constructor <;> intro h
      · rw [← h]; abel
      · rw [h]; abel
    have err (p q v : K) : (if p ≠ q then v else 0) = v*(p+q) := by
      fin_cases p <;> fin_cases q <;> fin_cases v <;> decide
    change (∑ t ∈ Finset.univ.filter _, g t) = _
    rw [Finset.sum_filter]
    simp_rw [err,mul_add]
    rw [Finset.sum_add_distrib]
    congr 1
    simp_rw [equiv, mul_ite, mul_one, mul_zero]
    simp
  constructor
  · have e := bs (fun _ => 1)
    have u := weighted i ∅ (by simp) base
    simp [weight,cz] at u
    have h : (bad.card : K) = 1 := by simpa [u] using e
    exact Nat.odd_iff.mp (ZMod.natCast_eq_one_iff_odd.mp h)
  · intro k
    have e := bs (fun t => t k)
    have u := weighted i {k} (by simp) base
    simp only [weight,Finset.prod_singleton] at u
    rw [u] at e
    rw [e]
    change c i {k} + (point i k - base i k) = base i k + (point i k + c i {k})
    have neg (a : K) : -a=a := by fin_cases a <;> rfl
    rw [sub_eq_add_neg,neg]
    ac_rfl
