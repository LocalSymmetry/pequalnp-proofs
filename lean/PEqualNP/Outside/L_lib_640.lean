import Mathlib

namespace PEqualNP.Outside.L_lib_640_aux
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

def transform {n : ℕ} (f : Cube n → ℤ) (a : Cube n) := ∑ x : Cube n, f x * ch a x

theorem adj {n : ℕ} (f h : Cube n → ℤ) :
    (∑ a : Cube n, transform f a * h a) = ∑ z : Cube n, f z * transform h z := by
  classical
  unfold transform
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro x _
  rw [symm x z]
  ring

theorem inv {n : ℕ} (f : Cube n → ℤ) (a : Cube n) :
    transform (transform f) a = (2:ℤ)^n * f a := by
  classical
  change (∑ x : Cube n, transform f x * ch a x) = _
  rw [adj]
  have lookup (z : Cube n) : transform (ch a) z = if a=z then (2:ℤ)^n else 0 := ortho a z
  simp_rw [lookup]
  simp [mul_ite,mul_comm]

theorem sign_inj : Function.Injective sgn := by
  intro a b
  revert a b
  decide

theorem one_or_neg (t : ZMod 2) : sgn t = 1 ∨ sgn t = -1 := by
  revert t
  decide

theorem square (t : ZMod 2) : sgn t * sgn t = 1 := by
  revert t
  decide

def supportSpace {n : ℕ} (F : Cube n → ℕ) (z : Cube n) : Submodule (ZMod 2) (Cube n) := by
  refine { carrier := {a | ∀ x, F x ≠ 0 → dotProduct a x = dotProduct a z}, zero_mem' := ?_, add_mem' := ?_, smul_mem' := ?_ }
  · intro a b ha hb x hx
    rw [add_dotProduct, add_dotProduct, ha x hx, hb x hx]
  · simp
  ·
    intro c a ha x hx
    rw [smul_dotProduct,smul_dotProduct,ha x hx]

noncomputable def spec {n : ℕ} (U : Submodule (ZMod 2) (Cube n)) (z a : Cube n) : ℤ :=
  @ite ℤ (a ∈ U) (Classical.propDecidable _) (ch a z) 0

theorem sign_flip {b c : ZMod 2} (h : b ≠ c) : sgn b * sgn c = -1 := by
  revert b c
  decide

theorem transform_spec {n : ℕ} (U : Submodule (ZMod 2) (Cube n)) (z x : Cube n) :
    transform (spec U z) x =
      @ite ℤ (∀ a ∈ U, dotProduct a x = dotProduct a z)
        (Classical.propDecidable _) (2^(Module.finrank (ZMod 2) U)) 0 := by
  classical
  by_cases good : ∀ a ∈ U, dotProduct a x = dotProduct a z
  · rw [if_pos good]
    have term (a : Cube n) : spec U z a * ch x a = if a ∈ U then 1 else 0 := by
      rw [symm x a]
      by_cases mem : a ∈ U
      · simp only [spec,if_pos mem,ch,good a mem,square]
      · simp [spec,mem]
    change (∑ a, spec U z a * ch x a) = _
    simp_rw [term]
    rw [Finset.sum_boole]
    have cardU : Fintype.card U = 2 ^ Module.finrank (ZMod 2) U := by
      simpa [ZMod.card] using (Module.card_eq_pow_finrank (K := ZMod 2) (V := U))
    rw [Fintype.card_subtype] at cardU
    exact_mod_cast cardU
  · rw [if_neg good]
    push_neg at good
    obtain ⟨b,hb,diff⟩ := good
    let f (a : Cube n) := spec U z a * ch x a
    have flip (a : Cube n) : f (a+b) = - f a := by
      have memiff : a+b ∈ U ↔ a ∈ U := by
        constructor
        · intro hab
          simpa using U.sub_mem hab hb
        · exact fun ha => U.add_mem ha hb
      dsimp only [f]
      rw [symm x (a+b),symm x a]
      by_cases ha : a ∈ U
      · simp only [spec,if_pos ha,if_pos (memiff.mpr ha),ch,add_dotProduct,sign_add]
        have neg := sign_flip (Ne.symm diff)
        calc
          _ = (sgn (dotProduct a z) * sgn (dotProduct a x)) *
              (sgn (dotProduct b z) * sgn (dotProduct b x)) := by ring
          _ = _ := by rw [neg]; ring
      · simp [spec,ha,memiff]
    have same := Equiv.sum_comp (Equiv.addRight b) f
    change (∑ a : Cube n, f (a+b)) = ∑ a : Cube n, f a at same
    simp_rw [flip] at same
    rw [Finset.sum_neg_distrib] at same
    change (∑ a : Cube n, f a) = 0
    omega

theorem mixed_bound {n : ℕ} (F : Cube n → ℕ) (a p q : Cube n)
    (hp : F p ≠ 0) (hq : F q ≠ 0) (pp : ch a p = 1) (qq : ch a q = -1) :
    -(∑ x, (F x : ℤ)) < transform (fun x => (F x : ℤ)) a ∧
    transform (fun x => (F x : ℤ)) a < ∑ x, (F x : ℤ) := by
  classical
  change _ < (∑ x, (F x : ℤ) * ch a x) ∧ (∑ x, (F x : ℤ) * ch a x) < _
  constructor
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_lt_sum
    · intro x _
      rcases one_or_neg (dotProduct a x) with h | h <;> change ch a x = _ at h <;> rw [h] <;> simp
    · refine ⟨p,Finset.mem_univ _,?_⟩
      rw [pp,mul_one]
      have : 0 < (F p : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hp
      omega
  · apply Finset.sum_lt_sum
    · intro x _
      rcases one_or_neg (dotProduct a x) with h | h <;> change ch a x = _ at h <;> rw [h] <;> simp
    · refine ⟨q,Finset.mem_univ _,?_⟩
      rw [qq,mul_neg_one]
      have : 0 < (F q : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hq
      omega

theorem spectral {n : ℕ} (F : Cube n → ℕ) (total : (∑ x, F x) = 2^n)
    (z : Cube n) (hz : F z ≠ 0)
    (hd : ∀ a, (2:ℤ)^n ∣ transform (fun x => (F x : ℤ)) a) (a : Cube n) :
    transform (fun x => (F x : ℤ)) a = (2:ℤ)^n * spec (supportSpace F z) z a := by
  classical
  have mass : (∑ x, (F x : ℤ)) = (2:ℤ)^n := by exact_mod_cast total
  by_cases h : a ∈ supportSpace F z
  · have law : ∀ x, F x ≠ 0 → dotProduct a x = dotProduct a z := h
    have term (x : Cube n) : (F x : ℤ) * ch a x = (F x : ℤ) * ch a z := by
      by_cases hx : F x = 0
      · simp [hx]
      · rw [ch,ch,law x hx]
    simp only [transform,spec,if_pos h]
    simp_rw [term]
    rw [← Finset.sum_mul,mass]
  · simp only [spec,if_neg h,mul_zero]
    change ¬ (∀ x, F x ≠ 0 → dotProduct a x = dotProduct a z) at h
    push_neg at h
    obtain ⟨x,hx,hdiff⟩ := h
    have ne : ch a x ≠ ch a z := fun e => hdiff (sign_inj e)
    have both : -(∑ i, (F i : ℤ)) < transform (fun i => (F i : ℤ)) a ∧
        transform (fun i => (F i : ℤ)) a < ∑ i, (F i : ℤ) := by
      rcases one_or_neg (dotProduct a x) with hx' | hx' <;>
        rcases one_or_neg (dotProduct a z) with hz' | hz' <;>
        change ch a x = _ at hx' <;> change ch a z = _ at hz'
      · exact False.elim (ne (hx'.trans hz'.symm))
      · exact mixed_bound F a x z hx hz hx' hz'
      · exact mixed_bound F a z x hz hx hz' hx'
      · exact False.elim (ne (hx'.trans hz'.symm))
    rw [mass] at both
    exact Int.eq_zero_of_abs_lt_dvd (hd a) (abs_lt.mpr both)

theorem classify : ∀ d : ℕ,
  let V := Fin d → ZMod 2
  let dot := fun (a x : V) => ∑ i, a i * x i
  let spin := fun (a x : V) => if dot a x = 0 then (1 : ℤ) else -1
  ∀ F : V → ℕ, (∑ x, F x) = 2^d →
    ((∀ a : V, (2^d : ℤ) ∣ ∑ x : V, (F x : ℤ) * spin a x) ↔
      ∃ (U : Submodule (ZMod 2) V) (z : V),
        ∀ x : V, F x = @ite ℕ (∀ a ∈ U, dot a x = dot a z)
          (Classical.propDecidable _) (2^(Module.finrank (ZMod 2) U)) 0) := by
  classical
  intro n V dot spin F total
  change (∀ a, (2:ℤ)^n ∣ transform (fun x => (F x : ℤ)) a) ↔
    ∃ (U : Submodule (ZMod 2) (Cube n)) (z : Cube n), ∀ x,
      F x = @ite ℕ (∀ a ∈ U, dotProduct a x = dotProduct a z) (Classical.propDecidable _) (2^Module.finrank (ZMod 2) U) 0
  constructor
  · intro hd
    obtain ⟨z,hz⟩ : ∃ z, F z ≠ 0 := by
      by_contra! h
      simp [h] at total
      exact (by positivity : 0 < (2:ℕ)^n).ne total
    let U := supportSpace F z
    refine ⟨U,z,?_⟩
    intro x
    have mulW := inv (fun i => (F i : ℤ)) x
    have freq (a : Cube n) : transform (fun i => (F i : ℤ)) a = (2:ℤ)^n * spec U z a :=
      spectral F total z hz hd a
    change (∑ a, transform (fun i => (F i : ℤ)) a * ch x a) = _ at mulW
    simp_rw [freq,mul_assoc] at mulW
    rw [← Finset.mul_sum] at mulW
    change (2:ℤ)^n * transform (spec U z) x = (2:ℤ)^n * (F x : ℤ) at mulW
    have heq : (F x : ℤ) = transform (spec U z) x := by
      exact (mul_left_cancel₀ (by positivity : (2:ℤ)^n ≠ 0) mulW).symm
    rw [transform_spec] at heq
    split_ifs at heq ⊢ <;> exact_mod_cast heq
  · rintro ⟨U,z,h⟩ a
    have feq : (fun x => (F x : ℤ)) = transform (spec U z) := by
      funext x
      rw [transform_spec,h x]
      split_ifs <;> simp
    rw [feq,inv]
    exact dvd_mul_right _ _


def weight {m d : ℕ} (row : Fin m → Cube d) (off : Fin m → ZMod 2) (x : Cube d) : ℕ :=
  (Finset.univ.filter (fun i => dotProduct (row i) x + off i = 1)).card

def bal {m d : ℕ} (row : Fin m → Cube d) (off : Fin m → ZMod 2) (a : Cube d) : ℤ :=
  ((Finset.univ.filter (fun i => row i = a ∧ off i = 1)).card : ℤ) -
    ((Finset.univ.filter (fun i => row i = a ∧ off i = 0)).card : ℤ)

theorem bal_zero {m d : ℕ} (row : Fin m → Cube d) (off : Fin m → ZMod 2)
    (hr : ∀ i, row i ≠ 0) : bal row off 0 = 0 := by
  simp [bal,hr]

theorem bal_sum {m d : ℕ} (row : Fin m → Cube d) (off : Fin m → ZMod 2) (a : Cube d) :
    bal row off a = ∑ i, if row i = a then -sgn (off i) else 0 := by
  classical
  unfold bal
  rw [← Finset.sum_boole, ← Finset.sum_boole, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases he : row i = a
  · simp only [he,true_and,ite_true]
    generalize off i = b
    revert b
    decide
  · simp [he]

theorem signed_bit (t b : ZMod 2) :
    -sgn b * sgn t = 2 * (if t+b=1 then (1:ℤ) else 0) - 1 := by
  revert t b
  decide

theorem weight_formula {m d : ℕ} (row : Fin m → Cube d) (off : Fin m → ZMod 2) (x : Cube d) :
    transform (bal row off) x = 2 * (weight row off x : ℤ) - m := by
  classical
  unfold transform
  simp_rw [bal_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  have singleton (i : Fin m) : (∑ a : Cube d, (if row i = a then -sgn (off i) else 0) * ch x a) =
      -sgn (off i) * sgn (dotProduct (row i) x) := by
    simp [ite_mul, ch, dotProduct_comm]
  simp_rw [singleton,signed_bit]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum,Finset.sum_boole]
  simp [weight]

theorem at_zero {d : ℕ} (f : Cube d → ℤ) : transform f 0 = ∑ x, f x := by
  simp [transform,ch,sgn]

theorem zero_of_sign {d : ℕ} (b : Cube d → ℤ) (bz : b 0 = 0)
    (hn : ∀ x, 0 ≤ transform b x) : ∀ a, b a = 0 := by
  classical
  have sumzero := inv b 0
  rw [at_zero,bz,mul_zero] at sumzero
  have zerof : transform b = 0 := by
    funext x
    exact ((Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hn i)).mp sumzero) x (Finset.mem_univ _)
  intro a
  have ha := inv b a
  rw [zerof] at ha
  simpa [transform] using ha.symm

noncomputable def bump {d : ℕ} (b : Cube d → ℤ) (a : Cube d) : ℤ :=
  b a + if a=0 then 1 else 0

theorem transform_bump {d : ℕ} (b : Cube d → ℤ) (x : Cube d) :
    transform (bump b) x = transform b x + 1 := by
  classical
  simp only [transform,bump,add_mul,Finset.sum_add_distrib]
  congr 1
  simp only [ite_mul,one_mul,zero_mul]
  simp [ch,sgn]

theorem odd_profile {m d g : ℕ} (row : Fin m → Cube d) (off : Fin m → ZMod 2)
    (hr : ∀ i, row i ≠ 0) (hm : m = 2*g+1) (hg : ∀ x, g ≤ weight row off x) :
    ∃ (U : Submodule (ZMod 2) (Cube d)) (z : Cube d), 0 < Module.finrank (ZMod 2) U ∧
      (∀ a, bal row off a = @ite ℤ (a ∈ U ∧ a ≠ 0) (Classical.propDecidable _) (ch a z) 0) ∧
      ∀ x, weight row off x = g + @ite ℕ (∀ a ∈ U, dotProduct a x = dotProduct a z)
        (Classical.propDecidable _) (2^(Module.finrank (ZMod 2) U-1)) 0 := by
  classical
  let b := bal row off
  let Q := bump b
  let F (x : Cube d) := 2*(weight row off x-g)
  have bz : b 0 = 0 := bal_zero row off hr
  have qz : Q 0 = 1 := by simp [Q,bump,bz]
  have point (x : Cube d) : (F x : ℤ) = transform Q x := by
    change ((2*(weight row off x-g) : ℕ) : ℤ) = transform (bump (bal row off)) x
    rw [transform_bump,weight_formula,Nat.cast_mul,Nat.cast_sub (hg x)]
    norm_num
    omega
  have fspec (a : Cube d) : transform (fun x => (F x : ℤ)) a = (2:ℤ)^d * Q a := by
    have equal : (fun x => (F x : ℤ)) = transform Q := funext point
    rw [equal,inv]
  have mass : (∑ x, F x) = 2^d := by
    have hz := fspec 0
    rw [at_zero,qz,mul_one] at hz
    exact_mod_cast hz
  obtain ⟨U,z,form⟩ := (classify d F mass).mp (fun a => ⟨Q a,fspec a⟩)
  have shape (x : Cube d) : F x =
      @ite ℕ (∀ a ∈ U, dotProduct a x = dotProduct a z) (Classical.propDecidable _)
        (2^Module.finrank (ZMod 2) U) 0 := form x
  have fx : (fun x => (F x : ℤ)) = transform (spec U z) := by
    funext x
    rw [transform_spec,shape]
    split_ifs <;> simp
  have specQ (a : Cube d) : Q a = spec U z a := by
    have lhs := fspec a
    rw [fx,inv] at lhs
    exact (mul_left_cancel₀ (by positivity : (2:ℤ)^d ≠ 0) lhs).symm
  have rankpos : 0 < Module.finrank (ZMod 2) U := by
    by_contra! hz
    have h := shape z
    have rz : Module.finrank (ZMod 2) U = 0 := by omega
    have yes : ∀ a ∈ U, dotProduct a z = dotProduct a z := by simp
    rw [if_pos yes,rz,pow_zero] at h
    dsimp only [F] at h
    omega
  refine ⟨U,z,rankpos,?_,?_⟩
  · intro a
    by_cases ha : a = 0
    · subst a
      simpa using bz
    · have h := specQ a
      simpa [Q,bump,ha,spec,b] using h
  · intro x
    have h := shape x
    have hgx := hg x
    dsimp only [F] at h
    have p : 2^Module.finrank (ZMod 2) U = 2^(Module.finrank (ZMod 2) U-1) * (2:ℕ) := by
      conv_lhs => rw [← Nat.sub_add_cancel rankpos]
      rw [pow_succ]
    rw [p] at h
    by_cases yes : ∀ a ∈ U, dotProduct a x = dotProduct a z
    · rw [if_pos yes] at h ⊢
      have cut : weight row off x - g = 2^(Module.finrank (ZMod 2) U-1) := by
        exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) (h.trans (Nat.mul_comm _ _))
      calc
        _ = (weight row off x - g) + g := (Nat.sub_add_cancel hgx).symm
        _ = _ := by rw [cut,Nat.add_comm]
    · rw [if_neg yes] at h ⊢
      omega

end PEqualNP.Outside.L_lib_640_aux



namespace PEqualNP.Outside.L_lib_640_aux
open scoped symmDiff

theorem inconsistency : (∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) (ZMod 2)) (b : Fin m → ZMod 2),
  (¬ ∃ x : Fin n → ZMod 2, A.mulVec x = b) ↔
    ∃ y : Fin m → ZMod 2, A.vecMul y = 0 ∧ dotProduct y b = 1) := by
  intro m n A b
  constructor
  · intro h
    have hb : b ∉ LinearMap.range A.mulVecLin := by
      rintro ⟨x, hx⟩
      exact h ⟨x, by simpa using hx⟩
    obtain ⟨f, hfb, hf⟩ := Submodule.exists_le_ker_of_notMem hb
    have key : ∀ v : Fin m → ZMod 2, dotProduct (fun i => f (Pi.single i 1)) v = f v := by
      intro v
      conv_rhs => rw [← Finset.univ_sum_single v]
      rw [map_sum]
      unfold dotProduct
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hs : (Pi.single i (v i) : Fin m → ZMod 2) = v i • Pi.single i (1 : ZMod 2) := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      rw [hs, map_smul, smul_eq_mul, mul_comm]
    refine ⟨fun i => f (Pi.single i 1), ?_, ?_⟩
    · funext j
      have h1 : A.vecMul (fun i => f (Pi.single i 1)) j = f (fun i => A i j) := key (fun i => A i j)
      have hmem : (fun i => A i j) ∈ LinearMap.range A.mulVecLin := by
        refine ⟨Pi.single j 1, ?_⟩
        funext i
        simp
      rw [h1]
      simpa using hf hmem
    · rw [key]
      exact (show ∀ a : ZMod 2, a ≠ 0 → a = 1 by decide) _ hfb
  · rintro ⟨y, hy, hyb⟩ ⟨x, hx⟩
    rw [← hx, Matrix.dotProduct_mulVec, hy, zero_dotProduct] at hyb
    exact zero_ne_one hyb

theorem sumSD {m : ℕ} (s t : Finset (Fin m)) (f : Fin m → ZMod 2) :
    (s ∆ t).sum f = s.sum f + t.sum f := by
  classical
  have un (X : Finset (Fin m)) : X.sum f = ∑ i, if i ∈ X then f i else 0 := by
    rw [← Finset.sum_filter]
    simp
  rw [un (s ∆ t),un s,un t,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have add : ∀ z : ZMod 2, z + z = 0 := by decide
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp [Finset.mem_symmDiff,hs,ht,add]

open scoped symmDiff

theorem average : ∀ (n m : ℕ) (row : Fin m → Fin n → ZMod 2) (rhs : Fin m → ZMod 2),
  let ok := fun (rows : Finset (Fin m)) => ∃ x : Fin n → ZMod 2,
    ∀ e ∈ rows, (∑ j, row e j * x j) = rhs e
  let W := Finset.univ.filter (fun indices : Finset (Fin m) =>
    (∀ j : Fin n, indices.sum (fun e => row e j) = 0) ∧ indices.sum rhs = 1)
  ¬ ok Finset.univ → (∀ e : Fin m, ¬ ok (Finset.univ.erase e)) →
    W.Nonempty ∧
    (∀ e ∈ W.biUnion id, 2*(W.filter (fun subset => e ∈ subset)).card = W.card) ∧
    ∀ w : Fin m → ℕ,
      2*W.sum (fun support => support.sum w) = W.card * (W.biUnion id).sum w ∧
      ∃ D ∈ W, 2*D.sum w ≤ (W.biUnion id).sum w := by
  classical
  intro n m row rhs
  dsimp only
  intro no erased
  let W := Finset.univ.filter (fun S : Finset (Fin m) =>
    (∀ j, S.sum (fun i => row i j) = 0) ∧ S.sum rhs = 1)
  change W.Nonempty ∧ (∀ e ∈ W.biUnion id, _) ∧ _
  have cert (T : Finset (Fin m)) (hT : ¬ ∃ x : Fin n → ZMod 2,
      ∀ e ∈ T, (∑ j, row e j * x j) = rhs e) : ∃ S ∈ W, S ⊆ T := by
    let A : Matrix (Fin m) (Fin n) (ZMod 2) := fun i j => if i ∈ T then row i j else 0
    let b := fun i => if i ∈ T then rhs i else 0
    have h : ¬ ∃ x, A.mulVec x = b := by
      rintro ⟨x,hx⟩
      apply hT
      refine ⟨x,?_⟩
      intro i hi
      simpa [A,b,Matrix.mulVec,dotProduct,hi] using congrFun hx i
    obtain ⟨y,hy,hb⟩ := (PEqualNP.Outside.L_lib_640_aux.inconsistency m n A b).mp h
    let S := Finset.univ.filter (fun i => i ∈ T ∧ y i = 1)
    have convert (f : Fin m → ZMod 2) :
        S.sum f = ∑ i, y i * (if i ∈ T then f i else 0) := by
      rw [show S.sum f = _ from Finset.sum_filter _ _]
      apply Finset.sum_congr rfl
      intro i _
      have dich : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
      rcases dich (y i) with eq|eq <;> by_cases hi : i ∈ T <;> simp [eq,hi]
    refine ⟨S,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_⟩,?_⟩
    · intro j
      rw [convert]
      exact congrFun hy j
    · rw [convert]
      exact hb
    · exact fun e he => (Finset.mem_filter.mp he).2.1
  obtain ⟨D,hD,_⟩ := cert _ no
  have half (e : Fin m) (he : e ∈ W.biUnion id) :
      2 * (W.filter (fun S => e ∈ S)).card = W.card := by
    obtain ⟨A,hA,ie⟩ := Finset.mem_biUnion.mp he
    change e ∈ A at ie
    obtain ⟨B,hB,sub⟩ := cert _ (erased e)
    have out : e ∉ B := fun h => Finset.notMem_erase e _ (sub h)
    let T := A ∆ B
    have toggle : e ∈ T := Finset.mem_symmDiff.mpr (Or.inl ⟨ie,out⟩)
    have act {S} (hS : S ∈ W) : S ∆ T ∈ W := by
      obtain ⟨sa,sb⟩ := (Finset.mem_filter.mp hS).2
      obtain ⟨aa,ab⟩ := (Finset.mem_filter.mp hA).2
      obtain ⟨ba,bb⟩ := (Finset.mem_filter.mp hB).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · intro j
        simp [T,PEqualNP.Outside.L_lib_640_aux.sumSD,sa,aa,ba]
      · rw [PEqualNP.Outside.L_lib_640_aux.sumSD,PEqualNP.Outside.L_lib_640_aux.sumSD,ab,bb,sb]
        decide
    have eq : (W.filter (fun S => e ∈ S)).card = (W.filter (fun S => e ∉ S)).card := by
      apply Finset.card_bij' (fun S _ => S ∆ T) (fun S _ => S ∆ T)
      · intro S h
        obtain ⟨inW,inc⟩ := Finset.mem_filter.mp h
        exact Finset.mem_filter.mpr ⟨act inW, by simp [Finset.mem_symmDiff,inc,toggle]⟩
      · intro S h
        obtain ⟨inW,exc⟩ := Finset.mem_filter.mp h
        exact Finset.mem_filter.mpr ⟨act inW, by simp [Finset.mem_symmDiff,exc,toggle]⟩
      · intro; intro; simp
      · intro; intro; simp
    have total := Finset.card_filter_add_card_filter_not (s := W) (fun S => e ∈ S)
    omega
  refine ⟨⟨D,hD⟩,half,?_⟩
  intro w
  let U := W.biUnion id
  have expand (S : Finset (Fin m)) (hS : S ∈ W) :
      S.sum w = ∑ e ∈ U, if e ∈ S then w e else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext e
    have h (he : e ∈ S) : e ∈ U := Finset.mem_biUnion.mpr ⟨S,hS,he⟩
    simp only [Finset.mem_filter]
    exact ⟨fun he => ⟨h he,he⟩,fun he => he.2⟩
  have count (e : Fin m) :
      (∑ S ∈ W, if e ∈ S then w e else 0) = (W.filter (fun S => e ∈ S)).card * w e := by
    rw [← Finset.sum_filter]
    simp
  have value : 2 * (∑ S ∈ W, S.sum w) = W.card * U.sum w := by
    rw [Finset.sum_congr rfl expand,Finset.sum_comm,Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [count,← Nat.mul_assoc,half e he]
  refine ⟨value,?_⟩
  by_contra! bad
  have gt : (∑ _S ∈ W, U.sum w) < ∑ S ∈ W, 2*S.sum w := by
    apply Finset.sum_lt_sum
    · intro S hS
      exact Nat.le_of_lt (bad S hS)
    · exact ⟨D,hD,bad D hD⟩
  rw [← Finset.mul_sum] at gt
  simpa [value] using gt

end PEqualNP.Outside.L_lib_640_aux

namespace PEqualNP.Outside.L_lib_640_aux

def words {m n : ℕ} (A : Fin m → Cube n) (b : Cube m) : Finset (Finset (Fin m)) :=
  Finset.univ.filter fun D => (∀ j, D.sum (fun e => A e j) = 0) ∧ D.sum b = 1

def fails {m n : ℕ} (A : Fin m → Cube n) (b : Cube m) (x : Cube n) : Finset (Fin m) :=
  Finset.univ.filter fun e => dotProduct (A e) x ≠ b e

def bit {m : ℕ} (D : Finset (Fin m)) (e : Fin m) : ZMod 2 := if e ∈ D then 1 else 0

def supp {m : ℕ} (y : Cube m) := Finset.univ.filter fun e => y e = 1

theorem binary (u : ZMod 2) : u = 0 ∨ u = 1 := by revert u; decide

theorem zz (u : ZMod 2) : u+u=0 := by revert u; decide

theorem dot_bit {m : ℕ} (D : Finset (Fin m)) (v : Cube m) : dotProduct (bit D) v = D.sum v := by
  classical
  simp [bit,dotProduct,ite_mul,← Finset.sum_filter]

theorem bit_supp {m : ℕ} (y : Cube m) : bit (supp y) = y := by
  funext e
  rcases binary (y e) with h | h <;> simp [bit,supp,h]

theorem supp_bit {m : ℕ} (D : Finset (Fin m)) : supp (bit D) = D := by
  ext e
  simp [supp,bit]

def valid {m n : ℕ} (A : Fin m → Cube n) (b y : Cube m) :=
  (∀ j, dotProduct y (fun e => A e j) = 0) ∧ dotProduct y b = 1

theorem mem_words {m n : ℕ} (A : Fin m → Cube n) (b y : Cube m) :
    supp y ∈ words A b ↔ valid A b y := by
  have key (v : Cube m) : (supp y).sum v = dotProduct y v := by
    rw [← dot_bit,bit_supp]
  simp [words,valid,key]

theorem cert_bits {m n : ℕ} {A : Fin m → Cube n} {b : Cube m} {D : Finset (Fin m)}
    (h : D ∈ words A b) : valid A b (bit D) := by
  apply (mem_words A b _).mp
  rwa [supp_bit]

def word {m d : ℕ} (r : Fin m → Cube d) (o : Cube m) (x : Cube d) : Cube m :=
  fun i => dotProduct (r i) x + o i

theorem word_dot {m d : ℕ} (r : Fin m → Cube d) (o v : Cube m) (x : Cube d) :
    dotProduct (word r o x) v =
       (∑ j, dotProduct (fun e => r e j) v * x j) + dotProduct o v := by
  classical
  simp only [dotProduct,word,add_mul,Finset.sum_add_distrib,Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem parametrize {m n : ℕ} (A : Fin m → Cube n) (b : Cube m) (non : (words A b).Nonempty) :
    ∃ (d : ℕ) (r : Fin m → Cube d) (o : Cube m),
      (∀ x, supp (word r o x) ∈ words A b) ∧
      ∀ D ∈ words A b, ∃ x, supp (word r o x) = D := by
  classical
  obtain ⟨D0,h0⟩ := non
  let o := bit D0
  have start : valid A b o := cert_bits h0
  let H := {y : Cube m // (∀ j, dotProduct y (fun e => A e j) = 0) ∧ dotProduct y b = 0}
  let d := Fintype.card H
  let basis : Fin d ≃ H := (Fintype.equivFin H).symm
  let r (i : Fin m) (j : Fin d) := (basis j).val i
  have reconstruct (j : Fin d) : word r o (Pi.single j 1) = (basis j).val + o := by
    funext i
    simp [word,r]
  refine ⟨d,r,o,?_,?_⟩
  · intro x
    apply (mem_words A b _).mpr
    constructor
    · intro j
      rw [word_dot,start.1 j]
      have col (l : Fin d) : dotProduct (fun e => r e l) (fun e => A e j) = 0 := (basis l).property.1 j
      simp [col]
    · rw [word_dot,start.2]
      have col (l : Fin d) : dotProduct (fun e => r e l) b = 0 := (basis l).property.2
      simp [col]
  · intro D hD
    have hv := cert_bits hD
    have direction : (∀ j, dotProduct (bit D + o) (fun e => A e j) = 0) ∧ dotProduct (bit D + o) b = 0 := by
      constructor
      · intro j
        rw [add_dotProduct,hv.1 j,start.1 j,zero_add]
      · rw [add_dotProduct,hv.2,start.2]
        decide
    let h : H := ⟨bit D + o,direction⟩
    let j := basis.symm h
    refine ⟨Pi.single j 1,?_⟩
    rw [reconstruct]
    have hj : (basis j).val = bit D + o := by simp [j,h]
    rw [hj]
    have cancel : bit D + o + o = bit D := by
      funext e
      change bit D e + o e + o e = bit D e
      rw [add_assoc,zz,add_zero]
    rw [cancel,supp_bit]

theorem certify_rhs {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) (b delta : Cube m)
    (non : (words A b).Nonempty) (h : ∀ D ∈ words A b, dotProduct (bit D) delta = 1) :
    ∃ x, A.mulVec x = b+delta := by
  classical
  by_contra no
  obtain ⟨y,hy,opp⟩ := (inconsistency m n A (b+delta)).mp no
  have col (j : Fin n) : dotProduct y (fun e => A e j) = 0 := congrFun hy j
  have eval (v : Cube m) (hv : valid A b v) : dotProduct v delta = 1 := by
    simpa [bit_supp] using h (supp v) ((mem_words A b v).mpr hv)
  rw [dotProduct_add] at opp
  rcases binary (dotProduct y b) with hb|hb
  · obtain ⟨D,hD⟩ := non
    have zero := cert_bits hD
    have v : valid A b (y+bit D) := by
      constructor
      · intro j
        rw [add_dotProduct,col j,zero.1 j,zero_add]
      · rw [add_dotProduct,hb,zero.2,zero_add]
    have hv := eval _ v
    rw [add_dotProduct,h D hD] at hv
    rw [hb,zero_add] at opp
    rw [opp] at hv
    exact (by decide : (1:ZMod 2)+1 ≠ 1) hv
  · rw [hb,eval y ⟨col,hb⟩] at opp
    exact (by decide : (1:ZMod 2)+1 ≠ 1) opp

theorem pair_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) (b : Cube m) (e f : Fin m)
    (hne : e ≠ f) (non : (words A b).Nonempty) :
    (∃ x, fails A b x = {e,f}) ↔ ∀ D ∈ words A b, bit D e + bit D f = 1 := by
  classical
  let delta : Cube m := Pi.single e 1 + Pi.single f 1
  have dotd (y : Cube m) : dotProduct y delta = y e + y f := by simp [delta,dotProduct_add]
  have dmem (i : Fin m) : delta i ≠ 0 ↔ i ∈ ({e,f}:Finset _) := by
    by_cases hi : i=e
    · subst i
      simp [delta,Pi.single_apply,hne,hne.symm]
    by_cases hj : i=f
    · subst i
      simp [delta,Pi.single_apply,hne,hne.symm]
    simp [delta,Pi.single_apply,hi,hj,Ne.symm hi,Ne.symm hj]
  constructor
  · rintro ⟨x,hx⟩ D hD
    have y := cert_bits hD
    have mat : A.vecMul (bit D) = 0 := funext y.1
    have eqx : A.mulVec x = b+delta := by
      funext i
      have test : (dotProduct (A i) x ≠ b i) ↔ delta i ≠ 0 := by
        simpa [fails] using ((show i ∈ fails A b x ↔ i ∈ ({e,f} : Finset _) by rw [hx]).trans (dmem i).symm)
      change dotProduct (A i) x = b i + delta i
      generalize dotProduct (A i) x = p at test ⊢
      generalize b i = q at test ⊢
      generalize delta i = t at test ⊢
      revert p q t
      decide
    have val : dotProduct (bit D) (A.mulVec x) = 0 := by rw [Matrix.dotProduct_mulVec,mat,zero_dotProduct]
    rw [eqx,dotProduct_add,y.2,dotd] at val
    have : ∀ p : ZMod 2, 1+p = 0 → p=1 := by decide
    exact this _ val
  · intro h
    obtain ⟨x,hx⟩ := certify_rhs A b delta non (fun D hD => (dotd _).trans (h D hD))
    refine ⟨x,?_⟩
    ext i
    have eqi : dotProduct (A i) x = b i + delta i := congrFun hx i
    simp only [fails,Finset.mem_filter,Finset.mem_univ,true_and,eqi]
    rw [← dmem]
    simp


def nfixed {m : ℕ} (f : Fin m → Fin m) := (Finset.univ.filter (fun i => f i=i)).card

def bestLoss {m n : ℕ} (A : Fin m → Cube n) (b : Cube m) (loss : ℕ) := IsLeast
    {k : ℕ | ∃ mate : Fin m → Fin m, Function.Involutive mate ∧ nfixed mate = k ∧
      ∀ e, mate e ≠ e → ∃ x, fails A b x = {e,mate e}} loss

theorem ins_count {m : ℕ} {α : Type*} [DecidableEq α] (tag : Fin m → α)
    (s : Finset (Fin m)) (e : Fin m) (he : e ∉ s) (a : α) :
    ((insert e s).filter (fun i => tag i = a)).card =
      (s.filter (fun i => tag i = a)).card + if tag e=a then 1 else 0 := by
  classical
  by_cases h : tag e=a <;> simp [Finset.filter_insert,h,he]

theorem build_pairs {m : ℕ} {α : Type*} [DecidableEq α] (tag : Fin m → α)
    (S T : Finset (Fin m)) (dis : Disjoint S T)
    (hcount : ∀ a, (S.filter (fun i => tag i=a)).card ≤ (T.filter (fun i => tag i=a)).card) :
    ∃ mate : Fin m → Fin m, Function.Involutive mate ∧
      (∀ e ∈ S, mate e ∈ T ∧ tag (mate e) = tag e) ∧
      (∀ e, mate e ≠ e → e ∈ S ∨ mate e ∈ S) ∧ nfixed mate + 2*S.card=m := by
  classical
  induction S using Finset.induction_on generalizing T with
  | empty =>
    exact ⟨id,fun _ => rfl,by simp,by simp,by simp [nfixed]⟩
  | @insert e S he ih =>
    have cnt := hcount (tag e)
    rw [ins_count tag S e he (tag e),if_pos rfl] at cnt
    have ex : (T.filter (fun i => tag i=tag e)).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨j,hj'⟩ := ex
    obtain ⟨hj,htag⟩ := Finset.mem_filter.mp hj'
    have allDis := Finset.disjoint_left.mp dis
    have je : j ≠ e := by
      rintro rfl
      exact allDis (Finset.mem_insert_self _ _) hj
    have jS : j ∉ S := fun h => allDis (Finset.mem_insert_of_mem h) hj
    have eT : e ∉ T := allDis (Finset.mem_insert_self _ _)
    have newdis : Disjoint S (T.erase j) := Finset.disjoint_left.mpr fun i hi hi' =>
      allDis (Finset.mem_insert_of_mem hi) (Finset.mem_of_mem_erase hi')
    have newcount (a : α) : (S.filter (fun i => tag i=a)).card ≤
        ((T.erase j).filter (fun i => tag i=a)).card := by
      have h := hcount a
      rw [ins_count tag S e he] at h
      have hr := ins_count tag (T.erase j) j (Finset.notMem_erase _ _) a
      rw [Finset.insert_erase hj,htag] at hr
      omega
    obtain ⟨f,inv,mapS,used,oldcard⟩ := ih (T.erase j) newdis newcount
    have fixed (i : Fin m) (hiS : i ∉ S) (hiT : i ∉ T.erase j) : f i = i := by
      by_contra ne
      rcases used i ne with h|h
      · exact hiS h
      · have ht := (mapS _ h).1
        rw [inv] at ht
        exact hiT ht
    have fe : f e=e := fixed e he (fun h => eT (Finset.mem_of_mem_erase h))
    have fj : f j=j := fixed j jS (Finset.notMem_erase _ _)
    let g (i : Fin m) := if i=e then j else if i=j then e else f i
    have ge : g e=j := by simp [g]
    have gj : g j=e := by simp [g,je]
    have other (i : Fin m) (hi : i≠e) (hj₂ : i≠j) : g i=f i := by simp [g,hi,hj₂]
    have invol : Function.Involutive g := by
      intro i
      by_cases hi : i=e
      · subst i; rw [ge,gj]
      by_cases hj₂ : i=j
      · subst i; rw [gj,ge]
      have ei : f i ≠ e := fun eq => hi (inv.injective (eq.trans fe.symm))
      have ji : f i ≠ j := fun eq => hj₂ (inv.injective (eq.trans fj.symm))
      rw [other i hi hj₂,other _ ei ji,inv]
    refine ⟨g,invol,?_,?_,?_⟩
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl|hi
      · simpa [ge] using And.intro hj htag
      · rw [other i (fun eq => he (eq ▸ hi)) (fun eq => jS (eq ▸ hi))]
        exact ⟨Finset.mem_of_mem_erase (mapS i hi).1,(mapS i hi).2⟩
    · intro i ne
      by_cases hi : i=e
      · exact Or.inl (Finset.mem_insert.mpr (Or.inl hi))
      by_cases hj₂ : i=j
      · subst i; exact Or.inr (by simp [gj])
      rw [other i hi hj₂] at ne ⊢
      exact (used i ne).imp Finset.mem_insert_of_mem Finset.mem_insert_of_mem
    · let F := Finset.univ.filter (fun i => f i=i)
      have eF : e ∈ F := by simp [F,fe]
      have jF : j ∈ F.erase e := by simp [F,je,fj]
      have eq : Finset.univ.filter (fun i => g i=i) = (F.erase e).erase j := by
        ext i
        by_cases h : i=e
        · subst i; simp [ge,je]
        by_cases hj₂ : i=j
        · subst i; simp [gj,Ne.symm je]
        simp [F,other i h hj₂,h,hj₂]
      have c1 := Finset.card_erase_add_one eF
      have c2 := Finset.card_erase_add_one jF
      change F.card + 2*S.card=m at oldcard
      unfold nfixed
      rw [eq,Finset.card_insert_of_notMem he]
      omega

theorem lower_pair {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) (b : Cube m)
    (D : Finset (Fin m)) (hD : D ∈ words A b) (f : Fin m → Fin m) (inv : Function.Involutive f)
    (ok : ∀ e, f e ≠ e → ∃ x, fails A b x = {e,f e}) :
    2*D.card ≤ m + nfixed f := by
  classical
  let P := D.filter (fun e => f e ≠ e)
  have sub : P.image f ⊆ Finset.univ \ D := by
    intro j hj
    obtain ⟨e,hp,rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨he,ne⟩ := Finset.mem_filter.mp hp
    have eq := (pair_iff A b e (f e) ne.symm ⟨D,hD⟩).mp (ok e ne) D hD
    simp only [bit,if_pos he] at eq
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro h
    rw [if_pos h] at eq
    exact (by decide : (1:ZMod 2)+1≠1) eq
  have count := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ inv.injective,Finset.card_sdiff_of_subset (Finset.subset_univ D),
    Finset.card_univ,Fintype.card_fin] at count
  have add := Finset.card_filter_add_card_filter_not (s:=D) (fun e => f e=e)
  have fixed_le : (D.filter (fun e => f e=e)).card ≤ nfixed f :=
    Finset.card_le_card (fun e he => Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp he).2⟩)
  have max := Finset.card_le_univ D
  simp only [Fintype.card_fin] at max
  have same : (D.filter (fun a => ¬ f a = a)) = P := by ext i; simp [P]
  rw [same] at add
  omega


def supportAll {m n : ℕ} (A : Fin m → Cube n) (b : Cube m) := (words A b).biUnion id

theorem bit_zero {m : ℕ} {D : Finset (Fin m)} {e : Fin m} : bit D e = 0 ↔ e ∉ D := by
  by_cases h : e∈D <;> simp [bit,h]

theorem bit_one {m : ℕ} {D : Finset (Fin m)} {e : Fin m} : bit D e = 1 ↔ e ∈ D := by
  by_cases h : e∈D <;> simp [bit,h]

theorem active_eq {m n d : ℕ} (A : Fin m → Cube n) (b : Cube m) (r : Fin m → Cube d) (o : Cube m)
    (into : ∀ x, supp (word r o x) ∈ words A b)
    (onto : ∀ D ∈ words A b, ∃ x, supp (word r o x)=D)
    (avoid : ∀ e, ∃ D ∈ words A b, e ∉ D) :
    (∀ e, r e=0 → o e=0) ∧ (∀ e, e ∈ supportAll A b ↔ r e≠0) := by
  classical
  have oz (e : Fin m) (re : r e=0) : o e=0 := by
    obtain ⟨D,hD,no⟩ := avoid e
    obtain ⟨x,rfl⟩ := onto D hD
    have eq := bit_zero.mpr no
    simpa [bit_supp,word,re] using eq
  refine ⟨oz,?_⟩
  intro e
  constructor
  · rintro he re
    obtain ⟨D,hD,inc⟩ := Finset.mem_biUnion.mp he
    obtain ⟨x,rfl⟩ := onto D hD
    have good : bit (supp (word r o x)) e = 1 := bit_one.mpr inc
    simp [bit_supp,word,re,oz e re] at good
  · intro ne
    by_contra absent
    have never (x : Cube d) : word r o x e=0 := by
      rw [← bit_supp (word r o x)]
      exact bit_zero.mpr (fun h => absent (Finset.mem_biUnion.mpr ⟨_,into x,h⟩))
    have bo : o e=0 := by simpa [word] using never 0
    apply ne
    funext j
    simpa [word,bo] using never (Pi.single j 1)

theorem class_pairing {m n d : ℕ} (A : Fin m → Cube n) (b : Cube m) (r : Fin m → Cube d) (o : Cube m)
    (into : ∀ x, supp (word r o x) ∈ words A b)
    (onto : ∀ D ∈ words A b, ∃ x, supp (word r o x)=D)
    (oz : ∀ e, r e=0 → o e=0) (act : ∀ e, e ∈ supportAll A b ↔ r e≠0)
    (z : Cube d) (bias : ∀ a, a≠0 → 0 ≤ bal r o a * ch a z) :
    ∃ f : Fin m → Fin m, Function.Involutive f ∧
      (∀ e, f e ≠ e → ∃ x, fails A b x={e,f e}) ∧
      nfixed f + 2*((supportAll A b).card-weight r o z)=m := by
  classical
  let S := Finset.univ.filter fun i => r i≠0 ∧ word r o z i=0
  let T := Finset.univ.filter fun i => r i≠0 ∧ word r o z i=1
  have dis : Disjoint S T := Finset.disjoint_left.mpr (by
    intro e hS hT
    have x := (Finset.mem_filter.mp hS).2.2
    have y := (Finset.mem_filter.mp hT).2.2
    exact zero_ne_one (x.symm.trans y))
  have combined : S ∪ T = supportAll A b := by
    ext i
    rw [act]
    simp only [Finset.mem_union,S,T,Finset.mem_filter,Finset.mem_univ,true_and]
    rcases binary (word r o z i) with eq|eq <;> simp [eq]
  have T_eq : T = supp (word r o z) := by
    ext i
    simp only [T,supp,Finset.mem_filter,Finset.mem_univ,true_and,and_iff_right_iff_imp]
    intro y re
    simp [word,re,oz i re] at y
  have st : S.card+T.card=(supportAll A b).card := by rw [← combined,Finset.card_union_of_disjoint dis]
  have tc : T.card = weight r o z := by rw [T_eq]; rfl
  have caseset (a : Cube d) (v : ZMod 2) (ha : a ≠ 0) :
      ((Finset.univ.filter fun i => r i ≠ 0 ∧ word r o z i = v).filter (fun i => r i=a)) =
      Finset.univ.filter (fun i => r i=a ∧ dotProduct a z + o i=v) := by
    ext i
    constructor
    · intro hi
      obtain ⟨hl,hh⟩ := Finset.mem_filter.mp hi
      have hv := (Finset.mem_filter.mp hl).2.2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh,by simpa [word,hh] using hv⟩
    · intro hi
      obtain ⟨hh,hv⟩ := (Finset.mem_filter.mp hi).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun eq => ha (hh.symm.trans eq),?_⟩,hh⟩
      simpa [word,hh] using hv
  have count (a : Cube d) : (S.filter (fun i => r i=a)).card ≤ (T.filter (fun i => r i=a)).card := by
    by_cases ha : a=0
    · subst a
      have em : S.filter (fun i => r i=0) = ∅ := by
        ext i
        simp only [Finset.mem_filter,S,Finset.mem_univ,true_and,Finset.notMem_empty,iff_false]
        tauto
      rw [em,Finset.card_empty]
      exact Nat.zero_le _
    have cmp := bias a ha
    change ((Finset.univ.filter _).filter _).card ≤ ((Finset.univ.filter _).filter _).card
    rw [caseset a 0 ha,caseset a 1 ha]
    have flip0 (u : ZMod 2) : (1+u=0) ↔ u=1 := by revert u; decide
    have flip1 (u : ZMod 2) : (1+u=1) ↔ u=0 := by revert u; decide
    rcases binary (dotProduct a z) with h|h
    · simp only [h,zero_add]
      simp [ch,sgn,h,bal] at cmp
      omega
    · simp only [h,flip0,flip1]
      simp [ch,sgn,h,bal] at cmp
      omega
  obtain ⟨f,iv,lf,use,cnt⟩ := build_pairs r S T dis count
  have pair (e j : Fin m) (he : e ∈ S) (hj : j ∈ T) (same : r j=r e) (ne : j≠e) :
      ∃ x, fails A b x={e,j} := by
    apply (pair_iff A b e j ne.symm ⟨_,into z⟩).mpr
    intro D hD
    obtain ⟨x,rfl⟩ := onto D hD
    rw [bit_supp]
    have ze := (Finset.mem_filter.mp he).2.2
    have zj := (Finset.mem_filter.mp hj).2.2
    change dotProduct (r e) z + o e=0 at ze
    change dotProduct (r j) z + o j=1 at zj
    change (dotProduct (r e) x + o e) + (dotProduct (r j) x + o j) = 1
    rw [same] at zj ⊢
    generalize dotProduct (r e) z = c at ze zj
    generalize dotProduct (r e) x = t
    generalize o e = u at ze ⊢
    generalize o j = v at zj ⊢
    revert c t u v
    decide
  refine ⟨f,iv,?_,?_⟩
  · intro e ne
    rcases use e ne with he|he
    · exact pair _ _ he (lf e he).1 (lf e he).2 ne
    · have hp := pair _ _ he (lf _ he).1 (lf _ he).2 (by rw [iv]; exact ne.symm)
      rw [iv e] at hp
      obtain ⟨x,hx⟩ := hp
      exact ⟨x,hx.trans (Finset.pair_comm _ _)⟩
  · omega

theorem zbal {m n d : ℕ} (A : Fin m → Cube n) (b : Cube m) (r : Fin m → Cube d) (o : Cube m)
    (oz : ∀ e, r e=0 → o e=0) (act : ∀ e, e ∈ supportAll A b ↔ r e≠0) :
    bal r o 0 = -(((Finset.univ \ supportAll A b).card : ℕ) : ℤ) := by
  classical
  have yes : Finset.univ.filter (fun i => r i=0 ∧ o i=1) = ∅ := by
    ext i
    by_cases h : r i=0 <;> simp [h,oz i]
  have no : Finset.univ.filter (fun i => r i=0 ∧ o i=0) = Finset.univ \ supportAll A b := by
    ext i
    by_cases h : r i=0 <;> simp [h,oz i,act]
  simp [bal,yes,no]

theorem nbest_unused {m n : ℕ} (A : Fin m → Cube n) (b : Cube m) (e : Fin m) (he : e ∉ supportAll A b)
    (avoid : ∀ i, ∃ D ∈ words A b, i ∉ D) (f : Fin m → Fin m) (iv : Function.Involutive f)
    (ok : ∀ i, f i≠i → ∃ x, fails A b x = {i,f i}) : 1 ≤ nfixed f := by
  classical
  have eq : f e=e := by
    by_contra h
    obtain ⟨D,hD,exc⟩ := avoid (f e)
    have ne : e ∉ D := fun h => he (Finset.mem_biUnion.mpr ⟨D,hD,h⟩)
    have z := (pair_iff A b e (f e) (Ne.symm h) ⟨D,hD⟩).mp (ok e h) D hD
    simp [bit,exc,ne] at z
  exact Finset.card_pos.mpr ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq⟩⟩


theorem count_high {m : ℕ} (W : Finset (Finset (Fin m))) (g r : ℕ) (rh : 0 < r)
    (avg : 2 * W.sum Finset.card = W.card * (2*g+1))
    (profile : ∀ D ∈ W, D.card=g ∨ D.card=g+2^(r-1)) :
    2^r * (W.filter (fun D => D.card=g+2^(r-1))).card = W.card := by
  classical
  let p : ℕ := 2^(r-1)
  have hp : 0 < p := by dsimp [p]; positivity
  have each (D) (hD : D ∈ W) : D.card = g + (if D.card=g+p then p else 0) := by
    rcases profile D hD with h|h
    · have neq : D.card≠g+p := by omega
      rw [if_neg neq,add_zero,h]
    · rw [if_pos h,h]
  rw [Finset.sum_congr rfl each,Finset.sum_add_distrib,← Finset.sum_filter] at avg
  simp only [Finset.sum_const,nsmul_eq_mul] at avg
  have power : 2^r = p*2 := by
    conv_lhs => rw [← Nat.sub_add_cancel rh]
    rw [pow_succ]
  rw [power]
  dsimp only [p] at *
  nlinarith

end PEqualNP.Outside.L_lib_640_aux

open PEqualNP.Outside.L_lib_640_aux in
theorem PEqualNP.Outside.L_lib_640 : ∀ (n m : ℕ) (A : Fin m → Fin n → ZMod 2) (b : Fin m → ZMod 2),
  let faults := fun x : Fin n → ZMod 2 =>
    Finset.univ.filter (fun e => (∑ j, A e j * x j) ≠ b e)
  let W := Finset.univ.filter (fun D : Finset (Fin m) =>
    (∀ j, D.sum (fun e => A e j) = 0) ∧ D.sum b = 1)
  let best := fun loss : ℕ => IsLeast
    {k : ℕ | ∃ mate : Fin m → Fin m, Function.Involutive mate ∧
      (Finset.univ.filter (fun i => mate i = i)).card = k ∧
      ∀ e, mate e ≠ e → ∃ word, faults word = {e, mate e}} loss
  (∀ x, (faults x).Nonempty) → (∀ i, ∀ x, ∃ j ∈ faults x, j ≠ i) →
  ∀ g : ℕ, m = 2*g+1 → (∀ D ∈ W, g ≤ D.card) →
    W.Nonempty ∧
    (((Finset.univ \ W.biUnion id).card = 1 ∧ (∀ D ∈ W, D.card = g) ∧ best 1) ∨
     (W.biUnion id = Finset.univ ∧ ∃ r : ℕ, 0 < r ∧
       (∀ D ∈ W, D.card = g ∨ D.card = g+2^(r-1)) ∧
       2^r * (W.filter (fun D => D.card = g+2^(r-1))).card = W.card ∧
       best (2^r-1))) := by
  classical
  intro n m A b faults W best non robust g odd lower
  change (words A b).Nonempty ∧
    (((Finset.univ \ supportAll A b).card = 1 ∧ (∀ D ∈ words A b, D.card=g) ∧ bestLoss A b 1) ∨
     (supportAll A b = Finset.univ ∧ ∃ r : ℕ, 0 < r ∧
       (∀ D ∈ words A b, D.card=g ∨ D.card=g+2^(r-1)) ∧
       2^r * ((words A b).filter (fun D => D.card=g+2^(r-1))).card = (words A b).card ∧ bestLoss A b (2^r-1)))
  have all := average n m A b
  have bad : ¬ ∃ x : Cube n, ∀ e ∈ (Finset.univ : Finset (Fin m)), dotProduct (A e) x = b e := by
    rintro ⟨x,hx⟩
    obtain ⟨i,hi⟩ := non x
    exact (Finset.mem_filter.mp hi).2 (hx _ (Finset.mem_univ _))
  have single (e : Fin m) : ¬ ∃ x : Cube n, ∀ i ∈ (Finset.univ.erase e), dotProduct (A i) x = b i := by
    rintro ⟨x,hx⟩
    obtain ⟨i,hi,ne⟩ := robust e x
    exact (Finset.mem_filter.mp hi).2 (hx _ (Finset.mem_erase.mpr ⟨ne,Finset.mem_univ _⟩))
  have stats := all bad single
  have hnon : (words A b).Nonempty := stats.1
  have avoid (i : Fin m) : ∃ D ∈ words A b, i ∉ D := by
    by_contra! everything
    obtain ⟨D,hD⟩ := hnon
    have covered : i ∈ supportAll A b := Finset.mem_biUnion.mpr ⟨D,hD,everything _ hD⟩
    have half : 2*((words A b).filter (fun s => i ∈ s)).card = (words A b).card := stats.2.1 i covered
    have allwords : (words A b).filter (fun s => i ∈ s) = words A b := Finset.filter_eq_self.mpr everything
    rw [allwords] at half
    have pos := Finset.card_pos.mpr (show (words A b).Nonempty from ⟨D,hD⟩)
    omega
  obtain ⟨d,row,off,into,onto⟩ := parametrize A b hnon
  obtain ⟨oz,act⟩ := active_eq A b row off into onto avoid
  have point (x : Cube d) : g ≤ weight row off x := lower _ (into x)
  have mean := stats.2.2 (fun _ => 1)
  have avg : 2*(words A b).sum Finset.card = (words A b).card * (supportAll A b).card := by
    simpa [words,supportAll] using mean.1
  obtain ⟨D,hD,hmin⟩ := mean.2
  have least : 2*D.card ≤ (supportAll A b).card := by
    simpa [words,supportAll] using hmin
  have lb : g≤D.card := lower D hD
  have width : (supportAll A b).card ≤ m := by simpa using Finset.card_le_univ (supportAll A b)
  have gap := Finset.card_sdiff_of_subset (Finset.subset_univ (supportAll A b))
  rw [Finset.card_univ,Fintype.card_fin] at gap
  refine ⟨hnon,?_⟩
  by_cases full : supportAll A b = Finset.univ
  · right
    have active : ∀ e, row e ≠ 0 := fun e => (act e).mp (full ▸ Finset.mem_univ _)
    obtain ⟨U,z,rpos,balances,weights⟩ := odd_profile row off active odd point
    let r := Module.finrank (ZMod 2) U
    have rp : 0 < r := rpos
    have power : (2:ℕ)^r = 2^(r-1)*2 := by
      conv_lhs => rw [← Nat.sub_add_cancel rp]
      rw [pow_succ]
    have pgt : 0 < (2:ℕ)^(r-1) := by positivity
    have profile (D) (hd : D ∈ words A b) : D.card=g ∨ D.card=g+2^(r-1) := by
      obtain ⟨x,rfl⟩ := onto D hd
      change weight row off x = _ ∨ weight row off x = _
      rw [weights x]
      split_ifs <;> simp [r]
    have high : weight row off z = g+2^(r-1) := by simpa [r] using weights z
    have bias (a : Cube d) (ha : a ≠ 0) : 0 ≤ bal row off a * ch a z := by
      rw [balances]
      by_cases h : a∈U
      · rw [if_pos ⟨h,ha⟩]; change 0 ≤ sgn _ * sgn _; rw [square]; decide
      · simp [h]
    have width' : (supportAll A b).card=m := by simp [full]
    have avg' := avg.trans (congrArg (fun k => (words A b).card * k) (width'.trans odd))
    refine ⟨full,r,rp,profile,count_high _ g r rp avg' profile,?_⟩
    obtain ⟨f,iv,ok,count⟩ := class_pairing A b row off into onto oz act z bias
    have hweight : weight row off z ≤ m := by
      unfold weight
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)
    have nf : nfixed f=2^r-1 := by rw [width',high] at count; omega
    refine ⟨⟨f,iv,nf,ok⟩,?_⟩
    rintro k ⟨h,hi,hk,hok⟩
    have cz : (supp (word row off z)).card = g+2^(r-1) := high
    have lim := lower_pair A b _ (into z) h hi hok
    rw [cz,hk] at lim
    omega
  · left
    have strict : (supportAll A b).card < m := by
      by_contra! ge
      apply full
      exact Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simpa using ge)
    have uc : (supportAll A b).card=2*g := by omega
    have gc : (Finset.univ \ supportAll A b).card=1 := by omega
    have bz := zbal A b row off oz act
    rw [gc] at bz
    have z0 : bump (bal row off) 0 = 0 := by simp [bump,bz]
    have nonneg (x : Cube d) : 0 ≤ transform (bump (bal row off)) x := by
      rw [transform_bump,weight_formula]
      have hx := point x
      omega
    have zero := zero_of_sign _ z0 nonneg
    have weightg (x : Cube d) : weight row off x=g := by
      have h : transform (bump (bal row off)) x = 0 := by simp [transform,zero]
      rw [transform_bump,weight_formula] at h
      omega
    have profile (D) (hd : D∈words A b) : D.card=g := by
      obtain ⟨x,rfl⟩ := onto _ hd
      exact weightg x
    have bias (a : Cube d) (ha : a ≠ 0) : 0≤bal row off a*ch a 0 := by
      have h := zero a
      simp [bump,ha] at h
      simp [h]
    obtain ⟨f,iv,ok,cnt⟩ := class_pairing A b row off into onto oz act 0 bias
    have nf : nfixed f = 1 := by rw [uc,weightg] at cnt; omega
    obtain ⟨e,he⟩ := Finset.card_pos.mp (show 0 < (Finset.univ \ supportAll A b).card by omega)
    refine ⟨gc,profile,⟨f,iv,nf,ok⟩,?_⟩
    rintro k ⟨q,iq,hk,hq⟩
    rw [← hk]
    exact nbest_unused A b e (Finset.mem_sdiff.mp he).2 avoid q iq hq

