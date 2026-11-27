import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_343_aux

lemma prefix_getD (a b : List Bool) (h : a <+: b) (i : ℕ) (hi : i<a.length) :
    b.getD i false=a.getD i false := by
  obtain ⟨t,ht⟩ := h
  rw [←ht]
  exact List.getD_append _ _ _ _ hi

lemma prefix_eq_of_ge (a b : List Bool) (h : a <+: b) (hlen : b.length≤a.length) :
    a=b := by
  obtain ⟨t,ht⟩ := h
  have hz : t.length=0 := by
    have hh := congrArg List.length ht
    simp only [List.length_append] at hh
    omega
  have ht0 : t=[] := List.length_eq_zero_iff.mp hz
  simpa [ht0] using ht

lemma prefix_block_card (L : ℕ) (a : List Bool) :
    ((Finset.univ : Finset (Fin L → Bool)).filter (fun x => a <+: List.ofFn x)).card
      ≤ 2^(L-a.length) := by
  classical
  let A := (Finset.univ : Finset (Fin L → Bool)).filter (fun x => a <+: List.ofFn x)
  let tail : (Fin L → Bool) → (Fin (L-a.length) → Bool) :=
    fun x j => x ⟨a.length+j.val,by omega⟩
  have hinj : Function.Injective (fun x : ↥A => tail x.val) := by
    intro x y h
    apply Subtype.ext
    funext i
    by_cases hi : i.val<a.length
    · have hx := prefix_getD a (List.ofFn x.val) (Finset.mem_filter.mp x.property).2 i.val hi
      have hy := prefix_getD a (List.ofFn y.val) (Finset.mem_filter.mp y.property).2 i.val hi
      have hh := hx.trans hy.symm
      simpa using hh
    · have hj : i.val-a.length<L-a.length := by omega
      have hh := congrFun h (⟨i.val-a.length,hj⟩ : Fin (L-a.length))
      change x.val ⟨a.length+(i.val-a.length),_⟩=
        y.val ⟨a.length+(i.val-a.length),_⟩ at hh
      have he : a.length+(i.val-a.length)=i.val := by omega
      simpa only [he] using hh
  have hh := Fintype.card_le_of_injective _ hinj
  change A.card ≤ _
  change Fintype.card ↥A ≤ Fintype.card (Fin (L-a.length) → Bool) at hh
  simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] using hh

lemma kraft_budget {k : ℕ} (L : ℕ) (l : Fin k → ℕ) (hl : ∀ i, l i≤L)
    (h : ((1:ℚ)/2)^L+∑ i,((1:ℚ)/2)^(l i)≤1) :
    (∑ i,2^(L-l i))+1≤2^L := by
  have hscale (n : ℕ) (hn : n≤L) :
      (2:ℚ)^L*(((1:ℚ)/2)^n)=(2:ℚ)^(L-n) := by
    rw [div_pow,one_pow,mul_one_div]
    have hnz : (2:ℚ)^n≠0 := pow_ne_zero _ (by norm_num)
    apply (div_eq_iff hnz).mpr
    rw [←pow_add,Nat.sub_add_cancel hn]
  have hm := mul_le_mul_of_nonneg_left h (by positivity : 0≤(2:ℚ)^L)
  rw [mul_add,Finset.mul_sum,hscale L (by omega)] at hm
  simp_rw [hscale _ (hl _)] at hm
  simp only [Nat.sub_self,pow_zero,mul_one] at hm
  have hn : (∑ i,(2:ℚ)^(L-l i))+1≤(2:ℚ)^L := by linarith
  exact_mod_cast hn

lemma fresh_word {k : ℕ} (L : ℕ) (c : Fin k → List Bool)
    (h : (∑ i,2^(L-(c i).length))+1≤2^L) :
    ∃ w : List Bool, w.length=L ∧ ∀ i, ¬(c i <+: w) := by
  classical
  let A : Fin k → Finset (Fin L → Bool) :=
    fun i => Finset.univ.filter (fun x => c i <+: List.ofFn x)
  let bad := Finset.univ.biUnion A
  have hsum : ∑ i,(A i).card ≤ ∑ i,2^(L-(c i).length) := by
    apply Finset.sum_le_sum
    intro i hi
    exact prefix_block_card L (c i)
  have hb : bad.card<2^L := by
    have hu := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin k))) (t := A)
    dsimp [bad]
    omega
  have hex : ∃ x : Fin L → Bool, x∉bad := by
    by_contra hn
    push Not at hn
    have hi : (Finset.univ : Finset (Fin L → Bool))⊆bad := by intro x hx; exact hn x
    have hc := Finset.card_le_card hi
    simp only [Finset.card_univ,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] at hc
    omega
  obtain ⟨x,hx⟩ := hex
  refine ⟨List.ofFn x,by simp,?_⟩
  intro i hp
  apply hx
  apply Finset.mem_biUnion.mpr
  exact ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩⟩

lemma construct : ∀ (k : ℕ) (l : Fin k → ℕ), (∑ i,((1:ℚ)/2)^(l i))≤1 →
    ∃ c : Fin k → List Bool, (∀ i,(c i).length=l i) ∧
      ∀ i j,i≠j → ¬(c i <+: c j) := by
  classical
  intro k
  induction k with
  | zero =>
    intro l h
    refine ⟨Fin.elim0,?_,?_⟩
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
  | succ k ih =>
    intro l h
    obtain ⟨m,hm,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin (k+1))) l
      ⟨0,Finset.mem_univ _⟩
    let L := l m
    let rest : Fin k → ℕ := fun i => l (m.succAbove i)
    have hsplit := Fin.sum_univ_succAbove (fun i => ((1:ℚ)/2)^(l i)) m
    have hbudget : ((1:ℚ)/2)^L+∑ i,((1:ℚ)/2)^(rest i)≤1 := by
      dsimp [L,rest]
      linarith
    have hpos : 0≤((1:ℚ)/2)^L := by positivity
    have hrest : (∑ i,((1:ℚ)/2)^(rest i))≤1 := by linarith
    obtain ⟨c,hc,hpf⟩ := ih rest hrest
    have hlen : ∀ i, rest i≤L := fun i => hmax _ (Finset.mem_univ _)
    have hnat : (∑ i,2^(L-(c i).length))+1≤2^L := by
      simp_rw [hc]
      exact kraft_budget L rest hlen hbudget
    obtain ⟨w,hw,hfresh⟩ := fresh_word L c hnat
    let C : Fin (k+1) → List Bool := m.insertNth w c
    refine ⟨C,?_,?_⟩
    · refine (Fin.forall_iff_succAbove (P := fun i => (C i).length=l i) m).mpr ?_
      constructor
      · simpa [C,L] using hw
      · intro i
        simpa [C,rest] using hc i
    · intro i j hij hp
      rcases Fin.eq_self_or_eq_succAbove m i with hi|⟨u,hi⟩
      · rcases Fin.eq_self_or_eq_succAbove m j with hj|⟨v,hj⟩
        · exact hij (hi.trans hj.symm)
        · have hh : w <+: c v := by simpa [hi,hj,C] using hp
          have heq : w=c v := prefix_eq_of_ge w (c v) hh (by rw [hc v,hw]; exact hlen v)
          apply hfresh v
          rw [heq]
      · rcases Fin.eq_self_or_eq_succAbove m j with hj|⟨v,hj⟩
        · exact hfresh u (by simpa [hi,hj,C] using hp)
        · have huv : u≠v := by
            intro he
            apply hij
            exact hi.trans ((congrArg m.succAbove he).trans hj.symm)
          exact hpf u v huv (by simpa [hi,hj,C] using hp)

def shape (N J : Finset (List Bool)) : Prop :=
  [] ∈ N ∧ J ⊆ N ∧
  (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
  ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N

lemma shape_leaf : shape {[]} ∅ := by
  refine ⟨by simp, by simp, ?_, ?_⟩
  · intro p b h
    simp only [Finset.mem_singleton] at h
    have := congrArg List.length h
    simp at this
  · intro p hp
    exact absurd hp (Finset.notMem_empty _)

lemma shape_combine {N0 J0 N1 J1 : Finset (List Bool)}
    (h0 : shape N0 J0) (h1 : shape N1 J1) :
    shape (insert [] (N0.image (false :: ·) ∪ N1.image (true :: ·)))
      (insert [] (J0.image (false :: ·) ∪ J1.image (true :: ·))) := by
  refine ⟨Finset.mem_insert_self _ _, ?_, ?_, ?_⟩
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp ⊢
    rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · left; rfl
    · right; left; exact ⟨q, h0.2.1 hq, rfl⟩
    · right; right; exact ⟨q, h1.2.1 hq, rfl⟩
  · intro p b hp
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp ⊢
    rcases hp with hnil | ⟨q, hq, hEq⟩ | ⟨q, hq, hEq⟩
    · have := congrArg List.length hnil; simp at this
    · cases p with
      | nil => left; rfl
      | cons d rest =>
        simp only [List.cons_append, List.cons.injEq] at hEq
        rcases hEq with ⟨rfl, rfl⟩
        right; left; exact ⟨rest, h0.2.2.1 rest b hq, rfl⟩
    · cases p with
      | nil => left; rfl
      | cons d rest =>
        simp only [List.cons_append, List.cons.injEq] at hEq
        rcases hEq with ⟨rfl, rfl⟩
        right; right; exact ⟨rest, h1.2.2.1 rest b hq, rfl⟩
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp ⊢
    rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · constructor
      · right; left; exact ⟨[], h0.1, rfl⟩
      · right; right; exact ⟨[], h1.1, rfl⟩
    · constructor
      · right; left; exact ⟨q ++ [false], (h0.2.2.2 q hq).1, rfl⟩
      · right; left; exact ⟨q ++ [true], (h0.2.2.2 q hq).2, rfl⟩
    · constructor
      · right; right; exact ⟨q ++ [false], (h1.2.2.2 q hq).1, rfl⟩
      · right; right; exact ⟨q ++ [true], (h1.2.2.2 q hq).2, rfl⟩

lemma sdiff_combine (N0 J0 N1 J1 : Finset (List Bool)) :
    insert [] (N0.image (false :: ·) ∪ N1.image (true :: ·)) \
      insert [] (J0.image (false :: ·) ∪ J1.image (true :: ·)) =
    (N0 \ J0).image (false :: ·) ∪ (N1 \ J1).image (true :: ·) := by
  ext p
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩, hnot⟩
    · exact absurd (Or.inl rfl) hnot
    · left; refine ⟨q, ⟨hq, fun hqJ => hnot (Or.inr (Or.inl ⟨q, hqJ, rfl⟩))⟩, rfl⟩
    · right; refine ⟨q, ⟨hq, fun hqJ => hnot (Or.inr (Or.inr ⟨q, hqJ, rfl⟩))⟩, rfl⟩
  · rintro (⟨q, ⟨hqN, hqJ⟩, rfl⟩ | ⟨q, ⟨hqN, hqJ⟩, rfl⟩)
    · refine ⟨Or.inr (Or.inl ⟨q, hqN, rfl⟩), ?_⟩
      rintro (h | ⟨q', hq', hEq⟩ | ⟨q', _, hEq⟩)
      · cases h
      · exact hqJ ((List.cons.inj hEq).2 ▸ hq')
      · exact Bool.noConfusion (List.cons.inj hEq).1
    · refine ⟨Or.inr (Or.inr ⟨q, hqN, rfl⟩), ?_⟩
      rintro (h | ⟨q', _, hEq⟩ | ⟨q', hq', hEq⟩)
      · cases h
      · exact Bool.noConfusion (List.cons.inj hEq).1
      · exact hqJ ((List.cons.inj hEq).2 ▸ hq')

lemma disjoint_cons_images (S0 S1 : Finset (List Bool)) :
    Disjoint (S0.image (false :: ·)) (S1.image (true :: ·)) := by
  rw [Finset.disjoint_left]
  intro p h0 h1
  obtain ⟨q0, _, rfl⟩ := Finset.mem_image.mp h0
  obtain ⟨q1, _, hEq⟩ := Finset.mem_image.mp h1
  exact Bool.noConfusion (List.cons.inj hEq).1

theorem prefix_inner (N J : Finset (List Bool)) (hs : shape N J) (p : List Bool) (hp : p∈N)
    (j : ℕ) (hj : j<p.length) : p.take j∈J := by
  induction p using List.reverseRecOn generalizing j with
  | nil => simp at hj
  | append_singleton l b ih =>
    have hi := hs.2.2.1 l b hp
    have bound : j ≤ l.length := by simp at hj; omega
    rw [List.take_append_of_le_length bound]
    rcases bound.eq_or_lt with h|h
    · simpa [h] using hi
    · exact ih (hs.2.1 hi) _ h

theorem query_leaf {V : Type} (N J : Finset (List Bool)) (hs : shape N J) (q : List Bool→V) (x : V→Bool) :
    ∃ p∈N\J,∀ j : Fin p.length,p.get j=x (q (p.take j.val)) := by
  classical
  let ok := fun p : List Bool => ∀ j : Fin p.length,p.get j=x (q (p.take j.val))
  let paths := N.filter ok
  have root : []∈paths := Finset.mem_filter.mpr ⟨hs.1,by simp [ok]⟩
  obtain ⟨p,hp,mx⟩ := Finset.exists_max_image paths List.length ⟨_,root⟩
  obtain ⟨pn,op⟩ := Finset.mem_filter.mp hp
  refine ⟨p,Finset.mem_sdiff.mpr ⟨pn,?_⟩,op⟩
  intro pj
  let b := x (q p)
  have sub : p++[b]∈N := by cases e : b <;> simp [e,(hs.2.2.2 p pj).1,(hs.2.2.2 p pj).2]
  have ext : ok (p++[b]) := by
    intro i
    by_cases h : i.val<p.length
    · have z := op ⟨i.val,h⟩
      simpa only [List.get_eq_getElem,List.getElem_append_left h,List.take_append_of_le_length (Nat.le_of_lt h)] using z
    · have z : i.val=p.length := by have := i.isLt; simp at this; omega
      simp [List.get_eq_getElem,z,List.getElem_append_right (by omega : p.length ≤ i.val),b]
  have le := mx _ (Finset.mem_filter.mpr ⟨sub,ext⟩)
  simp at le


abbrev FF := ZMod 2
abbrev XX (n : ℕ) := Fin n→FF
def Aff (V : Type) [AddCommGroup V] [Module FF V] : Set (V→Bool) :=
  {f | ∃(l : V→ₗ[FF] FF)(b : FF),f=fun x=>decide (l x=b)}
def Run {V : Type} (q : List Bool→V→Bool) (p : List Bool) (x : V) := ∀ j : Fin p.length,q (p.take j.val) x=p.get j
def TreeFits {V O : Type} (qs : Set (V→Bool)) (ok : V→O→Prop) (depth fee : O→ℕ) (H K : ℕ) :=
  ∃ (N J : Finset (List Bool)) (q : List Bool→V→Bool) (out : List Bool→O),
    (shape N J ∧ (∀ p∈J,q p∈qs) ∧ ∀ p∈N\J,∀ x,Run q p x → ok x (out p)) ∧
    (∀ p∈N\J,p.length+depth (out p) ≤ H) ∧ (N\J).sum (fun p=>fee (out p)) ≤ K

lemma prefixes {a b w : List Bool} (ha : a <+: w) (hb : b <+: w) (len : a.length ≤ b.length) : a <+: b := by
  obtain ⟨c,ec⟩ := ha; obtain ⟨d,ed⟩ := hb
  have e : a=b.take a.length := by
    calc
      a=(a++c).take a.length := by simp
      _=(b++d).take a.length := by rw [ec,ed]
      _=b.take a.length := List.take_append_of_le_length len
  rw [e]; exact List.take_prefix ..
lemma leaf_prefix_free {N J : Finset (List Bool)} (s : shape N J) {p q : List Bool} (hp : p∈N\J) (hq : q∈N\J)
    (pref : p <+: q) : p=q := by
  by_contra ne
  have len : p.length < q.length := by
    by_contra no; exact ne (prefix_eq_of_ge _ _ pref (by omega))
  obtain ⟨t,et⟩ := pref
  have prefJ := prefix_inner N J s q (Finset.mem_sdiff.mp hq).1 p.length len
  rw [←et,List.take_left] at prefJ
  exact (Finset.mem_sdiff.mp hp).2 prefJ

theorem wide_kraft (N J : Finset (List Bool)) (sh : shape N J) (H : ℕ) (height : ∀ p∈N\J,p.length ≤ H) :
    (N\J).sum (fun p=>2^(H-p.length)) ≤ 2^H := by
  classical
  let ext := fun p : List Bool=>(Finset.univ : Finset (Fin (H-p.length)→Bool)).image (fun f=>p++List.ofFn f)
  have cnt (p : List Bool) : (ext p).card=2^(H-p.length) := by
    have inj : Function.Injective (fun f : Fin (H-p.length)→Bool=>p++List.ofFn f) := fun _ _ e=>List.ofFn_inj.mp (List.append_cancel_left e)
    simp [ext,Finset.card_image_of_injective _ inj]
  have dis : (↑(N\J) : Set (List Bool)).PairwiseDisjoint ext := by
    intro a ha b hb ne; change Disjoint (ext a) (ext b); rw [Finset.disjoint_left]
    intro z za zb
    obtain ⟨fa,_,ea⟩ := Finset.mem_image.mp za; obtain ⟨fb,_,eb⟩ := Finset.mem_image.mp zb
    have az : a <+: z := ⟨_,ea⟩
    have bz : b <+: z := ⟨_,eb⟩
    rcases le_total a.length b.length with eq|eq
    · exact ne (leaf_prefix_free sh ha hb (prefixes az bz eq))
    · exact ne (leaf_prefix_free sh hb ha (prefixes bz az eq)).symm
  let all := (Finset.univ : Finset (Fin H→Bool)).image List.ofFn
  have sub : (N\J).biUnion ext ⊆ all := by
    intro z hz
    obtain ⟨p,hp,hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨f,_,rfl⟩ := Finset.mem_image.mp hz
    have length : (p++List.ofFn f).length=H := by simp; have := height p hp; omega
    let xs := p++List.ofFn f
    let word := fun j : Fin H=>xs.getD j.val false
    apply Finset.mem_image.mpr
    refine ⟨word,Finset.mem_univ _,?_⟩
    apply List.ext_getElem
    · simpa [xs] using length.symm
    · intro i hi hr; simp [word,xs,List.getElem?_eq_getElem hr]
  have bound := Finset.card_le_card sub
  rw [Finset.card_biUnion dis] at bound
  simp_rw [cnt] at bound
  have allsize : all.card  ≤  2^H := (Finset.card_image_le).trans (by simp)
  exact bound.trans allsize


theorem odd_subset {X : Type} [AddCommGroup X] [Module FF X] {m : ℕ} (row : Fin m→X→ₗ[FF] FF)
    (rhs : Fin m→FF) (R : Finset (Fin m)) (uns : ¬∃ x,∀ i∈R,row i x=rhs i) :
    ∃ S⊆R,S.sum row=0 ∧ S.sum rhs=1 := by
  classical
  let E : X→ₗ[FF] (↥R→FF) := LinearMap.pi fun i=>row i.val
  let target := fun i : ↥R=>rhs i.val
  have no : target∉LinearMap.range E := by
    rintro ⟨x,e⟩; exact uns ⟨x,fun i hi=>congrFun e (⟨i,hi⟩ : ↥R)⟩
  obtain ⟨f,fb,fzero⟩ := Submodule.exists_le_ker_of_notMem no
  let a := fun i : ↥R=>f (Pi.single i 1)
  have sumf (v : ↥R→FF) : (∑ i,a i*v i)=f v := by
    conv_rhs => rw [← Finset.univ_sum_single v]
    rw [map_sum]; refine Finset.sum_congr rfl ?_
    intro i _
    have eq : (Pi.single i (v i) : ↥R→FF) = v i • Pi.single i (1:FF) := by rw [←Pi.single_smul,smul_eq_mul,mul_one]
    rw [eq,map_smul,smul_eq_mul,mul_comm]
  let keep := Finset.univ.filter fun i : ↥R=>a i=1
  let emb : ↥R ↪ Fin m := ⟨Subtype.val,Subtype.val_injective⟩
  have value (v : ↥R→FF) : keep.sum v=f v := by
    rw [←sumf,Finset.sum_filter]; apply Finset.sum_congr rfl; intro i _
    by_cases e : a i=1
    · simp [e]
    · have z : a i=0 := by
        have two : ∀ z : FF,z≠1 → z=0 := by decide
        exact two _ e
      simp [z]
  refine ⟨keep.map emb,?_,?_,?_⟩
  · intro i h; obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp h; exact j.property
  · ext x
    rw [Finset.sum_map,LinearMap.sum_apply]
    exact (value (E x)).trans (fzero (show E x∈LinearMap.range E from ⟨x,rfl⟩))
  · rw [Finset.sum_map]
    exact (value target).trans ((show ∀ z : FF,z≠0 → z=1 by decide) _ fb)

theorem weighted_lower {X : Type} [AddCommGroup X] [Module FF X] {m : ℕ} (row : Fin m→X→ₗ[FF] FF)
    (rhs : Fin m→FF) (depth : Fin m→ℕ) (H K : ℕ)
    (h : TreeFits (Aff X) (fun x i=>row i x≠rhs i) depth (fun i=>2^(depth i)) H K) :
    ∃ S : Finset (Fin m), (S.sum row=0 ∧ S.sum rhs=1) ∧ S.sum (fun i=>2^depth i) ≤ K ∧ S.sum (fun i=>2^depth i) ≤ 2^H := by
  classical
  obtain ⟨N,J,q,out,⟨sh,_,valid⟩,height,cost⟩ := h
  let leaf := N\J
  let R := leaf.image out
  have uns : ¬∃ x,∀ i∈R,row i x=rhs i := by
    rintro ⟨x,hx⟩
    obtain ⟨p,hp,agree⟩ := query_leaf N J sh (fun p=>q p x) id
    exact valid p hp x (fun j=>(agree j).symm) (hx _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩))
  obtain ⟨S,sub,zero,one⟩ := odd_subset row rhs R uns
  have sc : S.sum (fun i=>2^depth i)  ≤  leaf.sum (fun p=>2^depth (out p)) := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _=>Nat.zero_le _))
    exact Finset.sum_image_le_of_nonneg (fun _ _=>Nat.zero_le _)
  refine ⟨S,⟨zero,one⟩,sc.trans cost,sc.trans ?_⟩
  have lH (p) (hp : p∈leaf) : p.length  ≤  H := by have := height p hp; omega
  apply le_trans _ (wide_kraft N J sh H lH)
  apply Finset.sum_le_sum; intro p hp
  exact Nat.pow_le_pow_right (by omega) (by have := height p hp; omega)


inductive Plan (I : Type) where
  | tip (i : I)
  | split (l r : Plan I)
def labels {I : Type} [DecidableEq I] : Plan I→Finset I
  | .tip i=>{i}
  | .split l r=>labels l ∪ labels r
def proper {I : Type} [DecidableEq I] : Plan I→Prop
  | .tip _=>True
  | .split l r=>proper l ∧ proper r ∧ Disjoint (labels l) (labels r)
def depthCost {I : Type} (d : I→ℕ) : Plan I→ℕ
  | .tip i=>d i
  | .split l r=>1+max (depthCost d l) (depthCost d r)

lemma code_plan {I : Type} [DecidableEq I] (d : I→ℕ) (H : ℕ) (S : Finset I) (c : I→List Bool) (ne : S.Nonempty)
    (pref : ∀ i∈S,∀ j∈S,i≠j → ¬ (c i <+: c j))
    (height : ∀ i∈S,(c i).length+d i ≤ H) : ∃ P : Plan I, labels P=S ∧ proper P ∧ depthCost d P ≤ H := by
  classical
  induction H generalizing S c with
  | zero =>
    obtain ⟨i,hi⟩ := ne
    have e (j) (hj : j∈S) : c j=[] := List.length_eq_zero_iff.mp (by have := height j hj; omega)
    have eq : S={i} := by
      ext j
      constructor
      · intro hj; apply Finset.mem_singleton.mpr; by_contra h
        exact pref j hj i hi h (by simp [e _ hj,e _ hi])
      · intro hj; rw [Finset.mem_singleton.mp hj]; exact hi
    exact ⟨.tip i,eq.symm,True.intro,by have := height i hi; dsimp [depthCost]; omega⟩
  | succ H ih =>
    by_cases empty : ∃ i∈S,c i=[]
    · obtain ⟨i,hi,ci⟩ := empty
      have eq : S={i} := by
        ext j; constructor
        · intro hj; apply Finset.mem_singleton.mpr; by_contra h
          exact pref i hi j hj (Ne.symm h) (by simp [ci])
        · intro hj; rw [Finset.mem_singleton.mp hj]; exact hi
      exact ⟨.tip i,eq.symm,True.intro,by have := height i hi; dsimp [depthCost]; omega⟩
    let B := fun b : Bool=>S.filter (fun i=>(c i).head?=some b)
    have cons (b : Bool) (i) (hi : i∈B b) : c i=b::(c i).tail := by
      have head := (Finset.mem_filter.mp hi).2
      cases eq : c i with
      | nil => simp [eq] at head
      | cons v t => simp [eq] at head; simp [eq,head]
    have both : S=B false∪B true := by
      ext i; constructor
      · intro hi
        cases eq : c i with
        | nil => exact False.elim (empty ⟨i,hi,eq⟩)
        | cons v t => cases v <;> simp [B,eq,hi]
      · intro h; rcases Finset.mem_union.mp h with h|h <;> exact (Finset.mem_filter.mp h).1
    have sep : Disjoint (B false) (B true) := by
      rw [Finset.disjoint_left]; intro i hl hr
      have l := (Finset.mem_filter.mp hl).2; have r := (Finset.mem_filter.mp hr).2
      rw [l] at r; contradiction
    have sub (b : Bool) (nn : (B b).Nonempty) : ∃ t : Plan I,labels t=B b ∧ proper t ∧ depthCost d t ≤ H := by
      apply ih (B b) (fun i=>(c i).tail) nn
      · intro i hi j hj ne cmp
        apply pref i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 ne
        obtain ⟨t,et⟩ := cmp
        use t
        calc
          c i ++ t = (b::(c i).tail)++t := congrArg (fun z=>z++t) (cons b i hi)
          _ = b::(c j).tail := congrArg (List.cons b) et
          _ = c j := (cons b j hj).symm
      · intro i hi
        have h := height i (Finset.mem_filter.mp hi).1
        have len := congrArg List.length (cons b i hi)
        simp only [List.length_cons] at len; omega
    by_cases nl : (B false).Nonempty
    · obtain ⟨l,el,pl,dl⟩ := sub false nl
      by_cases nr : (B true).Nonempty
      · obtain ⟨r,er,pr,dr⟩ := sub true nr
        exact ⟨.split l r,by simp [labels,el,er,both],⟨pl,pr,el ▸ er ▸ sep⟩,by dsimp [depthCost]; omega⟩
      · have er := Finset.not_nonempty_iff_eq_empty.mp nr
        exact ⟨l,by simpa only [both,er,Finset.union_empty] using el,pl,by omega⟩
    · have el := Finset.not_nonempty_iff_eq_empty.mp nl
      have eq : S=B true := by simpa [el] using both
      obtain ⟨r,er,pr,dr⟩ := sub true (eq ▸ ne)
      exact ⟨r,er.trans eq.symm,pr,by omega⟩

theorem weighted_plan {m : ℕ} (S : Finset (Fin m)) (d : Fin m→ℕ) (H : ℕ) (ne : S.Nonempty)
    (bound : (S.sum fun i=>2^d i) ≤ 2^H) : ∃ P : Plan (Fin m),labels P=S ∧ proper P ∧ depthCost d P ≤ H := by
  classical
  let e := Fintype.equivFin ↥S
  let inv := fun i : Fin (Fintype.card ↥S)=>(e.symm i).val
  have dh (i) (hi : i∈S) : d i ≤ H := by
    have p := (Finset.single_le_sum (f:=fun i=>2^d i) (fun _ _=>Nat.zero_le _) hi).trans bound
    exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp p
  have rhs : (∑ i,2^d (inv i)) ≤ 2^H := by
    have m := e.symm.sum_comp (fun i : ↥S=>2^d i.val)
    rw [m]
    exact (Finset.sum_attach S (fun i=>2^d i)).le.trans bound
  have rat : (∑ i,((1:ℚ)/2)^(H-d (inv i))) ≤ 1 := by
    conv_rhs => rw [←div_self (show (2:ℚ)^H≠0 by positivity)]
    apply (le_div_iff₀ (by positivity : 0 < (2:ℚ)^H)).mpr
    rw [Finset.sum_mul]
    have each (i) : ((1:ℚ)/2)^(H-d (inv i)) * 2^H=(2:ℚ)^d (inv i) := by
      rw [div_pow,one_pow,div_mul_eq_mul_div,one_mul]
      apply (div_eq_iff (by positivity)).mpr
      have hi := dh (inv i) (e.symm i).property
      rw [←pow_add,show d (inv i)+(H-d (inv i))=H by omega]
    simp_rw [each]
    exact_mod_cast rhs
  obtain ⟨code,lens,free⟩ := construct _ _ rat
  let c := fun i=>if h : i∈S then code (e ⟨i,h⟩) else []
  apply code_plan d H S c ne
  · intro i hi j hj ne
    dsimp only [c]; rw [dif_pos hi,dif_pos hj]
    exact free _ _ (fun eq=>ne (congrArg Subtype.val (e.injective eq)))
  · intro i hi; dsimp only [c]; rw [dif_pos hi,lens]
    have eq : inv (e ⟨i,hi⟩)=i := by simp [inv]
    rw [eq]; have := dh i hi; omega


def fork {A : Type} (a : A) (l r : List Bool→A) : List Bool→A
  | []=>a
  | false::p=>l p
  | true::p=>r p

lemma combine_fits {V O : Type} {qs : Set (V→Bool)} {ok L R : V→O→Prop} {d f : O→ℕ}
    {hl hr kl kr : ℕ} (test : V→Bool) (aff : test∈qs)
    (bl : TreeFits qs L d f hl kl) (br : TreeFits qs R d f hr kr)
    (ml : ∀ x i,test x=false → L x i → ok x i) (mr : ∀ x i,test x=true → R x i → ok x i) :
    TreeFits qs ok d f (1+max hl hr) (kl+kr) := by
  classical
  obtain ⟨Nl,Jl,ql,ol,⟨sl,al,vl⟩,dl,cl⟩ := bl
  obtain ⟨Nr,Jr,qr,or',⟨sr,ar,vr⟩,dr,cr⟩ := br
  let q := fork test ql qr
  let out := fork (ol []) ol or'
  refine ⟨_,_,q,out,⟨shape_combine sl sr,?_,?_⟩,?_,?_⟩
  · intro p hp
    simp only [Finset.mem_insert,Finset.mem_union,Finset.mem_image] at hp
    rcases hp with rfl|⟨a,h,rfl⟩|⟨a,h,rfl⟩
    · exact aff
    · exact al a h
    · exact ar a h
  · intro p hp x run
    rw [sdiff_combine] at hp
    rcases Finset.mem_union.mp hp with h|h
    · obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp h
      apply ml x _ (by simpa [q,fork] using run ⟨0,by simp⟩)
      apply vl _ ht x
      intro j; simpa [q,fork,List.get_eq_getElem] using run ⟨j.val+1,by simp⟩
    · obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp h
      apply mr x _ (by simpa [q,fork] using run ⟨0,by simp⟩)
      apply vr _ ht x
      intro j; simpa [q,fork,List.get_eq_getElem] using run ⟨j.val+1,by simp⟩
  · intro p hp
    rw [sdiff_combine] at hp
    rcases Finset.mem_union.mp hp with h|h
    · obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp h; have := dl t ht; change (false::t).length+d (ol t)  ≤  _; simp; omega
    · obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp h; have := dr t ht; change (true::t).length+d (or' t)  ≤  _; simp; omega
  · rw [sdiff_combine,Finset.sum_union (disjoint_cons_images ..),
      Finset.sum_image (fun _ _ _ _ e=>(List.cons.inj e).2),Finset.sum_image (fun _ _ _ _ e=>(List.cons.inj e).2)]
    exact Nat.add_le_add cl cr

lemma weaken_tree {V O : Type} {qs : Set (V→Bool)} {a b : V→O→Prop} {d f : O→ℕ} {h k H K}
    (fits : TreeFits qs a d f h k) (out : ∀ x i,a x i → b x i) (e : h ≤ H) (e' : k ≤ K) : TreeFits qs b d f H K := by
  obtain ⟨N,J,q,o,⟨s,qa,l⟩,len,sum⟩ := fits
  exact ⟨N,J,q,o,⟨s,qa,fun p hp x a=>out _ _ (l p hp x a)⟩,fun p hp=>(len p hp).trans e,sum.trans e'⟩

lemma paid_tree {X : Type} [AddCommGroup X] [Module FF X] {m : ℕ} (row : Fin m→X→ₗ[FF] FF) (rhs : Fin m→FF)
    (d f : Fin m→ℕ) (P : Plan (Fin m)) (h : proper P) :
    TreeFits (Aff X) (fun x i=>(labels P).sum row x≠(labels P).sum rhs → row i x≠rhs i)
      d f (depthCost d P) ((labels P).sum f) := by
  classical
  induction P with
  | tip i =>
    refine ⟨{[]},∅,fun _ _=>false,fun _=>i,⟨shape_leaf,by simp,?_⟩,?_,?_⟩
    · intro p hp x _; simp [labels]
    · intro p hp; simp only [Finset.sdiff_empty,Finset.mem_singleton] at hp; subst p; simp [depthCost]
    · simp [labels]
  | split l r ihl ihr =>
    obtain ⟨pl,pr,dis⟩ := h
    let test := fun x=>decide (((labels l).sum row) x=(labels l).sum rhs)
    have yes : test∈Aff X := ⟨(labels l).sum row,(labels l).sum rhs,rfl⟩
    simp only [labels,Finset.sum_union dis,LinearMap.add_apply,depthCost]
    apply combine_fits test yes (ihl pl) (ihr pr)
    · intro x i b h _
      apply h
      simpa [test] using b
    · intro x i b h total eq
      apply total
      have left : ((labels l).sum row) x=(labels l).sum rhs := by simpa [test] using b
      have right : ((labels r).sum row) x=(labels r).sum rhs := by
        by_contra ne
        exact h ne eq
      rw [left,right]

lemma weighted_upper {X : Type} [AddCommGroup X] [Module FF X] {m : ℕ} (row : Fin m→X→ₗ[FF] FF) (rhs : Fin m→FF)
    (d : Fin m→ℕ) (H K : ℕ) (S : Finset (Fin m)) (z : S.sum row=0) (o : S.sum rhs=1)
    (kb : (S.sum fun i=>2^d i) ≤ K) (hb : (S.sum fun i=>2^d i) ≤ 2^H) :
    TreeFits (Aff X) (fun x i=>row i x≠rhs i) d (fun i=>2^d i) H K := by
  classical
  have ne : S.Nonempty := by
    by_contra h; rw [Finset.not_nonempty_iff_eq_empty.mp h] at o; simp at o
  obtain ⟨P,e,valid,h⟩ := weighted_plan S d H ne hb
  apply weaken_tree (paid_tree row rhs d (fun i=>2^d i) P valid) _ h (e ▸ kb)
  intro x i hi; apply hi; rw [e,z,o]; simp


noncomputable def price {k t : ℕ} (M : XX k→ₗ[FF] XX t) := 2^(Module.finrank FF (LinearMap.range M))

lemma fiber_price {k t : ℕ} (M : XX k→ₗ[FF] XX t) (y : XX t) :
    (∑ u : XX k, if M u=y then price M else 0) ≤ Fintype.card (XX k) := by
  classical
  let f := M.rangeRestrict
  let R := LinearMap.range M
  let E (a b : R) : {u : XX k // f u=a} ≃ {u : XX k // f u=b} := by
    have ex : ∃ c, f c=b-a := by
      obtain ⟨c,hc⟩ := (b-a).property
      exact ⟨c,Subtype.ext hc⟩
    let c := Classical.choose ex
    have hc : f c=b-a := Classical.choose_spec ex
    refine ⟨fun x=>⟨x.val+c,?_⟩,fun x=>⟨x.val-c,?_⟩,?_,?_⟩
    · change f (x.val+c)=_; rw [map_add,x.property,hc]; abel
    · change f (x.val-c)=_; rw [map_sub,x.property,hc]; abel
    · intro x; apply Subtype.ext; simp
    · intro x; apply Subtype.ext; simp
  by_cases mem : y∈R
  · let a : R := ⟨y,mem⟩
    have cardr : Fintype.card R=price M := by
      simpa [R,price,ZMod.card] using (Module.card_eq_pow_finrank (K:=FF) (V:=R))
    have cnt : Fintype.card (XX k)=Fintype.card R * Fintype.card {u : XX k // f u=a} := by
      rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv f),Fintype.card_sigma]
      calc
        _ = ∑ _ : R, Fintype.card {u : XX k // f u=a} := Finset.sum_congr rfl fun b _=>Fintype.card_congr (E b a)
        _ = _ := by simp
    have hv (u : XX k) : (M u=y) ↔ (f u=a) := by constructor <;> intro h; exact Subtype.ext h; exact congrArg Subtype.val h
    simp_rw [hv]
    rw [←Finset.sum_filter,Finset.sum_const,smul_eq_mul,←Fintype.card_subtype]
    rw [cnt,cardr,mul_comm]
  · have no (u : XX k) : M u≠y := fun e=>mem ⟨u,e⟩
    simp [no]

theorem observed_lower {n k t m : ℕ} (row : Fin m→XX n→ₗ[FF] FF) (rhs : Fin m→FF)
    (M : Fin m→XX k→ₗ[FF] XX t) (H K : ℕ)
    (h : TreeFits (Aff (XX n×XX k)) (fun z (a : Fin m×XX t)=>row a.1 z.1≠rhs a.1 ∧ a.2=M a.1 z.2)
      (fun _=>0) (fun _=>1) H K) :
    ∃ S : Finset (Fin m), (S.sum row=0 ∧ S.sum rhs=1) ∧ S.sum (fun i=>price (M i)) ≤ K ∧ S.sum (fun i=>price (M i)) ≤ 2^H := by
  classical
  obtain ⟨N,J,q,out,⟨sh,_,valid⟩,height,cost⟩ := h
  let D := N\J
  let fee := fun p=>price (M (out p).1)
  let load := fun u=>(D.sum fun p=>if M (out p).1 u=(out p).2 then fee p else 0)
  have avg : (∑ u,load u) ≤ Fintype.card (XX k) * D.card := by
    dsimp [load]
    rw [Finset.sum_comm,mul_comm]
    calc
      _ ≤ ∑ _p∈D,Fintype.card (XX k) := Finset.sum_le_sum fun p _=>fiber_price _ _
      _ = _ := by simp
  obtain ⟨u,low⟩ : ∃ u,load u≤D.card := by
    by_contra! none
    have lt := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty : (Finset.univ : Finset (XX k)).Nonempty) (fun i _=>none i)
    simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at lt
    omega
  let filt := D.filter fun p=>M (out p).1 u=(out p).2
  let R := filt.image fun p=>(out p).1
  have uns : ¬∃ x,∀ i∈R,row i x=rhs i := by
    rintro ⟨x,hx⟩
    obtain ⟨p,hp,agree⟩ := query_leaf N J sh (fun p=>q p (x,u)) id
    have v := valid p hp (x,u) (fun j=>(agree j).symm)
    exact v.1 (hx _ (Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,v.2.symm⟩,rfl⟩))
  obtain ⟨S,sub,zero,one⟩ := odd_subset row rhs R uns
  have sc : S.sum (fun i=>price (M i)) ≤ load u := by
    change _ ≤ D.sum _
    rw [←Finset.sum_filter]
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _=>Nat.zero_le _))
    exact Finset.sum_image_le_of_nonneg (fun _ _=>Nat.zero_le _)
  have path (p) (hp : p∈D) : p.length≤H := by simpa using height p hp
  have nl : D.card ≤ 2^H := calc
    _ = D.sum (fun _=>1) := by simp
    _ ≤ D.sum (fun p=>2^(H-p.length)) := Finset.sum_le_sum (fun _ _=>Nat.one_le_pow _ _ (by omega))
    _ ≤ _ := wide_kraft N J sh H path
  exact ⟨S,⟨zero,one⟩,sc.trans (low.trans (by simpa [D] using cost)),sc.trans (low.trans nl)⟩

lemma complete_bits {V O : Type} (qs : Set (V→Bool)) (d : ℕ) (bits : Fin d→V→Bool) (legal : ∀ j,bits j∈qs)
    (decode : (Fin d→Bool)→O) :
    TreeFits qs (fun x o=>o=decode (fun j=>bits j x)) (fun _=>0) (fun _=>1) d (2^d) := by
  classical
  induction d with
  | zero =>
    refine ⟨{[]},∅,fun _ _=>false,fun _=>decode (fun _=>false),⟨shape_leaf,by simp,?_⟩,?_,?_⟩
    · intro p hp x _; apply congrArg decode; funext j; exact Fin.elim0 j
    · intro p hp; simp only [Finset.sdiff_empty,Finset.mem_singleton] at hp; subst p; simp
    · simp
  | succ d ih =>
    let tail := fun j : Fin d=>bits j.succ
    let branch := fun b : Bool=> ih tail (fun j=>legal j.succ) (fun v=>decode (Fin.cons b v))
    have eq (x : V) (b : Bool) (hb : bits 0 x=b) : Fin.cons b (fun j=>tail j x)=(fun j=>bits j x) := by
      funext j; refine Fin.cases ?_ (fun i=>?_) j
      · simpa using hb.symm
      · simp [tail]
    have a := combine_fits (ok:=fun x o=>o=decode (fun j=>bits j x)) (bits 0) (legal 0) (branch false) (branch true)
      (fun x o h e=>e.trans (congrArg decode (eq x false h))) (fun x o h e=>e.trans (congrArg decode (eq x true h)))
    simpa [pow_succ,Nat.one_add,Nat.mul_two] using a

lemma observe_one {n k t m : ℕ} (M : Fin m→XX k→ₗ[FF] XX t) (i : Fin m) :
    TreeFits (Aff (XX n×XX k)) (fun z (a : Fin m×XX t)=>a.1=i ∧ a.2=M i z.2)
      (fun _=>0) (fun _=>1) (Module.finrank FF (LinearMap.range (M i))) (price (M i)) := by
  classical
  let R := LinearMap.range (M i)
  let d := Module.finrank FF R
  let e := (Module.finBasis FF R).equivFun
  let w := e.toLinearMap.comp ((M i).rangeRestrict.comp (LinearMap.snd FF (XX n) (XX k)))
  let get := fun j : Fin d => (LinearMap.proj j).comp w
  let bits := fun j (z : XX n×XX k)=>decide (get j z=1)
  let decode := fun v : (Fin d→Bool)=>(i,(e.symm (fun j=>if v j then 1 else 0)).val)
  have a := complete_bits (Aff (XX n×XX k)) d bits (fun j=>⟨get j,1,rfl⟩) decode
  apply weaken_tree a _ (le_refl _) (le_refl _)
  rintro z o rfl
  have eq : (fun j=>if bits j z then (1:FF) else 0)=w z := by
    funext j; change (if decide (get j z=1) then (1:FF) else 0)=get j z
    exact (show ∀ a : FF,(if decide (a=1) then (1:FF) else 0)=a by decide) _
  refine ⟨rfl,?_⟩
  change (e.symm (fun j=>if bits j z then (1:FF) else 0)).val=_
  rw [eq]; change (e.symm (e ((M i).rangeRestrict z.2))).val=_
  simp

lemma observed_plan {n k t m : ℕ} (row : Fin m→XX n→ₗ[FF] FF) (rhs : Fin m→FF) (M : Fin m→XX k→ₗ[FF] XX t)
    (P : Plan (Fin m)) (h : proper P) :
    TreeFits (Aff (XX n×XX k)) (fun z (a : Fin m×XX t)=>((labels P).sum row z.1≠(labels P).sum rhs → row a.1 z.1≠rhs a.1) ∧ a.2=M a.1 z.2)
      (fun _=>0) (fun _=>1) (depthCost (fun i=>Module.finrank FF (LinearMap.range (M i))) P) ((labels P).sum (fun i=>price (M i))) := by
  classical
  induction P with
  | tip i =>
    apply weaken_tree (observe_one (n:=n) M i) _ (by rfl) (by simp [labels])
    intro z a ha; obtain ⟨e,v⟩ := ha; simp [labels,e,v]
  | split l r ihl ihr =>
    obtain ⟨pl,pr,dis⟩ := h
    let form := ((labels l).sum row).comp (LinearMap.fst FF (XX n) (XX k))
    let test := fun z : XX n×XX k=>decide (form z=(labels l).sum rhs)
    have yes : test∈Aff (XX n×XX k) := ⟨form,(labels l).sum rhs,rfl⟩
    simp only [labels,Finset.sum_union dis,LinearMap.add_apply,depthCost]
    apply combine_fits test yes (ihl pl) (ihr pr)
    · intro z a b v; refine ⟨fun _=>v.1 ?_,v.2⟩; simpa [test,form] using b
    · intro z a b v; refine ⟨?_,v.2⟩; intro total eq
      apply total
      have left : ((labels l).sum row) z.1=(labels l).sum rhs := by simpa [test,form] using b
      have right : ((labels r).sum row) z.1=(labels r).sum rhs := by by_contra ne; exact v.1 ne eq
      rw [left,right]

theorem observed_upper {n k t m : ℕ} (row : Fin m→XX n→ₗ[FF] FF) (rhs : Fin m→FF) (M : Fin m→XX k→ₗ[FF] XX t)
    (H K : ℕ) (S : Finset (Fin m)) (z : S.sum row=0) (o : S.sum rhs=1)
    (kb : S.sum (fun i=>price (M i)) ≤ K) (hb : S.sum (fun i=>price (M i)) ≤ 2^H) :
    TreeFits (Aff (XX n×XX k)) (fun p (a : Fin m×XX t)=>row a.1 p.1≠rhs a.1 ∧ a.2=M a.1 p.2)
      (fun _=>0) (fun _=>1) H K := by
  classical
  have ne : S.Nonempty := by
    by_contra h; rw [Finset.not_nonempty_iff_eq_empty.mp h] at o; simp at o
  obtain ⟨P,e,valid,h⟩ := weighted_plan S (fun i=>Module.finrank FF (LinearMap.range (M i))) H ne hb
  apply weaken_tree (observed_plan row rhs M P valid) _ h (e ▸ kb)
  intro x i hi; refine ⟨hi.1 ?_,hi.2⟩; rw [e,z,o]; simp

end PEqualNP.Outside.L_pcx_343_aux

open PEqualNP.Outside.L_pcx_343_aux in
theorem PEqualNP.Outside.L_pcx_343 : ∀ (n k t : ℕ),
  let X := Fin n → ZMod 2
  let U := Fin k → ZMod 2
  let Y := Fin t → ZMod 2
  let shape := fun (N J : Finset (List Bool)) =>
    [] ∈ N ∧ J ⊆ N ∧
    (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
    ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N
  let queries := fun (V : Type) [AddCommGroup V] [Module (ZMod 2) V] =>
    {f : V → Bool | ∃ (l : V →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), f = fun x => decide (l x = b)}
  let cert := fun {V O : Type} (qs : Set (V → Bool)) (ok : V → O → Prop)
      (N J : Finset (List Bool)) (q : List Bool → V → Bool) (out : List Bool → O) =>
    shape N J ∧ (∀ p ∈ J, q p ∈ qs) ∧ ∀ p ∈ N \ J, ∀ x : V,
      (∀ j : Fin p.length, q (p.take j.val) x = p.get j) → ok x (out p)
  let fits := fun {V O : Type} (qs : Set (V → Bool)) (ok : V → O → Prop)
      (depth leaves : O → ℕ) (H K : ℕ) =>
    ∃ (N J : Finset (List Bool)) (q : List Bool → V → Bool) (out : List Bool → O),
      cert qs ok N J q out ∧ (∀ p ∈ N \ J, p.length + depth (out p) ≤ H) ∧
      (N \ J).sum (fun p => leaves (out p)) ≤ K
  ∀ (m : ℕ) (row : Fin m → X →ₗ[ZMod 2] ZMod 2) (rhs : Fin m → ZMod 2)
      (M : Fin m → U →ₗ[ZMod 2] Y),
    let oddDep := fun S : Finset (Fin m) => S.sum row = 0 ∧ S.sum rhs = 1
    let wt := fun i : Fin m => 2^(Module.finrank (ZMod 2) (LinearMap.range (M i)))
    let answer := fun (z : X × U) (a : Fin m × Y) => row a.1 z.1 ≠ rhs a.1 ∧ a.2 = M a.1 z.2
    ∀ H K : ℕ, fits (queries (X × U)) answer (fun _ => 0) (fun _ => 1) H K ↔
      ∃ S : Finset (Fin m), oddDep S ∧ S.sum wt ≤ K ∧ S.sum wt ≤ 2^H := by
  intro n k t
  dsimp only
  intro m row rhs M H K
  constructor
  · exact observed_lower row rhs M H K
  · rintro ⟨S,⟨z,o⟩,kb,hb⟩
    exact observed_upper row rhs M H K S z o kb hb
