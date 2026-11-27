import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_227_aux
open Finset

variable {m : ℕ}
abbrev Family (m : ℕ) := Finset (Finset (Fin m))
def Intervals (F : Family m) : Prop :=
  ∀ I ∈ F, I.Nonempty ∧ ∀ a ∈ I, ∀ b ∈ I, ∀ x : Fin m, a ≤ x → x ≤ b → x ∈ I
def Hits (H : Finset (Fin m)) (F : Family m) : Prop := ∀ I ∈ F, (H ∩ I).Nonempty
def Feasible (F : Family m) (p : Finset (Fin m) → ℕ) (c : Fin m → ℕ) : Prop :=
  ∀ x, (∑ I ∈ F, if x ∈ I then p I else 0) ≤ c x

theorem weak {F : Family m} {H : Finset (Fin m)} {p : Finset (Fin m) → ℕ} {c : Fin m → ℕ}
    (hh : Hits H F) (hp : Feasible F p c) : (∑ I ∈ F, p I) ≤ ∑ x ∈ H, c x := by
  classical
  calc
    (∑ I ∈ F, p I) ≤ ∑ I ∈ F, ∑ x ∈ H, if x ∈ I then p I else 0 := by
      apply Finset.sum_le_sum
      intro I hI
      obtain ⟨x,hx⟩ := hh I hI
      obtain ⟨hxH,hxI⟩ := Finset.mem_inter.mp hx
      exact (show p I = (if x ∈ I then p I else 0) by simp [hxI]).le.trans
        (Finset.single_le_sum (f := fun x : Fin m => if x ∈ I then p I else 0)
          (fun _ _ => Nat.zero_le _) hxH)
    _ = ∑ x ∈ H, ∑ I ∈ F, if x ∈ I then p I else 0 := Finset.sum_comm
    _ ≤ ∑ x ∈ H, c x := Finset.sum_le_sum fun x _ => hp x

def rightEnd (J : Finset (Fin m)) : ℕ :=
  if h : J.Nonempty then (J.max' h).val else 0

def positive (c : Fin m → ℕ) := Finset.univ.filter fun x => 0 < c x

theorem liftHits {F : Family m} {I : Finset (Fin m)} (hF : Intervals F) (hI : I ∈ F)
    (earliest : ∀ J ∈ F, rightEnd I ≤ rightEnd J)
    (H : Finset (Fin m)) (hits : Hits H (F.erase I)) (z : Fin m) (hz : z ∈ I) :
    ∃ k ∈ I, (k ∈ H ∨ k=z) ∧ Hits (insert k (H \ I)) F := by
  classical
  let T := H ∩ I
  have choose : ∃ k ∈ I, (k ∈ H ∨ k=z) ∧ ∀ x ∈ T, x ≤ k := by
    by_cases hT : T.Nonempty
    · have hk := Finset.max'_mem T hT
      obtain ⟨hkH,hkI⟩ := Finset.mem_inter.mp hk
      exact ⟨T.max' hT, hkI, Or.inl hkH, fun x hx => Finset.le_max' _ x hx⟩
    · refine ⟨z,hz,Or.inr rfl,fun x hx => ?_⟩
      exact False.elim (hT ⟨x,hx⟩)
  obtain ⟨k,hk,hcase,large⟩ := choose
  refine ⟨k,hk,hcase,?_⟩
  intro J hJ
  by_cases eq : J=I
  · subst J
    exact ⟨k,Finset.mem_inter.mpr ⟨Finset.mem_insert_self _ _,hk⟩⟩
  obtain ⟨x,hx⟩ := hits J (Finset.mem_erase.mpr ⟨eq,hJ⟩)
  obtain ⟨hxH,hxJ⟩ := Finset.mem_inter.mp hx
  by_cases xi : x ∈ I
  · have xk := large x (Finset.mem_inter.mpr ⟨hxH,xi⟩)
    have rJ := (hF J hJ).1
    have rI := (hF I hI).1
    have e := earliest J hJ
    simp only [rightEnd, dif_pos rJ, dif_pos rI] at e
    have kj : k ≤ J.max' rJ := (Finset.le_max' I k hk).trans (show I.max' rI ≤ J.max' rJ from e)
    exact ⟨k,Finset.mem_inter.mpr ⟨Finset.mem_insert_self _ _,
      (hF J hJ).2 x hxJ (J.max' rJ) (Finset.max'_mem _ _) k xk kj⟩⟩
  · exact ⟨x,Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hxH,xi⟩),hxJ⟩⟩

theorem solve (F : Family m) : ∀ (c : Fin m → ℕ), Intervals F →
    ∃ (H : Finset (Fin m)) (p : Finset (Fin m) → ℕ),
    Hits H F ∧ Feasible F p c ∧ (F.filter (fun I => 0 < p I)).card ≤ (positive c).card ∧
    (∑ x ∈ H, c x) ≤ ∑ I ∈ F, p I := by
  classical
  induction F using Finset.strongInductionOn with
  | _ F ih =>
    intro c hF
    by_cases hne : F.Nonempty
    swap
    · have e : F=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst F
      exact ⟨∅,fun _ => 0,by simp [Hits],by simp [Feasible],by simp,by simp⟩
    obtain ⟨I,hI,earliest⟩ := Finset.exists_min_image F rightEnd hne
    obtain ⟨z,hz,lo⟩ := Finset.exists_min_image I c (hF I hI).1
    let d := c z
    let R := F.erase I
    let b (x : Fin m) := if x ∈ I then c x - d else c x
    have hrest : R ⊂ F := Finset.erase_ssubset hI
    obtain ⟨H,p,hitR,capR,ns,cost⟩ := ih R hrest b (fun J hj => hF J (Finset.mem_of_mem_erase hj))
    obtain ⟨k,hk,kcase,newhit⟩ := liftHits hF hI earliest H hitR z hz
    let K := H \ I
    let q (J : Finset (Fin m)) := if J=I then d else p J
    have hIK : I ∉ R := Finset.notMem_erase _ _
    have eqF : insert I R = F := Finset.insert_erase hI
    have put (f : Finset (Fin m) → ℕ → ℕ) :
        (∑ J ∈ F, f J (q J)) = f I d + ∑ J ∈ R, f J (p J) := by
      rw [← eqF,Finset.sum_insert hIK]
      simp only [q,if_pos rfl]
      congr 1
      apply Finset.sum_congr rfl
      intro J hJ
      rw [if_neg (Finset.ne_of_mem_erase hJ)]
    have capacity : Feasible F q c := by
      intro x
      rw [put (fun J w => if x ∈ J then w else 0)]
      have h := capR x
      by_cases xi : x ∈ I
      · have low := lo x xi
        simp only [b,xi,if_pos] at h ⊢
        dsimp [d] at *
        omega
      · simpa [xi,b] using h
    have bz : b z = 0 := by simp [b,hz,d]
    have sub : positive b ⊆ positive c := by
      intro x hx
      have h := (Finset.mem_filter.mp hx).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      by_cases xi : x∈I <;> simp [b,xi] at h <;> omega
    have ns' : (F.filter fun J => 0 < q J).card ≤ (positive c).card := by
      let S := R.filter fun J => 0 < p J
      have e : (F.filter fun J => 0 < q J) = if 0<d then insert I S else S := by
        ext J
        by_cases same : J=I
        · subst J
          by_cases pos : 0<d <;> simp [q,hI,pos,S,R]
        · by_cases pos : 0<d <;> simp [q,same,S,R,pos]
      rw [e]
      by_cases pos : 0<d
      · rw [if_pos pos]
        have no : z ∉ positive b := by simp [positive,bz]
        have yes : z ∈ positive c := Finset.mem_filter.mpr ⟨Finset.mem_univ _,pos⟩
        have proper : positive b ⊂ positive c := Finset.ssubset_iff_subset_ne.mpr
          ⟨sub,fun h => no (h.symm ▸ yes)⟩
        have less := Finset.card_lt_card proper
        have ic := Finset.card_insert_le I S
        change S.card ≤ _ at ns
        omega
      · rw [if_neg pos]
        exact ns.trans (Finset.card_le_card sub)
    have kN : k ∉ K := fun h => (Finset.mem_sdiff.mp h).2 hk
    have Ksub : K ⊆ H := fun _ h => (Finset.mem_sdiff.mp h).1
    have kb : (∑ x ∈ K, b x)+ b k ≤ ∑ x ∈ H, b x := by
      rcases kcase with kin|eq
      · have su : insert k K ⊆ H := Finset.insert_subset kin Ksub
        have h := Finset.sum_le_sum_of_subset_of_nonneg (f := b) su (fun _ _ _ => Nat.zero_le _)
        rw [Finset.sum_insert kN] at h
        omega
      · rw [eq,bz,Nat.add_zero]
        exact Finset.sum_le_sum_of_subset_of_nonneg Ksub (fun _ _ _ => Nat.zero_le _)
    have sameK : (∑ x ∈ K,c x) = ∑ x ∈ K,b x := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [b,(Finset.mem_sdiff.mp hx).2]
    have ck : c k = d+b k := by
      have low := lo k hk
      simp only [b,hk,if_true]
      dsimp [d]
      omega
    refine ⟨insert k K,q,newhit,capacity,ns',?_⟩
    rw [Finset.sum_insert kN, sameK, ck, put (fun _ a => a)]
    omega


theorem packing : ∀ (m : ℕ) (F : Finset (Finset (Fin m))) (c : Fin m → ℕ),
  (∀ I ∈ F, I.Nonempty ∧ ∀ a ∈ I, ∀ b ∈ I, ∀ x : Fin m, a ≤ x → x ≤ b → x ∈ I) →
  ∃ (H : Finset (Fin m)) (p : Finset (Fin m) → ℕ),
    (∀ I ∈ F, (H ∩ I).Nonempty) ∧
    (∀ x : Fin m, (∑ I ∈ F, if x ∈ I then p I else 0) ≤ c x) ∧
    (F.filter (fun I => 0 < p I)).card ≤ m ∧
    (∑ x ∈ H, c x) = ∑ I ∈ F, p I := by
  intro m F c ints
  obtain ⟨H,p,hh,hp,hcount,le⟩ := PEqualNP.Outside.L_pcx_227_aux.solve F c ints
  refine ⟨H,p,hh,hp,?_,Nat.le_antisymm le (PEqualNP.Outside.L_pcx_227_aux.weak hh hp)⟩
  exact hcount.trans (by simpa using Finset.card_le_univ (PEqualNP.Outside.L_pcx_227_aux.positive c))

end PEqualNP.Outside.L_pcx_227_aux

namespace PEqualNP.Outside.L_pcx_227_aux
open PEqualNP.ProofComplexity

def Can (t : ℕ → Bool → Bool → Bool) : ℕ → ℕ → Bool → Prop
  | _,0,_ => True
  | s,k+1,a => ∃ b, t s a b = true ∧ Can t (s+1) k b

theorem can_iff (t : ℕ → Bool → Bool → Bool) (s k : ℕ) (a : Bool) :
    Can t s k a ↔ ∃ x : ℕ → Bool, x s=a ∧ ∀ j, s≤j → j<s+k → t j (x j) (x (j+1)) = true := by
  induction k generalizing s a with
  | zero => exact ⟨fun _=>⟨fun _=>a,rfl,by omega⟩,fun _=>True.intro⟩
  | succ k ih =>
    constructor
    · rintro ⟨b,edge,tail⟩
      obtain ⟨x,xb,h⟩ := (ih (s+1) b).mp tail
      refine ⟨fun j=>if j=s then a else x j,by simp,?_⟩
      intro j lo hi
      by_cases eq : j=s
      · subst j; simpa [xb] using edge
      · simpa [eq,show j+1≠s by omega] using h j (by omega) (by omega)
    · rintro ⟨x,eq,h⟩
      use x (s+1)
      exact ⟨eq ▸ h s (by omega) (by omega), (ih (s+1) _).mpr ⟨x,rfl,fun j a b=>h j (by omega) (by omega)⟩⟩

variable {V : Type} [DecidableEq V]
abbrev Seq (V : Type) := List (Clause V)
def Valid (G : Set (Clause V)) (p : Seq V) := IsDerivation G p ∧ ∀ C∈p, C.card≤2
def Extend (p q : Seq V) (k : ℕ) := (∀ C∈p, C∈q) ∧ q.length≤p.length+k

lemma grow_parent {G : Set (Clause V)} {p : Seq V} (valid : Valid G p)
    (target : Clause V) (width : target.card≤2)
    (source : target∈G ∨ ∃ C∈p,C⊆target) :
    ∃ q, Valid G q ∧ Extend p q 1 ∧ ∃ C∈q,C⊆target := by
  rcases source with h|h
  · refine ⟨target::p,⟨.ax valid.1 h,?_⟩,⟨fun _ h=>List.mem_cons_of_mem _ h,by simp⟩,target,by simp,by rfl⟩
    intro C hC
    rcases List.mem_cons.mp hC with rfl|hC
    · exact width
    · exact valid.2 _ hC
  · exact ⟨p,valid,⟨fun _ h=>h,by omega⟩,h⟩

lemma resolve_down {G : Set (Clause V)} {p : Seq V} (v : Valid G p) (j : V)
    (goal : Clause V) (gw : goal.card≤2)
    (pos : ∃ A∈p,A⊆insert (j,true) goal) (neg : ∃ B∈p,B⊆insert (j,false) goal) :
    ∃ q, Valid G q ∧ Extend p q 1 ∧ ∃ C∈q,C⊆goal := by
  obtain ⟨A,ha,sa⟩ := pos
  obtain ⟨B,hb,sb⟩ := neg
  by_cases a : (j,true)∈A
  · by_cases b : (j,false)∈B
    · let C := A.erase (j,true) ∪ B.erase (j,false)
      have sub : C ⊆ goal := by
        intro l hl
        rcases Finset.mem_union.mp hl with h|h
        · exact (Finset.mem_insert.mp (sa (Finset.mem_of_mem_erase h))).resolve_left (Finset.ne_of_mem_erase h)
        · exact (Finset.mem_insert.mp (sb (Finset.mem_of_mem_erase h))).resolve_left (Finset.ne_of_mem_erase h)
      refine ⟨C::p,⟨.res v.1 ha hb ⟨j,a,b,rfl⟩,?_⟩,⟨fun _ h=>List.mem_cons_of_mem _ h,by simp⟩,C,by simp,sub⟩
      intro X hX
      rcases List.mem_cons.mp hX with rfl|hX
      · exact (Finset.card_le_card sub).trans gw
      · exact v.2 _ hX
    · refine ⟨p,v,⟨fun _ h=>h,by omega⟩,B,hb,?_⟩
      intro l hl
      exact (Finset.mem_insert.mp (sb hl)).resolve_left (fun e=>b (e ▸ hl))
  · refine ⟨p,v,⟨fun _ h=>h,by omega⟩,A,ha,?_⟩
    intro l hl
    exact (Finset.mem_insert.mp (sa hl)).resolve_left (fun e=>a (e ▸ hl))

lemma extend_trans {p q r : Seq V} {u v : ℕ} (a : Extend p q u) (b : Extend q r v) :
    Extend p r (u+v) := ⟨fun C h=>b.1 C (a.1 C h),by have := a.2; have := b.2; omega⟩

def Forbidden (u : ℕ→V) (t : ℕ→Bool→Bool→Bool) (s k : ℕ) (G : Set (Clause V)) :=
  ∀ j, s≤j → j<s+k → ∀ a b, t j a b=false → ({(u j,!a),(u (j+1),!b)} : Clause V)∈G

def Mark (u : ℕ→V) (s : ℕ) (a : Bool) (p : Seq V) := ∃ C∈p,C⊆{(u s,!a)}

lemma step_mark {G : Set (Clause V)} (u : ℕ→V) (t : ℕ→Bool→Bool→Bool) (s k : ℕ)
    {p : Seq V} (v : Valid G p) (row : ∀ a b, t s a b=false → ({(u s,!a),(u (s+1),!b)} : Clause V)∈G)
    (tail : ∀ b,¬Can t (s+1) k b → Mark u (s+1) b p) (a : Bool) :
    ∃ q, Valid G q ∧ Extend p q 3 ∧ (¬Can t s (k+1) a → Mark u s a q) := by
  classical
  by_cases yes : Can t s (k+1) a
  · exact ⟨p,v,⟨fun _ h=>h,by omega⟩,fun h=>False.elim (h yes)⟩
  let base : Clause V := {(u s,!a)}
  have obtainParent (b : Bool) : insert (u (s+1),!b) base∈G ∨
      ∃ C∈p,C⊆insert (u (s+1),!b) base := by
    by_cases e : t s a b=true
    · obtain ⟨C,h,sub⟩ := tail b (fun hb=>yes ⟨b,e,hb⟩)
      exact Or.inr ⟨C,h,sub.trans (by simp)⟩
    · left; simpa [base,Finset.pair_comm] using row a b (by cases h : t s a b <;> simp_all)
  have wid (b : Bool) : (insert (u (s+1),!b) base).card≤2 := by
    have := Finset.card_insert_le (u (s+1),!b) base
    simpa [base] using this
  obtain ⟨q,vq,eq,A,ha,sa⟩ := grow_parent v _ (wid false) (obtainParent false)
  obtain ⟨r,vr,er,B,hb,sb⟩ := grow_parent vq _ (wid true) ((obtainParent true).imp_right
    (fun ⟨C,h,sub⟩=>⟨C,eq.1 C h,sub⟩))
  obtain ⟨z,vz,ez,h⟩ := resolve_down vr (u (s+1)) base (by simp [base])
    ⟨A,er.1 _ ha,sa⟩ ⟨B,hb,sb⟩
  exact ⟨z,vz,extend_trans (extend_trans eq er) ez,fun _=>h⟩

theorem path_lines {G : Set (Clause V)} (u : ℕ→V) (t : ℕ→Bool→Bool→Bool) (s k : ℕ)
    (ax : Forbidden u t s k G) :
    ∃ p, Valid G p ∧ p.length≤6*k ∧ ∀ a,¬Can t s k a → Mark u s a p := by
  induction k generalizing s with
  | zero => exact ⟨[],⟨.nil,by simp⟩,by simp,fun a h=>False.elim (h trivial)⟩
  | succ k ih =>
    obtain ⟨p,v,hp,mark⟩ := ih (s+1) (fun j hj hj' a b e=>ax j (by omega) (by omega) a b e)
    have row := ax s (by omega) (by omega)
    obtain ⟨q,vq,eq,m0⟩ := step_mark u t s k v row mark false
    have mq (b : Bool) (hb : ¬Can t (s+1) k b) : Mark u (s+1) b q := by
      obtain ⟨C,h,sub⟩ := mark _ hb; exact ⟨C,eq.1 C h,sub⟩
    obtain ⟨r,vr,er,m1⟩ := step_mark u t s k vq row mq true
    refine ⟨r,vr,by have h := eq.2; have h' := er.2; omega,?_⟩
    intro a ha
    cases a with
    | false => obtain ⟨C,h,sub⟩ := m0 ha; exact ⟨C,er.1 C h,sub⟩
    | true => exact m1 ha

theorem path_refute {G : Set (Clause V)} (u : ℕ→V) (t : ℕ→Bool→Bool→Bool) (s k : ℕ)
    (ax : Forbidden u t s k G) (bad : ¬ ∃ a,Can t s k a) :
    ∃ p, IsRefutation G p ∧ p.length≤6*k+1 ∧ ∀ C∈p,C.card≤2 := by
  obtain ⟨p,v,hp,mark⟩ := path_lines u t s k ax
  obtain ⟨q,vq,eq,C,hc,sub⟩ := resolve_down v (u s) ∅ (by simp)
    (by simpa [Mark] using mark false (fun h=>bad ⟨_,h⟩))
    (by simpa [Mark] using mark true (fun h=>bad ⟨_,h⟩))
  have ec := Finset.subset_empty.mp sub
  exact ⟨q,⟨vq.1,ec ▸ hc⟩,by have := eq.2; omega,vq.2⟩

def segment (m s k : ℕ) := (Finset.univ : Finset (Fin m)).filter fun i=>s ≤ i.val ∧ i.val < s+k
@[simp] lemma mem_segment {m s k : ℕ} (i : Fin m) : i∈segment m s k ↔ s ≤ i.val ∧ i.val < s+k := by simp [segment]

def IsBad (t : ℕ→Bool→Bool→Bool) {m : ℕ} (J : Finset (Fin m)) := ∃ s k : ℕ, 0 < k ∧ s+k ≤ m ∧
  J=segment m s k ∧ ¬∃ b,Can t s k b

noncomputable def badFamily (t : ℕ→Bool→Bool→Bool) (m : ℕ) : Family m := by
  classical exact Finset.univ.filter (IsBad t)

lemma mem_bad {t : ℕ→Bool→Bool→Bool} {m} {J : Finset (Fin m)} : J∈badFamily t m ↔ IsBad t J := by
  classical simp [badFamily]

lemma bad_intervals (t : ℕ→Bool→Bool→Bool) (m : ℕ) : Intervals (badFamily t m) := by
  intro J hJ
  obtain ⟨s,k,pos,bound,rfl,_⟩ := mem_bad.mp hJ
  refine ⟨⟨⟨s,by omega⟩,mem_segment _ |>.mpr ⟨le_rfl,by dsimp; omega⟩⟩,?_⟩
  intro a ha b hb x ax xb
  exact (mem_segment x).mpr ⟨((mem_segment a).mp ha).1.trans ax, lt_of_le_of_lt xb ((mem_segment b).mp hb).2⟩

lemma patch_path (t : ℕ→Bool→Bool→Bool) (m : ℕ) (keep : ℕ→Prop)
    (good : ∀ s k,0 < k → s+k ≤ m → (∀ j,s ≤ j → j < s+k → keep j) → ∃ b, Can t s k b)
    (s k : ℕ) (bound : s+k ≤ m) :
    ∃ x : ℕ→Bool, ∀ j,s ≤ j → j < s+k → keep j → t j (x j) (x (j+1))=true := by
  classical
  induction k using Nat.strong_induction_on generalizing s with
  | ind k ih =>
    by_cases empty : k=0
    · exact ⟨fun _=>false,by omega⟩
    by_cases all : ∀ j,s ≤ j → j < s+k → keep j
    · obtain ⟨b,hb⟩ := good s k (by omega) bound all
      obtain ⟨x,_,hx⟩ := (can_iff _ _ _ _).mp hb
      exact ⟨x,fun j a b _=>hx j a b⟩
    push_neg at all
    obtain ⟨j,lo,hi,hole⟩ := all
    obtain ⟨x,hx⟩ := ih (j-s) (by omega) s (by omega)
    obtain ⟨y,hy⟩ := ih (s+k-(j+1)) (by omega) (j+1) (by omega)
    refine ⟨fun i=>if i ≤ j then x i else y i,?_⟩
    intro i ilo ihi act
    by_cases before : i < j
    · simpa [show i ≤ j by omega,show i+1 ≤ j by omega] using hx i ilo (by omega) act
    · have diff : i≠j := fun e=>hole (e ▸ act)
      simpa [show ¬i ≤ j by omega,show ¬i+1 ≤ j by omega] using hy i (by omega) (by omega) act

def loss {m : ℕ} (t : ℕ→Bool→Bool→Bool) (c : Fin m→ℕ) (x : ℕ→Bool) :=
  ∑ i : Fin m, if t i.val (x i.val) (x (i.val+1))=false then c i else 0

lemma violations_hit (m : ℕ) (t : ℕ→Bool→Bool→Bool) (x : ℕ→Bool) :
    Hits (Finset.univ.filter fun i : Fin m=>t i.val (x i.val) (x (i.val+1))=false) (badFamily t m) := by
  classical
  intro J hJ
  obtain ⟨s,k,_,bound,rfl,cant⟩ := mem_bad.mp hJ
  by_contra none
  apply cant
  refine ⟨x s,(can_iff _ _ _ _).mpr ⟨x,rfl,?_⟩⟩
  intro j a b
  cases e : t j (x j) (x (j+1)) with
  | true => rfl
  | false =>
    exfalso; apply none
    exact ⟨⟨j,by omega⟩,Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,e⟩,
      (mem_segment _).mpr ⟨a,b⟩⟩⟩

theorem linearPack (t : ℕ→Bool→Bool→Bool) (m : ℕ) (c : Fin m→ℕ) :
    ∃ (P : Family m) (q : Finset (Fin m)→ℕ) (x : ℕ→Bool), P.card ≤ m ∧
      (∀ I∈P, IsBad t I ∧ 0 < q I) ∧ Feasible P q c ∧
      loss t c x=P.sum q ∧ ∀ y, P.sum q ≤ loss t c y := by
  classical
  let F := badFamily t m
  obtain ⟨H,q,hit,cap,num,eq⟩ := packing m F c (bad_intervals t m)
  let P := F.filter (fun I=>0 < q I)
  have sumq : P.sum q=F.sum q := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro I hI out
    by_contra ne
    exact out (Finset.mem_filter.mpr ⟨hI,Nat.pos_of_ne_zero ne⟩)
  have low (y : ℕ→Bool) : P.sum q ≤ loss t c y := by
    rw [sumq]
    simpa only [loss,Finset.sum_filter] using weak (violations_hit m t y) cap
  let keep := fun j : ℕ=>∀ i : Fin m, i.val=j → i∉H
  have ok (s k : ℕ) (pos : 0 < k) (bound : s+k ≤ m) (all : ∀ j,s ≤ j → j < s+k → keep j) : ∃ b,Can t s k b := by
    by_contra no
    have inF : segment m s k∈F := mem_bad.mpr ⟨s,k,pos,bound,rfl,no⟩
    obtain ⟨i,hi⟩ := hit _ inF
    obtain ⟨ih,is⟩ := Finset.mem_inter.mp hi
    obtain ⟨a,b⟩ := (mem_segment i).mp is
    exact all i.val a b i rfl ih
  obtain ⟨x,hx⟩ := patch_path t m keep ok 0 m (by omega)
  have upper : loss t c x ≤ ∑ i∈H,c i := by
    have Hsame : H=Finset.univ.filter (fun i=>i∈H) := by ext; simp
    have HS : (∑ i∈H,c i)=(Finset.univ.filter (fun i=>i∈H)).sum c := congrArg (fun K : Finset (Fin m)=>K.sum c) Hsame
    rw [HS,Finset.sum_filter]; unfold loss
    apply Finset.sum_le_sum
    intro i _
    by_cases mem : i∈H
    · simp [mem]; split  <;> omega
    · have hk : keep i.val := by intro j hj; have e : j=i := Fin.ext hj; simpa [e] using mem
      have h := hx i.val (by omega) (by simpa using i.isLt) hk
      simp [mem,h]
  refine ⟨P,q,x,num,fun I hI=>⟨mem_bad.mp (Finset.mem_filter.mp hI).1,(Finset.mem_filter.mp hI).2⟩,?_,
    le_antisymm (upper.trans (eq.trans sumq.symm).le) (low x),low⟩
  intro i
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _=>Nat.zero_le _)).trans (cap i)

def seg_card (m s k : ℕ) (hk : s+k  ≤  m) : (segment m s k).card = k := by
  classical
  let f : Fin k → Fin m := fun j=>⟨s+j.val,by have := j.isLt; omega⟩
  have inj : Function.Injective f := by
    intro i j e; apply Fin.ext; have e' := congrArg Fin.val e; dsimp [f] at e'; omega
  have eq : Finset.univ.image f = segment m s k := by
    ext i
    rw [Finset.mem_image,mem_segment]
    constructor
    · rintro ⟨j,_,rfl⟩; have := j.isLt; dsimp [f]; omega
    · rintro ⟨lo,hi⟩; exact ⟨⟨i.val-s,by omega⟩,Finset.mem_univ _,Fin.ext (by dsimp [f]; omega)⟩
  rw [←eq,Finset.card_image_of_injective _ inj]; simp

variable {n : ℕ} [NeZero n]
def idx (n : ℕ) [NeZero n] (j : ℕ) : Fin n := ⟨j%n,Nat.mod_lt _ (NeZero.pos n)⟩
@[simp] lemma idx_val (i : Fin n) : idx n i.val=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
def perm (h : Fin n) : Fin n ≃ Fin n := Equiv.addLeft (idx n (h.val+1))
def station (h : Fin n) (j : ℕ) := perm h (idx n j)
lemma station_add (h : Fin n) (s k : ℕ) : idx n ((station h s).val+k)=station h (s+k) := by
  apply Fin.ext
  simp [station,perm,idx,Fin.val_add,Nat.mod_add_mod,Nat.add_mod_mod,Nat.add_assoc]
lemma station_index (h : Fin n) {j : ℕ} (hj : j < n) : ((perm h).symm (station h j)).val=j := by
  simp [station,idx,Nat.mod_eq_of_lt hj]
lemma station_last (h : Fin n) : station h (n-1)=h := by
  apply Fin.ext
  have pos := NeZero.pos n
  simp [station,perm,idx,Fin.val_add,Nat.mod_add_mod,Nat.add_mod_mod,show h.val+1+(n-1)=h.val+n by omega,Nat.mod_eq_of_lt h.isLt]
def embed (h : Fin n) : Fin (n-1) ↪ Fin n where
  toFun i := station h i.val
  inj' := by
    intro i j e
    have hi := i.isLt; have hj := j.isLt
    have eq := congrArg (fun z=>( (perm h).symm z).val) e
    change ((perm h).symm (station h i.val)).val=((perm h).symm (station h j.val)).val at eq
    rw [station_index h (by omega),station_index h (by omega)] at eq
    exact Fin.ext eq

lemma whole (h : Fin n) : Finset.univ.map (embed h) = Finset.univ.filter (fun i=>i≠h) := by
  classical
  have pos := NeZero.pos n
  ext i
  simp only [Finset.mem_map,Finset.mem_univ,true_and,Finset.mem_filter]
  constructor
  · rintro ⟨j,rfl⟩ e
    change station h j.val=h at e
    have e2 := e.trans (station_last h).symm
    have eq := congrArg (fun z=>((perm h).symm z).val) e2
    change ((perm h).symm (station h j.val)).val=((perm h).symm (station h (n-1))).val at eq
    have hj := j.isLt
    rw [station_index h (by omega),station_index h (by omega)] at eq
    omega
  · intro ne
    let j := (perm h).symm i
    have get : station h j.val=i := by simp [station,j]
    have lt : j.val < n-1 := by
      have hn := j.isLt
      by_contra no
      have e : j.val=n-1 := by omega
      exact ne (get.symm.trans (e ▸ station_last h))
    exact ⟨⟨j.val,lt⟩,get⟩

def cycRows (h : Fin n) (I : Finset (Fin (n-1))) := I.map (embed h)
lemma enc_inj (h : Fin n) : Function.Injective (cycRows h) := Finset.map_injective _
def axiomSet (T : Fin n→Bool→Bool→Bool) (R : Finset (Fin n)) : Set (Clause (Fin n)) :=
  {C | ∃ i∈R,∃ a b : Bool,T i a b=false ∧ C={(i,!a),(idx n (i.val+1),!b)}}
def Arc (h : Fin n) (R : Finset (Fin n)) := h∉R ∧ ∃ (z : Fin n) (k : ℕ),0 < k ∧ k < n ∧
  R=(Finset.range k).image (fun j=>idx n (z.val+j))

theorem certified (h : Fin n) (T : Fin n→Bool→Bool→Bool) (I : Finset (Fin (n-1)))
    (bad : IsBad (fun j=>T (station h j)) I) :
    Arc h (cycRows h I) ∧ ∃ p, IsRefutation (axiomSet T (cycRows h I)) p ∧
      p.length  ≤  6*(cycRows h I).card+1 ∧ ∀ C∈p,C.card  ≤  2 := by
  classical
  obtain ⟨s,k,pos,lim,rfl,imp⟩ := bad
  let I := segment (n-1) s k
  have member (j : ℕ) (lo : s ≤ j) (hi : j < s+k) : station h j∈cycRows h I :=
    Finset.mem_map.mpr ⟨⟨j,by omega⟩,(mem_segment _).mpr ⟨lo,hi⟩,rfl⟩
  have arc : Arc h (cycRows h I) := by
    constructor
    · intro m
      obtain ⟨j,_,ej⟩ := Finset.mem_map.mp m
      have all : h∈Finset.univ.map (embed h) := Finset.mem_map.mpr ⟨j,Finset.mem_univ _,ej⟩
      rw [whole] at all; simpa using all
    · refine ⟨station h s,k,pos,by omega,?_⟩
      ext i; constructor
      · rintro hi
        obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
        obtain ⟨lo,hi⟩ := (mem_segment j).mp hj
        refine Finset.mem_image.mpr ⟨j.val-s,Finset.mem_range.mpr (by omega),?_⟩
        rw [station_add]
        change station h (s+(j.val-s))=station h j.val
        congr 1; omega
      · intro hi
        obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
        rw [station_add]
        exact member (s+j) (by omega) (by have := Finset.mem_range.mp hj; omega)
  have ax : Forbidden (station h) (fun j=>T (station h j)) s k (axiomSet T (cycRows h I)) := by
    intro j lo hi a b e
    exact ⟨station h j,member j lo hi,a,b,e,by rw [station_add]⟩
  obtain ⟨p,hp,len,w⟩ := path_refute _ _ _ _ ax imp
  refine ⟨arc,p,hp,?_,w⟩
  simpa only [cycRows,Finset.card_map,I,seg_card _ _ _ lim] using len

def cutcost (T : Fin n→Bool→Bool→Bool) (price : Fin n→ℕ) (h : Fin n) (x : Fin n→Bool) :=
  ∑ i : Fin n, if i≠h ∧ T i (x i) (x (idx n (i.val+1)))=false then price i else 0

lemma loss_station (T : Fin n→Bool→Bool→Bool) (price : Fin n→ℕ) (h : Fin n) (x : Fin n→Bool) :
    cutcost T price h x = loss (fun j=>T (station h j)) (fun j : Fin (n-1)=>price (station h j.val)) (fun j=>x (station h j)) := by
  classical
  let term := fun i : Fin n=>if T i (x i) (x (idx n (i.val+1)))=false then price i else 0
  have splitCost : cutcost T price h x=(Finset.univ.filter (fun i=>i≠h)).sum term := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _; by_cases eq : i=h  <;> simp [eq,term]
  rw [splitCost,←whole,Finset.sum_map]
  unfold loss
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun z=>if T (station h i.val) (x (station h i.val)) (x z)=false then price (station h i.val) else 0) (station_add h i.val 1)

theorem cut_pack (T : Fin n→Bool→Bool→Bool) (price : Fin n→ℕ) (h : Fin n) :
    ∃ (P : Finset (Finset (Fin n))) (q : Finset (Fin n)→ℕ) (x : Fin n→Bool), P.card < n ∧
    (∀ J∈P,Arc h J ∧ (∃ p,IsRefutation (axiomSet T J) p ∧ p.length  ≤  6*J.card+1 ∧ ∀ C∈p,C.card  ≤  2) ∧ 0 < q J) ∧
    (∀ i : Fin n,(∑ J∈P,if i∈J then q J else 0)  ≤  price i) ∧
    cutcost T price h x=P.sum q ∧ ∀ y,P.sum q  ≤  cutcost T price h y := by
  classical
  let t := fun j=>T (station h j)
  let c := fun j : Fin (n-1)=>price (station h j.val)
  obtain ⟨A,z,y,card,hi,cap,val,low⟩ := linearPack t (n-1) c
  let f := cycRows h
  have injective : Function.Injective f := enc_inj h
  let q := fun J=>z (Function.invFun f J)
  have qeq (I) : q (f I)=z I := congrArg z (Function.leftInverse_invFun injective I)
  have total : (A.image f).sum q = A.sum z := by rw [Finset.sum_image (fun _ _ _ _ e=>injective e)]; exact Finset.sum_congr rfl (fun i _=>qeq i)
  let x := fun i : Fin n=>y ((perm h).symm i).val
  refine ⟨A.image f,q,x,by rw [Finset.card_image_of_injective _ injective]; have := NeZero.pos n; omega,?_,?_,?_,?_⟩
  · intro J hJ
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hJ
    obtain ⟨a,b⟩ := certified h T I (hi I hI).1
    exact ⟨a,b,(qeq I).symm ▸ (hi I hI).2⟩
  · intro i; rw [Finset.sum_image (fun _ _ _ _ e=>injective e)]
    by_cases cover : ∃ j,embed h j=i
    · obtain ⟨j,rfl⟩ := cover
      simp_rw [qeq]
      change (∑ I∈A,if embed h j∈I.map (embed h) then z I else 0) ≤ c j
      simpa using cap j
    · have clear (I) : i∉f I := fun mem=>by obtain ⟨j,_,e⟩ := Finset.mem_map.mp mem; exact cover ⟨j,e⟩
      simp [clear]
  · rw [total,loss_station,←val]
    unfold loss
    apply Finset.sum_congr rfl
    intro i _
    have lt := i.isLt; have pos := NeZero.pos n
    simp [t,c,x,station_index h (show i.val < n by omega),station_index h (show i.val+1 < n by omega)]
  · intro word; rw [total,loss_station]; exact low _
end PEqualNP.Outside.L_pcx_227_aux

open PEqualNP.Outside.L_pcx_227_aux PEqualNP.ProofComplexity in
theorem PEqualNP.Outside.L_pcx_227 : ∀ (n : ℕ) (hn : 0 < n) (T : Fin n → Bool → Bool → Bool) (price : Fin n → ℕ),
  let pos := fun k : ℕ => (⟨k % n, Nat.mod_lt _ hn⟩ : Fin n)
  let fails := fun (x : Fin n → Bool) (i : Fin n) => !(T i (x i) (x (pos (i.val + 1))))
  let cost := fun assignment => ∑ i : Fin n, if fails assignment i then price i else 0
  let openCost := fun (h : Fin n) (word : Fin n → Bool) =>
    ∑ i : Fin n, if i ≠ h ∧ fails word i = true then price i else 0
  let arc := fun (anchor : Fin n) (J : Finset (Fin n)) =>
    anchor ∉ J ∧ ∃ (s : Fin n) (k : ℕ), 0 < k ∧ k < n ∧
      J = (Finset.range k).image (fun j => pos (s.val + j))
  let axioms := fun (rows : Finset (Fin n)) =>
    {C : PEqualNP.ProofComplexity.Clause (Fin n) |
      ∃ i ∈ rows, ∃ a b : Bool, T i a b = false ∧
        C = {(i, !a), (pos (i.val + 1), !b)}}
  let cert := fun (J : Finset (Fin n)) =>
    ∃ π : List (PEqualNP.ProofComplexity.Clause (Fin n)),
      PEqualNP.ProofComplexity.IsRefutation (axioms J) π ∧ π.length ≤ 6 * J.card + 1 ∧
        ∀ C ∈ π, C.card ≤ 2
  ∃ (pack : Fin n → Finset (Finset (Fin n))) (qty : Fin n → Finset (Fin n) → ℕ)
    (witness : Fin n → (Fin n → Bool)),
    let value := fun cut : Fin n => ∑ J ∈ pack cut, qty cut J
    (∀ h : Fin n, (pack h).card < n ∧
      (∀ J ∈ pack h, arc h J ∧ cert J ∧ 0 < qty h J) ∧
      (∀ i : Fin n, (∑ J ∈ pack h, if i ∈ J then qty h J else 0) ≤ price i) ∧
      openCost h (witness h) = value h ∧ ∀ y : Fin n → Bool, value h ≤ openCost h y) ∧
    ((∀ z : Fin n → Bool, ∃ i : Fin n, fails z i = true) →
      ∃ (x : Fin n → Bool) (h : Fin n), cost x = price h + value h ∧
        (∀ k : Fin n, cost x ≤ price k + value k) ∧ ∀ y : Fin n → Bool, cost x ≤ cost y) := by
  classical
  intro n hn T price pos fails cost openCost arc ax cert
  letI : NeZero n := ⟨by omega⟩
  have eqcut (h : Fin n) (x : Fin n→Bool) : openCost h x=cutcost T price h x := by
    unfold cutcost; dsimp only [openCost,fails,pos]
    apply Finset.sum_congr rfl
    intro i _
    have flip (b : Bool) : ((!b)=true) ↔ b=false := by cases b <;> decide
    simp only [flip]
    rfl
  choose P q x spec using cut_pack T price
  let val := fun h=> (P h).sum (q h)
  have open_eq (h : Fin n) : openCost h (x h)=val h := (eqcut ..).trans (spec h).2.2.2.1
  have open_min (h : Fin n) (y : Fin n→Bool) : val h ≤ openCost h y := (eqcut h y).symm ▸ (spec h).2.2.2.2 y
  refine ⟨P,q,x,?_,?_⟩
  · intro h
    exact ⟨(spec h).1,(spec h).2.1,(spec h).2.2.1,open_eq h,open_min h⟩
  · intro bad
    have split (y : Fin n→Bool) (h : Fin n) :
        cost y=(if fails y h then price h else 0)+openCost h y := by
      calc
        _ = ∑ i : Fin n, ((if h=i then (if fails y h then price h else 0) else 0)+
          (if i≠h ∧ fails y i=true then price i else 0)) := by
            apply Finset.sum_congr rfl
            intro i _
            by_cases e : i=h
            · subst i; simp
            · simp [e,Ne.symm e]
        _ = _ := by simp [Finset.sum_add_distrib,openCost]
    let f := fun h=>price h+val h
    obtain ⟨h,_,mh⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin n)) f Finset.univ_nonempty
    have lower (y) : f h ≤ cost y := by
      obtain ⟨j,hj⟩ := bad y
      rw [split y j,hj,if_pos rfl]
      exact (mh j (Finset.mem_univ _)).trans (Nat.add_le_add_left (open_min j y) _)
    have up : cost (x h) ≤ f h := by
      rw [split,open_eq]; dsimp only [f]; split <;> omega
    have eq := le_antisymm up (lower (x h))
    exact ⟨x h,h,eq,fun j=>eq ▸ mh j (Finset.mem_univ _),fun y=>eq ▸ lower y⟩
