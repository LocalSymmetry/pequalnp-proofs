import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25535_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

variable {n : ℕ}

abbrev Pred (n : ℕ) := Fin n → Fin n → Prop
def lit (i : Fin n) : Pred n := fun u v => i = u ∨ i = v
def input (u v : Fin n) := List.ofFn fun i : Fin n => decide (i = u ∨ i = v)

def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def vals (gs : List Gate) (u v : Fin n) := gs.foldl step (input u v)

lemma foldLen (gs : List Gate) (w : List Bool) : (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma vals_snoc (gs : List Gate) (g : Gate) (u v : Fin n) :
    vals (gs ++ [g]) u v = step (vals gs u v) g := by simp [vals, List.foldl_append]

lemma valLen (gs : List Gate) (u v : Fin n) : (vals gs u v).length = n + gs.length := by
  simp [vals, foldLen, input]

structure Net (n : ℕ) where
  gs : List Gate
  mono : Monotone2 ⟨gs, 0⟩
  back : ReadsBack n ⟨gs, 0⟩

def Has (N : Net n) (p : Pred n) : Prop :=
  ∃ i, i < n + N.gs.length ∧ ∀ u v, (vals N.gs u v).getD i false = true ↔ p u v

lemma Has.congr {N : Net n} {p q : Pred n} (h : Has N p) (e : ∀ u v, p u v ↔ q u v) :
    Has N q := by
  obtain ⟨i, hi, he⟩ := h
  exact ⟨i, hi, fun u v => (he u v).trans (e u v)⟩

def Ext (A B : Net n) (k : ℕ) : Prop :=
  B.gs.length ≤ A.gs.length + k ∧ ∀ p, Has A p → Has B p

lemma Ext.refl (A : Net n) : Ext A A 0 := ⟨by omega, fun _ h => h⟩
lemma Ext.trans {A B C : Net n} {a b : ℕ} (h : Ext A B a) (h' : Ext B C b) :
    Ext A C (a+b) := ⟨by have := h.1; have := h'.1; omega, fun p x => h'.2 p (h.2 p x)⟩
lemma Ext.weaken {A B : Net n} {a b : ℕ} (h : Ext A B a) (le : a ≤ b) :
    Ext A B b := ⟨by have := h.1; omega, h.2⟩

lemma getLeft {α : Type} (a b : List α) (i : ℕ) (d : α) (hi : i < a.length) :
    (a ++ b).getD i d = a.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append, hi]

lemma getLast {α : Type} (a : List α) (x d : α) : (a ++ [x]).getD a.length d = x := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append]

def snoc (A : Net n) (g : Gate) (hm : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hb : ∀ i ∈ g.inputs, i < n + A.gs.length) : Net n where
  gs := A.gs ++ [g]
  mono := by
    intro x hx
    change x ∈ A.gs ++ [g] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact A.mono x hx
    · obtain rfl := List.mem_singleton.mp hx
      exact hm
  back := by
    intro j hj i hi
    change j < (A.gs ++ [g]).length at hj
    change i ∈ ((A.gs ++ [g]).getD j _).inputs at hi
    by_cases h : j < A.gs.length
    · rw [getLeft _ _ _ _ h] at hi
      exact A.back j h i hi
    · have hj' : j = A.gs.length := by simp at hj; omega
      subst j
      rw [getLast] at hi
      exact hb i hi

lemma snocExt (A : Net n) (g : Gate) (hm hb) : Ext A (snoc A g hm hb) 1 := by
  constructor
  · simp [snoc]
  · rintro p ⟨i, hi, he⟩
    refine ⟨i, by simp [snoc]; omega, fun u v => ?_⟩
    change (vals (A.gs ++ [g]) u v).getD i false = true ↔ p u v
    rw [vals_snoc, step, getLeft _ _ _ _ (by simpa [valLen] using hi)]
    exact he u v

lemma newHas (A : Net n) (g : Gate) (hm hb) :
    Has (snoc A g hm hb) (fun u v => g.op.eval (g.inputs.map fun i => (vals A.gs u v).getD i false) = true) := by
  refine ⟨n + A.gs.length, by simp [snoc], fun u v => ?_⟩
  change (vals (A.gs ++ [g]) u v).getD _ false = true ↔ _
  rw [vals_snoc, ← valLen A.gs u v, step, getLast]

lemma combine (A : Net n) {p q : Pred n} (hp : Has A p) (hq : Has A q) (both : Bool) :
    ∃ B, Ext A B 1 ∧ Has B (fun u v => if both then p u v ∧ q u v else p u v ∨ q u v) := by
  obtain ⟨i, hi, ei⟩ := hp
  obtain ⟨j, hj, ej⟩ := hq
  let g : Gate := ⟨if both then GateOp.and else GateOp.or, [i,j]⟩
  have hm : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by cases both <;> simp [g]
  have hb : ∀ a ∈ g.inputs, a < n + A.gs.length := by simp [g, hi, hj]
  refine ⟨_, snocExt A g hm hb, (newHas A g hm hb).congr ?_⟩
  intro u v
  cases both <;> simp [g, GateOp.eval, ← ei u v, ← ej u v]

def blank (n : ℕ) : Net n where
  gs := []
  mono := by intro g h; cases h
  back := by intro j h; exact (Nat.not_lt_zero j h).elim

lemma raw (i : Fin n) : Has (blank n) (lit i) := by
  refine ⟨i.val, by simpa [blank] using i.isLt, fun u v => ?_⟩
  simp [blank, vals, input, List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, lit]

lemma seed (n : ℕ) : ∃ A : Net n, A.gs.length ≤ 1 ∧ Has A (fun _ _ => False) ∧ ∀ i, Has A (lit i) := by
  let g : Gate := ⟨.or, []⟩
  have hm : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by simp [g]
  have hb : ∀ i ∈ g.inputs, i < n + (blank n).gs.length := by simp [g]
  have e := snocExt (blank n) g hm hb
  exact ⟨_, by simpa [blank] using e.1, (newHas (blank n) g hm hb).congr (by simp [g, GateOp.eval]), fun i => e.2 _ (raw i)⟩

def group (f : Fin n → Option (Fin n)) (s : Finset (Fin n)) (a : Fin n) : Pred n :=
  fun u v => (u ∈ s ∧ f u = some a) ∨ (v ∈ s ∧ f v = some a)

lemma packGroups (A : Net n) (hz : Has A (fun _ _ => False)) (hr : ∀ i, Has A (lit i))
    (f : Fin n → Option (Fin n)) (s : Finset (Fin n)) :
    ∃ B, Ext A B s.card ∧ ∀ a, Has B (group f s a) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨A, by simpa using Ext.refl A, fun a => hz.congr (by simp [group])⟩
  | @insert i s hi ih =>
    obtain ⟨B, e, h⟩ := ih
    cases hf : f i with
    | none =>
      refine ⟨B, e.weaken (by simp [hi]), fun a => (h a).congr ?_⟩
      intro u v
      simp only [group, Finset.mem_insert]
      grind
    | some a =>
      obtain ⟨C, e', hw⟩ := combine B (h a) (e.2 _ (hr i)) false
      refine ⟨C, by simpa [hi] using e.trans e', fun b => ?_⟩
      by_cases hab : a = b
      · subst b
        apply hw.congr
        intro u v
        simp only [group, lit, Bool.false_eq_true, if_false, Finset.mem_insert]
        grind
      · apply (e'.2 _ (h b)).congr
        intro u v
        simp only [group, Finset.mem_insert]
        grind

def seen (f : Fin n → Option (Fin n)) (s : Finset (Fin n)) (i : Fin n) :=
  ∃ a ∈ s, f i = some a
def anySeen (f : Fin n → Option (Fin n)) (s : Finset (Fin n)) : Pred n :=
  fun u v => seen f s u ∨ seen f s v
def twoSeen (f : Fin n → Option (Fin n)) (s : Finset (Fin n)) : Pred n :=
  fun u v => seen f s u ∧ seen f s v ∧ f u ≠ f v

lemma seen_insert (f : Fin n → Option (Fin n)) (s : Finset (Fin n)) (a i : Fin n) :
    seen f (insert a s) i ↔ f i = some a ∨ seen f s i := by
  simp [seen, Finset.exists_mem_insert]

lemma two_insert (f : Fin n → Option (Fin n)) (s : Finset (Fin n)) (a : Fin n) (ha : a ∉ s) (u v : Fin n) :
    (twoSeen f s u v ∨ ((f u = some a ∨ f v = some a) ∧ anySeen f s u v)) ↔
      twoSeen f (insert a s) u v := by
  have hdis (i : Fin n) : f i = some a → ¬seen f s i := by
    rintro he ⟨b, hb, hb'⟩
    grind
  have hsame : f u = f v → (seen f s u ↔ seen f s v) := by intro h; simp [seen, h]
  simp only [twoSeen, anySeen, seen_insert]
  have := hdis u
  have := hdis v
  grind

lemma scan (A : Net n) (hz : Has A (fun _ _ => False)) (f : Fin n → Option (Fin n))
    (hgrp : ∀ a, Has A (fun u v => f u = some a ∨ f v = some a)) (s : Finset (Fin n)) :
    ∃ B, Ext A B (3*s.card) ∧ Has B (anySeen f s) ∧ Has B (twoSeen f s) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨A, by simpa using Ext.refl A, hz.congr (by simp [seen,anySeen]), hz.congr (by simp [seen,twoSeen])⟩
  | @insert a s ha ih =>
    obtain ⟨B,e,oldAny,oldTwo⟩ := ih
    have tag := e.2 _ (hgrp a)
    obtain ⟨C,eC,hCross⟩ := combine B tag oldAny true
    obtain ⟨D,eD,hTwo⟩ := combine C (eC.2 _ oldTwo) hCross false
    obtain ⟨E,eE,hAny⟩ := combine D (eD.2 _ (eC.2 _ tag)) (eD.2 _ (eC.2 _ oldAny)) false
    refine ⟨E, (((e.trans eC).trans eD).trans eE).weaken (by rw [Finset.card_insert_of_notMem ha]; omega),
      hAny.congr ?_, (eE.2 _ hTwo).congr ?_⟩
    · intro u v
      simp only [Bool.false_eq_true, if_false, anySeen, seen_insert]
      tauto
    · intro u v
      simpa only [Bool.false_eq_true, if_false, if_true] using two_insert f s a ha u v

def different (f : Fin n → Option (Fin n)) : Pred n :=
  fun u v => f u ≠ none ∧ f v ≠ none ∧ f u ≠ f v

lemma distinctTags (A : Net n) (hz : Has A (fun _ _ => False)) (hr : ∀ i, Has A (lit i))
    (f : Fin n → Option (Fin n)) : ∃ B, Ext A B (4*n) ∧ Has B (different f) := by
  classical
  obtain ⟨B,e,h⟩ := packGroups A hz hr f Finset.univ
  obtain ⟨C,e',_,hTwo⟩ := scan B (e.2 _ hz) f (fun a => (h a).congr (by simp [group])) Finset.univ
  refine ⟨C, (e.trans e').weaken (by simp; omega), hTwo.congr ?_⟩
  intro u v
  cases hu : f u <;> cases hv : f v <;> simp [different, twoSeen, seen, hu, hv]


def paint (r : Fin n → ℕ) (p : Fin n → Option (Fin n)) (bound : ∀ i, r i < n)
    (inc : ∀ i j, p i = some j → r i < r j) (i : Fin n) : Bool :=
  match hp : p i with
  | none => false
  | some j => !(paint r p bound inc j)
termination_by n - r i
decreasing_by have := inc i j hp; have := bound j; omega

lemma paint_edge (r : Fin n → ℕ) (p : Fin n → Option (Fin n)) (bound : ∀ i, r i < n)
    (inc : ∀ i j, p i = some j → r i < r j) {i j} (h : p i = some j) :
    paint r p bound inc i ≠ paint r p bound inc j := by
  conv_lhs => rw [paint]
  split <;> simp_all

def center (p : Fin n → Option (Fin n)) (color : Fin n → Bool) (b : Bool) (i : Fin n) : Option (Fin n) :=
  some (if color i = b then (p i).getD i else i)
def leaves (color : Fin n → Bool) (b : Bool) (i : Fin n) : Option (Fin n) :=
  if color i = b then some i else none

def allows (p : Fin n → Option (Fin n)) (c : Fin n → Bool) (b : Bool) : Pred n :=
  fun u v => u ≠ v ∧ ¬(c u = b ∧ p u = some v) ∧ ¬(c v = b ∧ p v = some u)

lemma allows_iff (p : Fin n → Option (Fin n)) (c : Fin n → Bool)
    (proper : ∀ i j, p i = some j → c i ≠ c j) (b : Bool) (u v : Fin n) :
    (different (center p c b) u v ∨ different (leaves c b) u v) ↔ allows p c b u v := by
  have huv := proper u v
  have hvu := proper v u
  by_cases he : u = v
  · subst v; simp [different,allows]
  · by_cases hu : c u = b <;> by_cases hv : c v = b <;>
      cases hpu : p u <;> cases hpv : p v <;>
      simp_all [different, center, leaves, allows, eq_comm]

lemma star (A : Net n) (hz : Has A (fun _ _ => False)) (hr : ∀ i, Has A (lit i))
    (p : Fin n → Option (Fin n)) (c : Fin n → Bool) (proper : ∀ i j, p i = some j → c i ≠ c j)
    (b : Bool) : ∃ B, Ext A B (8*n+1) ∧ Has B (allows p c b) := by
  obtain ⟨B,e,hC⟩ := distinctTags A hz hr (center p c b)
  obtain ⟨C,e',hL⟩ := distinctTags B (e.2 _ hz) (fun i => e.2 _ (hr i)) (leaves c b)
  obtain ⟨D,eD,hw⟩ := combine C (e'.2 _ hC) hL false
  exact ⟨D, ((e.trans e').trans eD).weaken (by omega), hw.congr (by simpa using allows_iff p c proper b)⟩

lemma buildAll {ι : Type} [DecidableEq ι] (A : Net n) (hz : Has A (fun _ _ => False))
    (hr : ∀ i, Has A (lit i)) {q : Pred n} (hq : Has A q)
    (p : ι → Fin n → Option (Fin n)) (c : ι → Fin n → Bool) (b : ι → Bool)
    (proper : ∀ t i j, p t i = some j → c t i ≠ c t j) (s : Finset ι) :
    ∃ B, Ext A B (s.card * (8*n+2)) ∧ Has B (fun u v => q u v ∧ ∀ t ∈ s, allows (p t) (c t) (b t) u v) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨A, by simpa using Ext.refl A, hq.congr (by simp)⟩
  | @insert t s ht ih =>
    obtain ⟨B,e,h⟩ := ih
    obtain ⟨C,e',hs⟩ := star B (e.2 _ hz) (fun i => e.2 _ (hr i)) (p t) (c t) (proper t) (b t)
    obtain ⟨D,eD,hw⟩ := combine C (e'.2 _ h) hs true
    refine ⟨D, ((e.trans e').trans eD).weaken (by rw [Finset.card_insert_of_notMem ht, Nat.add_mul]; omega), hw.congr ?_⟩
    intro u v
    simp only [if_true, Finset.forall_mem_insert]
    tauto

def neighbors (G : Fin n → Fin n → Bool) (r : Equiv.Perm (Fin n)) (i : Fin n) :=
  Finset.univ.filter fun j : Fin n => r i < r j ∧ (G i j = true ∨ G j i = true)

noncomputable def parent {d : ℕ} (G : Fin n → Fin n → Bool) (r : Equiv.Perm (Fin n))
    (t : Fin d) (i : Fin n) : Option (Fin n) := (neighbors G r i).toList[t.val]?

lemma parent_mem {d : ℕ} (G : Fin n → Fin n → Bool) (r : Equiv.Perm (Fin n))
    (t : Fin d) {i j} (hp : parent G r t i = some j) : j ∈ neighbors G r i :=
  Finset.mem_toList.mp (List.mem_of_getElem? hp)

lemma parent_iff {d : ℕ} (G : Fin n → Fin n → Bool) (r : Equiv.Perm (Fin n))
    (hd : ∀ i, (neighbors G r i).card ≤ d) (i j : Fin n) :
    (∃ t : Fin d, parent G r t i = some j) ↔ r i < r j ∧ (G i j = true ∨ G j i = true) := by
  constructor
  · rintro ⟨t,ht⟩
    exact (Finset.mem_filter.mp (parent_mem G r t ht)).2
  · intro h
    have hm : j ∈ (neighbors G r i).toList := Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    obtain ⟨k,hk,he⟩ := List.getElem_of_mem hm
    have hk' : k < d := lt_of_lt_of_le (by simpa using hk : k < (neighbors G r i).card) (hd i)
    exact ⟨⟨k,hk'⟩, by simpa [parent, List.getElem?_eq_getElem hk] using congrArg some he⟩

lemma construct (n d : ℕ) (G : Fin n → Fin n → Bool) (rank : Equiv.Perm (Fin n))
    (hd : ∀ i, (neighbors G rank i).card ≤ d) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.output < n + D.size ∧
      D.size ≤ 8 * (n+1) * (2*d+1) + 2 ∧
      ∀ u v : Fin n, D.eval (input u v) = decide (u ≠ v ∧ G u v = false ∧ G v u = false) := by
  classical
  let p := @parent n d G rank
  let r := fun i : Fin n => (rank i).val
  have hbound : ∀ i, r i < n := fun i => (rank i).isLt
  have hinc (t : Fin d) (i j : Fin n) (hp : p t i = some j) : r i < r j :=
    (Finset.mem_filter.mp (parent_mem G rank t hp)).2.1
  let c := fun t : Fin d => paint r (p t) hbound (hinc t)
  have hproper (t : Fin d) (i j : Fin n) (hp : p t i = some j) : c t i ≠ c t j :=
    paint_edge r (p t) hbound (hinc t) hp
  obtain ⟨A,hA,hz,hr⟩ := seed n
  obtain ⟨B,e,hq⟩ := distinctTags A hz hr some
  have hneq : Has B (fun u v => u ≠ v) := hq.congr (by simp [different])
  obtain ⟨C,e',hw⟩ := buildAll B (e.2 _ hz) (fun i => e.2 _ (hr i)) hneq
    (ι := Fin d × Bool) (fun t => p t.1) (fun t => c t.1) Prod.snd (fun t => hproper t.1) Finset.univ
  obtain ⟨w,hwlt,he⟩ := hw
  refine ⟨⟨C.gs,w⟩, C.mono,C.back, hwlt, ?_, ?_⟩
  · change C.gs.length ≤ _
    have h1 := e.1
    have h2 := e'.1
    simp at h2
    nlinarith
  · intro u v
    have hm : (u ≠ v ∧ ∀ t : Fin d × Bool, t ∈ Finset.univ → allows (p t.1) (c t.1) t.2 u v) ↔
        u ≠ v ∧ G u v = false ∧ G v u = false := by
      have hf := parent_iff G rank hd u v
      have hb := parent_iff G rank hd v u
      change (∃ t, p t u = some v) ↔ _ at hf
      change (∃ t, p t v = some u) ↔ _ at hb
      constructor
      · rintro ⟨hne, hall⟩
        have neverUV (t : Fin d) := (hall (t,c t u) (Finset.mem_univ _)).2.1
        have neverVU (t : Fin d) := (hall (t,c t v) (Finset.mem_univ _)).2.2
        have hruv : rank u ≠ rank v := fun h => hne (rank.injective h)
        rcases lt_or_gt_of_ne hruv with hlt | hlt
        · have hnot : ¬(G u v = true ∨ G v u = true) := by
            intro h
            obtain ⟨t,ht⟩ := hf.mpr ⟨hlt,h⟩
            exact neverUV t ⟨rfl,ht⟩
          cases hu : G u v <;> cases hv : G v u <;> simp_all
        · have hnot : ¬(G v u = true ∨ G u v = true) := by
            intro h
            obtain ⟨t,ht⟩ := hb.mpr ⟨hlt,h⟩
            exact neverVU t ⟨rfl,ht⟩
          cases hu : G u v <;> cases hv : G v u <;> simp_all
      · rintro ⟨hne,hu,hv⟩
        refine ⟨hne, fun t _ => ⟨hne, ?_, ?_⟩⟩
        · rintro ⟨_,h⟩
          simpa [hu,hv] using (hf.mp ⟨t.1,h⟩).2
        · rintro ⟨_,h⟩
          simpa [hu,hv] using (hb.mp ⟨t.1,h⟩).2
    change (vals C.gs u v).getD w false = _
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using (he u v).trans hm

end PEqualNP.Outside.L_meta_25535_aux

theorem PEqualNP.Outside.L_meta_25535 : (∀ (n d : ℕ) (G : Fin n → Fin n → Bool) (rank : Equiv.Perm (Fin n)),
  (∀ i : Fin n, (Finset.univ.filter (fun j : Fin n =>
    rank i < rank j ∧ (G i j = true ∨ G j i = true))).card ≤ d) →
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.Monotone2 D ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n D ∧
    D.output < n + D.size ∧ D.size ≤ 8 * (n + 1) * (2 * d + 1) + 2 ∧
    ∀ u v : Fin n,
      D.eval (List.ofFn (fun i : Fin n => decide (i = u ∨ i = v))) =
        decide (u ≠ v ∧ G u v = false ∧ G v u = false)) := by
  exact PEqualNP.Outside.L_meta_25535_aux.construct
