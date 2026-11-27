import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_26027_aux.Normalize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_init (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_init [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_init gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_init gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)

def rv (w : List Bool) : Bool ⊕ ℕ → Bool
  | .inl b => b
  | .inr t => w.getD t false
theorem rv_ext (hs e : List Gate) (y : List Bool) (r : Bool ⊕ ℕ) (h : ∀ t, r = .inr t → t < y.length + hs.length) :
    rv (run (hs ++ e) y) r = rv (run hs y) r := by
  rcases r with b | t
  · rfl
  · exact run_init _ _ _ _ (h t rfl)

theorem gv (N : ℕ) (C : Circuit) (hb : ReadsBack N C) (x : List Bool) (hx : x.length = N) (j : ℕ)
    (hj : j < C.gates.length) :
    (run C.gates x).getD (N + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (run C.gates x).getD i false) := by
  have hw := run_gate C.gates x j hj
  have he : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  rw [hx, ← he] at hw
  rw [hw]
  congr 1
  exact List.map_congr_left fun i hi => if_pos (hb j hj i hi)

theorem past (gs : List Gate) (x : List Bool) (i : ℕ) (hi : x.length + gs.length ≤ i) :
    (run gs x).getD i false = false :=
  List.getD_eq_default _ _ (by rw [run_length]; exact hi)

theorem oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) :
    (PEqualNP.Represents.oneEach u v).length = n + m := by
  simp [PEqualNP.Represents.oneEach]

theorem oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (PEqualNP.Represents.oneEach u v).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  unfold PEqualNP.Represents.oneEach
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < n
  · rw [List.getElem?_append_left (by simpa using h)]
    simp only [List.getElem?_ofFn]
    simp [h, Fin.ext_iff]
    omega
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn, List.getElem?_ofFn]
    by_cases h2 : i - n < m
    · simp [h2, Fin.ext_iff]
      have hu : ¬ i = u.val := by omega
      by_cases hv : i = n + v.val
      · simp [hv]
      · have hv' : ¬ i - n = v.val := by omega
        simp [hu, hv, hv']
    · simp [h2]
      omega

theorem sa_val {n : ℕ} (u : Fin (n + 1)) (a : Fin n) :
    ((u.succAbove a : Fin (n + 1)) : ℕ) = if (a : ℕ) < u then (a : ℕ) else a + 1 := by
  by_cases h : (a : ℕ) < u
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h)]; simp [h]
  · rw [Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)]; simp [h]

def reads (g : Gate) (w : ℕ) : Prop :=
  (g.op = .not ∧ g.inputs.head? = some w) ∨ (g.op ≠ .not ∧ w ∈ g.inputs)

def Good (P : Prop) (g : Gate) : Prop :=
  ((g.op = .not ∧ ∃ a, g.inputs = [a]) ∨
    ((g.op = .and ∨ g.op = .or) ∧ ∃ a b, a ≠ b ∧ g.inputs = [a,b])) ∧
    (P → g.op = .and ∨ g.op = .or)

theorem good_shape {P : Prop} {g : Gate} (h : Good P g) :
    (g.op = .not → g.inputs.length = 1) ∧
    (g.op ≠ .not → g.inputs.length = 2 ∧ g.inputs.Nodup) := by
  rcases h.1 with ⟨ho,a,ha⟩ | ⟨ho,a,b,hn,ha⟩
  · simp [ho,ha]
  · rcases ho with ho|ho <;> simp [ho,ha,hn]

theorem good_fan {P : Prop} {C : Circuit} (h : ∀ g ∈ C.gates, Good P g) : FanInTwo C := by
  intro g hg
  rcases (h g hg).1 with ⟨ho,a,ha⟩ | ⟨ho,a,b,_,ha⟩
  · simp [ho,ha]
  · rcases ho with ho|ho <;> simp [ho,ha]

theorem good_mono {P : Prop} {C : Circuit} (h : ∀ g ∈ C.gates, Good P g) :
    P → Monotone2 C := by
  intro p g hg
  exact ⟨by simpa using (h g hg).2 p,(good_fan h g hg).2⟩

theorem good_read {P : Prop} {g : Gate} (h : Good P g) (w : ℕ) : reads g w ↔ w ∈ g.inputs := by
  rcases h.1 with ⟨ho,a,ha⟩ | ⟨ho,a,b,_,ha⟩
  · simp [reads,ho,ha,eq_comm]
  · rcases ho with ho|ho <;> simp [reads,ho]

end PEqualNP.Outside.L_meta_26027_aux.Normalize

namespace PEqualNP.Outside.L_meta_26027_aux.Normalize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem emit (P : Prop) (N : ℕ) (hs : List Gate) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (hmon : P → op = GateOp.and ∨ op = GateOp.or)
    (rs : List (Bool ⊕ ℕ)) (hl : rs.length ≤ 2) (hv : ∀ r ∈ rs, ∀ t, r = .inr t → t < N + hs.length) :
    ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, Good P g) ∧
      (∀ g ∈ e, ∀ t ∈ g.inputs, t < N + hs.length) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
      ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
  have keep : ∀ r : Bool ⊕ ℕ, (∀ t, r = .inr t → t < N + hs.length) → (∀ y : List Bool, y.length = N → rv (run hs y) r = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, Good P g) ∧
        (∀ g ∈ e, ∀ t ∈ g.inputs, t < N + hs.length) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro r h1 h2
    exact ⟨r, [], by simp, by simp, by simp, by simpa using h1, fun y hy => by rw [List.append_nil]; exact h2 y hy⟩
  have add : ∀ g : Gate, Good P g → (∀ t ∈ g.inputs, t < N + hs.length) →
      (∀ y : List Bool, y.length = N → g.op.eval (g.inputs.map fun i => (run hs y).getD i false) = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, Good P g) ∧
        (∀ g ∈ e, ∀ t ∈ g.inputs, t < N + hs.length) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro g h1 h1' h2
    refine ⟨.inr (N + hs.length), [g], by simp, by simpa using h1, by simpa using h1', ?_, fun y hy => ?_⟩
    · intro t ht
      cases ht
      simp
    · have : N + hs.length = (run hs y).length := by rw [run_length, hy]
      simp only [rv]
      rw [run_snoc, this, getD_at]
      exact h2 y hy
  by_cases hn : op = GateOp.not
  · subst op
    rcases rs with _ | ⟨r, rs⟩
    · exact keep (.inl true) (by simp) (by intro y hy; rfl)
    · have hr := hv r (by simp)
      rcases r with b | t
      · exact keep (.inl (!b)) (by simp) (by intro y hy; rfl)
      · exact add ⟨.not,[t]⟩ ⟨Or.inl ⟨rfl,t,rfl⟩,hmon⟩ (by simpa using hr t rfl)
          (by intro y hy; rfl)
  have hop' : op = GateOp.and ∨ op = GateOp.or := by tauto
  rcases rs with _ | ⟨r, _ | ⟨s, _ | ⟨u, rs⟩⟩⟩
  · rcases hop' with rfl | rfl
    · exact keep (.inl true) (by simp) (by intro y _; rfl)
    · exact keep (.inl false) (by simp) (by intro y _; rfl)
  · have hr := hv r (by simp)
    rcases hop' with rfl | rfl
    · exact keep r hr (by intro y _; simp [GateOp.eval])
    · exact keep r hr (by intro y _; simp [GateOp.eval])
  · have hr := hv r (by simp)
    have hs' := hv s (by simp)
    rcases hop' with rfl | rfl
    · rcases r with b | t
      · cases b
        · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
        · by_cases same : t=q
          · subst q
            exact keep (.inr t) hr (by intro y _; simp [GateOp.eval,rv])
          · exact add ⟨GateOp.and,[t,q]⟩ ⟨Or.inr ⟨Or.inl rfl,t,q,same,rfl⟩,fun _ => Or.inl rfl⟩
              (by simp; exact ⟨hr t rfl, hs' q rfl⟩) (by intro y _; simp [GateOp.eval,rv])
    · rcases r with b | t
      · cases b
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
        · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · by_cases same : t=q
          · subst q
            exact keep (.inr t) hr (by intro y _; simp [GateOp.eval,rv])
          · exact add ⟨GateOp.or,[t,q]⟩ ⟨Or.inr ⟨Or.inr rfl,t,q,same,rfl⟩,fun _ => Or.inr rfl⟩
              (by simp; exact ⟨hr t rfl, hs' q rfl⟩) (by intro y _; simp [GateOp.eval,rv])
  · simp at hl

theorem engine {X : Type} (P : Prop) (n M : ℕ) (C : Circuit) (src tgt : X → List Bool) (hsrc : ∀ x, (src x).length = n) (htgt : ∀ x, (tgt x).length = M) (F : Finset ℕ)
    (hC : FanInTwo C) (hmon : P → Monotone2 C)
    (h0 : ∀ w < n, (∃ b, ∀ x, (src x).getD w false = b) ∨ ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false)
    (hne : ¬∃ b, ∀ x, C.eval (src x) = b)
    (hF : ∀ j ∈ F, j < C.gates.length ∧ ((∃ b, ∀ x, (run C.gates (src x)).getD (n + j) false = b) ∨
      ∃ w < n + j, ∀ x, (run C.gates (src x)).getD (n + j) false = (run C.gates (src x)).getD w false)) :
    ∃ D : Circuit, (∀ g ∈ D.gates, Good P g) ∧ ReadsBack M D ∧ D.size + F.card ≤ C.size ∧
      ∀ x, D.eval (tgt x) = C.eval (src x) := by
  classical
  have key : ∀ k, k ≤ C.gates.length → ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, Good P g) ∧
      (∀ i (hi : i < hs.length), ∀ t ∈ hs[i].inputs, t < M + i) ∧
      hs.length + (F.filter fun j => j < k).card ≤ k ∧
      (∀ w t, w < n + k → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + k, (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fun w => if h : ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false then .inr h.choose else if hb : ∃ b, ∀ x, (src x).getD w false = b then .inl hb.choose else .inl false, by simp, by simp, by simp, ?_, ?_⟩
      · intro w t hw ht
        beta_reduce at ht
        split_ifs at ht with h1 h2
        cases ht
        simpa using h1.choose_spec.1
      · intro x w hw
        simp only [Nat.add_zero] at hw
        rw [run_input _ _ _ (by rw [hsrc]; exact hw)]
        beta_reduce
        split_ifs with h1 h2
        · exact h1.choose_spec.2 x
        · exact h2.choose_spec x
        · rcases h0 w hw with h | h
          · exact absurd h h2
          · exact absurd h h1
    | succ k ih =>
      intro hk
      obtain ⟨hs, m, h1, h5, h2, h3, h4⟩ := ih (by omega)
      have hk' : k < C.gates.length := by omega
      have fin : ∀ (r : Bool ⊕ ℕ) (e : List Gate), (∀ g ∈ e, Good P g) → (∀ g ∈ e, ∀ t ∈ g.inputs, t < M + hs.length) →
          (∀ t, r = .inr t → t < M + hs.length + e.length) → e.length + (if k ∈ F then 1 else 0) ≤ 1 →
          (∀ x : X, (run C.gates (src x)).getD (n + k) false = rv (run (hs ++ e) (tgt x)) r) →
          ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, Good P g) ∧
      (∀ i (hi : i < hs.length), ∀ t ∈ hs[i].inputs, t < M + i) ∧
      hs.length + (F.filter fun j => j < k + 1).card ≤ k + 1 ∧
      (∀ w t, w < n + (k + 1) → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + (k + 1), (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
        intro r e he he' hr hlen hval
        refine ⟨hs ++ e, Function.update m (n + k) r, ?_, ?_, ?_, ?_, ?_⟩
        · intro g hg
          rcases List.mem_append.1 hg with hg | hg
          · exact h1 g hg
          · exact he g hg
        · intro i hi t ht
          rw [List.getElem_append] at ht
          split_ifs at ht with hih
          · exact h5 i hih t ht
          · have hmem : e[i - hs.length]'(by simp at hi; omega) ∈ e := List.mem_iff_getElem.mpr ⟨_, _, rfl⟩
            have := he' _ hmem t ht
            omega
        · have e1 : (F.filter fun j => j < k + 1) ⊆ (F.filter fun j => j < k) ∪ (if k ∈ F then {k} else ∅) := by
            intro j hj
            rw [Finset.mem_filter] at hj
            rcases Nat.lt_or_ge j k with h | h
            · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hj.1, h⟩)
            · have : j = k := by omega
              subst this
              rw [if_pos hj.1]; simp
          have e2 := (Finset.card_le_card e1).trans (Finset.card_union_le _ _)
          rw [List.length_append]
          by_cases hkF : k ∈ F
          · rw [if_pos hkF] at e2 hlen
            rw [Finset.card_singleton] at e2
            omega
          · rw [if_neg hkF] at e2 hlen
            rw [Finset.card_empty] at e2
            omega
        · intro w t hw ht
          rw [List.length_append]
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self] at ht
            have := hr t ht; omega
          · rw [Function.update_of_ne hwe] at ht
            have := h3 w t (by omega) ht; omega
        · intro x w hw
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self]; exact hval x
          · rw [Function.update_of_ne hwe, h4 x w (by omega)]
            refine (rv_ext hs e (tgt x) (m w) fun t ht => ?_).symm
            have := h3 w t (by omega) ht
            rw [htgt]; exact this
      by_cases hkF : k ∈ F
      · rcases (hF k hkF).2 with ⟨b, hb⟩ | ⟨w, hw, hb⟩
        · exact fin (.inl b) [] (by simp) (by simp) (by simp) (by simp [hkF]) (fun x => hb x)
        · refine fin (m w) [] (by simp) (by simp) (fun t ht => by simpa using h3 w t hw ht) (by simp [hkF]) (fun x => ?_)
          rw [List.append_nil, ← h4 x w hw]
          exact hb x
      · have hg := hC _ (List.getElem_mem hk')
        have hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or ∨ C.gates[k].op = GateOp.not := by simpa using hg.1
        let m' : ℕ → Bool ⊕ ℕ := fun i => if i < n + k then m i else .inl false
        obtain ⟨r, e, e1, e2, e2', e3, e4⟩ := emit P M hs C.gates[k].op hop (fun p => by simpa using (hmon p _ (List.getElem_mem hk')).1) (C.gates[k].inputs.map m') (by rw [List.length_map]; exact hg.2) (by
          intro r hr t ht
          obtain ⟨i, _, rfl⟩ := List.mem_map.1 hr
          simp only [m'] at ht
          split_ifs at ht with h
          exact h3 i t h ht)
        refine fin r e e2 e2' e3 (by simp [hkF]; exact e1) (fun x => ?_)
        rw [e4 _ (htgt x)]
        have rg := run_gate C.gates (src x) k hk'
        rw [hsrc] at rg
        rw [rg, List.map_map]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        simp only [Function.comp, m']
        split_ifs with h
        · exact h4 x i h
        · rfl
  obtain ⟨hs, m, h1, h5, h2, h3, h4⟩ := key C.gates.length le_rfl
  have hFc : (F.filter fun j => j < C.gates.length) = F := Finset.filter_true_of_mem fun j hj => (hF j hj).1
  rw [hFc] at h2
  have hout : C.output < n + C.gates.length := by
    by_contra h
    refine hne ⟨false, fun x => ?_⟩
    change (run C.gates (src x)).getD C.output false = false
    rw [List.getD_eq_default _ _ (by rw [run_length, hsrc]; omega)]
  have hev : ∀ x, C.eval (src x) = rv (run hs (tgt x)) (m C.output) := fun x => h4 x _ hout
  rcases hm : m C.output with b | t
  · exact absurd ⟨b, fun x => by rw [hev, hm]; rfl⟩ hne
  · refine ⟨⟨hs, t⟩, ?_, ?_, h2, fun x => ?_⟩
    · exact h1
    · intro j hj i hi
      have hj' : j < hs.length := hj
      have he : gateAt ⟨hs, t⟩ j = hs[j] := List.getD_eq_getElem _ _ hj'
      rw [he] at hi
      exact h5 j hj' i hi
    · have := hev x
      rw [hm] at this
      exact this.symm

end PEqualNP.Outside.L_meta_26027_aux.Normalize

namespace PEqualNP.Outside.L_meta_26027_aux.Normalize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def collapses {X : Type} (W : X → ℕ → Bool) (top : ℕ) (out : X → Bool) : Prop :=
  (∃ b, ∀ x, out x = b) ∨ ∃ w < top, ∀ x, out x = W x w

theorem read_pair (l : List ℕ) (w : ℕ) (hlen : l.length ≤ 2) (hw : w ∈ l) :
    l = [w] ∨ ∃ v, l = [w,v] ∨ l = [v,w] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨d,tail⟩⟩⟩
  · simp at hw
  · have e : w=a := by simpa using hw
    exact Or.inl (by rw [e])
  · rcases List.mem_cons.mp hw with e | h
    · exact Or.inr ⟨b,Or.inl (by rw [e])⟩
    · have e : w=b := by simpa using h
      exact Or.inr ⟨a,Or.inr (by rw [e])⟩
  · simp at hlen

theorem not_value {X : Type} (W : X → ℕ → Bool) (g : Gate) {w : ℕ} {b : Bool}
    (op : g.op = .not) (r : reads g w) (fixed : ∀ x, W x w = b) (x : X) :
    g.op.eval (g.inputs.map (W x)) = !b := by
  have he : g.inputs.head? = some w := by simpa [reads,op] using r
  cases h : g.inputs with
  | nil => simp [h] at he
  | cons a tail =>
    have e : a=w := by simpa [h] using he
    simp [op,h,GateOp.eval,e,fixed]

theorem dominant {X : Type} (W : X → ℕ → Bool) (g : Gate) (w : ℕ)
    (hlen : g.inputs.length ≤ 2) (r : reads g w) (op : g.op = .and ∨ g.op = .not)
    (fixed : ∀ x, W x w = false) :
    ∃ b, ∀ x, g.op.eval (g.inputs.map (W x)) = b := by
  rcases op with h|h
  · have mem : w ∈ g.inputs := by simpa [reads,h] using r
    refine ⟨false,fun x => ?_⟩
    rcases read_pair _ w hlen mem with e | ⟨v,e|e⟩ <;> simp [h,e,GateOp.eval,fixed]
  · exact ⟨true,not_value W g h r fixed⟩

theorem when_read {X : Type} (W : X → ℕ → Bool) (g : Gate) (top w : ℕ) (b : Bool)
    (ok : g.op = .and ∨ g.op = .or ∨ g.op = .not) (hlen : g.inputs.length ≤ 2)
    (before : ∀ t ∈ g.inputs, t < top) (r : reads g w) (fixed : ∀ x, W x w = b) :
    collapses W top (fun x => g.op.eval (g.inputs.map (W x))) := by
  by_cases hn : g.op = .not
  · exact Or.inl ⟨!b,not_value W g hn r fixed⟩
  have hop : g.op = .and ∨ g.op = .or := by tauto
  have mem : w ∈ g.inputs := by simpa [reads,hn] using r
  rcases read_pair _ w hlen mem with e | ⟨v,e⟩
  · refine Or.inl ⟨b,fun x => ?_⟩
    rcases hop with ho|ho <;> simp [ho,e,GateOp.eval,fixed]
  · have hv : v < top := before v (by rcases e with h|h <;> simp [h])
    rcases hop with h|h
    · cases b
      · refine Or.inl ⟨false,fun x => ?_⟩
        rcases e with h'|h' <;> simp [h,h',GateOp.eval,fixed]
      · refine Or.inr ⟨v,hv,fun x => ?_⟩
        rcases e with h'|h' <;> simp [h,h',GateOp.eval,fixed]
    · cases b
      · refine Or.inr ⟨v,hv,fun x => ?_⟩
        rcases e with h'|h' <;> simp [h,h',GateOp.eval,fixed]
      · refine Or.inl ⟨true,fun x => ?_⟩
        rcases e with h'|h' <;> simp [h,h',GateOp.eval,fixed]

def toNat {s : ℕ} (K : Finset (Fin s)) : Finset ℕ := K.map ⟨Fin.val,Fin.val_injective⟩

theorem marked {X : Type} (N : ℕ) (C : Circuit) (src : X → List Bool)
    (hs : ∀ x, (src x).length=N) (u : ℕ) (hu : u<N) (hu0 : ∀ x, (src x).getD u false=false)
    (fan : FanInTwo C) (back : ReadsBack N C) (K : Finset (Fin C.gates.length))
    (mark : ∀ j ∈ K, reads (C.gates.get j) u ∨ ∃ i : Fin C.gates.length, i<j ∧
      reads (C.gates.get i) u ∧ ((C.gates.get i).op=.and ∨ (C.gates.get i).op=.not) ∧
      reads (C.gates.get j) (N+i.val)) :
    ∀ k ∈ toNat K, k < C.gates.length ∧
      collapses (fun x w => (run C.gates (src x)).getD w false) (N+k)
        (fun x => (run C.gates (src x)).getD (N+k) false) := by
  let W := fun (x : X) (w : ℕ) => (run C.gates (src x)).getD w false
  have raw (x : X) : W x u = false :=
    (run_input _ _ _ (by rw [hs]; exact hu)).trans (hu0 x)
  have atGate (j : Fin C.gates.length) : gateAt C j.val=C.gates.get j :=
    List.getD_eq_getElem _ _ j.isLt
  have ev (j : Fin C.gates.length) (x : X) :
      W x (N+j.val) = (C.gates.get j).op.eval ((C.gates.get j).inputs.map (W x)) := by
    simpa only [W,atGate j] using gv N C back (src x) (hs x) j.val j.isLt
  intro k hk
  obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hk
  refine ⟨j.isLt,?_⟩
  change collapses W (N+j.val) (fun x => W x (N+j.val))
  have same := funext (ev j)
  rw [same]
  have ok := fan (C.gates.get j) (List.get_mem _ _)
  have before (t : ℕ) (ht : t∈(C.gates.get j).inputs) : t<N+j.val :=
    back j.val j.isLt t (by rwa [atGate])
  have folded (w : ℕ) (b : Bool) (r : reads (C.gates.get j) w) (h : ∀ x, W x w=b) :=
    when_read W _ (N+j.val) w b (by simpa using ok.1) ok.2 before r h
  rcases mark j hj with direct | ⟨i,_,ri,oi,rj⟩
  · exact folded u false direct raw
  · have fi := fan (C.gates.get i) (List.get_mem _ _)
    obtain ⟨b,hb⟩ := dominant W _ u fi.2 ri oi raw
    exact folded (N+i.val) b rj (fun x => (ev i x).trans (hb x))

end PEqualNP.Outside.L_meta_26027_aux.Normalize

namespace PEqualNP.Outside.L_meta_26027_aux.Normalize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

def oldFace {n m : ℕ} (u : Fin (n+1)) (x : List Bool) : Option (Fin n × Fin m) → List Bool
  | none => x
  | some p => oneEach (u.succAbove p.1) p.2

def newFace {n m : ℕ} (u : Fin (n+1)) (x : List Bool) : Option (Fin n × Fin m) → List Bool
  | none => List.ofFn (fun j : Fin (n+m) => x.getD (if j.val<u.val then j.val else j.val+1) false)
  | some p => oneEach p.1 p.2

theorem old_len {n m : ℕ} (u : Fin (n+1)) (x : List Bool) (hx : x.length=n+1+m)
    (p : Option (Fin n × Fin m)) : (oldFace u x p).length=n+1+m := by
  cases p <;> simp [oldFace,oneEach_length,hx]

theorem new_len {n m : ℕ} (u : Fin (n+1)) (x : List Bool)
    (p : Option (Fin n × Fin m)) : (newFace u x p).length=n+m := by
  cases p <;> simp [newFace,oneEach_length]

theorem off_face {n m : ℕ} (u : Fin (n+1)) (x : List Bool) (hx : x.getD u.val false=false)
    (p : Option (Fin n × Fin m)) : (oldFace u x p).getD u.val false=false := by
  cases p with
  | none => exact hx
  | some p =>
    simp only [oldFace,oneEach_getD,decide_eq_false_iff_not,sa_val]
    have := u.isLt
    split_ifs <;> omega

theorem face_inputs {n m : ℕ} (u : Fin (n+1)) (x : List Bool) (hx : x.getD u.val false=false)
    (w : ℕ) (hw : w<n+1+m) :
    (∃ b, ∀ p : Option (Fin n × Fin m), (oldFace u x p).getD w false = b) ∨
    ∃ t, t<n+m ∧ ∀ p : Option (Fin n × Fin m), (oldFace u x p).getD w false =
      (newFace u x p).getD t false := by
  have hu := u.isLt
  rcases lt_trichotomy w u.val with h | h | h
  · have ht : w<n+m := by omega
    refine Or.inr ⟨w,ht,?_⟩
    intro p
    cases p with
    | none => simp [oldFace,newFace,ht,h]
    | some p =>
      have := p.1.isLt
      have := p.2.isLt
      simp only [oldFace,newFace,oneEach_getD,decide_eq_decide,sa_val]
      split_ifs <;> omega
  · subst w
    exact Or.inl ⟨false,off_face u x hx⟩
  · have ht : w-1<n+m := by omega
    have hn : ¬ w-1<u.val := by omega
    have eq : w-1+1=w := by omega
    refine Or.inr ⟨w-1,ht,?_⟩
    intro p
    cases p with
    | none => simp [oldFace,newFace,ht,hn,eq]
    | some p =>
      have := p.1.isLt
      have := p.2.isLt
      simp only [oldFace,newFace,oneEach_getD,decide_eq_decide,sa_val]
      split_ifs <;> omega

end PEqualNP.Outside.L_meta_26027_aux.Normalize

namespace PEqualNP.Outside.L_meta_26027_aux.Normalize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

private theorem blank_dead_signed (P : Prop) (N : ℕ) (C : Circuit)
    (hc : FanInTwo C) (hm : P → Monotone2 C) (hb : ReadsBack N C)
    (j : ℕ) (hj : j < C.gates.length)
    (hdead : ∀ k < C.gates.length, N + j ∉ (gateAt C k).inputs) (ho : C.output ≠ N + j) :
    let E : Circuit := ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩
    FanInTwo E ∧ (P → Monotone2 E) ∧ ReadsBack N E ∧ E.size = C.size ∧
      (∀ x : List Bool, x.length = N → E.eval x = C.eval x) ∧
      (∀ x : List Bool, x.length = N → (run E.gates x).getD (N + j) false = false) := by
  let E : Circuit := ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩
  have hlen : E.gates.length = C.gates.length := by simp [E]
  have hg : ∀ k, gateAt E k = if k = j then ⟨GateOp.or, []⟩ else gateAt C k := by
    intro k
    simp only [gateAt, E, List.getD_eq_getElem?_getD, List.getElem?_set]
    by_cases hk : k = j
    · subst hk; simp [hj]
    · simp [hk, Ne.symm hk]
  have hc' : FanInTwo E := by
    intro g h
    rcases List.mem_or_eq_of_mem_set h with h | h
    · exact hc g h
    · subst h; simp
  have hm' : P → Monotone2 E := by
    intro hP g h
    rcases List.mem_or_eq_of_mem_set h with h | h
    · exact hm hP g h
    · subst h; simp
  have hb' : ReadsBack N E := by
    intro k hk i hi
    rw [hg] at hi
    split_ifs at hi with h
    · simp at hi
    · exact hb k (by rw [hlen] at hk; exact hk) i hi
  have agree : ∀ x : List Bool, x.length = N → ∀ i, i ≠ N + j →
      (run E.gates x).getD i false = (run C.gates x).getD i false := by
    intro x hx i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      by_cases hlo : i < N
      · rw [run_input _ _ _ (by omega), run_input _ _ _ (by omega)]
      by_cases hhi : N + C.gates.length ≤ i
      · rw [past _ _ _ (by rw [hlen]; omega), past _ _ _ (by omega)]
      have hk : i - N < C.gates.length := by omega
      have hik : i = N + (i - N) := by omega
      rw [hik, gv N E hb' x hx _ (by rw [hlen]; exact hk), gv N C hb x hx _ hk, hg,
        if_neg (by omega)]
      congr 1
      refine List.map_congr_left fun i' hi' => ih i' ?_ ?_
      · have := hb _ hk i' hi'; omega
      · rintro rfl; exact hdead _ hk hi'
  refine ⟨hc', hm', hb', hlen, fun x hx => agree x hx _ ho, fun x hx => ?_⟩
  change (run E.gates x).getD (N + j) false = false
  rw [gv N E hb' x hx j (by rw [hlen]; exact hj), hg, if_pos rfl]
  simp [GateOp.eval]

theorem finish_live {X : Type} (P : Prop) (M : ℕ) (y : X → List Bool)
    (hy : ∀ x, (y x).length = M) (f : X → Bool)
    (hnc : ¬ ∃ b : Bool, ∀ x, f x = b) (C : Circuit)
    (hg : ∀ g ∈ C.gates, Good P g) (hb : ReadsBack M C) (hf : ∀ x, C.eval (y x) = f x) :
    ∃ D : Circuit, (∀ g ∈ D.gates, Good P g) ∧ ReadsBack M D ∧ D.size ≤ C.size ∧
      (∀ x, D.eval (y x) = f x) ∧
      ∀ i : Fin D.gates.length, M + i.val ≠ D.output →
        ∃ j : Fin D.gates.length, i < j ∧ reads (D.gates.get j) (M + i.val) := by
  classical
  have hex : ∃ k, ∃ D : Circuit, (∀ g ∈ D.gates, Good P g) ∧ ReadsBack M D ∧
      D.size ≤ k ∧ ∀ x, D.eval (y x) = f x := ⟨C.size, C, hg, hb, le_rfl, hf⟩
  obtain ⟨D, hgood, hback, hsize, hval⟩ := Nat.find_spec hex
  have hmin0 : Nat.find hex ≤ C.size := Nat.find_min' hex ⟨C, hg, hb, le_rfl, hf⟩
  refine ⟨D, hgood, hback, hsize.trans hmin0, hval, ?_⟩
  intro i hout
  by_contra hn
  have dead : ∀ k < D.gates.length, M + i.val ∉ (gateAt D k).inputs := by
    intro k hk hpin
    have hh := hback k hk _ hpin
    have later : i < (⟨k, hk⟩ : Fin D.gates.length) := by
      change i.val < k
      omega
    have eqg : D.gates.get ⟨k, hk⟩ = gateAt D k := (List.getD_eq_getElem _ _ hk).symm
    have hgk : Good P (D.gates.get ⟨k, hk⟩) := hgood _ (List.getElem_mem hk)
    have hread : reads (D.gates.get ⟨k, hk⟩) (M + i.val) ↔
        M + i.val ∈ (D.gates.get ⟨k, hk⟩).inputs := by
      apply good_read
      exact hgk
    exact hn ⟨⟨k, hk⟩, later, hread.2 (by rwa [eqg])⟩
  let E : Circuit := ⟨D.gates.set i.val ⟨GateOp.or, []⟩, D.output⟩
  have hdf : FanInTwo D := by apply good_fan; exact hgood
  have hdm : P → Monotone2 D := by
    intro hP
    apply good_mono <;> assumption
  obtain ⟨hef, hem, _, hes, heq, hzero⟩ :=
    blank_dead_signed P M D hdf hdm hback i.val i.isLt dead hout.symm
  have heval (x : X) : E.eval (y x) = f x := (heq _ (hy x)).trans (hval x)
  have hmarked : ∀ j ∈ ({i.val} : Finset ℕ), j < E.gates.length ∧
      ((∃ b, ∀ x, (run E.gates (y x)).getD (M + j) false = b) ∨
       ∃ w < M + j, ∀ x, (run E.gates (y x)).getD (M + j) false =
         (run E.gates (y x)).getD w false) := by
    intro j hj
    rw [Finset.mem_singleton] at hj
    subst j
    exact ⟨by simpa [E] using i.isLt, Or.inl ⟨false, fun x => hzero _ (hy x)⟩⟩
  obtain ⟨J, hJg, hJb, hJs, hJv⟩ := engine P M M E y y hy hy {i.val} hef hem
    (fun w hw => Or.inr ⟨w, hw, fun _ => rfl⟩)
    (fun ⟨b, h⟩ => hnc ⟨b, fun x => (heval x).symm.trans (h x)⟩) hmarked
  have lower : Nat.find hex ≤ J.size :=
    Nat.find_min' hex ⟨J, hJg, hJb, le_rfl, fun x => (hJv x).trans (heval x)⟩
  rw [Finset.card_singleton] at hJs
  change E.size = D.size at hes
  omega

end PEqualNP.Outside.L_meta_26027_aux.Normalize

namespace PEqualNP.Outside.L_meta_26027_aux.Normalize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical
noncomputable def listed (p : GateOp → Nat) (gs : List Gate) : Nat := (gs.map (fun g=>p g.op)).sum
noncomputable def remaining (p : GateOp → Nat) (C : Circuit) (F : Finset Nat) (k : Nat) : Nat :=
  ∑ j∈Finset.range k, if j∈F then 0 else p (gateAt C j).op

theorem full_price (p : GateOp → Nat) (C : Circuit) : remaining p C ∅ C.size=listed p C.gates := by
  have appendOne (l : List Gate) (g : Gate) : listed p (l++[g])=listed p l+p g.op := by
    simp [listed]
  have below (k : Nat) (h : k≤C.gates.length) : remaining p C ∅ k=listed p (C.gates.take k) := by
    induction k with
    | zero => simp [remaining,listed]
    | succ k ih =>
      have low : k<C.gates.length:=by omega
      rw [List.take_succ_eq_append_getElem low]
      change (∑j∈Finset.range (k+1),if j∈(∅ : Finset Nat) then 0 else p (gateAt C j).op)=_
      rw [Finset.sum_range_succ]
      change remaining p C ∅ k+_=_
      rw [ih (by omega)]
      rw [show gateAt C k=C.gates[k] from List.getD_eq_getElem _ _ low,appendOne] <;> simp
  simpa [Circuit.size] using below C.gates.length le_rfl

theorem blank_price (p : GateOp → Nat) (C : Circuit) (i : Fin C.gates.length) :
    let E : Circuit:=⟨C.gates.set i.val ⟨GateOp.or,[]⟩,C.output⟩
    remaining p E {i.val} E.size≤listed p C.gates := by
  intro E
  rw [←full_price p C]
  have sizes : E.size=C.size := by simp [E,Circuit.size]
  unfold remaining; rw [sizes]; apply Finset.sum_le_sum
  intro j hj
  have low : j<C.gates.length:=Finset.mem_range.mp hj
  have newer : j<E.gates.length := by simpa [E] using low
  by_cases same : j=i.val
  · simp [same]
  · have ne : i.val≠j:=Ne.symm same
    simp [E,gateAt,List.getD_eq_getElem _ _ low,List.getD_eq_getElem _ _ newer,low,same,ne,List.getElem_set]

theorem emission_price (p : GateOp → Nat) (e : List Gate) (op : GateOp) (len : e.length≤1) (same : ∀g∈e,g.op=op) :
    listed p e≤p op := by
  cases e with
  | nil => simp [listed]
  | cons g tail =>
    have h:=same g List.mem_cons_self
    have empty : tail=[] := List.length_eq_zero_iff.mp (by change tail.length+1≤1 at len;omega)
    subst tail; simp [listed,h]

theorem emitWeighted (P : Prop) (N : ℕ) (hs : List Gate) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (hmon : P → op = GateOp.and ∨ op = GateOp.or)
    (rs : List (Bool ⊕ ℕ)) (hl : rs.length ≤ 2) (hv : ∀ r ∈ rs, ∀ t, r = .inr t → t < N + hs.length) :
    ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g∈e,g.op=op) ∧ (∀ g ∈ e, Good P g) ∧
      (∀ g ∈ e, ∀ t ∈ g.inputs, t < N + hs.length) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
      ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
  have keep : ∀ r : Bool ⊕ ℕ, (∀ t, r = .inr t → t < N + hs.length) → (∀ y : List Bool, y.length = N → rv (run hs y) r = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g∈e,g.op=op) ∧ (∀ g ∈ e, Good P g) ∧
        (∀ g ∈ e, ∀ t ∈ g.inputs, t < N + hs.length) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro r h1 h2
    exact ⟨r, [], by simp, by simp, by simp, by simp, by simpa using h1, fun y hy => by rw [List.append_nil]; exact h2 y hy⟩
  have add : ∀ g : Gate, g.op=op → Good P g → (∀ t ∈ g.inputs, t < N + hs.length) →
      (∀ y : List Bool, y.length = N → g.op.eval (g.inputs.map fun i => (run hs y).getD i false) = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g∈e,g.op=op) ∧ (∀ g ∈ e, Good P g) ∧
        (∀ g ∈ e, ∀ t ∈ g.inputs, t < N + hs.length) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro g same h1 h1' h2
    refine ⟨.inr (N + hs.length), [g], by simp, by simpa using same, by simpa using h1, by simpa using h1', ?_, fun y hy => ?_⟩
    · intro t ht
      cases ht
      simp
    · have : N + hs.length = (run hs y).length := by rw [run_length, hy]
      simp only [rv]
      rw [run_snoc, this, getD_at]
      exact h2 y hy
  by_cases hn : op = GateOp.not
  · subst op
    rcases rs with _ | ⟨r, rs⟩
    · exact keep (.inl true) (by simp) (by intro y hy; rfl)
    · have hr := hv r (by simp)
      rcases r with b | t
      · exact keep (.inl (!b)) (by simp) (by intro y hy; rfl)
      · exact add ⟨.not,[t]⟩ rfl ⟨Or.inl ⟨rfl,t,rfl⟩,hmon⟩ (by simpa using hr t rfl)
          (by intro y hy; rfl)
  have hop' : op = GateOp.and ∨ op = GateOp.or := by tauto
  rcases rs with _ | ⟨r, _ | ⟨s, _ | ⟨u, rs⟩⟩⟩
  · rcases hop' with rfl | rfl
    · exact keep (.inl true) (by simp) (by intro y _; rfl)
    · exact keep (.inl false) (by simp) (by intro y _; rfl)
  · have hr := hv r (by simp)
    rcases hop' with rfl | rfl
    · exact keep r hr (by intro y _; simp [GateOp.eval])
    · exact keep r hr (by intro y _; simp [GateOp.eval])
  · have hr := hv r (by simp)
    have hs' := hv s (by simp)
    rcases hop' with rfl | rfl
    · rcases r with b | t
      · cases b
        · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
        · by_cases same : t=q
          · subst q
            exact keep (.inr t) hr (by intro y _; simp [GateOp.eval,rv])
          · exact add ⟨GateOp.and,[t,q]⟩ rfl ⟨Or.inr ⟨Or.inl rfl,t,q,same,rfl⟩,fun _ => Or.inl rfl⟩
              (by simp; exact ⟨hr t rfl, hs' q rfl⟩) (by intro y _; simp [GateOp.eval,rv])
    · rcases r with b | t
      · cases b
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
        · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · by_cases same : t=q
          · subst q
            exact keep (.inr t) hr (by intro y _; simp [GateOp.eval,rv])
          · exact add ⟨GateOp.or,[t,q]⟩ rfl ⟨Or.inr ⟨Or.inr rfl,t,q,same,rfl⟩,fun _ => Or.inr rfl⟩
              (by simp; exact ⟨hr t rfl, hs' q rfl⟩) (by intro y _; simp [GateOp.eval,rv])
  · simp at hl

theorem engineWeighted {X : Type} (P : Prop) (n M : ℕ) (C : Circuit) (src tgt : X → List Bool) (hsrc : ∀ x, (src x).length = n) (htgt : ∀ x, (tgt x).length = M) (F : Finset ℕ)
    (hC : FanInTwo C) (hmon : P → Monotone2 C)
    (h0 : ∀ w < n, (∃ b, ∀ x, (src x).getD w false = b) ∨ ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false)
    (hne : ¬∃ b, ∀ x, C.eval (src x) = b)
    (hF : ∀ j ∈ F, j < C.gates.length ∧ ((∃ b, ∀ x, (run C.gates (src x)).getD (n + j) false = b) ∨
      ∃ w < n + j, ∀ x, (run C.gates (src x)).getD (n + j) false = (run C.gates (src x)).getD w false)) :
    ∃ D : Circuit, (∀ g ∈ D.gates, Good P g) ∧ ReadsBack M D ∧ D.size + F.card ≤ C.size ∧ (∀ p, listed p D.gates≤remaining p C F C.size) ∧
      ∀ x, D.eval (tgt x) = C.eval (src x) := by
  classical
  have key : ∀ k, k ≤ C.gates.length → ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, Good P g) ∧
      (∀ i (hi : i < hs.length), ∀ t ∈ hs[i].inputs, t < M + i) ∧
      hs.length + (F.filter fun j => j < k).card ≤ k ∧
      (∀ p, listed p hs≤remaining p C F (k)) ∧
      (∀ w t, w < n + k → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + k, (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fun w => if h : ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false then .inr h.choose else if hb : ∃ b, ∀ x, (src x).getD w false = b then .inl hb.choose else .inl false, by simp, by simp, by simp, by simp [listed,remaining], ?_, ?_⟩
      · intro w t hw ht
        beta_reduce at ht
        split_ifs at ht with h1 h2
        cases ht
        simpa using h1.choose_spec.1
      · intro x w hw
        simp only [Nat.add_zero] at hw
        rw [run_input _ _ _ (by rw [hsrc]; exact hw)]
        beta_reduce
        split_ifs with h1 h2
        · exact h1.choose_spec.2 x
        · exact h2.choose_spec x
        · rcases h0 w hw with h | h
          · exact absurd h h2
          · exact absurd h h1
    | succ k ih =>
      intro hk
      obtain ⟨hs, m, h1, h5, h2, spent, h3, h4⟩ := ih (by omega)
      have hk' : k < C.gates.length := by omega
      have fin : ∀ (r : Bool ⊕ ℕ) (e : List Gate), (∀ g ∈ e, Good P g) → (∀ g ∈ e, ∀ t ∈ g.inputs, t < M + hs.length) →
          (∀ t, r = .inr t → t < M + hs.length + e.length) → e.length + (if k ∈ F then 1 else 0) ≤ 1 →
          (∀ p, listed p e≤(if k∈F then 0 else p (gateAt C k).op)) →
          (∀ x : X, (run C.gates (src x)).getD (n + k) false = rv (run (hs ++ e) (tgt x)) r) →
          ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, Good P g) ∧
      (∀ i (hi : i < hs.length), ∀ t ∈ hs[i].inputs, t < M + i) ∧
      hs.length + (F.filter fun j => j < k + 1).card ≤ k + 1 ∧
      (∀ p, listed p hs≤remaining p C F (k + 1)) ∧
      (∀ w t, w < n + (k + 1) → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + (k + 1), (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
        intro r e he he' hr hlen charge hval
        refine ⟨hs ++ e, Function.update m (n + k) r, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro g hg
          rcases List.mem_append.1 hg with hg | hg
          · exact h1 g hg
          · exact he g hg
        · intro i hi t ht
          rw [List.getElem_append] at ht
          split_ifs at ht with hih
          · exact h5 i hih t ht
          · have hmem : e[i - hs.length]'(by simp at hi; omega) ∈ e := List.mem_iff_getElem.mpr ⟨_, _, rfl⟩
            have := he' _ hmem t ht
            omega
        · have e1 : (F.filter fun j => j < k + 1) ⊆ (F.filter fun j => j < k) ∪ (if k ∈ F then {k} else ∅) := by
            intro j hj
            rw [Finset.mem_filter] at hj
            rcases Nat.lt_or_ge j k with h | h
            · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hj.1, h⟩)
            · have : j = k := by omega
              subst this
              rw [if_pos hj.1]; simp
          have e2 := (Finset.card_le_card e1).trans (Finset.card_union_le _ _)
          rw [List.length_append]
          by_cases hkF : k ∈ F
          · rw [if_pos hkF] at e2 hlen
            rw [Finset.card_singleton] at e2
            omega
          · rw [if_neg hkF] at e2 hlen
            rw [Finset.card_empty] at e2
            omega
        · intro p
          change listed p (hs++e)≤remaining p C F (k+1)
          have lhs : listed p (hs++e)=listed p hs+listed p e := by simp [listed]
          rw [lhs,remaining,Finset.sum_range_succ]
          exact Nat.add_le_add (spent p) (charge p)
        · intro w t hw ht
          rw [List.length_append]
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self] at ht
            have := hr t ht; omega
          · rw [Function.update_of_ne hwe] at ht
            have := h3 w t (by omega) ht; omega
        · intro x w hw
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self]; exact hval x
          · rw [Function.update_of_ne hwe, h4 x w (by omega)]
            refine (rv_ext hs e (tgt x) (m w) fun t ht => ?_).symm
            have := h3 w t (by omega) ht
            rw [htgt]; exact this
      by_cases hkF : k ∈ F
      · rcases (hF k hkF).2 with ⟨b, hb⟩ | ⟨w, hw, hb⟩
        · exact fin (.inl b) [] (by simp) (by simp) (by simp) (by simp [hkF]) (by simp [listed,hkF]) (fun x => hb x)
        · refine fin (m w) [] (by simp) (by simp) (fun t ht => by simpa using h3 w t hw ht) (by simp [hkF]) (by simp [listed,hkF]) (fun x => ?_)
          rw [List.append_nil, ← h4 x w hw]
          exact hb x
      · have hg := hC _ (List.getElem_mem hk')
        have hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or ∨ C.gates[k].op = GateOp.not := by simpa using hg.1
        let m' : ℕ → Bool ⊕ ℕ := fun i => if i < n + k then m i else .inl false
        obtain ⟨r, e, e1, sameOps, e2, e2', e3, e4⟩ := emitWeighted P M hs C.gates[k].op hop (fun p => by simpa using (hmon p _ (List.getElem_mem hk')).1) (C.gates[k].inputs.map m') (by rw [List.length_map]; exact hg.2) (by
          intro r hr t ht
          obtain ⟨i, _, rfl⟩ := List.mem_map.1 hr
          simp only [m'] at ht
          split_ifs at ht with h
          exact h3 i t h ht)
        refine fin r e e2 e2' e3 (by simp [hkF]; exact e1) (by intro p; rw [if_neg hkF,show gateAt C k=C.gates[k] from List.getD_eq_getElem _ _ hk']; exact emission_price p e C.gates[k].op e1 sameOps) (fun x => ?_)
        rw [e4 _ (htgt x)]
        have rg := run_gate C.gates (src x) k hk'
        rw [hsrc] at rg
        rw [rg, List.map_map]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        simp only [Function.comp, m']
        split_ifs with h
        · exact h4 x i h
        · rfl
  obtain ⟨hs, m, h1, h5, h2, spent, h3, h4⟩ := key C.gates.length le_rfl
  have hFc : (F.filter fun j => j < C.gates.length) = F := Finset.filter_true_of_mem fun j hj => (hF j hj).1
  rw [hFc] at h2
  have hout : C.output < n + C.gates.length := by
    by_contra h
    refine hne ⟨false, fun x => ?_⟩
    change (run C.gates (src x)).getD C.output false = false
    rw [List.getD_eq_default _ _ (by rw [run_length, hsrc]; omega)]
  have hev : ∀ x, C.eval (src x) = rv (run hs (tgt x)) (m C.output) := fun x => h4 x _ hout
  rcases hm : m C.output with b | t
  · exact absurd ⟨b, fun x => by rw [hev, hm]; rfl⟩ hne
  · refine ⟨⟨hs, t⟩, ?_, ?_, h2, spent, fun x => ?_⟩
    · exact h1
    · intro j hj i hi
      have hj' : j < hs.length := hj
      have he : gateAt ⟨hs, t⟩ j = hs[j] := List.getD_eq_getElem _ _ hj'
      rw [he] at hi
      exact h5 j hj' i hi
    · have := hev x
      rw [hm] at this
      exact this.symm

theorem finishWeighted {X : Type} (P : Prop) (M : ℕ) (y : X → List Bool)
    (hy : ∀ x, (y x).length = M) (f : X → Bool)
    (hnc : ¬ ∃ b : Bool, ∀ x, f x = b) (C : Circuit)
    (hg : ∀ g ∈ C.gates, Good P g) (hb : ReadsBack M C) (hf : ∀ x, C.eval (y x) = f x) :
    ∃ D : Circuit, (∀ g ∈ D.gates, Good P g) ∧ ReadsBack M D ∧ D.size ≤ C.size ∧ (∀ p, listed p D.gates≤listed p C.gates) ∧
      (∀ x, D.eval (y x) = f x) ∧
      ∀ i : Fin D.gates.length, M + i.val ≠ D.output →
        ∃ j : Fin D.gates.length, i < j ∧ reads (D.gates.get j) (M + i.val) := by
  classical
  have hex : ∃ k, ∃ D : Circuit, (∀ g ∈ D.gates, Good P g) ∧ ReadsBack M D ∧
      D.size ≤ k ∧ (∀ p, listed p D.gates≤listed p C.gates) ∧ ∀ x, D.eval (y x) = f x := ⟨C.size, C, hg, hb, le_rfl, fun _=>le_rfl, hf⟩
  obtain ⟨D, hgood, hback, hsize, hprice, hval⟩ := Nat.find_spec hex
  have hmin0 : Nat.find hex ≤ C.size := Nat.find_min' hex ⟨C, hg, hb, le_rfl, fun _=>le_rfl, hf⟩
  refine ⟨D, hgood, hback, hsize.trans hmin0, hprice, hval, ?_⟩
  intro i hout
  by_contra hn
  have dead : ∀ k < D.gates.length, M + i.val ∉ (gateAt D k).inputs := by
    intro k hk hpin
    have hh := hback k hk _ hpin
    have later : i < (⟨k, hk⟩ : Fin D.gates.length) := by
      change i.val < k
      omega
    have eqg : D.gates.get ⟨k, hk⟩ = gateAt D k := (List.getD_eq_getElem _ _ hk).symm
    have hgk : Good P (D.gates.get ⟨k, hk⟩) := hgood _ (List.getElem_mem hk)
    have hread : reads (D.gates.get ⟨k, hk⟩) (M + i.val) ↔
        M + i.val ∈ (D.gates.get ⟨k, hk⟩).inputs := by
      apply good_read
      exact hgk
    exact hn ⟨⟨k, hk⟩, later, hread.2 (by rwa [eqg])⟩
  let E : Circuit := ⟨D.gates.set i.val ⟨GateOp.or, []⟩, D.output⟩
  have hdf : FanInTwo D := by apply good_fan; exact hgood
  have hdm : P → Monotone2 D := by
    intro hP
    apply good_mono <;> assumption
  obtain ⟨hef, hem, _, hes, heq, hzero⟩ :=
    blank_dead_signed P M D hdf hdm hback i.val i.isLt dead hout.symm
  have heval (x : X) : E.eval (y x) = f x := (heq _ (hy x)).trans (hval x)
  have hmarked : ∀ j ∈ ({i.val} : Finset ℕ), j < E.gates.length ∧
      ((∃ b, ∀ x, (run E.gates (y x)).getD (M + j) false = b) ∨
       ∃ w < M + j, ∀ x, (run E.gates (y x)).getD (M + j) false =
         (run E.gates (y x)).getD w false) := by
    intro j hj
    rw [Finset.mem_singleton] at hj
    subst j
    exact ⟨by simpa [E] using i.isLt, Or.inl ⟨false, fun x => hzero _ (hy x)⟩⟩
  obtain ⟨J, hJg, hJb, hJs, hpriceJ, hJv⟩ := engineWeighted P M M E y y hy hy {i.val} hef hem
    (fun w hw => Or.inr ⟨w, hw, fun _ => rfl⟩)
    (fun ⟨b, h⟩ => hnc ⟨b, fun x => (heval x).symm.trans (h x)⟩) hmarked
  have lower : Nat.find hex ≤ J.size :=
    Nat.find_min' hex ⟨J, hJg, hJb, le_rfl, fun p=>(hpriceJ p).trans ((blank_price p D i).trans (hprice p)), fun x => (hJv x).trans (heval x)⟩
  rw [Finset.card_singleton] at hJs
  change E.size = D.size at hes
  omega

end PEqualNP.Outside.L_meta_26027_aux.Normalize

namespace PEqualNP.Outside.L_meta_26027_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Normalize
open scoped Classical

def FixedAt {X : Type} (W : X → Nat → Bool) (i : Nat) := ∃ b, ∀ x, W x i = b
noncomputable def inputsFixed {X : Type} (W : X → Nat → Bool) (g : Gate) :=
  g.inputs.toFinset.filter (FixedAt W)
noncomputable def eliminated {X : Type} (N : Nat) (C : Circuit) (W : X → Nat → Bool) :=
  (Finset.range C.size).filter (fun j=> FixedAt W (N+j) ∨ ∃ i∈(gateAt C j).inputs, FixedAt W i)
noncomputable def bin (op : GateOp) : Nat := if op=.not then 0 else 1
noncomputable def inv (op : GateOp) : Nat := if op=.not then 1 else 0

theorem countLocal {X : Type} (W : X → Nat → Bool) (g : Gate) (o : Nat)
    (shape : Good False g) (evaluate : ∀x, W x o=g.op.eval (g.inputs.map (W x))) :
    (inputsFixed W g).card ≤ (if FixedAt W o then 1 else 0)+
      (if FixedAt W o ∨ ∃ i∈g.inputs, FixedAt W i then bin g.op else 0) := by
  classical
  have singleton (i : Nat) : (Finset.filter (FixedAt W) {i}) = (if FixedAt W i then {i} else ∅) := by
    by_cases h : FixedAt W i <;> ext v <;> simp [h] <;> aesop
  rcases shape.1 with ⟨op,a,inputs⟩|⟨op,a,b,ab,inputs⟩
  · by_cases ha : FixedAt W a
    · obtain ⟨v,hv⟩:=ha
      have fa : FixedAt W a:=⟨v,hv⟩
      have out : FixedAt W o:=⟨!v,fun x=>by simp [evaluate x,op,inputs,GateOp.eval,hv]⟩
      simp [inputsFixed,inputs,singleton,fa,out,bin,op]
    · simp [inputsFixed,inputs,singleton,ha]
  · have budget : bin g.op=1 := by rcases op with e|e <;> simp [bin,e]
    by_cases fa : FixedAt W a <;> by_cases fb : FixedAt W b
    · obtain ⟨u,hu⟩:=fa
      obtain ⟨v,hv⟩:=fb
      have ca : FixedAt W a:=⟨u,hu⟩
      have cb : FixedAt W b:=⟨v,hv⟩
      have out : FixedAt W o:=⟨g.op.eval [u,v],fun x=>by simp [evaluate x,inputs,hu,hv]⟩
      simp [inputsFixed,inputs,ca,cb,out,budget,ab,Finset.filter_insert,singleton]
    · by_cases c : FixedAt W o <;> simp [inputsFixed,inputs,fa,fb,budget,Finset.filter_insert,singleton,c]
    · by_cases c : FixedAt W o <;> simp [inputsFixed,inputs,fa,fb,budget,Finset.filter_insert,singleton,c]
    · simp [inputsFixed,inputs,fa,fb,Finset.filter_insert,singleton]

theorem cancelConstants {X : Type} (N : Nat) (C : Circuit) (W : X→Nat→Bool)
    (shape : ∀g∈C.gates, Good False g)
    (evaluate : ∀j<C.size,∀x,W x (N+j)=(gateAt C j).op.eval ((gateAt C j).inputs.map (W x)))
    (A : Finset Nat) (raw : ∀i∈A,i<N)
    (seen : ∀i∈A,FixedAt W i ∧ ∃j<C.size,i∈(gateAt C j).inputs)
    (live : ∀j<C.size, FixedAt W (N+j) → ∃k<C.size,N+j∈(gateAt C k).inputs) :
    A.card + remaining bin C (eliminated N C W) C.size ≤ listed bin C.gates := by
  classical
  let I:=Finset.range C.size
  let T:=I.filter (fun j=>FixedAt W (N+j))
  let B:=T.image (fun j=>N+j)
  let F:=eliminated N C W
  let pieces:=fun j=>inputsFixed W (gateAt C j)
  have source {w} (h : FixedAt W w) (use : ∃j<C.size,w∈(gateAt C j).inputs) : w∈I.biUnion pieces := by
    obtain ⟨j,less,pin⟩:=use
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_range.mpr less,Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr pin,h⟩⟩
  have sub : A∪B⊆I.biUnion pieces := by
    intro w hw
    rcases Finset.mem_union.mp hw with ha|hb
    · exact source (seen _ ha).1 (seen _ ha).2
    · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hb
      obtain ⟨idx,fixed⟩:=Finset.mem_filter.mp hj
      exact source fixed (live j (Finset.mem_range.mp idx) fixed)
  have dis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro i hi h
    obtain ⟨j,_,wire⟩:=Finset.mem_image.mp h
    have below:=raw i hi;change N+j=i at wire;omega
  have first:=(Finset.card_le_card sub).trans (Finset.card_biUnion_le)
  have inj : Function.Injective (fun j : Nat=>N+j):=fun _ _ e=>Nat.add_left_cancel e
  rw [Finset.card_union_of_disjoint dis,show B.card=T.card from Finset.card_image_of_injective _ inj] at first
  let dropped:=fun j=>if j∈F then bin (gateAt C j).op else 0
  have charge (j) (hj : j∈I) : (pieces j).card ≤ (if FixedAt W (N+j) then 1 else 0)+dropped j := by
    have idx:=Finset.mem_range.mp hj
    have eqg : gateAt C j=C.gates[j] := List.getD_eq_getElem _ _ idx
    have good : Good False (gateAt C j):=eqg ▸ shape _ (List.getElem_mem idx)
    simpa [pieces,dropped,F,eliminated,idx] using countLocal W (gateAt C j) (N+j) good (evaluate j idx)
  have total:=Finset.sum_le_sum charge
  rw [Finset.sum_add_distrib,←show T.card=(∑j∈I,if FixedAt W (N+j) then 1 else 0) from Finset.card_filter _ _] at total
  have both : (∑j∈I,dropped j)+remaining bin C F C.size=listed bin C.gates := by
    rw [←full_price bin C]
    unfold remaining;rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _;by_cases mem : j∈F <;> simp [dropped,mem]
  change A.card+remaining bin C F C.size≤_
  omega
end PEqualNP.Outside.L_meta_26027_aux

namespace PEqualNP.Outside.L_meta_26027_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Normalize
open scoped Classical

theorem readFn {n : Nat} (x : Fin n → Bool) (i : Fin n) : (List.ofFn x).getD i.val false=x i := by
  rw [List.getD_eq_getElem _ _ (by simpa using i.isLt)]; simp

theorem rawReader {n : Nat} (C : Circuit) (back : ReadsBack n C) (s : Fin n)
    (out : C.output ≠ s.val) (x : Fin n→Bool)
    (diff : C.eval (List.ofFn (Function.update x s false)) ≠ C.eval (List.ofFn (Function.update x s true))) :
    ∃j<C.size,s.val∈(gateAt C j).inputs := by
  classical
  by_contra! absent
  let a:=List.ofFn (Function.update x s false)
  let b:=List.ofFn (Function.update x s true)
  have la : a.length=n:=List.length_ofFn
  have lb : b.length=n:=List.length_ofFn
  have same (w : Nat) (off : w≠s.val) : (run C.gates a).getD w false=(run C.gates b).getD w false := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases raw : w<n
      · let i : Fin n:=⟨w,raw⟩
        have ne : i≠s:=fun he=>off (congrArg Fin.val he)
        rw [run_input _ _ _ (by rwa [la]),run_input _ _ _ (by rwa [lb])]
        change (List.ofFn _).getD i.val false=(List.ofFn _).getD i.val false
        rw [readFn,readFn];simp [Function.update_of_ne ne]
      by_cases far : n+C.size≤w
      · rw [past C.gates a _ (by rwa [la]),past C.gates b _ (by rwa [lb])]
      let j:=w-n
      have add : n+j=w:=Nat.add_sub_of_le (by omega)
      have idx : j<C.size:=by dsimp [j];omega
      rw [←add,gv n C back a la j idx,gv n C back b lb j idx]
      congr 1
      apply List.map_congr_left
      intro v pin
      exact ih v (by have h:=back j idx v pin;omega) (fun h=>absent j idx (h ▸ pin))
  exact diff (same C.output out)

theorem initial {n : Nat} (C : Circuit) (fan : FanInTwo C)
    (f : (Fin n→Bool)→Bool) (rep : ∀x, C.eval (List.ofFn x)=f x)
    (nc : ¬∃b,∀x,f x=b) :
    ∃D : Circuit,(∀g∈D.gates,Good False g) ∧ ReadsBack n D ∧
      (∀p,listed p D.gates≤listed p C.gates) ∧ (∀x,D.eval (List.ofFn x)=f x) ∧
      ∀ i : Fin D.gates.length,n+i.val≠D.output → ∃ j : Fin D.gates.length,i<j ∧ reads (D.gates.get j) (n+i.val) := by
  obtain ⟨E,good,back,_,prices,value⟩:=engineWeighted False n n C (fun x : Fin n→Bool=>List.ofFn x) (fun x=>List.ofFn x)
    (fun _=>List.length_ofFn) (fun _=>List.length_ofFn) ∅ fan False.elim
    (fun w h=>Or.inr ⟨w,h,fun _=>rfl⟩) (fun ⟨b,v⟩=>nc ⟨b,fun x=>(rep x).symm.trans (v x)⟩) (by simp)
  obtain ⟨D,g,b,_,costs,eq,live⟩:=finishWeighted False n (fun x=>List.ofFn x) (fun _=>List.length_ofFn) f nc E
    good back (fun x=>(value x).trans (rep x))
  exact ⟨D,g,b,fun p=>(costs p).trans ((prices p).trans_eq (full_price p C)),eq,live⟩

theorem costs (C : Circuit) : listed inv C.gates=(C.gates.filter (fun g=>decide (g.op=GateOp.not))).length ∧
    listed bin C.gates=C.size-(C.gates.filter (fun g=>decide (g.op=GateOp.not))).length := by
  have h (gs : List Gate) : listed inv gs=(gs.filter (fun g=>decide (g.op=GateOp.not))).length ∧
      listed inv gs+listed bin gs=gs.length := by
    induction gs with
    | nil => simp [listed]
    | cons g gs ih =>
      by_cases yes : g.op=GateOp.not <;> simp [listed,inv,bin,yes] at ih ⊢ <;> omega
  obtain ⟨e,s⟩:=h C.gates
  exact ⟨e,by change _=C.gates.length-_;omega⟩
noncomputable def plug {n k : Nat} (wire : Fin k→Fin n) (fixed : Fin n→Bool) (y : Fin k→Bool) (i : Fin n) :=
  if i∈Finset.univ.image wire then decide (∃j,wire j=i ∧ y j=true) else fixed i

theorem onWire {n k : Nat} (wire : Fin k→Fin n) (fixed : Fin n→Bool) (inj : Function.Injective wire)
    (y : Fin k→Bool) (j : Fin k) : plug wire fixed y (wire j)=y j := by
  have inside : wire j∈Finset.univ.image wire:=Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
  have eq : (∃z,wire z=wire j ∧ y z=true) ↔ y j=true := by
    constructor
    · rintro ⟨z,h,v⟩;exact inj h ▸ v
    · exact fun v=>⟨j,rfl,v⟩
  simp [plug,inside,eq]

theorem restrict {n k : Nat} (C : Circuit) (fan : FanInTwo C) (wire : Fin k→Fin n) (fixed : Fin n→Bool)
    (inj : Function.Injective wire) (f : (Fin n→Bool)→Bool) (rep : ∀x,C.eval (List.ofFn x)=f x)
    (outside : ∀i, i∉Finset.univ.image wire → ∃x,f (Function.update x i false)≠f (Function.update x i true))
    (varies : ∃a b,f (plug wire fixed a)≠f (plug wire fixed b)) :
    ∃D : Circuit,FanInTwo D ∧ listed bin D.gates+
             (n-k) ≤ listed bin C.gates ∧ listed inv D.gates≤listed inv C.gates ∧ ∀y,D.eval (List.ofFn y)=f (plug wire fixed y) := by
  classical
  obtain ⟨a,b,diff⟩:=varies
  have nc : ¬∃v,∀x,f x=v := fun ⟨v,h⟩=>diff ((h _).trans (h _).symm)
  obtain ⟨E,good,back,prices,ef,live⟩:=initial C fan f rep nc
  let X:=Fin k→Bool
  let src : X→List Bool:=fun y=>List.ofFn (plug wire fixed y)
  let W:=fun (y : X) w=>(run E.gates (src y)).getD w false
  have val (j : Nat) (idx : j<E.size) (y : X) : W y (n+j)=(gateAt E j).op.eval ((gateAt E j).inputs.map (W y)):=
    gv n E back (src y) List.length_ofFn j idx
  have out (y : X) : W y E.output=f (plug wire fixed y):=ef _
  have varying : ¬FixedAt W E.output := fun ⟨v,c⟩=>diff ((out a).symm.trans ((c a).trans ((c b).symm.trans (out b))))
  let image:=Finset.univ.image wire
  let ess:=(Finset.univ : Finset (Fin n)).filter (fun i=>∃x,f (Function.update x i false)≠f (Function.update x i true))
  let miss:=ess\image
  let A:=miss.image Fin.val
  have low (w) (hw : w∈A) : w<n := by obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hw;exact i.isLt
  have gateGood j (h : j<E.size) : Good False (gateAt E j) := by
    rw [show gateAt E j=E.gates[j] from List.getD_eq_getElem _ _ h];exact good _ (List.getElem_mem h)
  have rawValue (i : Fin n) (y : X) : W y i.val=plug wire fixed y i := by
    unfold W; rw [run_input _ _ _ (by simpa [src] using i.isLt)];exact readFn _ _
  have seen (w) (hw : w∈A) : FixedAt W w ∧ ∃j<E.size,w∈(gateAt E j).inputs := by
    obtain ⟨i,mem,rfl⟩:=Finset.mem_image.mp hw
    obtain ⟨active,off⟩:=Finset.mem_sdiff.mp mem
    have c : FixedAt W i.val:=⟨fixed i,fun y=>by rw [rawValue];exact if_neg off⟩
    have ne : E.output≠i.val:=fun eq=>varying (eq ▸ c)
    obtain ⟨x,hx⟩:=(Finset.mem_filter.mp active).2
    exact ⟨c,rawReader E back i ne x (by simpa only [ef] using hx)⟩
  have used (j) (idx : j<E.size) (fix : FixedAt W (n+j)) : ∃l<E.size,n+j∈(gateAt E l).inputs := by
    have ne : n+j≠E.output:=fun eq=>varying (eq ▸ fix)
    obtain ⟨l,_,read⟩:=live ⟨j,idx⟩ ne
    have e : E.gates.get l=gateAt E l.val:=(List.getD_eq_getElem _ _ l.isLt).symm
    rw [e] at read
    exact ⟨l.val,l.isLt,(good_read (gateGood _ l.isLt) _).mp read⟩
  let F:=eliminated n E W
  have charged:=cancelConstants n E W good val A low seen used
  have mark (j) (hj : j∈F) : j<E.gates.length ∧ collapses W (n+j) (fun x=>W x (n+j)) := by
    obtain ⟨idx,why⟩:=Finset.mem_filter.mp hj
    have h:=Finset.mem_range.mp idx
    refine ⟨h,?_⟩
    rcases why with c|⟨w,mem,v,z⟩
    · exact Or.inl c
    · let g:=gateAt E j
      have shape:=gateGood j h
      have fanE:=good_fan good
      have belongs : g∈E.gates:=by rw [show g=E.gates[j] from List.getD_eq_getElem _ _ h];exact List.getElem_mem _
      have ops : g.op=.and ∨ g.op=.or ∨ g.op=.not := by rcases shape.1 with ⟨op,_⟩|⟨op,_⟩ <;> tauto
      have fold:=when_read W g (n+j) w v ops (fanE g belongs).2 (back j h) ((good_read shape w).mpr mem) z
      simpa only [val j h] using fold
  have inputs (w : Nat) (h : w<n) : (∃v,∀y,(src y).getD w false=v) ∨ ∃t,t<k ∧ ∀y,(src y).getD w false=(List.ofFn y).getD t false := by
    let i : Fin n:=⟨w,h⟩
    by_cases mem : i∈image
    · obtain ⟨j,_,e⟩:=Finset.mem_image.mp mem
      exact Or.inr ⟨j.val,j.isLt,fun y=>(readFn _ i).trans (e ▸ (onWire wire fixed inj y j).trans (readFn y j).symm)⟩
    · exact Or.inl ⟨fixed i,fun y=>(readFn _ i).trans (if_neg mem)⟩
  obtain ⟨D,dgood,_,_,dcost,deval⟩:=engineWeighted False n k E src (fun y=>List.ofFn y)
    (fun _=>List.length_ofFn) (fun _=>List.length_ofFn) F (good_fan good) False.elim inputs
    (fun ⟨v,h⟩=>varying ⟨v,h⟩) mark
  have cov : ess⊆miss∪image := by
    intro i hi;by_cases mem : i∈image
    · exact Finset.mem_union_right _ mem
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hi,mem⟩)
  have many:=(Finset.card_le_card cov).trans (Finset.card_union_le _ _)
  have im : image.card=k:=by simp [image,Finset.card_image_of_injective _ inj]
  have am : A.card=miss.card:=Finset.card_image_of_injective _ Fin.val_injective
  have saved:=dcost bin
  change A.card+remaining bin E F E.size≤listed bin E.gates at charged
  have ib := prices bin
  have inversion : remaining inv E F E.size≤listed inv E.gates := by
    rw [←full_price inv E];unfold remaining;apply Finset.sum_le_sum
    intro j _;by_cases mem : j∈F <;> simp [mem]
  have offeq : miss = Finset.univ \ image := by
    ext z
    simp only [miss, Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact ⟨And.right, fun h => ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,outside z h⟩,h⟩⟩
  have missing : miss.card = n-k := by simp [offeq, Finset.card_sdiff, im]
  exact ⟨D,good_fan dgood,by omega,
    (dcost inv).trans (inversion.trans (prices inv)),fun y=>(deval y).trans (ef _)⟩
end PEqualNP.Outside.L_meta_26027_aux

namespace PEqualNP.Outside.L_meta_26027_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
theorem getD_snoc (V : List Bool) (e : Bool) (i : ℕ) :
    (V ++ [e]).getD i false = if i = V.length then e else V.getD i false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem op_mono (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (S T : ℕ → Bool) (h : ∀ i, S i = true → T i = true)
    (he : g.op.eval (g.inputs.map S) = true) : g.op.eval (g.inputs.map T) = true := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop <;> rw [hop] at he ⊢
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id] at he ⊢
    exact fun i hi => h i (he i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id] at he ⊢
    obtain ⟨i, hi, hv⟩ := he
    exact ⟨i, hi, h i hv⟩

theorem mono (gs : List Gate) (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (x y : List Bool) (hl : x.length = y.length)
    (h : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (Normalize.run gs x).getD i false = true → (Normalize.run gs y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => exact h
  | append_singleton gs g ih =>
    have H := ih fun g' h' => hg g' (List.mem_append_left _ h')
    intro i
    rw [Normalize.run_snoc, Normalize.run_snoc, getD_snoc, getD_snoc, Normalize.run_length, Normalize.run_length,
      hl]
    split_ifs with hk
    · exact op_mono g (hg g (by simp)) _ _ H
    · exact H i

def inp (N : ℕ) (P : Finset ℕ) : List Bool := List.ofFn fun i : Fin N => decide ((i : ℕ) ∈ P)

theorem inp_getD (N : ℕ) (P : Finset ℕ) (i : ℕ) :
    (inp N P).getD i false = decide (i < N ∧ i ∈ P) := by
  unfold inp
  by_cases h : i < N <;> simp [List.getD_eq_getElem?_getD, h]

theorem oneEach_eq {n m : ℕ} (u : Fin n) (v : Fin m) :
    oneEach u v = inp (n + m) {(u : ℕ), n + (v : ℕ)} := by
  have hu := u.2
  have hv := v.2
  apply List.ext_getElem
  · simp [oneEach, inp]
  · intro i h1 h2
    simp only [oneEach, inp, List.length_append, List.length_ofFn] at h1 h2 ⊢
    by_cases hi : i < n
    · rw [List.getElem_append_left (by simpa using hi)]
      simp only [List.getElem_ofFn, Fin.ext_iff, Finset.mem_insert, Finset.mem_singleton,
        decide_eq_decide]
      omega
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.getElem_ofFn, List.length_ofFn, Fin.ext_iff, Finset.mem_insert,
        Finset.mem_singleton, decide_eq_decide]
      omega
end PEqualNP.Outside.L_meta_26027_aux
namespace PEqualNP.Outside.L_meta_26027_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open scoped Classical

def left {n : Nat} (m : Nat) (i : Fin n) : Fin (n+m) := i.castAdd m
def right (n : Nat) {m : Nat} (j : Fin m) : Fin (n+m) := j.natAdd n
def two {n : Nat} (i j w : Fin n) := decide (w=i ∨ w=j)
def one {n : Nat} (j w : Fin n) := decide (w=j)
def fn {n : Nat} (C : Circuit) (x : Fin n → Bool) := C.eval (List.ofFn x)

theorem atPair {n m : Nat} {A : Fin n→Fin m→Bool} {C : Circuit} (rep : Represents A C) (i : Fin n) (j : Fin m) :
    fn C (two (left m i) (right n j))=A i j := by
  rw [←rep i j,oneEach_eq]
  congr 1
  funext w
  simp [two,left,right,Fin.ext_iff]

theorem monoFn {n : Nat} {C : Circuit} (hc : Monotone2 C) {x y : Fin n→Bool}
    (h : ∀i,x i=true → y i=true) : fn C x=true → fn C y=true := by
  apply mono C.gates (fun g hg=>(hc g hg).1) _ _ (by simp) _ C.output
  intro w
  by_cases hw : w<n
  · let i : Fin n:=⟨w,hw⟩
    exact (by simpa only [readFn] using h i : (List.ofFn x).getD i.val false=true → (List.ofFn y).getD i.val false=true)
  · simp [List.getD_eq_getElem?_getD,hw]

theorem pivot {n : Nat} {C : Circuit} (hc : Monotone2 C) (i j i' : Fin n) (ne : i≠j)
    (yes : fn C (two i j)=true) (no : fn C (two i' j)=false) :
    ∃x,fn C (Function.update x i false)≠fn C (Function.update x i true) := by
  refine ⟨one j,?_⟩
  have off : Function.update (one j) i false=one j := by
    funext w;by_cases e : w=i
    · subst w;simp [one,ne]
    · simp [Function.update_of_ne e]
  have on : Function.update (one j) i true=two i j := by
    funext w;by_cases e : w=i
    · subst w;simp [two]
    · simp [Function.update_of_ne e,two,one,e]
  rw [off,on,yes]
  intro h
  have v:=monoFn hc (x:=one j) (y:=two i' j) (by intro w; simp [one,two];tauto) h
  rw [no] at v
  contradiction

def wire {n m a b : Nat} (x : Fin a ↪ Fin n) (y : Fin b ↪ Fin m) (w : Fin (a+b)) : Fin (n+m) :=
  finSumFinEquiv (Sum.map x y (finSumFinEquiv.symm w))

theorem wireInj {n m a b : Nat} (x : Fin a ↪ Fin n) (y : Fin b ↪ Fin m) : Function.Injective (wire x y) :=
  finSumFinEquiv.injective.comp ((Sum.map_injective.mpr ⟨x.injective,y.injective⟩).comp finSumFinEquiv.symm.injective)

@[simp] theorem wireLeft {n m a b : Nat} (x : Fin a ↪ Fin n) (y : Fin b ↪ Fin m) (i : Fin a) :
    wire x y (left b i)=left m (x i) := by
  change finSumFinEquiv (Sum.map x y (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i))))=_
  rw [Equiv.symm_apply_apply];rfl

@[simp] theorem wireRight {n m a b : Nat} (x : Fin a ↪ Fin n) (y : Fin b ↪ Fin m) (j : Fin b) :
    wire x y (right a j)=right n (y j) := by
  change finSumFinEquiv (Sum.map x y (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr j))))=_
  rw [Equiv.symm_apply_apply];rfl

theorem plugTwo {n k : Nat} (g : Fin k→Fin n) (inj : Function.Injective g) (i j : Fin k) :
    plug g (fun _=>false) (two i j) = two (g i) (g j) := by
  funext w
  by_cases h : w∈Finset.univ.image g
  · obtain ⟨q,_,rfl⟩:=Finset.mem_image.mp h
    rw [onWire _ _ inj]
    simp [two,inj.eq_iff]
  · have off (q : Fin k) : w≠g q:=fun e=>h (e ▸ Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩)
    simp [plug,h,two,off]

end PEqualNP.Outside.L_meta_26027_aux

open PEqualNP.Outside.L_meta_26027_aux in
theorem PEqualNP.Outside.L_meta_26027 : ∀ (n m a b : Nat) (A : Fin n → Fin m → Bool)
    (x : Fin a ↪ Fin n) (y : Fin b ↪ Fin m),
  (∃ i k j l, A (x i) (y j) ≠ A (x k) (y l)) →
  (∀ i, (∀ h, x h ≠ i) → ∃ k j, A i j = true ∧ A k j = false) →
  (∀ j, (∀ h, y h ≠ j) → ∃ l i, A i j = true ∧ A i l = false) →
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.Represents.Represents A C →
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      PEqualNP.Represents.Represents (fun i j => A (x i) (y j)) D ∧
      D.size + (n-a) + (m-b) ≤ C.size := by
  classical
  intro n m a b A x y varied rows cols C hc rep
  let g:=wire x y
  have inj : Function.Injective g:=wireInj x y
  have pair (i : Fin a) (j : Fin b) :
      fn C (plug g (fun _=>false) (two (left b i) (right a j))) = A (x i) (y j) := by
    rw [plugTwo _ inj];simpa [g] using atPair rep (x i) (y j)
  obtain ⟨i,k,j,l,hv⟩:=varied
  have extv : ∃p q, fn C (plug g (fun _=>false) p)≠fn C (plug g (fun _=>false) q) :=
    ⟨two (left b i) (right a j),two (left b k) (right a l),by rwa [pair,pair]⟩
  have miss (w : Fin (n+m)) (off : w∉Finset.univ.image g) :
      ∃z, fn C (Function.update z w false)≠fn C (Function.update z w true) := by
    have dif (q : Fin (a+b)) : g q≠w:=fun e=>off (Finset.mem_image.mpr ⟨q,Finset.mem_univ _,e⟩)
    induction w using Fin.addCases with
    | left u =>
      obtain ⟨v,c,hy,hn⟩:=rows u (by intro q e; apply dif (left b q);change wire x y (left b q)=_;rw [wireLeft,e];rfl)
      apply pivot hc (left m u) (right n c) (left m v)
      · intro e;have v:=congrArg Fin.val e;change u.val=n+c.val at v;omega
      · exact (atPair rep _ _).trans hy
      · exact (atPair rep _ _).trans hn
    | right v =>
      obtain ⟨u,r,hy,hn⟩:=cols v (by intro q e; apply dif (right a q);change wire x y (right a q)=_;rw [wireRight,e];rfl)
      have comm {N : Nat} (z w : Fin N) : two z w=two w z:=by funext i;simp [two,or_comm]
      apply pivot hc (right n v) (left m r) (right n u)
      · intro e;have h:=congrArg Fin.val e;change n+v.val=r.val at h;omega
      · rw [comm];exact (atPair rep _ _).trans hy
      · rw [comm];exact (atPair rep _ _).trans hn
  have fan : PEqualNP.MetaComplexity.FanInTwo C := by
    intro q h
    obtain ⟨op,len⟩:=hc q h
    refine ⟨?_,len⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op
    tauto
  obtain ⟨D,df,bs,ins,vals⟩:=restrict C fan g (fun _=>false) inj (fn C) (fun _=>rfl) miss extv
  have noC : ∀q∈C.gates,q.op≠PEqualNP.CircuitLowerBounds.GateOp.not := by
    intro q h;have ops:=(hc q h).1;simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ops;rcases ops with e|e <;> simp [e]
  have cz : (C.gates.filter (fun q=>decide (q.op=PEqualNP.CircuitLowerBounds.GateOp.not))).length=0 := by
    rw [List.length_eq_zero_iff,List.filter_eq_nil_iff];simpa using noC
  rw [(costs C).1,cz,(costs D).1] at ins
  have dz := Nat.eq_zero_of_le_zero ins
  have noD : ∀q∈D.gates,q.op≠PEqualNP.CircuitLowerBounds.GateOp.not := by
    rw [List.length_eq_zero_iff,List.filter_eq_nil_iff] at dz;simpa using dz
  have md : PEqualNP.MetaComplexity.Monotone2 D := by
    intro q h;rcases df q h with ⟨op,len⟩
    refine ⟨?_,len⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op ⊢
    have hn:=noD q h
    tauto
  have hi:=Fintype.card_le_of_injective x x.injective
  have hj:=Fintype.card_le_of_injective y y.injective
  simp only [Fintype.card_fin] at hi hj
  rw [(costs D).2,(costs C).2,cz,dz] at bs
  refine ⟨D,md,?_,by omega⟩
  intro u v
  have e := atPair (A:=fun u v=>D.eval (PEqualNP.Represents.oneEach u v)) (C:=D) (fun _ _=>rfl) u v
  exact e.symm.trans ((vals (two (left b u) (right a v))).trans (pair u v))

