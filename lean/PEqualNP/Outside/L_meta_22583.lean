import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22583_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.and, [1, 8]⟩,
    ⟨.or, [5, 9]⟩,
    ⟨.not, [10]⟩,
    ⟨.and, [6, 11]⟩
  ], 12⟩

def gateListOK (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with | GateOp.and => true | GateOp.or => true | GateOp.not => true | _ => false) && Nat.ble g.inputs.length 2

theorem gateListOK_sound (C : Circuit) (h : gateListOK C = true) : FanInTwo C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, Nat.ble_eq] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

end PEqualNP.Outside.L_meta_22583_aux

open PEqualNP.Outside.L_meta_22583_aux in
theorem PEqualNP.Outside.L_meta_22583 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (413 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨witness, gateListOK_sound witness (by decide +kernel), by decide, by decide +kernel⟩
