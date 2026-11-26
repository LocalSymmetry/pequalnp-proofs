import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23717_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[
    ⟨.or, [3, 4]⟩,
    ⟨.and, [0, 5]⟩,
    ⟨.or, [0, 5]⟩,
    ⟨.not, [7]⟩,
    ⟨.and, [1, 8]⟩,
    ⟨.or, [6, 9]⟩
  ], 10⟩

def gateListOK (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with | GateOp.and => true | GateOp.or => true | GateOp.not => true | _ => false) && Nat.ble g.inputs.length 2

theorem gateListOK_sound (C : Circuit) (h : gateListOK C = true) : FanInTwo C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, Nat.ble_eq] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

end PEqualNP.Outside.L_meta_23717_aux

open PEqualNP.Outside.L_meta_23717_aux in
theorem PEqualNP.Outside.L_meta_23717 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (216 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨witness, gateListOK_sound witness (by decide +kernel), by decide, by decide +kernel⟩
