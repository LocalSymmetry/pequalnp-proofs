import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25654_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[
    ⟨.or, [0, 8]⟩,
    ⟨.or, [1, 9]⟩,
    ⟨.or, [4, 7]⟩,
    ⟨.or, [2, 5]⟩,
    ⟨.or, [6, 3]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.and, [15, 14]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.and, [11, 12]⟩,
    ⟨.or, [18, 16]⟩,
    ⟨.and, [17, 13]⟩,
    ⟨.or, [20, 19]⟩
  ], 21⟩

def gateListOK (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with | GateOp.and => true | GateOp.or => true | GateOp.not => true | _ => false) && Nat.ble g.inputs.length 2

theorem gateListOK_sound (C : Circuit) (h : gateListOK C = true) : FanInTwo C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, Nat.ble_eq] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

end PEqualNP.Outside.L_meta_25654_aux

open PEqualNP.Outside.L_meta_25654_aux in
theorem PEqualNP.Outside.L_meta_25654 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
  PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
  PEqualNP.Represents.Represents (fun (u v : Fin 5) => decide (v.val = u.val ∨ v.val = (u.val + 1) % 5)) C :=
  ⟨witness, gateListOK_sound witness (by decide +kernel), by decide, by decide +kernel⟩
