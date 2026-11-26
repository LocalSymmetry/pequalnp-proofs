import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21181_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[
    ⟨.or, [1, 6]⟩,
    ⟨.or, [5, 9]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [3, 9]⟩,
    ⟨.or, [2, 5]⟩,
    ⟨.and, [12, 13]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.or, [14, 15]⟩,
    ⟨.and, [11, 16]⟩,
    ⟨.or, [4, 17]⟩
  ], 18⟩

def gateListOK (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with | GateOp.and => true | GateOp.or => true | _ => false) && Nat.ble g.inputs.length 2

theorem gateListOK_sound (C : Circuit) (h : gateListOK C = true) : Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, Nat.ble_eq] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

end PEqualNP.Outside.L_meta_21181_aux

open PEqualNP.Outside.L_meta_21181_aux in
theorem PEqualNP.Outside.L_meta_21181 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (103799 : ℕ).testBit (5 * u.val + v.val)) 10 :=
  ⟨witness, gateListOK_sound witness (by decide +kernel), by decide, by decide +kernel⟩
