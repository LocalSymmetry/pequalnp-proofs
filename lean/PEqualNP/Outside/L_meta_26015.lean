import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_26015_aux
open PEqualNP.CircuitLowerBounds
def witness : Circuit := ⟨[⟨.and, [1, 5]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [7, 10]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [8, 12]⟩, ⟨.not, [13]⟩], 14⟩
end PEqualNP.Outside.L_meta_26015_aux

theorem PEqualNP.Outside.L_meta_26015 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([15, 13, 7, 3] : List ℕ).getD u.val 0).testBit v.val) C := by
  refine ⟨PEqualNP.Outside.L_meta_26015_aux.witness, ?_, by decide, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_26015_aux.witness]
