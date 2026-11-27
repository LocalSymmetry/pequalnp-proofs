import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_824_aux
open CircuitLowerBounds MetaComplexity.NestedCover

def legalGate (g : Gate) : Prop := g.inputs.length ≤ 2 ∧
  (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))

noncomputable def paid (g : Gate) : Bool := @decide
  ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _)

def choose (a b : ℕ) (conj : Bool) (i : Fin 4) : Gate :=
  if i = 0 then ⟨.or,[a]⟩
  else if i = 1 then ⟨.or,[b]⟩
  else if (i = 2) = (conj = true) then ⟨.mod 2,[a,b]⟩
  else ⟨.and,[]⟩

theorem choice_spec (a b : ℕ) (c : Bool) (i : Fin 4) :
    legalGate (choose a b c i) ∧ paid (choose a b c i) = false ∧
    ∀ v ∈ (choose a b c i).inputs, v ∈ [a,b] := by
  classical
  fin_cases i <;> cases c <;> simp [choose, legalGate, paid]

def step (ws : List Bool) (g : Gate) := ws ++ [g.op.eval (g.inputs.map fun j => ws.getD j false)]

def repl (p s : List Gate) (out : ℕ) (g : Gate) : Circuit := ⟨p ++ g :: s, out⟩

theorem output_repl (p s : List Gate) (out : ℕ) (g : Gate) (x : List Bool) :
    (repl p s out g).eval x =
    let w := p.foldl step x
    (s.foldl step (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)])).getD out false := by
  unfold Circuit.eval Circuit.wires repl
  rw [List.foldl_append]
  rfl

theorem back {p s : List Gate} {out n : ℕ} {g h : Gate}
    (orig : ReadsBack n (repl p s out g)) (hh : ∀ k ∈ h.inputs, k ∈ g.inputs) :
    ReadsBack n (repl p s out h) := by
  have sub : ∀ (l : List Gate) (j : ℕ),
      ∀ v ∈ ((l ++ h :: s).getD j ⟨.or,[]⟩).inputs,
        v ∈ ((l ++ g :: s).getD j ⟨.or,[]⟩).inputs := by
    intro l
    induction l with
    | nil =>
      rintro (_ | j)
      · exact hh
      · exact fun _ hv => hv
    | cons x xs ih =>
      rintro (_ | j)
      · exact fun _ hv => hv
      · exact ih j
  intro j hj v hv
  exact orig j (by simpa [repl] using hj) v (sub p j v hv)

def S (v : Bool) : ℤ := if v then -1 else 1

theorem identity (a b : ℕ) (w : List Bool) (f : Bool → Bool) (c : Bool) :
    let val := fun (g : Gate) => f (g.op.eval (g.inputs.map fun j => w.getD j false))
    2 * S (val ⟨if c then .and else .or,[a,b]⟩) =
      S (val (choose a b c 0)) + S (val (choose a b c 1)) +
      S (val (choose a b c 2)) - S (val (choose a b c 3)) := by
  cases c <;> cases ha : w[a]?.getD false <;> cases hb : w[b]?.getD false <;>
    cases h0 : f false <;> cases h1 : f true <;>
    simp [choose, GateOp.eval, S, ha, hb, h0, h1]

theorem reduce {n : ℕ} {p s : List Gate} {out a b : ℕ} {c : Bool}
    (ok : ReadsBack n (repl p s out ⟨if c then .and else .or,[a,b]⟩))
    (hg : ∀ g ∈ (repl p s out ⟨if c then .and else .or,[a,b]⟩).gates, legalGate g) :
    let C := repl p s out ⟨if c then .and else .or,[a,b]⟩
    ∃ D : Fin 4 → Circuit,
      (∀ i, (ReadsBack n (D i) ∧ ∀ g ∈ (D i).gates, legalGate g) ∧
        (D i).gates.countP paid < C.gates.countP paid) ∧
      ∀ x : Fin n → Bool, let w := List.ofFn x
        2*S (C.eval w) = S ((D 0).eval w) + S ((D 1).eval w) +
          S ((D 2).eval w) - S ((D 3).eval w) := by
  classical
  dsimp only
  refine ⟨fun i => repl p s out (choose a b c i), ?_, ?_⟩
  · intro i
    obtain ⟨hl,hp,hsub⟩ := choice_spec a b c i
    refine ⟨⟨back ok hsub, ?_⟩, ?_⟩
    · intro g mem
      rcases List.mem_append.mp mem with h | h
      · exact hg _ (List.mem_append_left _ h)
      · rcases List.mem_cons.mp h with rfl | h
        · exact hl
        · exact hg _ (List.mem_append_right _ (List.mem_cons_of_mem _ h))
    · have old : paid ⟨if c then .and else .or,[a,b]⟩ = true := by cases c <;> simp [paid]
      simp [repl,List.countP_append,hp,old]
  · intro x
    simpa only [output_repl] using identity a b (p.foldl step (List.ofFn x))
      (fun k => (s.foldl step ((p.foldl step (List.ofFn x)) ++ [k])).getD out false) c

end PEqualNP.Outside.L_lib_824_aux

theorem PEqualNP.Outside.L_lib_824 : ∀ n : ℕ,
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (nW : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack nW C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
        (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)))
  let cost := fun (C : Circ) =>
    C.gates.countP (fun g => @decide
      ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _))
  let sig := fun (v : Bool) => if v then (-1 : ℤ) else 1
  ∀ C : Circ, legal n C → 0 < cost C →
    ∃ D : Fin 4 → Circ,
      (∀ i, legal n (D i) ∧ cost (D i) < cost C) ∧
      ∀ x : Fin n → Bool,
        let bits := List.ofFn x
        2*sig (C.eval bits) = sig ((D 0).eval bits) + sig ((D 1).eval bits) +
          sig ((D 2).eval bits) - sig ((D 3).eval bits) := by
  classical
  intro n
  dsimp only
  intro C hc hpos
  obtain ⟨gs,out⟩ := C
  change 0 < gs.countP L_lib_824_aux.paid at hpos
  obtain ⟨g,gm,gp⟩ := List.countP_pos_iff.mp hpos
  obtain ⟨p,s,rfl⟩ := List.append_of_mem gm
  obtain ⟨op,args⟩ := g
  unfold L_lib_824_aux.paid at gp
  rcases @of_decide_eq_true _ (Classical.propDecidable _) gp with ⟨hor,hargs⟩
  obtain ⟨a,b,rfl⟩ := List.length_eq_two.mp hargs
  rcases hor with rfl | rfl
  · exact L_lib_824_aux.reduce (c := true) hc.1 hc.2
  · exact L_lib_824_aux.reduce (c := false) hc.1 hc.2
