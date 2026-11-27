import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_323_aux
open PEqualNP.ProofComplexity

abbrev Raw {n : ℕ} (w : Fin n→ℕ) := (i : Fin n) × Fin (w i)
abbrev Tape {n : ℕ} (w : Fin n→ℕ) := (i : Fin n)→Bool→Fin (w i)→Bool
abbrev Gad {n : ℕ} (w : Fin n→ℕ) := (i : Fin n)→(Fin (w i)→Bool)→Bool
abbrev B (n : ℕ) := Clause (Fin n)

def vars {n : ℕ} (C : B n) := C.image Prod.fst
def clean {n : ℕ} (C : B n) := ∀ i,¬((i,true)∈C ∧ (i,false)∈C)
def slot {n : ℕ} (C : B n) (i : Fin n) := decide ((i,false)∈C)
def sectionOK {n : ℕ} {w : Fin n→ℕ} (g : Gad w) (s : Tape w) := ∀ i b,g i (s i b)=b
noncomputable def sections {n : ℕ} {w : Fin n→ℕ} (g : Gad w) : Finset (Tape w) :=
  Finset.univ.filter (fun s=>∀ i b,g i (s i b)=b)
def decoder {n : ℕ} {w : Fin n→ℕ} (g : Gad w) (x : Raw w→Bool) := fun i=>g i (fun j=>x ⟨i,j⟩)
def block {n : ℕ} (w : Fin n→ℕ) (C : B n) (x : Raw w→Bool) : Clause (Raw w) :=
  ((Finset.univ : Finset (Raw w)).filter (fun z=>z.1∈vars C)).image (fun z=>(z,!(x z)))
noncomputable def copies {n : ℕ} {w : Fin n→ℕ} (g : Gad w) (C : B n) : Finset (Clause (Raw w)) :=
  (Finset.univ.filter (fun x : Raw w→Bool=>∀ l∈C,decoder g x l.1≠l.2)).image (block w C)
def reprBlock {n : ℕ} {w : Fin n→ℕ} (C : B n) (s : Tape w) := block w C (fun z=>s z.1 (slot C z.1) z.2)

theorem slot_diff {n : ℕ} (C : B n) (cc : clean C) (l : Fin n×Bool) (hl : l∈C) : slot C l.1≠l.2 := by
  obtain ⟨i,t⟩ := l
  cases t
  · simp [slot,hl]
  · have no : (i,false)∉C := fun hf=>cc i ⟨hl,hf⟩
    simp [slot,no]

theorem slot_match {n : ℕ} (C : B n) (q : Fin n→Bool) (miss : ∀ l∈C,q l.1≠l.2)
    (i : Fin n) (h : i∈vars C) : q i=slot C i := by
  obtain ⟨⟨k,t⟩,hmem,e⟩ := Finset.mem_image.mp h
  change k=i at e
  subst k
  by_cases f : (i,false)∈C
  · have v := miss (i,false) f
    simpa [slot,f] using v
  · cases t
    · contradiction
    · have v := miss (i,true) hmem
      simpa [slot,f] using v

theorem block_mem {n : ℕ} {w : Fin n→ℕ} (C : B n) (x : Raw w→Bool) (z : Raw w) (b : Bool) :
    (z,b)∈block w C x ↔ z.1∈vars C ∧ (!(x z))=b := by
  constructor
  · intro h
    obtain ⟨k,hk,eq⟩ := Finset.mem_image.mp h
    have e : k=z := congrArg Prod.fst eq
    subst k
    exact ⟨(Finset.mem_filter.mp hk).2,congrArg Prod.snd eq⟩
  · rintro ⟨h,e⟩
    exact Finset.mem_image.mpr ⟨z,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,Prod.ext rfl e⟩

theorem block_eq {n : ℕ} {w : Fin n→ℕ} (C : B n) (x y : Raw w→Bool) :
    block w C x=block w C y ↔ ∀ z : Raw w,z.1∈vars C → x z=y z := by
  constructor
  · intro eq z h
    have m := eq ▸ (block_mem C x z (!(x z))).mpr ⟨h,rfl⟩
    have yz := ((block_mem C y z (!(x z))).mp m).2
    simpa using yz.symm
  · intro ag
    ext ⟨z,b⟩
    simp only [block_mem]
    exact and_congr_right (fun h=>by rw [ag z h])

theorem kills {n : ℕ} {w : Fin n→ℕ} (C : B n) (x y : Raw w→Bool) :
    ¬ ClauseSat x (block w C y) ↔ ∀ z : Raw w,z.1∈vars C → x z=y z := by
  constructor
  · intro no z h
    have bad : x z≠ !(y z) := fun eq=>no ⟨_,(block_mem C y z (!(y z))).mpr ⟨h,rfl⟩,eq⟩
    simpa using bad
  · rintro ag ⟨⟨z,b⟩,mem,yes⟩
    obtain ⟨h,eq⟩ := (block_mem C y z b).mp mem
    change x z=b at yes
    rw [ag z h,← eq] at yes
    simpa using yes

theorem copy_rep {n : ℕ} {w : Fin n→ℕ} (g : Gad w) (C : B n) (cc : clean C)
    (s : Tape w) (hs : sectionOK g s) : reprBlock C s∈copies g C := by
  refine Finset.mem_image.mpr ⟨fun z=>s z.1 (slot C z.1) z.2,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
  intro l hl
  change g l.1 (s l.1 (slot C l.1))≠l.2
  rw [hs]
  exact slot_diff C cc l hl

theorem dec_agree {n : ℕ} {w : Fin n→ℕ} (g : Gad w) (C : B n) (x y : Raw w→Bool)
    (ag : ∀ z : Raw w,z.1∈vars C → x z=y z) (l : Fin n×Bool) (h : l∈C) :
    decoder g x l.1=decoder g y l.1 :=
  congrArg (g l.1) (funext (fun k=>ag ⟨l.1,k⟩ (Finset.mem_image_of_mem _ h)))

noncomputable def project {n : ℕ} {w : Fin n→ℕ} (F : Finset (B n)) (A : Finset (Clause (Raw w))) (s : Tape w) :=
  F.filter (fun C=>reprBlock C s∈A)

theorem sat_equiv {n : ℕ} {w : Fin n→ℕ} (g : Gad w) (sur : ∀ i b,∃ x,g i x=b)
    (F : Finset (B n)) (cc : ∀ C∈F,clean C) (A : Finset (Clause (Raw w))) (sub : A⊆F.biUnion (copies g)) :
    Satisfiable (A : Set (Clause (Raw w))) ↔
      ∃ s∈sections g,Satisfiable (project F A s : Set (B n)) := by
  classical
  constructor
  · rintro ⟨x,sat⟩
    let q := decoder g x
    let s : Tape w := fun i b=>if b=q i then fun k=>x ⟨i,k⟩ else (sur i b).choose
    have hs : sectionOK g s := by
      intro i b
      by_cases eq : b=q i
      · subst b; simp [s,q,decoder]
      · simp [s,eq,(sur i b).choose_spec]
    refine ⟨s,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩,q,?_⟩
    intro C h
    obtain ⟨hC,member⟩ := Finset.mem_filter.mp h
    by_contra no
    have miss (l) (hl : l∈C) : q l.1≠l.2 := fun eq=>no ⟨l,hl,eq⟩
    have ag (z : Raw w) (hz : z.1∈vars C) : x z=s z.1 (slot C z.1) z.2 := by
      simp only [s,dite_eq_ite,if_pos (slot_match C q miss _ hz).symm]
    exact ((kills C _ (fun z=>s z.1 (slot C z.1) z.2)).mpr ag) (sat _ member)
  · rintro ⟨s,hs,q,sat⟩
    have valid : sectionOK g s := (Finset.mem_filter.mp hs).2
    let x : Raw w→Bool := fun z=>s z.1 (q z.1) z.2
    have dec (i : Fin n) : decoder g x i=q i := valid i (q i)
    refine ⟨x,?_⟩
    intro B0 hB
    obtain ⟨C,hC,hcopy⟩ := Finset.mem_biUnion.mp (sub hB)
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hcopy
    by_contra no
    have ag := (kills C x y).mp no
    have miss (l) (hl : l∈C) : q l.1≠l.2 := by
      rw [← dec,dec_agree g C x y ag l hl]
      exact (Finset.mem_filter.mp hy).2 l hl
    have eq : reprBlock C s=block w C y := (block_eq C _ y).mpr (by
      intro z hz
      change s z.1 (slot C z.1) z.2=y z
      rw [← slot_match C q miss _ hz]
      exact ag z hz)
    obtain ⟨l,hl,yes⟩ := sat C (Finset.mem_filter.mpr ⟨hC,eq ▸ hB⟩)
    exact miss l hl yes

def swapW {α : Type*} [DecidableEq α] (x y z : α) := if z=x then y else if z=y then x else z

theorem sw_invol {α : Type*} [DecidableEq α] (x y z : α) : swapW x y (swapW x y z)=z := by
  by_cases a : z=x <;> by_cases b : z=y <;> simp_all [swapW]

theorem sw_value {α β : Type*} [DecidableEq α] (g : α→β) (x y z : α) (eq : g x=g y) :
    g (swapW x y z)=g z := by
  by_cases a : z=x <;> by_cases b : z=y <;> simp_all [swapW]

noncomputable def swapTape {n : ℕ} {w : Fin n→ℕ} (C : B n) (x y : Raw w→Bool) (s : Tape w) : Tape w :=
  fun i b=>if i∈vars C ∧ b=slot C i then swapW (fun j=>x ⟨i,j⟩) (fun j=>y ⟨i,j⟩) (s i b) else s i b

theorem swap_twice {n : ℕ} {w : Fin n→ℕ} (C : B n) (x y : Raw w→Bool) (s : Tape w) :
    swapTape C x y (swapTape C x y s)=s := by
  funext i b
  by_cases h : i∈vars C ∧ b=slot C i <;> simp [swapTape,h,sw_invol]

theorem swap_ok {n : ℕ} {w : Fin n→ℕ} (C : B n) (g : Gad w) (x y : Raw w→Bool) (s : Tape w)
    (hx : ∀ l∈C, decoder g x l.1≠l.2) (hy : ∀ l∈C,decoder g y l.1≠l.2) (hs : sectionOK g s) :
    sectionOK g (swapTape C x y s) := by
  intro i b
  by_cases h : i∈vars C ∧ b=slot C i
  · have eq : g i (fun j=>x ⟨i,j⟩) = g i (fun j=>y ⟨i,j⟩) :=
      (slot_match C _ hx i h.1).trans (slot_match C _ hy i h.1).symm
    simp only [swapTape,if_pos h,sw_value (g i) _ _ _ eq]
    exact hs i b
  · simpa [swapTape,h] using hs i b

theorem swap_block {n : ℕ} {w : Fin n→ℕ} (C : B n) (x y : Raw w→Bool) (s : Tape w)
    (e : reprBlock C s=block w C x) : reprBlock C (swapTape C x y s)=block w C y := by
  have agree := (block_eq C _ x).mp e
  apply (block_eq C _ y).mpr
  rintro ⟨i,j⟩ h
  have h' : s i (slot C i)=(fun k=>x ⟨i,k⟩) := funext (fun k=>agree ⟨i,k⟩ h)
  simp only [swapTape,h,eq_self,and_self,ite_true,h',swapW]

theorem switch_comm {n : ℕ} {w : Fin n→ℕ} (C : B n) (x y : Raw w→Bool) :
    swapTape C x y=swapTape C y x := by
  funext s i b
  by_cases h : i∈vars C ∧ b=slot C i
  · have comm {α : Type} [DecidableEq α] (l r z : α) : swapW l r z=swapW r l z := by
      by_cases a : z=l <;> by_cases b : z=r <;> simp_all [swapW]
    simp only [swapTape,if_pos h]
    exact comm _ _ _
  · simp [swapTape,h]

theorem same_count {n : ℕ} {w : Fin n→ℕ} (C : B n) (g : Gad w) (A B0 : Clause (Raw w))
    (ha : A∈copies g C) (hb : B0∈copies g C) :
    ((sections g).filter (fun s=>reprBlock C s=A)).card = ((sections g).filter (fun s=>reprBlock C s=B0)).card := by
  classical
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hb
  let f := swapTape C x y
  have fx := (Finset.mem_filter.mp hx).2
  have fy := (Finset.mem_filter.mp hy).2
  apply Finset.card_bij' (fun s _=>f s) (fun s _=>f s)
  · intro s h
    obtain ⟨hs,eq⟩ := Finset.mem_filter.mp h
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,swap_ok C g x y s fx fy (Finset.mem_filter.mp hs).2⟩,
      swap_block C x y s eq⟩
  · intro s h
    obtain ⟨hs,eq⟩ := Finset.mem_filter.mp h
    have rev : f=swapTape C y x := switch_comm C x y
    rw [rev]
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,swap_ok C g y x s fy fx (Finset.mem_filter.mp hs).2⟩,
      swap_block C y x s eq⟩
  · exact fun s _=>swap_twice C x y s
  · exact fun s _=>swap_twice C x y s

theorem uniform {α β : Type*} [DecidableEq α] [DecidableEq β] (X : Finset α) (Y : Finset β)
    (f : α→β) (into : ∀ x∈X,f x∈Y)
    (eq : ∀ y∈Y,∀ z∈Y,(X.filter (fun x=>f x=y)).card=(X.filter (fun x=>f x=z)).card)
    (A : Finset β) :
    Y.card*(X.filter (fun x=>f x∈A)).card=X.card*(A∩Y).card := by
  classical
  by_cases ne : Y.Nonempty
  · obtain ⟨o,ho⟩ := ne
    let k := (X.filter (fun x=>f x=o)).card
    have tot : X.card=Y.card*k := by
      rw [Finset.card_eq_sum_card_fiberwise (f:=f) (t:=Y) into]
      calc ∑ y∈Y,(X.filter (fun x=>f x=y)).card = ∑ _y∈Y,k :=
             Finset.sum_congr rfl (fun y h=>eq y h o ho)
        _ = _ := by simp
    let Z := X.filter (fun x=>f x∈A)
    have count : Z.card=(A∩Y).card*k := by
      have fz (x : α) (h : x∈Z) : f x∈A∩Y :=
        Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp h).2,into x (Finset.mem_filter.mp h).1⟩
      rw [Finset.card_eq_sum_card_fiberwise (f:=f) (t:=A∩Y) fz]
      calc ∑ y∈A∩Y,(Z.filter (fun x=>f x=y)).card = ∑ _y∈A∩Y,k := by
             refine Finset.sum_congr rfl (fun y hy=>?_ )
             have mem := Finset.mem_inter.mp hy
             have same : Z.filter (fun x=>f x=y)=X.filter (fun x=>f x=y) := by
               ext x
               simp only [Z,Finset.mem_filter]
               constructor
               · exact fun h=>⟨h.1.1,h.2⟩
               · exact fun h=>⟨⟨h.1,h.2 ▸ mem.1⟩,h.2⟩
             rw [same]
             exact eq y mem.2 o ho
        _ = _ := by simp
    change Y.card*Z.card=_
    rw [tot,count]
    ac_rfl
  · have empty := Finset.not_nonempty_iff_eq_empty.mp ne
    simp [empty]



end PEqualNP.Outside.L_pcx_323_aux

open PEqualNP.Outside.L_pcx_323_aux PEqualNP.ProofComplexity in
theorem PEqualNP.Outside.L_pcx_323 : ∀ (n : ℕ) (w : Fin n → ℕ), (∀ i, 0 < w i) →
  ∀ g : (i : Fin n) → (Fin (w i) → Bool) → Bool, (∀ i b, ∃ x, g i x = b) →
  let B := PEqualNP.ProofComplexity.Clause (Fin n)
  let Raw := (i : Fin n) × Fin (w i)
  let Axiom := PEqualNP.ProofComplexity.Clause Raw
  let Tape := (i : Fin n) → Bool → Fin (w i) → Bool
  let sections := (Finset.univ : Finset Tape).filter (fun s => ∀ i b, g i (s i b) = b)
  let block := fun (C : B) (x : Raw → Bool) =>
    ((Finset.univ : Finset Raw).filter (fun j => j.1 ∈ C.image Prod.fst)).image (fun j => (j, !(x j)))
  let copies := fun (C : B) =>
    ((Finset.univ : Finset (Raw → Bool)).filter (fun x =>
      ∀ l ∈ C, g l.1 (fun j => x ⟨l.1,j⟩) ≠ l.2)).image (block C)
  ∀ F : Finset B, (∀ C ∈ F, ∀ i, ¬ ((i,true) ∈ C ∧ (i,false) ∈ C)) →
    let allAx := F.biUnion copies
    let project := fun (A : Finset Axiom) (s : Tape) => F.filter (fun C =>
      block C (fun z => s z.1 (decide ((z.1,false) ∈ C)) z.2) ∈ A)
    let bad := fun {V : Type} (K : Finset (PEqualNP.ProofComplexity.Clause V)) =>
      ¬ PEqualNP.ProofComplexity.Satisfiable (K : Set (PEqualNP.ProofComplexity.Clause V))
    ∀ A : Finset Axiom, A ⊆ allAx →
      (bad A ↔ ∀ s ∈ sections, bad (project A s)) ∧
      ∀ C ∈ F, (copies C).card * (sections.filter (fun s => C ∈ project A s)).card =
        sections.card * (A ∩ copies C).card := by
  classical
  intro n w _ g sur B0 Raw0 Axiom Tape0 sections0 block0 copies0 F cc allAx project0 bad A sub
  constructor
  · change (¬ Satisfiable (A : Set (Clause (Raw w)))) ↔
      ∀ s∈sections g,¬ Satisfiable (project F A s : Set (B n))
    simpa only [not_exists,not_and] using not_congr (sat_equiv g sur F cc A sub)
  · intro C hC
    have into (s : Tape w) (hs : s∈sections g) : reprBlock C s∈copies g C :=
      copy_rep g C (cc C hC) s (Finset.mem_filter.mp hs).2
    have eq := uniform (sections g) (copies g C) (reprBlock C) into (fun y hy z hz=>same_count C g y z hy hz) A
    have filt : (sections g).filter (fun s=>C∈project F A s)=(sections g).filter (fun s=>reprBlock C s∈A) := by
      ext s
      simp [project,hC]
    change (copies g C).card*((sections g).filter (fun s=>C∈project F A s)).card=_
    rw [filt]
    exact eq

