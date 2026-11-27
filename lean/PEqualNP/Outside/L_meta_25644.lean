import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25644_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def gates69 (C : Circuit) := Finset.range C.size
def reads69 (C : Circuit) (w : Nat) := readsIn C (gates69 C) w
noncomputable def neg69 (C : Circuit) : Finset Nat := by
  classical exact (gates69 C).filter (fun k=>(gateAt C k).op=.not)
noncomputable def special (N : Nat) (C : Circuit) : Finset Nat := by
  classical exact ((Finset.range (N+C.size)).filter (fun w=>2≤reads69 C w)) ∪
    (neg69 C).image (fun k=>N+k)
noncomputable def ordinary (N : Nat) (C : Circuit) : Finset Nat := by
  classical exact (gates69 C).filter (fun k=>N+k∉special N C)
noncomputable def exits69 (N : Nat) (C : Circuit) : Nat := by
  classical exact ∑k∈gates69 C \ ordinary N C,(gateAt C k).inputs.countP (fun w=>decide (w∉special N C))
noncomputable def entries69 (N : Nat) (C : Circuit) : Nat := by
  classical exact ∑k∈ordinary N C,(gateAt C k).inputs.countP (fun w=>decide (w∈special N C))
def once69 (N : Nat) (C : Circuit) := (Finset.range N).filter (fun w=>reads69 C w=1)
def shapes69 (C : Circuit) : Prop := ∀g∈C.gates,
  ((g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2) ∨ (g.op=.not ∧ g.inputs.length=1)

def tree69 (N : Nat) (C : Circuit) (S E : Finset Nat) : Prop := ∃ region : Finset Nat, ∃ root : Nat,
  let wires := S ∪ region.image (fun k=>N+k)
  let localReads := readsIn C region
  region ⊆ ordinary N C ∧ root∈wires ∧ localReads root=0 ∧
  (∀b∈E,b∉wires ∧ b<root ∧ localReads b=1) ∧
  (∀j∈region, ((gateAt C j).op=.and ∨ (gateAt C j).op=.or) ∧
    (gateAt C j).inputs.length=2 ∧ ∀w∈(gateAt C j).inputs, w∈wires ∨ w∈E) ∧
  (∀w∈wires,w≠root → localReads w=1 ∧ reads69 C w=1 ∧ C.output≠w)

theorem ordinary_reads69 {N : Nat} {C : Circuit} {k : Nat} (h : k∈ordinary N C) :
    reads69 C (N+k)≤1 := by
  classical
  obtain ⟨hk,hn⟩:=Finset.mem_filter.mp h
  have lt : k<C.size := Finset.mem_range.mp hk
  by_contra! many
  exact hn (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),many⟩))

theorem ordinary_index69 {N : Nat} {C : Circuit} {k : Nat} (h : k∈ordinary N C) :
    k<C.size := Finset.mem_range.mp (Finset.mem_filter.mp h).1

end PEqualNP.Outside.L_meta_25644_aux

namespace PEqualNP.Outside.L_meta_25644_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

noncomputable def color69 (N : Nat) (C : Circuit) (w : Nat) : Bool :=
  if w∈special N C then true else if w<N then false else
    (gateAt C (w-N)).inputs.any (fun v => if hv : v<w then color69 N C v else false)
termination_by w

noncomputable def split69 (N : Nat) (C : Circuit) :=
  (ordinary N C).filter (fun j=>2≤((gateAt C j).inputs.filter (color69 N C)).length)

noncomputable def keep69 (N : Nat) (C : Circuit) := ordinary N C \ split69 N C

theorem color_special {N w : Nat} {C : Circuit} (h : w∈special N C) : color69 N C w=true := by
  rw [color69,ite_eq_left h]

theorem color_raw {N w : Nat} {C : Circuit} (hw : w<N) (h : w∉special N C) :
    color69 N C w=false := by rw [color69,ite_eq_right h,ite_eq_left hw]

theorem color_ordinary_iff {N j : Nat} {C : Circuit} (back : ReadsBack N C)
    (hj : j∈ordinary N C) : color69 N C (N+j)=true ↔
      ∃ w∈(gateAt C j).inputs,color69 N C w=true := by
  have ns := (Finset.mem_filter.mp hj).2
  rw [color69,ite_eq_right ns,ite_eq_right (by omega : ¬N+j<N),Nat.add_sub_cancel_left,List.any_eq_true]
  apply exists_congr
  intro w
  constructor
  · rintro ⟨h,hc⟩
    exact ⟨h,by simpa [back j (ordinary_index69 hj) w h] using hc⟩
  · rintro ⟨h,hc⟩
    exact ⟨h,by simpa [back j (ordinary_index69 hj) w h] using hc⟩

theorem color_keep_iff {N j : Nat} {C : Circuit} (back : ReadsBack N C)
    (hj : j∈keep69 N C) : color69 N C (N+j)=true ↔
      ∃ w∈(gateAt C j).inputs,color69 N C w=true :=
  color_ordinary_iff back (Finset.mem_sdiff.mp hj).1

theorem marked_keep_slots {N j : Nat} {C : Circuit} (hj : j∈keep69 N C) :
    ((gateAt C j).inputs.filter (color69 N C)).length≤1 := by
  obtain ⟨ord,no⟩ := Finset.mem_sdiff.mp hj
  by_contra! two
  exact no (Finset.mem_filter.mpr ⟨ord,two⟩)

theorem color_split_all {N j : Nat} {C : Circuit} (sh : shapes69 C) (hj : j∈split69 N C) :
    ∀ w∈(gateAt C j).inputs,color69 N C w=true := by
  obtain ⟨ord,two⟩ := Finset.mem_filter.mp hj
  have jlt : j<C.gates.length := ordinary_index69 ord
  have mem : gateAt C j∈C.gates := by simp [gateAt,jlt]
  have len : (gateAt C j).inputs.length≤2 := by rcases sh _ mem with h|h <;> omega
  apply List.length_filter_eq_length_iff.mp
  have hl := List.length_filter_le (p:=color69 N C) (l:=(gateAt C j).inputs)
  omega

theorem color_split_self {N j : Nat} {C : Circuit} (back : ReadsBack N C) (hj : j∈split69 N C) :
    color69 N C (N+j)=true := by
  obtain ⟨ord,two⟩ := Finset.mem_filter.mp hj
  apply (color_ordinary_iff back ord).2
  rw [←List.countP_pos_iff,List.countP_eq_length_filter]
  omega

lemma maskedCount69 (l : List Nat) (A : Finset Nat) :
    l.countP (fun w=>decide (w∈A)) = ∑w∈A,l.count w := by
  classical
  let f := l.filter (fun w=>decide (w∈A))
  have sub : f.toFinset ⊆ A := by
    intro w hw
    exact of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp hw)).2
  rw [List.countP_eq_length_filter]
  change f.length=_
  calc
    _ = ∑w∈f.toFinset,f.count w := (List.sum_toFinset_count_eq_length f).symm
    _ = ∑w∈A,f.count w := Finset.sum_subset sub (fun _ _ h =>
      List.count_eq_zero.mpr (fun e=>h (List.mem_toFinset.mpr e)))
    _ = _ := Finset.sum_congr rfl (fun w hw=>List.count_filter (by simpa using hw))

lemma countCover69 (l : List Nat) (p s a : Nat→Bool)
    (cover : ∀w∈l,p w=true → s w=true ∨ a w=true) : l.countP p≤l.countP s+l.countP a := by
  induction l with
  | nil => simp
  | cons w ws ih =>
    have tail := ih (fun v hv=>cover v (List.mem_cons_of_mem _ hv))
    have head := cover w List.mem_cons_self
    cases hp : p w <;> cases hs : s w <;> cases ha : a w <;> simp_all [List.countP_cons] <;> omega

theorem countedSlots69 {N : Nat} {C : Circuit} (P A : Finset Nat)
    (p : Nat→Bool) (pg : P⊆ordinary N C) (ag : A⊆ordinary N C)
    (cover : ∀ j∈P, ∀w∈(gateAt C j).inputs,p w=true →
      w∈special N C ∨ w∈A.image (fun t=>N+t)) :
    (∑j∈P,(gateAt C j).inputs.countP p)≤entries69 N C+A.card := by
  classical
  let I := A.image (fun j=>N+j)
  let specialSlot := fun w=>decide (w∈special N C)
  have each (j : Nat) (hj : j∈P) : (gateAt C j).inputs.countP p ≤
      (gateAt C j).inputs.countP specialSlot + ∑w∈I,(gateAt C j).inputs.count w := by
    rw [←maskedCount69]
    apply countCover69
    intro w hw hp
    exact (cover j hj w hw hp).imp (fun h=>by simpa [specialSlot] using h) (fun h=>by simpa [I] using h)
  have sl : (∑ j∈P,(gateAt C j).inputs.countP specialSlot) ≤ entries69 N C :=
    Finset.sum_le_sum_of_subset_of_nonneg pg (fun _ _ _ => Nat.zero_le _)
  have rest (w : Nat) (hw : w∈I) : (∑ j∈P,(gateAt C j).inputs.count w) ≤ 1 := by
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
    apply le_trans (b:=reads69 C (N+j)) _ (ordinary_reads69 (ag hj))
    unfold reads69 readsIn
    apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => Nat.zero_le _)
    exact fun q hq=>(Finset.mem_filter.mp (pg hq)).1
  have total := Finset.sum_le_sum each
  rw [Finset.sum_add_distrib,Finset.sum_comm (s:=P) (t:=I)] at total
  have pool := Finset.sum_le_sum rest
  simp only [Finset.sum_const,smul_eq_mul,mul_one] at pool
  have cap : I.card≤A.card := Finset.card_image_le
  omega

theorem splitCard69 {N : Nat} {C : Circuit} (_sh : shapes69 C) (back : ReadsBack N C) :
    (split69 N C).card≤entries69 N C := by
  classical
  let A := (ordinary N C).filter (fun j=>color69 N C (N+j)=true)
  have cover (j : Nat) (hj : j∈ordinary N C) (w : Nat) (hw : w∈(gateAt C j).inputs)
      (hl : color69 N C w=true) : w∈special N C ∨ w∈A.image (fun t=>N+t) := by
    by_cases sp : w∈special N C
    · exact Or.inl sp
    right
    have wire : w<N+j := back j (ordinary_index69 hj) w hw
    have mid : N≤w := by by_contra! z;rw [color_raw z sp] at hl;contradiction
    have eq : N+(w-N)=w := by omega
    have idx : w-N<C.size := by have := ordinary_index69 hj;omega
    have good : w-N∈ordinary N C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr idx,by simpa only [eq] using sp⟩
    exact Finset.mem_image.mpr ⟨w-N,Finset.mem_filter.mpr ⟨good,by simpa only [eq] using hl⟩,eq⟩
  have account := countedSlots69 (ordinary N C) A (color69 N C) (fun _ h=>h)
    (fun _ h=>(Finset.mem_filter.mp h).1) cover
  have pay (j : Nat) (hj : j∈ordinary N C) :
      (if color69 N C (N+j)=true then 1 else 0) +
      (if 2≤((gateAt C j).inputs.filter (color69 N C)).length then 1 else 0) ≤
      (gateAt C j).inputs.countP (color69 N C) := by
    rw [List.countP_eq_length_filter]
    by_cases many : 2≤((gateAt C j).inputs.filter (color69 N C)).length
    · rw [ite_eq_left many];split <;> omega
    rw [ite_eq_right many]
    split
    · next hc =>
      have has := (color_ordinary_iff back hj).1 hc
      have pos := List.countP_pos_iff.mpr has
      rw [List.countP_eq_length_filter] at pos
      omega
    · omega
  have total := Finset.sum_le_sum pay
  rw [Finset.sum_add_distrib,←Finset.card_filter,←Finset.card_filter] at total
  change A.card+(split69 N C).card≤_ at total
  omega

theorem entrySlotsBound69 {N : Nat} {C : Circuit} (sh : shapes69 C) (back : ReadsBack N C) :
    (∑j∈keep69 N C,(gateAt C j).inputs.countP
      (fun w=>decide (w∈special N C ∨ (N≤w ∧ w-N∈split69 N C)))) ≤ 2*entries69 N C := by
  classical
  have cap := countedSlots69 (keep69 N C) (split69 N C)
    (fun w=>decide (w∈special N C ∨ (N≤w ∧ w-N∈split69 N C)))
    (fun _ h=>(Finset.mem_sdiff.mp h).1) (fun _ h=>(Finset.mem_filter.mp h).1) (by
      intro j hj w hw h
      rcases of_decide_eq_true h with s|⟨low,idx⟩
      · exact Or.inl s
      · exact Or.inr (Finset.mem_image.mpr ⟨w-N,idx,by omega⟩))
  have splitBound := splitCard69 sh back
  omega

end PEqualNP.Outside.L_meta_25644_aux

namespace PEqualNP.Outside.L_meta_25644_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def pool69 (N : Nat) (C : Circuit) (P : Finset Nat) :=
  once69 N C ∪ P.image (fun k=>N+k)

def branch69 (N : Nat) (C : Circuit) (P : Finset Nat) (x y : Nat) : Prop :=
  x∈pool69 N C P ∧ ∃k∈P, y=N+k ∧ x∈(gateAt C k).inputs

abbrev walk69 (N : Nat) (C : Circuit) (P : Finset Nat) :=
  Relation.ReflTransGen (branch69 N C P)

def sink69 (N : Nat) (C : Circuit) (P : Finset Nat) (x : Nat) : Prop :=
  ∀ y, ¬ branch69 N C P x y

noncomputable def owner69 (N : Nat) (C : Circuit) (P : Finset Nat) (x : Nat) : Nat := by
  classical exact if h : ∃y,walk69 N C P x y ∧ sink69 N C P y then h.choose else x

noncomputable def roots69 (N : Nat) (C : Circuit) (P : Finset Nat) :=
  (once69 N C).image (owner69 N C P)

noncomputable def src69 (N : Nat) (C : Circuit) (P : Finset Nat) (z : Nat) : Finset Nat := by
  classical exact (once69 N C).filter (fun w=>owner69 N C P w=z)

noncomputable def reg69 (N : Nat) (C : Circuit) (P : Finset Nat) (z : Nat) : Finset Nat := by
  classical exact P.filter (fun k=>owner69 N C P (N+k)=z)

noncomputable def outside69 (N : Nat) (C : Circuit) (P : Finset Nat) (z : Nat) : Finset Nat := by
  classical exact (reg69 N C P z).biUnion fun k =>
    (gateAt C k).inputs.toFinset.filter (fun w=>w∉pool69 N C P)

noncomputable def slots69 (N : Nat) (C : Circuit) (P : Finset Nat) (z : Nat) : Nat := by
  classical exact ∑ k∈reg69 N C P z,(gateAt C k).inputs.countP (fun w=>decide (w∉pool69 N C P))

variable {N : Nat} {C : Circuit} {P : Finset Nat}

theorem reads_le_one69 (hp : P⊆ordinary N C) {w : Nat} (hw : w∈pool69 N C P) : reads69 C w≤1 := by
  rcases Finset.mem_union.mp hw with h | h
  · exact (Finset.mem_filter.mp h).2.le
  · obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp h;exact ordinary_reads69 (hp hk)

theorem reader69 {w i j : Nat} (one : reads69 C w≤1) (hi : i<C.size) (hj : j<C.size)
    (a : w∈(gateAt C i).inputs) (b : w∈(gateAt C j).inputs) : i=j := by
  by_contra ne
  have h:=Finset.add_le_sum (f:=fun k=>(gateAt C k).inputs.count w) (fun _ _=>Nat.zero_le _)
    (Finset.mem_range.mpr hi) (Finset.mem_range.mpr hj) ne
  have ai:=List.count_pos_iff.mpr a
  have bj:=List.count_pos_iff.mpr b
  change _ ≤ reads69 C w at h
  omega

theorem next_unique69 (hp : P⊆ordinary N C) : Relator.RightUnique (branch69 N C P) := by
  rintro w x y ⟨hw,i,hi,rfl,a⟩ ⟨_,j,hj,rfl,b⟩
  rw [reader69 (reads_le_one69 hp hw) (ordinary_index69 (hp hi)) (ordinary_index69 (hp hj)) a b]

theorem next_lt69 (hp : P⊆ordinary N C) (back : ReadsBack N C) {x y : Nat}
    (h : branch69 N C P x y) : x<y ∧ y<N+C.size := by
  obtain ⟨_,k,hk,rfl,inp⟩:=h
  have lt:=ordinary_index69 (hp hk)
  exact ⟨back k lt x inp,by omega⟩

theorem walk_in69 {x y : Nat} (h : walk69 N C P x y) (hx : x∈pool69 N C P) :
    y∈pool69 N C P := by
  induction h with
  | refl => exact hx
  | tail _ e _ =>
    obtain ⟨_,k,hk,rfl,_⟩ := e
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk)

theorem owner_spec69 (hp : P⊆ordinary N C) (back : ReadsBack N C) (w : Nat) :
    walk69 N C P w (owner69 N C P w) ∧ sink69 N C P (owner69 N C P w) := by
  classical
  have exists' (i : Nat) : ∀x,N+C.size-x=i → ∃y,walk69 N C P x y ∧ sink69 N C P y := by
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      intro x eq
      by_cases e : ∃y,branch69 N C P x y
      · obtain ⟨y,hy⟩:=e
        obtain ⟨lt,bound⟩:=next_lt69 hp back hy
        obtain ⟨v,path,sink⟩:=ih (N+C.size-y) (by omega) y rfl
        exact ⟨v,path.head hy,sink⟩
      · exact ⟨x,.refl,fun y h=> e ⟨y,h⟩⟩
  have h:=exists' _ w rfl
  simpa only [owner69,dif_pos h] using h.choose_spec

theorem owner_same69 (hp : P⊆ordinary N C) (back : ReadsBack N C) {x y : Nat}
    (e : branch69 N C P x y) : owner69 N C P x = owner69 N C P y := by
  have a := owner_spec69 hp back x
  have b := owner_spec69 hp back y
  have term {u v : Nat} (s : sink69 N C P u) (path : walk69 N C P u v) : u=v := by
    rcases path.cases_head with eq|⟨z,e,_⟩
    · exact eq
    · exact (s z e).elim
  rcases Relation.ReflTransGen.total_of_right_unique (next_unique69 hp)
    a.1 (b.1.head e) with h|h
  · exact term a.2 h
  · exact (term b.2 h).symm

theorem fiber69 (z w : Nat) :
    w∈src69 N C P z ∪ (reg69 N C P z).image (fun k=>N+k) ↔
      w∈pool69 N C P ∧ owner69 N C P w=z := by
  classical
  constructor
  · intro h
    rcases Finset.mem_union.mp h with a|b
    · obtain ⟨h,e⟩:=Finset.mem_filter.mp a;exact ⟨Finset.mem_union_left _ h,e⟩
    · obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp b
      obtain ⟨h,e⟩:=Finset.mem_filter.mp hk;exact ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem _ h),e⟩
  · rintro ⟨pool,e⟩
    rcases Finset.mem_union.mp pool with a|b
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨a,e⟩)
    · obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp b
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hk,e⟩))

theorem root_info69 (hp : P⊆ordinary N C) (back : ReadsBack N C) {z : Nat} (hz : z∈roots69 N C P) :
    z∈pool69 N C P ∧ sink69 N C P z ∧ owner69 N C P z=z ∧ (src69 N C P z).Nonempty := by
  obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hz
  have sp:=owner_spec69 hp back u
  refine ⟨walk_in69 sp.1 (Finset.mem_union_left _ hu),sp.2,?_,⟨u,Finset.mem_filter.mpr ⟨hu,rfl⟩⟩⟩
  have p:=(owner_spec69 hp back (owner69 N C P u)).1
  rcases p.cases_head with eq|⟨x,step,_⟩
  · exact eq.symm
  · exact (sp.2 x step).elim

end PEqualNP.Outside.L_meta_25644_aux

namespace PEqualNP.Outside.L_meta_25644_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
variable {N : Nat} {C : Circuit} {P : Finset Nat}

theorem root_zero69 (hp : P⊆ordinary N C) (back : ReadsBack N C) {z : Nat} (hz : z∈roots69 N C P) :
    readsIn C (reg69 N C P z) z=0 := by
  obtain ⟨pool,sink,_,_⟩:=root_info69 hp back hz
  apply Finset.sum_eq_zero
  intro j hj;apply List.count_eq_zero.mpr
  intro h;exact sink (N+j) ⟨pool,j,(Finset.mem_filter.mp hj).1,rfl,h⟩

theorem local_read69 (hp : P⊆ordinary N C) (back : ReadsBack N C) {z w : Nat}
    (pool : w∈pool69 N C P) (ow : owner69 N C P w=z) (other : w≠z) :
    readsIn C (reg69 N C P z) w=1 ∧ reads69 C w=1 := by
  obtain ⟨way,_⟩:=owner_spec69 hp back w
  rw [ow] at way
  obtain ⟨_,⟨_,k,hk,rfl,hit⟩,_⟩:=way.cases_head.resolve_left other
  have eq := owner_same69 hp back (show branch69 N C P w (N+k) from ⟨pool,k,hk,rfl,hit⟩)
  have mem : k∈reg69 N C P z := Finset.mem_filter.mpr ⟨hk,eq.symm.trans ow⟩
  have le : (gateAt C k).inputs.count w ≤ readsIn C (reg69 N C P z) w :=
    Finset.single_le_sum (fun l _=>Nat.zero_le ((gateAt C l).inputs.count w)) mem
  have bound : readsIn C (reg69 N C P z) w ≤ reads69 C w :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun j hj =>
      Finset.mem_range.mpr (ordinary_index69 (hp (Finset.mem_filter.mp hj).1))) (fun _ _ _=>Nat.zero_le _)
  have counted:=List.count_pos_iff.mpr hit;have all:=reads_le_one69 hp pool
  omega

theorem pool_bound69 (hp : P⊆ordinary N C) {w : Nat} (pool : w∈pool69 N C P) : w<N+C.size := by
  rcases Finset.mem_union.mp pool with h|h
  · have lt:=Finset.mem_range.mp (Finset.mem_filter.mp h).1;omega
  · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp h;have:=ordinary_index69 (hp hj);omega

theorem walk_le69 (hp : P⊆ordinary N C) (back : ReadsBack N C) {x y : Nat} (path : walk69 N C P x y) :
    x≤y := by
  induction path with
  | refl => exact le_rfl
  | tail _ e ih => exact ih.trans (next_lt69 hp back e).1.le

theorem outside_mem69 {z w : Nat} :
    w∈outside69 N C P z ↔ w∉pool69 N C P ∧ ∃k∈reg69 N C P z,w∈(gateAt C k).inputs := by
  classical
  simp only [outside69,Finset.mem_biUnion,Finset.mem_filter,List.mem_toFinset]
  grind

theorem read_le_slots69 {z w : Nat} (out : w∉pool69 N C P) :
    readsIn C (reg69 N C P z) w ≤ slots69 N C P z := by
  classical
  apply Finset.sum_le_sum
  intro k _
  induction (gateAt C k).inputs with
  | nil => simp
  | cons a l ih =>
    simp only [decide_not] at ih
    by_cases eq : a=w
    · subst a;simp [List.count_cons,List.countP_cons,out,ih]
    · by_cases pa:a∈pool69 N C P <;> simp [List.count_cons,List.countP_cons,eq,pa,ih] <;> omega

theorem out_pos69 {z w : Nat} (h : w∈outside69 N C P z) :
    0<readsIn C (reg69 N C P z) w ∧ readsIn C (reg69 N C P z) w≤ slots69 N C P z := by
  obtain ⟨no,k,hk,hx⟩:=outside_mem69.mp h
  exact ⟨(List.count_pos_iff.mpr hx).trans_le
    (Finset.single_le_sum (fun j _=>Nat.zero_le ((gateAt C j).inputs.count w)) hk),read_le_slots69 no⟩

theorem outside_card69 {z : Nat} : (outside69 N C P z).card ≤ slots69 N C P z := by
  classical
  unfold outside69 slots69
  refine Finset.card_biUnion_le.trans (Finset.sum_le_sum ?_)
  intro k _
  have h (l : List Nat) : (l.toFinset.filter (fun w=>w∉pool69 N C P)).card ≤
      l.countP (fun w=>decide (w∉pool69 N C P)) := by
    induction l with
    | nil => simp
    | cons w l ih =>
      simp only [decide_not] at ih
      by_cases hw:w∈pool69 N C P
      · simpa [Finset.filter_insert,hw,List.countP_cons] using ih
      · simp [Finset.filter_insert,hw,List.countP_cons]
        exact (Finset.card_insert_le _ _).trans (by omega)
  exact h _

theorem outside_empty69 {z : Nat} : outside69 N C P z=∅ ↔ slots69 N C P z=0 := by
  classical
  constructor
  · intro empty;apply Finset.sum_eq_zero;intro k hk
    apply List.countP_eq_zero.mpr
    intro w hw
    simp only [Bool.not_eq_true,decide_eq_false_iff_not,not_not]
    by_contra out
    have h : w∈outside69 N C P z := outside_mem69.mpr ⟨out,k,hk,hw⟩
    simp [empty] at h
  · intro z0;apply Finset.card_eq_zero.mp;have le:=outside_card69 (N:=N) (C:=C) (P:=P) (z:=z);omega

theorem subtree69 (hp : P⊆ordinary N C) (back : ReadsBack N C) (sh : shapes69 C)
    (last : C.output+1=N+C.size) {z : Nat} (hz : z∈roots69 N C P)
    (slot : slots69 N C P z≤1) : tree69 N C (src69 N C P z) (outside69 N C P z) := by
  classical
  obtain ⟨zp,sink,zown,nonempty⟩:=root_info69 hp back hz
  have bound:=pool_bound69 hp zp
  refine ⟨reg69 N C P z,z,fun j hj=>hp (Finset.mem_filter.mp hj).1,
    (fiber69 z z).mpr ⟨zp,zown⟩,root_zero69 hp back hz,?_,?_,?_⟩
  · intro w hw
    obtain ⟨out,k,hk,read⟩:=outside_mem69.mp hw
    have lt:=back k (ordinary_index69 (hp (Finset.mem_filter.mp hk).1)) w read
    have path:=(owner_spec69 hp back (N+k)).1
    rw [(Finset.mem_filter.mp hk).2] at path
    have cmp:=walk_le69 hp back path
    obtain ⟨pos,le⟩:=out_pos69 hw
    exact ⟨fun h=>out ((fiber69 z w).mp h).1,by omega,by omega⟩
  · intro j hj
    obtain ⟨keep,own⟩:=Finset.mem_filter.mp hj
    have ord:=hp keep;have jl:=ordinary_index69 ord
    have mem : gateAt C j∈C.gates := by have h:j<C.gates.length:=jl;simp [gateAt,h]
    rcases sh _ mem with ao | no
    · refine ⟨ao.1,ao.2,?_⟩
      intro w wh
      by_cases pooled:w∈pool69 N C P
      · exact Or.inl ((fiber69 z w).mpr ⟨pooled,(owner_same69 hp back ⟨pooled,j,keep,rfl,wh⟩).trans own⟩)
      · exact Or.inr (outside_mem69.mpr ⟨pooled,j,hj,wh⟩)
    · have ns: N+j∉special N C := (Finset.mem_filter.mp ord).2
      apply (ns (Finset.mem_union_right _ (Finset.mem_image_of_mem _
        (show j∈neg69 C from Finset.mem_filter.mpr ⟨Finset.mem_range.mpr jl,no.1⟩)))).elim
  · intro w hw diff
    obtain ⟨pool,own⟩:=(fiber69 z w).mp hw
    obtain ⟨loc,all⟩:=local_read69 hp back pool own diff
    have path:=(owner_spec69 hp back w).1
    rw [own] at path
    have le:=walk_le69 hp back path
    exact ⟨loc,all,by omega⟩

end PEqualNP.Outside.L_meta_25644_aux

namespace PEqualNP.Outside.L_meta_25644_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
variable {N : Nat} {C:Circuit}
lemma keepSub69 : keep69 N C ⊆ ordinary N C := Finset.sdiff_subset
lemma colorOnce69 {w:Nat} (h:w∈once69 N C) : color69 N C w=false := by
  obtain ⟨hw,one⟩:=Finset.mem_filter.mp h
  have lo:=Finset.mem_range.mp hw
  apply color_raw lo
  intro hs
  rcases Finset.mem_union.mp hs with rep|notw
  · have high:2≤reads69 C w := (Finset.mem_filter.mp rep).2
    omega
  · obtain ⟨z,_,rfl⟩:=Finset.mem_image.mp notw;omega
lemma colorOuter69 (back:ReadsBack N C) {j w:Nat} (hp:j∈keep69 N C) (hit:w∈(gateAt C j).inputs)
    (out:w∉pool69 N C (keep69 N C)) : color69 N C w=true := by
  classical
  have jj:=ordinary_index69 (keepSub69 hp)
  have wr:=back j jj w hit
  by_cases hs:w∈special N C
  · exact color_special hs
  by_cases low:w<N
  · have used:0<reads69 C w := by
      have h:=Finset.single_le_sum (f:=fun k=>(gateAt C k).inputs.count w) (fun _ _=>Nat.zero_le _) (Finset.mem_range.mpr jj)
      have count:=List.count_pos_iff.mpr hit
      change _≤reads69 C w at h
      omega
    have one:reads69 C w=1 := by
      by_contra! ne
      apply hs
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by omega⟩)
    exact (out (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr low,one⟩))).elim
  · let k:=w-N
    have eq:N+k=w := by dsimp [k];omega
    have ord:k∈ordinary N C:=Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by dsimp [k];omega),by rwa [eq]⟩
    by_cases sp:k∈split69 N C
    · exact eq ▸ color_split_self back sp
    · have kkeep:k∈keep69 N C:=Finset.mem_sdiff.mpr ⟨ord,sp⟩
      exact (out (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k,kkeep,eq⟩))).elim

lemma markedInputs69 (back:ReadsBack N C) {j:Nat} (h:j∈keep69 N C) :
    (gateAt C j).inputs.countP (color69 N C) = if color69 N C (N+j) then 1 else 0 := by
  have le:=marked_keep_slots h
  rw [←List.countP_eq_length_filter] at le
  have pos := color_keep_iff back h
  rw [←List.countP_pos_iff] at pos
  cases hx:color69 N C (N+j)
  · change (gateAt C j).inputs.countP (color69 N C)=0
    by_contra! ne
    have eq:=pos.mpr (by omega)
    rw [hx] at eq;contradiction
  · change (gateAt C j).inputs.countP (color69 N C)=1
    have hp:=pos.mp hx
    omega

lemma splitInputCount69 (L:List Nat) (p:Nat→Bool) (pool A:Finset Nat)
    (spec:∀w∈L, (p w=true ↔ w∉pool ∨ w∈A) ∧ (w∈A → w∈pool)) :
    L.countP p = L.countP (fun w=>decide (w∉pool)) + ∑w∈A,L.count w := by
  classical
  induction L with
  | nil => simp
  | cons x xs ih =>
    have t:=ih (fun w hw=>spec w (List.mem_cons_of_mem _ hw))
    simp only [List.countP_cons,List.count_cons,Finset.sum_add_distrib]
    have a:=spec x (by simp)
    by_cases xA:x∈A <;> by_cases xp:x∈pool <;> cases xx:p x <;>
      simp_all <;> omega
end PEqualNP.Outside.L_meta_25644_aux

namespace PEqualNP.Outside.L_meta_25644_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
theorem conserved69 {N z:Nat} {C:Circuit} (back:ReadsBack N C)
    (hz:z∈roots69 N C (keep69 N C))
    (lr:∀ j∈reg69 N C (keep69 N C) z,
      readsIn C (reg69 N C (keep69 N C) z) (N+j)=if N+j=z then 0 else 1) :
    slots69 N C (keep69 N C) z = if color69 N C z then 1 else 0 := by
  classical
  let P:=keep69 N C
  let pool:=pool69 N C P
  let rg:=reg69 N C P z
  let hot:=rg.filter (fun j=>color69 N C (N+j)=true)
  let A:=hot.image (fun j=>N+j)
  have acard:A.card=hot.card:=Finset.card_image_of_injective _ (fun _ _ e=>Nat.add_left_cancel e)
  have rgKeep (j:Nat) (hj:j∈rg):j∈P:=(Finset.mem_filter.mp hj).1
  have memA {w:Nat} : w∈A ↔ w∈pool ∧ owner69 N C P w=z ∧ color69 N C w=true := by
    constructor
    · intro h;obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp h
      obtain ⟨jr,marked⟩:=Finset.mem_filter.mp hj
      exact ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem _ (rgKeep _ jr)),(Finset.mem_filter.mp jr).2,marked⟩
    · rintro ⟨h,o,t⟩
      rcases Finset.mem_union.mp h with raw|gate
      · exact (by rw [colorOnce69 raw] at t; contradiction : False).elim
      · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp gate
        exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hj,o⟩,t⟩,rfl⟩
  have inEq (j:Nat) (hj:j∈rg) :
      (gateAt C j).inputs.countP (color69 N C) =
        (gateAt C j).inputs.countP (fun w=>decide (w∉pool)) + ∑w∈A,(gateAt C j).inputs.count w := by
    apply splitInputCount69
    intro w hit
    have memPool (h:w∈pool) : owner69 N C P w=z := by
      have p:=owner_same69 (P:=P) keepSub69 back (show branch69 N C P w (N+j) from ⟨h,j,rgKeep _ hj,rfl,hit⟩)
      exact p.trans (Finset.mem_filter.mp hj).2
    refine ⟨⟨fun t=>?_,?_⟩,fun h=>(memA.mp h).1⟩
    · by_cases pw:w∈pool
      · exact Or.inr (memA.mpr ⟨pw,memPool pw,t⟩)
      · exact Or.inl pw
    · rintro (out|inside)
      · exact colorOuter69 back (rgKeep _ hj) hit out
      · exact (memA.mp inside).2.2
  have calcAll : hot.card=slots69 N C P z+∑w∈A,readsIn C rg w := by
    calc
      hot.card = ∑j∈rg, if color69 N C (N+j) then 1 else 0 := by simp only [hot,Finset.card_filter]
      _ = ∑j∈rg,(gateAt C j).inputs.countP (color69 N C) :=
        Finset.sum_congr rfl (fun j hj=>(markedInputs69 back (rgKeep _ hj)).symm)
      _ = _ := by
        rw [Finset.sum_congr rfl inEq,Finset.sum_add_distrib]
        congr 1;exact Finset.sum_comm
  have lower : (∑w∈A,readsIn C rg w)+(if z∈A then 1 else 0)=A.card := by
    calc
      _ = (∑w∈A,if w=z then 0 else 1) + (∑w∈A,if w=z then 1 else 0) := by
        congr 1
        · apply Finset.sum_congr rfl
          intro w hw;obtain ⟨j,m,rfl⟩:=Finset.mem_image.mp hw
          exact lr _ (Finset.mem_filter.mp m).1
        · simp
      _ = ∑_w∈A,1 := by
        rw [←Finset.sum_add_distrib];apply Finset.sum_congr rfl;intro w _;split <;> simp_all
      _ = _ := by simp
  have root:=root_info69 (P:=P) keepSub69 back hz
  have za : z∈A ↔ color69 N C z=true := ⟨fun h=>(memA.mp h).2.2,fun h=>memA.mpr ⟨root.1,root.2.2.1,h⟩⟩
  change slots69 N C P z=_
  simp only [za] at lower
  omega
end PEqualNP.Outside.L_meta_25644_aux

namespace PEqualNP.Outside.L_meta_25644_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
theorem fiberSlots69 {N z:Nat} {C:Circuit} (back:ReadsBack N C) (hz:z∈roots69 N C (keep69 N C)) :
    slots69 N C (keep69 N C) z = if color69 N C z then 1 else 0 := by
  apply conserved69 back hz
  intro j hj
  by_cases eq:N+j=z
  · rw [eq,ite_eq_left rfl]
    exact root_zero69 keepSub69 back hz
  · rw [ite_eq_right eq]
    obtain ⟨m,e⟩:=Finset.mem_filter.mp hj
    have pool:N+j∈pool69 N C (keep69 N C):=Finset.mem_union_right _ (Finset.mem_image_of_mem _ m)
    exact (local_read69 keepSub69 back pool e eq).1
end PEqualNP.Outside.L_meta_25644_aux

namespace PEqualNP.Outside.L_meta_25644_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

theorem sum_reads_mask69 (l : List Nat) (A : Finset Nat) :
    (∑w∈A,l.count w) = l.countP (fun w=>decide (w∈A)) := by
  classical
  let f:=l.filter (fun w=>decide (w∈A))
  have sub:f.toFinset⊆A := fun _ hw=>of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp hw)).2
  rw [List.countP_eq_length_filter]
  change _=f.length
  calc
    _ = ∑w∈A,f.count w := Finset.sum_congr rfl (fun w hw=>(List.count_filter (by simpa using hw)).symm)
    _ = ∑w∈f.toFinset,f.count w := (Finset.sum_subset sub (fun _ _ h=>
      List.count_eq_zero.mpr (fun e=>h (List.mem_toFinset.mpr e)))).symm
    _ = _ := List.sum_toFinset_count_eq_length f

theorem pure_sink69 {N z : Nat} {C : Circuit} (sh : shapes69 C) (back : ReadsBack N C)
    (last : C.output+1=N+C.size) (live : ∀j<C.size,j+1<C.size → 0<reads69 C (N+j))
    (hz : z∈roots69 N C (keep69 N C)) (zero : slots69 N C (keep69 N C) z=0) (out : z≠C.output) :
    z∉special N C ∧ ∃k∈gates69 C \ ordinary N C, z∈(gateAt C k).inputs := by
  classical
  obtain ⟨pool,sink,_,_⟩:=root_info69 keepSub69 back hz
  have slot:=fiberSlots69 back hz
  have off : color69 N C z=false := by cases h:color69 N C z <;> simp_all
  have ns : z∉special N C := fun h => by have a:=color_special h;rw [off] at a;contradiction
  have pos : 0<reads69 C z := by
    rcases Finset.mem_union.mp pool with raw|internal
    · have one : reads69 C z=1 := (Finset.mem_filter.mp raw).2;omega
    · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp internal
      have lt:=ordinary_index69 (keepSub69 hj)
      exact live j lt (by omega)
  have seek : ∃ k∈gates69 C, z∈(gateAt C k).inputs := by
    by_contra! no
    have none : reads69 C z=0 := Finset.sum_eq_zero (fun j hj=>List.count_eq_zero.mpr (no j hj))
    omega
  obtain ⟨k,hk,hit⟩:=seek
  refine ⟨ns,k,Finset.mem_sdiff.mpr ⟨hk,?_⟩,hit⟩
  intro ord
  by_cases split:k∈split69 N C
  · have on:=color_split_all sh split z hit
    rw [off] at on;contradiction
  · exact sink (N+k) ⟨pool,k,Finset.mem_sdiff.mpr ⟨ord,split⟩,rfl,hit⟩

theorem pure_count69 {N : Nat} {C : Circuit} (sh : shapes69 C) (back : ReadsBack N C)
    (last : C.output+1=N+C.size) (live : ∀j<C.size,j+1<C.size → 0<reads69 C (N+j)) :
    ((roots69 N C (keep69 N C)).filter (fun z=>slots69 N C (keep69 N C) z=0)).card ≤ exits69 N C+1 := by
  classical
  let T:=(roots69 N C (keep69 N C)).filter (fun z=>slots69 N C (keep69 N C) z=0)
  let A:=T.erase C.output
  let gs:=gates69 C \ ordinary N C
  have obs (w : Nat) (hw:w∈A) : w∉special N C ∧ ∃k∈gs, w∈(gateAt C k).inputs := by
    obtain ⟨different,hh⟩:=Finset.mem_erase.mp hw
    obtain ⟨inR,zero⟩:=Finset.mem_filter.mp hh
    exact pure_sink69 sh back last live inR zero different
  have each (w:Nat) (hw:w∈A) : 1 ≤ ∑k∈gs,(gateAt C k).inputs.count w := by
    obtain ⟨k,hk,hit⟩:=(obs w hw).2
    exact (List.count_pos_iff.mpr hit).trans_le
      (Finset.single_le_sum (fun t _=>Nat.zero_le ((gateAt C t).inputs.count w)) hk)
  have bound : A.card≤exits69 N C := by
    calc
      _ = ∑ _∈A,1 := by simp
      _ ≤ ∑w∈A,∑k∈gs,(gateAt C k).inputs.count w := Finset.sum_le_sum each
      _ = ∑k∈gs,∑w∈A,(gateAt C k).inputs.count w := Finset.sum_comm
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k _
        rw [sum_reads_mask69]
        exact List.countP_mono_left (fun w _ h => decide_eq_true ((obs w (of_decide_eq_true h)).1))
  change T.card≤exits69 N C+1
  have incl : T⊆insert C.output A := by
    intro z mem;by_cases e:z=C.output
    · exact Finset.mem_insert.mpr (Or.inl e)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨e,mem⟩))
  have step:=Finset.card_le_card incl
  have cap:=Finset.card_insert_le C.output A
  change T.card≤(insert C.output A).card at step
  omega
end PEqualNP.Outside.L_meta_25644_aux

namespace PEqualNP.Outside.L_meta_25644_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
theorem mixed_count69 {N:Nat} {C:Circuit} (sh:shapes69 C) (back:ReadsBack N C) :
    ((roots69 N C (keep69 N C)).filter (fun z=>slots69 N C (keep69 N C) z≠0)).card≤2*entries69 N C := by
  classical
  let P:=keep69 N C
  let R:=(roots69 N C P).filter (fun z=>slots69 N C P z≠0)
  let f:=fun j=>(gateAt C j).inputs.countP (fun w=>decide (w∉pool69 N C P))
  let g:=fun j=>(gateAt C j).inputs.countP (fun w=>decide (w∈special N C ∨ (N≤w ∧ w-N∈split69 N C)))
  have per (j:Nat) (hj:j∈P): f j≤g j := by
    apply List.countP_mono_left
    intro w hw out'
    have out:w∉pool69 N C P:=of_decide_eq_true out'
    apply decide_eq_true
    by_cases sp:w∈special N C
    · exact Or.inl sp
    · have color:=colorOuter69 back hj hw out
      have nle : N≤w:=by by_contra! h;rw [color_raw h sp] at color;contradiction
      have eq:N+(w-N)=w:=by omega
      have ji:=ordinary_index69 (keepSub69 hj)
      have wi:=back j ji w hw
      have ord:w-N∈ordinary N C:=Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by rwa [eq]⟩
      refine Or.inr ⟨nle,?_⟩
      by_contra ns
      have inside:w-N∈P:=Finset.mem_sdiff.mpr ⟨ord,ns⟩
      exact out (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w-N,inside,eq⟩))
  have lower (z:Nat) (hz:z∈R) : 1≤ slots69 N C P z := by
    have neq:slots69 N C P z≠0:=(Finset.mem_filter.mp hz).2
    omega
  change R.card≤_
  calc
    R.card = ∑_z∈R,1 := by simp
    _ ≤ ∑z∈R,slots69 N C P z := Finset.sum_le_sum lower
    _ = ∑j∈P.filter (fun i=>owner69 N C P (N+i)∈R), f j :=
      Finset.sum_fiberwise_eq_sum_filter P R (fun j=>owner69 N C P (N+j)) f
    _ ≤ ∑j∈P,f j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _=>Nat.zero_le _)
    _ ≤ ∑j∈P,g j := Finset.sum_le_sum per
    _ ≤ _ := entrySlotsBound69 sh back
end PEqualNP.Outside.L_meta_25644_aux

namespace PEqualNP.Outside.L_meta_25644_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

theorem finish69 (N : Nat) (C : Circuit) (sh : shapes69 C) (back : ReadsBack N C)
    (_pos : 0<C.size) (last : C.output+1=N+C.size)
    (live : ∀j<C.size,j+1<C.size → 0<reads69 C (N+j)) :
    ∃ pure chains : List (Finset Nat),
      pure.length≤exits69 N C+1 ∧ chains.length≤2*entries69 N C ∧
      (pure++chains).Pairwise (fun A B=>Disjoint A B) ∧
      (pure++chains).toFinset.biUnion (fun S=>S)=once69 N C ∧
      (∀S∈pure,S.Nonempty ∧ tree69 N C S ∅) ∧
      (∀S∈chains,S.Nonempty ∧ ∃b : Nat,tree69 N C S {b}) := by
  classical
  let P:=keep69 N C
  let roots:=roots69 N C P
  let Q:=roots.filter (fun z=>slots69 N C P z=0)
  let M:=roots.filter (fun z=>slots69 N C P z≠0)
  let leaf:=src69 N C P
  let qr:=Q.toList
  let mr:=M.toList
  have qmem (z:Nat) : z∈qr ↔ z∈roots ∧ slots69 N C P z=0 := by simp [qr,Q]
  have mmem (z:Nat) : z∈mr ↔ z∈roots ∧ slots69 N C P z≠0 := by simp [mr,M]
  have covered (z:Nat) : z∈qr++mr ↔ z∈roots := by
    rw [List.mem_append,qmem,mmem];tauto
  have nd : (qr++mr).Nodup := by
    refine List.nodup_append.mpr ⟨Q.nodup_toList,M.nodup_toList,?_⟩
    intro x hx y hy e;subst y;exact (mmem x|>.mp hy).2 ((qmem x|>.mp hx).2)
  have fiber {w z:Nat}: w∈leaf z ↔ w∈once69 N C ∧ owner69 N C P w=z := Finset.mem_filter
  have facts {z:Nat} (hz:z∈roots) : (leaf z).Nonempty ∧
      tree69 N C (leaf z) (outside69 N C P z) := by
    have count:=fiberSlots69 back hz
    have le : slots69 N C P z≤1 := by rw [count];split <;> decide
    exact ⟨(root_info69 keepSub69 back hz).2.2.2,subtree69 keepSub69 back sh last hz le⟩
  refine ⟨qr.map leaf,mr.map leaf,?_,?_,?_,?_,?_,?_⟩
  · simpa only [qr,List.length_map,Finset.length_toList] using pure_count69 sh back last live
  · simpa only [mr,List.length_map,Finset.length_toList] using mixed_count69 sh back
  · rw [←List.map_append,List.pairwise_map]
    apply nd.imp
    intro a b diff
    apply Finset.disjoint_left.mpr
    intro w ha hb;exact diff ((fiber.mp ha).2.symm.trans (fiber.mp hb).2)
  · rw [←List.map_append]
    ext w
    simp only [Finset.mem_biUnion,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨_,⟨z,_,rfl⟩,hit⟩;exact (fiber.mp hit).1
    · intro raw
      let z:=owner69 N C P w
      have root:z∈roots:=Finset.mem_image_of_mem _ raw
      exact ⟨leaf z,⟨z,(covered z).mpr root,rfl⟩,fiber.mpr ⟨raw,rfl⟩⟩
  · intro S hs
    obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hs
    obtain ⟨rt,zero⟩:=(qmem z).mp hz
    obtain ⟨ne,tree⟩:=facts rt
    rw [outside_empty69.mpr zero] at tree
    exact ⟨ne,tree⟩
  · intro S hs
    obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hs
    obtain ⟨rt,nz⟩:=(mmem z).mp hz
    obtain ⟨ne,tree⟩:=facts rt
    have card : (outside69 N C P z).card=1 := by
      have cap:=outside_card69 (N:=N) (C:=C) (P:=P) (z:=z)
      have count:=fiberSlots69 back rt
      have nonempty : (outside69 N C P z).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr (fun h=>nz (outside_empty69.mp h))
      have pos:=Finset.card_pos.mpr nonempty
      change slots69 N C P z=_ at count
      split at count <;> omega
    obtain ⟨b,eq⟩:=Finset.card_eq_one.mp card
    exact ⟨ne,b,eq ▸ tree⟩
end PEqualNP.Outside.L_meta_25644_aux

namespace PEqualNP.Outside.L_meta_25644_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
theorem splitStrict44 {N : Nat} {C : Circuit} (_sh : shapes69 C) (back : ReadsBack N C) (pos : 0<entries69 N C) :
    (split69 N C).card<entries69 N C := by
  classical
  let A := (ordinary N C).filter (fun j=>color69 N C (N+j)=true)
  have cover (j : Nat) (hj : j∈ordinary N C) (w : Nat) (hw : w∈(gateAt C j).inputs)
      (hl : color69 N C w=true) : w∈special N C ∨ w∈A.image (fun t=>N+t) := by
    by_cases sp : w∈special N C
    · exact Or.inl sp
    right
    have wire : w<N+j := back j (ordinary_index69 hj) w hw
    have mid : N≤w := by by_contra! z;rw [color_raw z sp] at hl;contradiction
    have eq : N+(w-N)=w := by omega
    have idx : w-N<C.size := by have := ordinary_index69 hj;omega
    have good : w-N∈ordinary N C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr idx,by simpa only [eq] using sp⟩
    exact Finset.mem_image.mpr ⟨w-N,Finset.mem_filter.mpr ⟨good,by simpa only [eq] using hl⟩,eq⟩
  by_cases ne : A.Nonempty
  case neg =>
    have emp : split69 N C=∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun j hj =>
      ne ⟨j,Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1,color_split_self back hj⟩⟩)
    simpa [emp] using pos
  let top := A.max' ne
  have incl : A.erase top⊆ordinary N C := fun j hj=>(Finset.mem_filter.mp (Finset.mem_erase.mp hj).2).1
  have cover' (j : Nat) (hj : j∈ordinary N C) (w : Nat) (hw : w∈(gateAt C j).inputs)
      (on : color69 N C w=true) : w∈special N C ∨ w∈(A.erase top).image (fun t=>N+t) := by
    rcases cover j hj w hw on with h|h
    · exact Or.inl h
    · obtain ⟨t,ht,rfl⟩:=Finset.mem_image.mp h
      have later : N+t<N+j := back j (ordinary_index69 hj) _ hw
      have marked : j∈A:=Finset.mem_filter.mpr ⟨hj,(color_ordinary_iff back hj).mpr ⟨N+t,hw,on⟩⟩
      have limit : j≤top := Finset.le_max' _ _ marked
      exact Or.inr (Finset.mem_image.mpr ⟨t,Finset.mem_erase.mpr ⟨by omega,ht⟩,rfl⟩)
  have account := countedSlots69 (ordinary N C) (A.erase top) (color69 N C) (fun _ h=>h) incl cover'
  rw [Finset.card_erase_of_mem (Finset.max'_mem A ne)] at account
  have nonzero:=Finset.card_pos.mpr ne

  have pay (j : Nat) (hj : j∈ordinary N C) :
      (if color69 N C (N+j)=true then 1 else 0) +
      (if 2≤((gateAt C j).inputs.filter (color69 N C)).length then 1 else 0) ≤
      (gateAt C j).inputs.countP (color69 N C) := by
    rw [List.countP_eq_length_filter]
    by_cases many : 2≤((gateAt C j).inputs.filter (color69 N C)).length
    · rw [ite_eq_left many];split <;> omega
    rw [ite_eq_right many]
    split
    · next hc =>
      have has := (color_ordinary_iff back hj).1 hc
      have pos := List.countP_pos_iff.mpr has
      rw [List.countP_eq_length_filter] at pos
      omega
    · omega
  have total := Finset.sum_le_sum pay
  rw [Finset.sum_add_distrib,←Finset.card_filter,←Finset.card_filter] at total
  change A.card+(split69 N C).card≤_ at total
  omega

theorem entryStrict44 {N : Nat} {C : Circuit} (sh : shapes69 C) (back : ReadsBack N C) (pos : 0<entries69 N C) :
    (∑j∈keep69 N C,(gateAt C j).inputs.countP
      (fun w=>decide (w∈special N C ∨ (N≤w ∧ w-N∈split69 N C)))) < 2*entries69 N C := by
  classical
  have cap := countedSlots69 (keep69 N C) (split69 N C)
    (fun w=>decide (w∈special N C ∨ (N≤w ∧ w-N∈split69 N C)))
    (fun _ h=>(Finset.mem_sdiff.mp h).1) (fun _ h=>(Finset.mem_filter.mp h).1) (by
      intro j hj w hw h
      rcases of_decide_eq_true h with s|⟨low,idx⟩
      · exact Or.inl s
      · exact Or.inr (Finset.mem_image.mpr ⟨w-N,idx,by omega⟩))
  have splitBound := splitStrict44 sh back pos
  omega

theorem mixedStrict44 {N:Nat} {C:Circuit} (sh:shapes69 C) (back:ReadsBack N C) (pos : 0<entries69 N C) :
    ((roots69 N C (keep69 N C)).filter (fun z=>slots69 N C (keep69 N C) z≠0)).card<2*entries69 N C := by
  classical
  let P:=keep69 N C
  let R:=(roots69 N C P).filter (fun z=>slots69 N C P z≠0)
  let f:=fun j=>(gateAt C j).inputs.countP (fun w=>decide (w∉pool69 N C P))
  let g:=fun j=>(gateAt C j).inputs.countP (fun w=>decide (w∈special N C ∨ (N≤w ∧ w-N∈split69 N C)))
  have per (j:Nat) (hj:j∈P): f j≤g j := by
    apply List.countP_mono_left
    intro w hw out'
    have out:w∉pool69 N C P:=of_decide_eq_true out'
    apply decide_eq_true
    by_cases sp:w∈special N C
    · exact Or.inl sp
    · have color:=colorOuter69 back hj hw out
      have nle : N≤w:=by by_contra! h;rw [color_raw h sp] at color;contradiction
      have eq:N+(w-N)=w:=by omega
      have ji:=ordinary_index69 (keepSub69 hj)
      have wi:=back j ji w hw
      have ord:w-N∈ordinary N C:=Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by rwa [eq]⟩
      refine Or.inr ⟨nle,?_⟩
      by_contra ns
      have inside:w-N∈P:=Finset.mem_sdiff.mpr ⟨ord,ns⟩
      exact out (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w-N,inside,eq⟩))
  have lower (z:Nat) (hz:z∈R) : 1≤ slots69 N C P z := by
    have neq:slots69 N C P z≠0:=(Finset.mem_filter.mp hz).2
    omega
  change R.card<_
  calc
    R.card = ∑_z∈R,1 := by simp
    _ ≤ ∑z∈R,slots69 N C P z := Finset.sum_le_sum lower
    _ = ∑j∈P.filter (fun i=>owner69 N C P (N+i)∈R), f j :=
      Finset.sum_fiberwise_eq_sum_filter P R (fun j=>owner69 N C P (N+j)) f
    _ ≤ ∑j∈P,f j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _=>Nat.zero_le _)
    _ ≤ ∑j∈P,g j := Finset.sum_le_sum per
    _ < _ := entryStrict44 sh back pos

end PEqualNP.Outside.L_meta_25644_aux

namespace PEqualNP.Outside.L_meta_25644_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped Classical
def shared44 (N : Nat) (C : Circuit) :=
  (Finset.range (N+C.size)).filter (fun w=>2≤reads69 C w)
def sharedG44 (N : Nat) (C : Circuit) :=
  (gates69 C).filter (fun j=>2≤reads69 C (N+j))
def marked44 (N : Nat) (C : Circuit) := ∑ w∈shared44 N C,reads69 C w
def lift44 (N : Nat) (C : Circuit) (w : Nat) :=
  if w<N ∨ w∈shared44 N C then w else w+C.size
def down44 (N : Nat) (C : Circuit) (w : Nat) :=
  if w<N+C.size then w else w-C.size
def exposed44 (N : Nat) (C : Circuit) (g : Gate) : Gate := ⟨g.op,g.inputs.map (lift44 N C)⟩
def splitC (N : Nat) (C : Circuit) : Circuit :=
  ⟨C.gates.map (exposed44 N C),C.output+C.size⟩

@[simp] theorem split_size {N : Nat} {C : Circuit} : (splitC N C).size=C.size := by
  simp [splitC,Circuit.size]
theorem project44 {N : Nat} {C : Circuit} (w : Nat) : down44 N C (lift44 N C w)=w := by
  unfold lift44 down44
  by_cases h : w<N ∨ w∈shared44 N C
  · rw [if_pos h,if_pos]; rcases h with h|h
    · omega
    · exact Finset.mem_range.mp (Finset.mem_filter.mp h).1
  · rw [if_neg h,if_neg] <;> omega
theorem inj44 (N : Nat) (C : Circuit) : Function.Injective (lift44 N C) := by
  intro x y e; simpa only [project44] using congrArg (down44 N C) e
theorem at44 {N : Nat} {C : Circuit} {j : Nat} (h : j<C.size) :
    gateAt (splitC N C) j=exposed44 N C (gateAt C j) := by
  have a : j<C.gates.length := h
  simp [gateAt,splitC,List.getD_eq_getElem,a]
theorem shapes44 {N : Nat} {C : Circuit} (sh : shapes69 C) : shapes69 (splitC N C) := by
  intro g hg
  obtain ⟨old,mem,rfl⟩:=List.mem_map.mp hg
  simpa [exposed44] using sh old mem
theorem back44 {N : Nat} {C : Circuit} (back : ReadsBack N C) : ReadsBack (N+C.size) (splitC N C) := by
  intro j hj w hw
  have ji : j<C.size := by simpa [splitC,Circuit.size] using hj
  rw [at44 ji] at hw
  obtain ⟨x,hit,rfl⟩ := List.mem_map.mp hw
  have lt := back j ji x hit
  unfold lift44; split <;> omega
theorem op_count44 {N : Nat} {C : Circuit} (l : List Nat) (w : Nat) :
    (l.map (lift44 N C)).count (lift44 N C w)=l.count w := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases e : x=w
    · subst x; simp [List.count_cons,ih]
    · have ne : lift44 N C x≠lift44 N C w := fun h=>e (inj44 N C h)
      simp [List.count_cons,ih,ne,e]
theorem local44 {N : Nat} {C : Circuit} {T : Finset Nat} (sub : T⊆gates69 C) (w : Nat) :
    readsIn (splitC N C) T (lift44 N C w)=readsIn C T w := by
  apply Finset.sum_congr rfl
  intro j hj; rw [at44 (Finset.mem_range.mp (sub hj))]
  exact op_count44 _ _
theorem reads44 {N : Nat} {C : Circuit} (w : Nat) :
    reads69 (splitC N C) (lift44 N C w)=reads69 C w := by
  unfold reads69 gates69; rw [split_size]; exact local44 (fun _ h=>h) _
theorem absent44 {N : Nat} {C : Circuit} {w : Nat} (never : ∀x,lift44 N C x≠w) :
    reads69 (splitC N C) w=0 := by
  unfold reads69 readsIn gates69
  rw [split_size]
  apply Finset.sum_eq_zero
  intro j hj
  have ji : j<C.size := Finset.mem_range.mp hj
  rw [at44 ji]
  apply List.count_eq_zero.mpr
  intro hit
  obtain ⟨x,_,e⟩ := List.mem_map.mp hit
  exact never x e
theorem dead44 {N : Nat} {C : Circuit} {j : Nat} (hj : j∈sharedG44 N C) :
    reads69 (splitC N C) (N+C.size+j)=0 := by
  obtain ⟨bound,many⟩:=Finset.mem_filter.mp hj
  have ji : j<C.size := Finset.mem_range.mp bound
  have mem : N+j∈shared44 N C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),many⟩
  apply absent44; intro x e
  have orig := congrArg (down44 N C) e
  rw [project44,down44,if_neg (by omega)] at orig
  have eq : x=N+j := by omega
  rw [eq,lift44,if_pos (Or.inr mem)] at e; omega
theorem gate_reads44 {N : Nat} {C : Circuit} {j : Nat} (ji : j<C.size) :
    reads69 (splitC N C) (N+C.size+j)=(if j∈sharedG44 N C then 0 else reads69 C (N+j)) := by
  by_cases g : j∈sharedG44 N C
  · rw [if_pos g]; exact dead44 g
  · rw [if_neg g]
    have h : N+j∉shared44 N C := fun mem=>g (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr ji,(Finset.mem_filter.mp mem).2⟩)
    simpa [lift44,h,Nat.add_right_comm] using (reads44 (N:=N) (C:=C) (N+j))
theorem gate_one44 {N : Nat} {C : Circuit} {j : Nat} (ji : j<C.size) :
    reads69 (splitC N C) (N+C.size+j)≤1 := by
  rw [gate_reads44 ji]; split
  · omega
  · next h => by_contra! many; exact h (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ji,many⟩)

theorem raw_reads44 {N : Nat} {C : Circuit} {w : Nat} (hw : w<N+C.size) :
    reads69 (splitC N C) w=(if w<N ∨ w∈shared44 N C then reads69 C w else 0) := by
  by_cases h : w<N ∨ w∈shared44 N C
  · simpa [lift44,h] using (reads44 (N:=N) (C:=C) w)
  · rw [if_neg h]
    apply absent44; intro x e
    have p:=congrArg (down44 N C) e
    rw [project44,down44,if_pos hw] at p
    subst x; rw [lift44,if_neg h] at e
    have ge : N≤w := by omega
    omega
theorem once44 (N : Nat) (C : Circuit) : once69 (N+C.size) (splitC N C)=once69 N C := by
  ext w
  constructor
  · intro mem
    obtain ⟨lt,one⟩ := Finset.mem_filter.mp mem
    have range:=Finset.mem_range.mp lt
    rw [raw_reads44 range] at one
    by_cases low : w<N
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr low,by simpa [low] using one⟩
    · by_cases shared : w∈shared44 N C
      · have many := (Finset.mem_filter.mp shared).2
        simp [low,shared] at one; omega
      · simp [low,shared] at one
  · intro mem
    obtain ⟨lt,one⟩ := Finset.mem_filter.mp mem
    have low:=Finset.mem_range.mp lt
    have wide : w<N+C.size:=by omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr wide,by simpa [raw_reads44 wide,low] using one⟩
theorem neg44 (N : Nat) (C : Circuit) : neg69 (splitC N C)=neg69 C := by
  ext j
  simp only [neg69,gates69,split_size,Finset.mem_filter,Finset.mem_range]
  by_cases h : j<C.size
  · simp [h,at44 h,exposed44]
  · simp [h]
theorem flagged44 {N : Nat} {C : Circuit} {j : Nat} (ji : j<C.size) :
    N+C.size+j∈special (N+C.size) (splitC N C) ↔ j∈neg69 C := by
  constructor
  · intro m
    rcases Finset.mem_union.mp m with hi|hn
    · have l := gate_one44 (N:=N) ji; have b := (Finset.mem_filter.mp hi).2; omega
    · obtain ⟨k,hk,e⟩:=Finset.mem_image.mp hn
      have eq : k=j:=Nat.add_left_cancel e
      subst k; rwa [neg44] at hk
  · intro hn; apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨j,by rwa [neg44],rfl⟩
theorem ord44 {N : Nat} {C : Circuit} {j : Nat} (ji : j<C.size) :
    j∈ordinary (N+C.size) (splitC N C) ↔ j∉neg69 C := by
  change (_∈(gates69 _).filter _) ↔ _
  simp [gates69,ji,flagged44 ji]
theorem special_wire44 {N : Nat} {C : Circuit} {w : Nat} (hw : w<N+C.size) :
    lift44 N C w∈special (N+C.size) (splitC N C) → w∈shared44 N C ∨ w∈(neg69 C).image (fun k=>N+k) := by
  intro h
  rcases Finset.mem_union.mp h with many|neg
  · have b : 2≤reads69 (splitC N C) (lift44 N C w):=(Finset.mem_filter.mp many).2
    rw [reads44] at b
    exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hw,b⟩)
  · obtain ⟨j,hj,e⟩:=Finset.mem_image.mp neg
    rw [neg44] at hj
    have k:=congrArg (down44 N C) e
    change down44 N C (N+C.size+j)=down44 N C (lift44 N C w) at k
    rw [project44,down44,if_neg (by omega)] at k
    exact Or.inr (Finset.mem_image.mpr ⟨j,hj,by omega⟩)

end PEqualNP.Outside.L_meta_25644_aux

namespace PEqualNP.Outside.L_meta_25644_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped Classical
theorem entries44 {N : Nat} {C : Circuit} (back : ReadsBack N C) :
    entries69 (N+C.size) (splitC N C)≤marked44 N C+(neg69 C).card := by
  classical
  let D:=splitC N C
  let O:=ordinary (N+C.size) D
  let S:=shared44 N C
  let I:=(neg69 C).image (fun k=>N+k) \ S
  let X:=S∪I
  have each (j : Nat) (hj : j∈O) :
      (gateAt D j).inputs.countP (fun w=>decide (w∈special (N+C.size) D)) ≤
        (gateAt C j).inputs.countP (fun x=>decide (x∈X)) := by
    have ji : j<C.size := by simpa only [D,split_size] using ordinary_index69 hj
    rw [show gateAt D j=exposed44 N C (gateAt C j) from at44 ji]
    change ((gateAt C j).inputs.map (lift44 N C)).countP _≤_
    rw [List.countP_map]
    apply List.countP_mono_left
    intro x hx use
    have low:=back j ji x hx
    have mark : lift44 N C x∈special (N+C.size) D:=of_decide_eq_true use
    rcases special_wire44 (by omega : x<N+C.size) mark with s|n
    · exact decide_eq_true (Finset.mem_union_left _ s)
    · apply decide_eq_true
      by_cases hit : x∈S
      · exact Finset.mem_union_left _ hit
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨n,hit⟩)
  have subO : O⊆gates69 C := by
    intro j hj
    have lt := ordinary_index69 hj
    exact Finset.mem_range.mpr (by simpa only [D,split_size] using lt)
  have mass : (∑ w∈I,reads69 C w)≤(neg69 C).card := by
    have per (w : Nat) (mem : w∈I) : reads69 C w≤1 := by
      obtain ⟨im,out⟩:=Finset.mem_sdiff.mp mem
      obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp im
      have ki : k<C.size := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
      by_contra! many; exact out (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),many⟩)
    have total:=Finset.sum_le_sum per
    simp only [Finset.sum_const,smul_eq_mul,mul_one] at total
    exact total.trans ((Finset.card_le_card Finset.sdiff_subset).trans Finset.card_image_le)
  have dis : Disjoint S I := Finset.disjoint_left.mpr (fun _ hw hx=>(Finset.mem_sdiff.mp hx).2 hw)
  calc
    _ ≤ ∑j∈O,(gateAt C j).inputs.countP (fun x=>decide (x∈X)) := Finset.sum_le_sum each
    _ ≤ ∑j∈gates69 C,(gateAt C j).inputs.countP (fun x=>decide (x∈X)) :=
      Finset.sum_le_sum_of_subset_of_nonneg subO (fun _ _ _=>Nat.zero_le _)
    _ = ∑w∈X,reads69 C w := by simp_rw [maskedCount69];exact Finset.sum_comm
    _ ≤ _ := by rw [Finset.sum_union dis]; exact Nat.add_le_add_left mass _

noncomputable def rootsPure (N : Nat) (C : Circuit) := (roots69 N C (keep69 N C)).filter (fun z=>slots69 N C (keep69 N C) z=0)
noncomputable def rootsMixed (N : Nat) (C : Circuit) := (roots69 N C (keep69 N C)).filter (fun z=>slots69 N C (keep69 N C) z≠0)
noncomputable def correction (N : Nat) (C : Circuit) := if 0<marked44 N C+(neg69 C).card then 1 else 0
theorem mixed44 {N : Nat} {C : Circuit} (sh : shapes69 C) (back : ReadsBack N C) :
    (rootsMixed (N+C.size) (splitC N C)).card+correction N C≤2*(marked44 N C+(neg69 C).card) := by
  classical
  have cap := entries44 back
  have old:=mixed_count69 (shapes44 sh) (back44 back)
  by_cases pos : 0<entries69 (N+C.size) (splitC N C)
  · have gain := mixedStrict44 (shapes44 sh) (back44 back) pos
    unfold rootsMixed correction; split <;> omega
  · unfold rootsMixed correction; split <;> omega

end PEqualNP.Outside.L_meta_25644_aux

namespace PEqualNP.Outside.L_meta_25644_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped Classical
noncomputable def places44 (N : Nat) (C : Circuit) :=
  insert (splitC N C).output
    (((sharedG44 N C).image (fun j=>N+C.size+j)) ∪
      ((neg69 C).image (fun j=>(gateAt (splitC N C) j).inputs.headD 0)))

theorem stop44 {N : Nat} {C : Circuit} (sh : shapes69 C) (last : C.output+1=N+C.size)
    (live : ∀j<C.size,j+1<C.size → 0<reads69 C (N+j))
    {z : Nat} (bounded : z<N+C.size+(splitC N C).size)
    (realRaw : z<N+C.size → 0<reads69 (splitC N C) z)
    (stopped : ∀j∈ordinary (N+C.size) (splitC N C),z∉(gateAt (splitC N C) j).inputs) :
    z∈places44 N C := by
  classical
  let D:=splitC N C
  by_cases read : 0<reads69 D z
  · have hit : ∃j∈gates69 D,z∈(gateAt D j).inputs := by
      by_contra! no
      have zero : reads69 D z=0 := Finset.sum_eq_zero (fun j hj=>List.count_eq_zero.mpr (no j hj))
      omega
    obtain ⟨j,hj,pin⟩:=hit
    have ji : j<C.size := by simpa only [D,split_size] using Finset.mem_range.mp hj
    have neg : j∈neg69 C := by
      by_contra notNeg
      exact stopped j ((ord44 ji).mpr notNeg) pin
    have valid : j<D.gates.length := by simpa [D,splitC,Circuit.size] using ji
    have gm : gateAt D j∈D.gates := by rw [gateAt,List.getD_eq_getElem _ _ valid];exact List.getElem_mem valid
    have nn : j∈neg69 D := by simpa only [D,neg44] using neg
    have op : (gateAt D j).op=.not := (Finset.mem_filter.mp nn).2
    have len : (gateAt D j).inputs.length=1 := by
      rcases shapes44 sh _ gm with ⟨ops,_⟩|⟨_,one⟩
      · rw [op] at ops; simp at ops
      · exact one
    have head {l : List Nat} (len : l.length=1) (mem : z∈l) : l.headD 0=z := by
      cases l with
      | nil => simp at mem
      | cons a tail =>
        cases tail with
        | nil => simpa using (List.mem_singleton.mp mem).symm
        | cons b rest => simp at len
    exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,neg,head len pin⟩))
  · have lo : N+C.size≤z := by by_contra! h; exact read (realRaw h)
    let j:=z-(N+C.size)
    have ident : N+C.size+j=z := by dsimp [j]; omega
    have ji : j<C.size := by rw [split_size] at bounded; omega
    by_cases share : j∈sharedG44 N C
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j,share,ident⟩))
    · have h:=gate_reads44 (N:=N) (C:=C) ji
      rw [if_neg share,ident] at h
      have endGate : j+1=C.size := by
        by_contra ne
        have pos:=live j ji (by omega)
        change ¬0<reads69 (splitC N C) z at read; omega
      have out : z=(splitC N C).output := by change z=C.output+C.size;omega
      exact Finset.mem_insert.mpr (Or.inl out)

theorem silent44 {N : Nat} {C : Circuit} (sh : shapes69 C) (back : ReadsBack N C)
    {z : Nat} (hz : z∈rootsPure N C) :
    color69 N C z=false ∧ (∀j∈ordinary N C,z∉(gateAt C j).inputs) := by
  obtain ⟨rt,zero⟩:=Finset.mem_filter.mp hz
  have off : color69 N C z=false := by
    have slot:=fiberSlots69 back rt
    cases h:color69 N C z <;> simp_all
  obtain ⟨pool,sink,_,_⟩:=root_info69 keepSub69 back rt
  refine ⟨off,?_⟩
  intro j hj pin
  by_cases join : j∈split69 N C
  · have yes:=color_split_all sh join z pin
    rw [off] at yes;contradiction
  · exact sink (N+j) ⟨pool,j,Finset.mem_sdiff.mpr ⟨hj,join⟩,rfl,pin⟩

theorem places_card (N : Nat) (C : Circuit) : (places44 N C).card≤(sharedG44 N C).card+(neg69 C).card+1 :=
  (Finset.card_insert_le ..).trans (Nat.add_le_add_right
    ((Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)) 1)

theorem pure_subset44 {N : Nat} {C : Circuit} (sh : shapes69 C) (back : ReadsBack N C)
    (last : C.output+1=N+C.size) (live : ∀j<C.size,j+1<C.size → 0<reads69 C (N+j)) :
    rootsPure (N+C.size) (splitC N C)⊆places44 N C := by
  intro z hz
  have b:=back44 back
  have rt:=(Finset.mem_filter.mp hz).1
  have pool:=(root_info69 keepSub69 b rt).1
  apply stop44 sh last live (pool_bound69 keepSub69 pool) _ (silent44 (shapes44 sh) b hz).2
  intro raw
  rcases Finset.mem_union.mp pool with src|gate
  · have one:=(Finset.mem_filter.mp src).2;omega
  · obtain ⟨j,_,e⟩:=Finset.mem_image.mp gate
    change N+C.size+j=z at e; omega

theorem pure44 {N : Nat} {C : Circuit} (sh : shapes69 C) (back : ReadsBack N C)
    (last : C.output+1=N+C.size) (live : ∀j<C.size,j+1<C.size → 0<reads69 C (N+j)) :
    (rootsPure (N+C.size) (splitC N C)).card+correction N C≤(sharedG44 N C).card+(neg69 C).card+1 := by
  classical
  let M:=N+C.size
  let D:=splitC N C
  let R:=rootsPure M D
  let A:=(Finset.range (M+D.size)).filter (fun w=>color69 M D w=true)
  have sub : R⊆places44 N C := pure_subset44 sh back last live
  have cap:=places_card N C
  by_cases active : 0<marked44 N C+(neg69 C).card
  case neg =>
    have c:=Finset.card_le_card sub
    simpa [correction,active] using c.trans cap
  have existsMark : A.Nonempty := by
    by_cases ne : (neg69 C).Nonempty
    · obtain ⟨j,hj⟩:=ne
      have ji : j<C.size := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
      have specialJ:=(flagged44 (N:=N) ji).mpr hj
      refine ⟨M+j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_,color_special specialJ⟩⟩
      change M+j<M+(splitC N C).size;rw [split_size];omega
    · have full : (shared44 N C).Nonempty := by
        by_contra none
        have a:=Finset.not_nonempty_iff_eq_empty.mp ne
        have b:=Finset.not_nonempty_iff_eq_empty.mp none
        simp [marked44,a,b] at active
      obtain ⟨w,hw⟩:=full
      have lo : w<M := Finset.mem_range.mp (Finset.mem_filter.mp hw).1
      have many : 2≤reads69 D w := by
        change 2≤reads69 (splitC N C) w
        rw [raw_reads44 lo,if_pos (Or.inr hw)]
        exact (Finset.mem_filter.mp hw).2
      have wr : w<M+D.size := by omega
      have mark : w∈special M D := Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr wr,many⟩)
      exact ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr wr,color_special mark⟩⟩
  let z:=A.max' existsMark
  have mz : z∈A := Finset.max'_mem _ _
  obtain ⟨rz,on⟩:=Finset.mem_filter.mp mz
  have bounded : z<M+D.size:=Finset.mem_range.mp rz
  have noOrd : ∀j∈ordinary M D,z∉(gateAt D j).inputs := by
    intro j hj use
    have ji:=ordinary_index69 hj
    have lit:=(color_ordinary_iff (back44 back) hj).mpr ⟨z,use,on⟩
    have marked : M+j∈A:=Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),lit⟩
    have greatest : M+j≤z:=Finset.le_max' _ _ marked
    have prior : z<M+j:=back44 back j ji z use
    omega
  have raw (low : z<M) : 0<reads69 D z := by
    have flag : z∈special M D := by
      by_contra no
      have off:=color_raw low no
      change color69 M D z=true at on
      rw [off] at on;contradiction
    rcases Finset.mem_union.mp flag with many|gate
    · have h:=(Finset.mem_filter.mp many).2;omega
    · obtain ⟨j,_,eq⟩:=Finset.mem_image.mp gate
      change M+j=z at eq;omega
  have allocation : z∈places44 N C := stop44 sh last live bounded raw noOrd
  have separate : z∉R := by
    intro hz
    have off:=(silent44 (shapes44 sh) (back44 back) hz).1
    change color69 M D z=false at off
    change color69 M D z=true at on
    rw [off] at on;contradiction
  have enlargement:=Finset.card_le_card (Finset.insert_subset allocation sub)
  rw [Finset.card_insert_of_notMem separate] at enlargement
  simpa [correction,active] using enlargement.trans cap

end PEqualNP.Outside.L_meta_25644_aux

namespace PEqualNP.Outside.L_meta_25644_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped Classical
def tree44 (N : Nat) (C : Circuit) (S E : Finset Nat) : Prop := ∃ region : Finset Nat, ∃ root : Nat,
  let wires := S ∪ region.image (fun k=>N+k)
  let localReads := readsIn C region
  region ⊆ gates69 C ∧ root∈wires ∧ localReads root=0 ∧
  (∀b∈E,b∉wires ∧ b<root ∧ localReads b=1) ∧
  (∀j∈region, ((gateAt C j).op=.and ∨ (gateAt C j).op=.or) ∧
    (gateAt C j).inputs.length=2 ∧ ∀w∈(gateAt C j).inputs, w∈wires ∨ w∈E) ∧
  (∀w∈wires,w≠root → localReads w=1 ∧ reads69 C w=1 ∧ C.output≠w)

def up44 (N : Nat) (C : Circuit) (w : Nat) := if w<N then w else w+C.size
theorem up_order44 {N : Nat} {C : Circuit} {w v : Nat} : up44 N C w≤up44 N C v ↔ w≤v := by
  unfold up44; split <;> split <;> omega
theorem undo44 {N : Nat} {C : Circuit} (w : Nat) : down44 N C (up44 N C w)=w := by
  unfold up44 down44; split <;> split <;> omega
theorem raw_gate44 {N j : Nat} {C : Circuit} : up44 N C (N+j)=N+C.size+j := by
  unfold up44;rw [if_neg (by omega)];omega
theorem mapped44 {N : Nat} {C : Circuit} {S T : Finset Nat} (sub : S⊆Finset.range N) :
    (S∪T.image (fun k=>N+k)).image (up44 N C)=S∪T.image (fun k=>N+C.size+k) := by
  ext y
  constructor
  · intro h
    obtain ⟨w,mem,rfl⟩:=Finset.mem_image.mp h
    rcases Finset.mem_union.mp mem with r|g
    · have low:=Finset.mem_range.mp (sub r); rw [up44,if_pos low];exact Finset.mem_union_left _ r
    · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp g; rw [raw_gate44]
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj)
  · intro h;rcases Finset.mem_union.mp h with r|g
    · exact Finset.mem_image.mpr ⟨y,Finset.mem_union_left _ r,if_pos (Finset.mem_range.mp (sub r))⟩
    · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp g
      exact Finset.mem_image.mpr ⟨N+j,Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj),raw_gate44⟩
theorem find_pin44 {C : Circuit} {T : Finset Nat} {w : Nat} (pos : 0<readsIn C T w) :
    ∃ j∈T,w∈(gateAt C j).inputs := by
  by_contra! no
  have zero : readsIn C T w=0 := Finset.sum_eq_zero (fun j hj=>List.count_eq_zero.mpr (no j hj))
  omega

theorem projectTree44 {N : Nat} {C : Circuit} (back : ReadsBack N C) (size : 0<C.size)
    (last : C.output+1=N+C.size) {S E : Finset Nat} (sub : S⊆Finset.range N)
    (t : tree69 (N+C.size) (splitC N C) S E) : tree44 N C S (E.image (down44 N C)) := by
  classical
  let M:=N+C.size
  let D:=splitC N C
  obtain ⟨T,z,info⟩:=t
  dsimp only at info
  obtain ⟨ordinary,root,_,ports,gates,inside⟩:=info
  let W:=S∪T.image (fun k=>N+k)
  let V:=S∪T.image (fun k=>M+k)
  have idx : T⊆gates69 C := fun j hj => by
    have g:=ordinary_index69 (ordinary hj)
    exact Finset.mem_range.mpr (by simpa only [split_size] using g)
  have mapping : W.image (up44 N C)=V := mapped44 sub
  have phys {w : Nat} (mem : w∈W) : up44 N C w∈V := mapping ▸ Finset.mem_image_of_mem _ mem
  have pre {v : Nat} (mem : v∈V) : ∃w∈W,up44 N C w=v := Finset.mem_image.mp (mapping.symm ▸ mem)
  obtain ⟨r,hr,hrz⟩:=pre root
  have maxRoot : ∀w∈V,w≤z := by
    let v:=V.max' ⟨z,root⟩
    have mv : v∈V := Finset.max'_mem _ _
    have top (w : Nat) (hw : w∈V) : w≤v := Finset.le_max' _ _ hw
    have equals : v=z := by
      by_contra ne
      have pc : readsIn D T v=1 := (inside v mv ne).1
      obtain ⟨j,hj,use⟩:=find_pin44 (by omega : 0<readsIn D T v)
      have prior : v<M+j := back44 back j (ordinary_index69 (ordinary hj)) v use
      have limit:=top (M+j) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj))
      omega
    intro w hw; exact (top w hw).trans_eq equals
  have oldBound {j w : Nat} (hj : j∈T) (pin : w∈(gateAt C j).inputs) : w<r := by
    have above:=maxRoot (M+j) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj))
    rw [←hrz,show M+j=up44 N C (N+j) from raw_gate44.symm] at above
    exact (back j (Finset.mem_range.mp (idx hj)) w pin).trans_le (up_order44.mp above)
  have entryPin {v : Nat} (one : readsIn D T v=1) : lift44 N C (down44 N C v)=v ∧ down44 N C v<r := by
    obtain ⟨j,hj,pin⟩:=find_pin44 (by omega : 0<readsIn D T v)
    have e : gateAt D j=exposed44 N C (gateAt C j) := at44 (Finset.mem_range.mp (idx hj))
    rw [e] at pin
    obtain ⟨w,use,rfl⟩:=List.mem_map.mp pin
    exact ⟨by rw [project44],by rw [project44];exact oldBound hj use⟩
  have coincide {w : Nat} (hw : w∈W) (diff : w≠r) : lift44 N C w=up44 N C w := by
    have ne : up44 N C w≠z := by intro eq;exact diff (by simpa only [undo44] using congrArg (down44 N C) (eq.trans hrz.symm))
    have on:=(inside _ (phys hw) ne).1
    have hit:=(entryPin on).1
    rwa [undo44] at hit
  refine ⟨T,r,idx,hr,?_,?_,?_,?_⟩
  · exact Finset.sum_eq_zero (fun j hj=>List.count_eq_zero.mpr (fun pin=>(Nat.lt_irrefl r) (oldBound hj pin)))
  · intro b hb;obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hb
    obtain ⟨out,_,one⟩:=ports v hv
    obtain ⟨eq,lt⟩:=entryPin one
    refine ⟨?_,lt,?_⟩
    · intro hw
      have u:=coincide hw (Nat.ne_of_lt lt)
      exact out ((eq.symm.trans u).symm ▸ phys hw)
    · rw [←local44 (N:=N) idx,eq];exact one
  · intro j hj
    obtain ⟨op,len,pins⟩:=gates j hj
    have e : gateAt (splitC N C) j=exposed44 N C (gateAt C j) := at44 (Finset.mem_range.mp (idx hj))
    rw [e] at op len pins
    refine ⟨op,by simpa [exposed44] using len,?_⟩
    intro w use
    have choices:=pins (lift44 N C w) (List.mem_map.mpr ⟨w,use,rfl⟩)
    rcases choices with isWire|port
    · obtain ⟨a,ha,eq⟩:=pre isWire
      have same:=congrArg (down44 N C) eq
      rw [undo44,project44] at same
      exact Or.inl (same ▸ ha)
    · exact Or.inr (Finset.mem_image.mpr ⟨_,port,project44 w⟩)
  · intro w hw diff
    have eq:=coincide hw diff
    have ne : up44 N C w≠z := fun h=>diff (by simpa only [undo44] using congrArg (down44 N C) (h.trans hrz.symm))
    obtain ⟨one,all,other⟩:=inside _ (phys hw) ne
    rw [←eq] at one all
    refine ⟨(local44 idx w).symm.trans one,(reads44 w).symm.trans all,?_⟩
    intro o;apply other
    change C.output+C.size=up44 N C w
    rw [←o,up44,if_neg (by omega)]

end PEqualNP.Outside.L_meta_25644_aux
open PEqualNP.Outside.L_meta_25644_aux in
theorem PEqualNP.Outside.L_meta_25644 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
  let gates := Finset.range C.size
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let reads := PEqualNP.MetaComplexity.NestedCover.readsIn C gates
  let neg := @Finset.filter ℕ (fun k => (gate k).op = PEqualNP.CircuitLowerBounds.GateOp.not)
    (fun k => Classical.propDecidable ((gate k).op = PEqualNP.CircuitLowerBounds.GateOp.not)) gates
  let shared := (Finset.range (n + C.size)).filter (fun w => 2 ≤ reads w)
  let sharedGates := gates.filter (fun k => 2 ≤ reads (n + k))
  let markedReads := ∑ w ∈ shared, reads w
  let once := (Finset.range n).filter (fun w => reads w = 1)
  let tree := fun (S E : Finset ℕ) => ∃ (region : Finset ℕ) (root : ℕ),
    let wires := S ∪ region.image (fun k => n + k)
    let localReads := PEqualNP.MetaComplexity.NestedCover.readsIn C region
    region ⊆ gates ∧ root ∈ wires ∧ localReads root = 0 ∧
    (∀ b ∈ E, b ∉ wires ∧ b < root ∧ localReads b = 1) ∧
    (∀ j ∈ region,
      ((gate j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
       (gate j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      (gate j).inputs.length = 2 ∧ ∀ w ∈ (gate j).inputs, w ∈ wires ∨ w ∈ E) ∧
    (∀ w ∈ wires, w ≠ root → localReads w = 1 ∧ reads w = 1 ∧ C.output ≠ w)
  (∀ g ∈ C.gates,
    ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack n C →
  0 < C.size → C.output + 1 = n + C.size →
  (∀ j < C.size, j + 1 < C.size → 0 < reads (n + j)) →
  ∃ (pure chains : List (Finset ℕ)) (markedComponents : ℕ),
    pure.length + markedComponents ≤ sharedGates.card + neg.card + 1 ∧
    chains.length + markedComponents ≤ 2 * (markedReads + neg.card) ∧
    (0 < markedReads + neg.card → 0 < markedComponents) ∧
    (pure ++ chains).Pairwise (fun A B => Disjoint A B) ∧
    (pure ++ chains).toFinset.biUnion (fun S => S) = once ∧
    (∀ S ∈ pure, S.Nonempty ∧ tree S ∅) ∧
    (∀ S ∈ chains, S.Nonempty ∧ ∃ b : ℕ, tree S {b}) := by
  intro N C
  dsimp only
  intro sh back size last live
  classical
  let M:=N+C.size
  let D:=splitC N C
  have shape : shapes69 D:=shapes44 sh
  have earlier : PEqualNP.MetaComplexity.NestedCover.ReadsBack M D:=back44 back
  have lastD : D.output+1=M+D.size := by
    change C.output+C.size+1=N+C.size+(splitC N C).size
    rw [split_size];omega

  let P:=keep69 M D
  let roots:=roots69 M D P
  let Q:=roots.filter (fun z=>slots69 M D P z=0)
  let mixedRoots:=roots.filter (fun z=>slots69 M D P z≠0)
  let leaf:=src69 M D P
  let qr:=Q.toList
  let mr:=mixedRoots.toList
  have qmem (z:Nat) : z∈qr ↔ z∈roots ∧ slots69 M D P z=0 := by simp [qr,Q]
  have mmem (z:Nat) : z∈mr ↔ z∈roots ∧ slots69 M D P z≠0 := by simp [mr,mixedRoots]
  have covered (z:Nat) : z∈qr++mr ↔ z∈roots := by
    rw [List.mem_append,qmem,mmem];tauto
  have nd : (qr++mr).Nodup := by
    refine List.nodup_append.mpr ⟨Q.nodup_toList,mixedRoots.nodup_toList,?_⟩
    intro x hx y hy e;subst y;exact (mmem x|>.mp hy).2 ((qmem x|>.mp hx).2)
  have fiber {w z:Nat}: w∈leaf z ↔ w∈once69 M D ∧ owner69 M D P w=z := Finset.mem_filter
  have facts {z:Nat} (hz:z∈roots) : (leaf z).Nonempty ∧
      tree69 M D (leaf z) (outside69 M D P z) := by
    have count:=fiberSlots69 earlier hz
    have le : slots69 M D P z≤1 := by rw [count];split <;> decide
    exact ⟨(root_info69 keepSub69 earlier hz).2.2.2,subtree69 keepSub69 earlier shape lastD hz le⟩
  have raw (z : Nat) : leaf z⊆Finset.range N := by
    intro w hw
    have once : w∈once69 M D := (fiber.mp hw).1
    rw [show once69 M D=once69 N C from once44 N C] at once
    exact (Finset.mem_filter.mp once).1
  refine ⟨qr.map leaf,mr.map leaf,correction N C,?_,?_,?_,?_,?_,?_,?_⟩
  · change (Q.toList.map leaf).length+correction N C≤(sharedG44 N C).card+(neg69 C).card+1
    rw [List.length_map,Finset.length_toList]; exact pure44 sh back last live
  · change (mixedRoots.toList.map leaf).length+correction N C≤2*(marked44 N C+(neg69 C).card)
    rw [List.length_map,Finset.length_toList]; exact mixed44 sh back
  · intro pos
    change 0<marked44 N C+(neg69 C).card at pos
    simp [correction,pos]
  · rw [←List.map_append,List.pairwise_map]
    apply nd.imp
    intro a b diff
    apply Finset.disjoint_left.mpr
    intro w ha hb;exact diff ((fiber.mp ha).2.symm.trans (fiber.mp hb).2)
  · change ((qr.map leaf)++(mr.map leaf)).toFinset.biUnion id=once69 N C
    rw [←once44 N C,←List.map_append]
    ext w
    simp only [Finset.mem_biUnion,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨_,⟨z,_,rfl⟩,hit⟩;exact (fiber.mp hit).1
    · intro raw
      let z:=owner69 M D P w
      have root:z∈roots:=Finset.mem_image_of_mem _ raw
      exact ⟨leaf z,⟨z,(covered z).mpr root,rfl⟩,fiber.mpr ⟨raw,rfl⟩⟩
  · intro S hs
    obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hs
    obtain ⟨rt,zero⟩:=(qmem z).mp hz
    obtain ⟨ne,tree⟩:=facts rt
    rw [outside_empty69.mpr zero] at tree
    refine ⟨ne,?_⟩
    change tree44 N C (leaf z) ∅
    simpa only [Finset.image_empty] using projectTree44 back size last (raw z) tree
  · intro S hs
    obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hs
    obtain ⟨rt,nz⟩:=(mmem z).mp hz
    obtain ⟨ne,tree⟩:=facts rt
    have card : (outside69 M D P z).card=1 := by
      have cap:=outside_card69 (N:=M) (C:=D) (P:=P) (z:=z)
      have count:=fiberSlots69 earlier rt
      have nonempty : (outside69 M D P z).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr (fun h=>nz (outside_empty69.mp h))
      have pos:=Finset.card_pos.mpr nonempty
      change slots69 M D P z=_ at count
      split at count <;> omega
    obtain ⟨b,eq⟩:=Finset.card_eq_one.mp card
    rw [eq] at tree
    refine ⟨ne,down44 N C b,?_⟩
    change tree44 N C (leaf z) {down44 N C b}
    simpa only [Finset.image_singleton] using projectTree44 back size last (raw z) tree
