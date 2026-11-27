import Mathlib
import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_29722_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem run_cat (gs hs : List Gate) (w : List Bool) :
    run (gs++hs) w=run hs (run gs w) := by simp [run,List.foldl_append]

theorem run_pref (gs : List Gate) (w : List Bool) :
    ∃ t,run gs w=w++t ∧ t.length=gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[],by simp [run],rfl⟩
  | cons g gs ih =>
    let b:=g.op.eval (g.inputs.map fun i=>w.getD i false)
    obtain ⟨t,ht,hlen⟩:=ih (w++[b])
    refine ⟨b::t,?_,by simp [hlen]⟩
    change run gs (w++[b])=_
    rw [ht];simp

theorem run_len (gs : List Gate) (w : List Bool) : (run gs w).length=w.length+gs.length := by
  obtain ⟨t,ht,hl⟩:=run_pref gs w
  simp [ht,hl]

theorem run_old (gs : List Gate) (w : List Bool) (i : Nat) (h : i<w.length) :
    (run gs w).getD i false=w.getD i false := by
  obtain ⟨t,ht,_⟩:=run_pref gs w
  rw [ht,List.getD_append _ _ _ _ h]

def Back (p : Nat) (gs : List Gate) := ∀j (hj : j<gs.length), ∀i∈gs[j].inputs,i<p+j

theorem back_cat {p : Nat} {gs hs : List Gate} (a : Back p gs) (b : Back (p+gs.length) hs) :
    Back p (gs++hs) := by
  intro j hj i hi
  by_cases h : j<gs.length
  · rw [List.getElem_append_left h] at hi
    exact a j h i hi
  · rw [List.getElem_append_right (by omega)] at hi
    have hh : j-gs.length<hs.length := by simp at hj;omega
    have := b _ hh i hi
    omega

def monoGate (g : Gate) := (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length=2
inductive Expr (k : Nat) where
  | pin (i : Fin k)
  | node (conj : Bool) (l r : Expr k)

def nodes {k} : Expr k → Nat
  | .pin _ => 0
  | .node _ l r => nodes l+nodes r+1

def applyBit (conj a b : Bool) := if conj then a && b else a || b

def meaning {k} (val : Fin k → Bool) : Expr k → Bool
  | .pin i => val i
  | .node c l r => applyBit c (meaning val l) (meaning val r)

theorem realize {k} (t : Expr k) (p : Nat) (hk : k≤p) :
    ∃ gs : List Gate, ∃ o : Nat, gs.length=nodes t ∧ o<p+gs.length ∧ Back p gs ∧
      (∀ g∈gs,monoGate g) ∧ ∀ W : List Bool,W.length=p →
      (run gs W).getD o false=meaning (fun i : Fin k=>W.getD i.val false) t := by
  induction t generalizing p with
  | pin i => exact ⟨[],i.val,rfl,by simp;omega,by simp [Back],by simp,by intros;rfl⟩
  | node c l r ihl ihr =>
    obtain ⟨ls,u,hl,hu,bl,ml,vl⟩:=ihl p hk
    obtain ⟨rs,v,hr,hv,br,mr,vr⟩:=ihr (p+ls.length) (by omega)
    let g : Gate:=⟨if c then .and else .or,[u,v]⟩
    let o:=p+(ls++rs).length
    have mg : monoGate g := by cases c <;> simp [g,monoGate]
    have bs : Back (p+(ls++rs).length) [g] := by
      intro j hj i hi
      have z : j=0 := by simp at hj;omega
      subst j
      simp [g] at hi
      rcases hi with rfl|rfl <;> simp <;> omega
    refine ⟨(ls++rs)++[g],o,by simp [hl,hr,nodes,Nat.add_assoc],by simp [o],back_cat (back_cat bl br) bs,?_,?_⟩
    · intro gate mem
      rcases List.mem_append.mp mem with m | m
      · rcases List.mem_append.mp m with m|m
        · exact ml gate m
        · exact mr gate m
      · have eq : gate=g := List.mem_singleton.mp m
        simpa [eq] using mg
    · intro W len
      let L:=run ls W
      let R:=run rs L
      have lenL : L.length=p+ls.length := by simp [L,run_len,len]
      have lenR : R.length=o := by simp [R,L,run_len,len,o,Nat.add_assoc]
      have va : R.getD u false=meaning (fun i : Fin k=>W.getD i.val false) l := by
        rw [show R=run rs L from rfl,run_old rs L _ (by omega)]
        exact vl W len
      have vb : R.getD v false=meaning (fun i : Fin k=>W.getD i.val false) r := by
        have same : (fun i : Fin k=>L.getD i.val false)=(fun i : Fin k=>W.getD i.val false) := by
          funext i
          exact run_old ls W i.val (by omega)
        simpa only [←same] using vr L lenL
      rw [run_cat,run_cat]
      change (R++[g.op.eval (g.inputs.map fun i=>R.getD i false)]).getD o false=_
      rw [←lenR]
      simp only [List.getD_eq_getElem?_getD] at va vb
      cases c <;> simp [g,GateOp.eval,meaning,applyBit,va,vb]

end PEqualNP.Outside.L_meta_29722_aux


namespace PEqualNP.Outside.L_meta_29722_aux
open scoped Classical

def rest {n : Nat} (x : Fin 4 ↪ Fin n) (i : Fin n) := i≠x 0 ∧ i≠x 1 ∧ i≠x 2
def outer {n : Nat} (x : Fin 4 ↪ Fin n) : Finset (Fin n) := (Finset.univ.map x)ᶜ
theorem outer_spec {n} (x : Fin 4 ↪ Fin n) (i : Fin n) :
    i∈outer x ↔ rest x i ∧ i≠x 3 := by
  classical
  simp only [outer,Finset.mem_compl,Finset.mem_map,Finset.mem_univ,true_and]
  constructor
  · intro absent
    exact ⟨⟨fun e=>absent ⟨0,e.symm⟩,fun e=>absent ⟨1,e.symm⟩,fun e=>absent ⟨2,e.symm⟩⟩,fun e=>absent ⟨3,e.symm⟩⟩
  · rintro ⟨⟨h0,h1,h2⟩,h3⟩ ⟨j,eq⟩
    fin_cases j <;> simp_all

theorem outer_card {n} (x : Fin 4 ↪ Fin n) : (outer x).card=n-4 := by simp [outer,Finset.card_compl]

theorem rest_last {n} (x : Fin 4 ↪ Fin n) : rest x (x 3) := by
  refine ⟨?_,?_,?_⟩ <;> intro e <;> have h:=x.injective e <;> contradiction

def extra {n m} (A : Fin n → Fin m → Bool) (x : Fin 4 ↪ Fin n) (y : Fin 4 ↪ Fin m) :=
  (outer x).filter (fun i => A i (y 3)=true)

def edges {n m} (A : Fin n → Fin m → Bool) (x : Fin 4 ↪ Fin n) (y : Fin 4 ↪ Fin m) :=
  ((outer x) ×ˢ (outer y)).filter (fun e=>A e.1 e.2=true)

theorem mem_edges {n m} {A : Fin n → Fin m → Bool} {x : Fin 4 ↪ Fin n} {y : Fin 4 ↪ Fin m}
    {e : Fin n × Fin m} :
    e∈edges A x y ↔ e.1∈outer x ∧ e.2∈outer y ∧ A e.1 e.2=true := by
  simp only [edges,Finset.mem_filter,Finset.mem_product,and_assoc]

theorem half_count {n m} (A : Fin n → Fin m → Bool) (x : Fin 4 ↪ Fin n) (y : Fin 4 ↪ Fin m)
    (unique : ∀ i j l,rest x i → rest y j → rest y l → A i j=true → A i l=true → j=l)
    (cover : ∀ i,rest x i → i≠x 3 → ∃ j,rest y j ∧ A i j=true) :
    (edges A x y).card+(extra A x y).card=(outer x).card := by
  classical
  let S:=edges A x y
  let P:=S.image Prod.fst
  let T:=extra A x y
  have hp : P.card=S.card := by
    apply Finset.card_image_of_injOn
    intro e he f hf same
    have a:=mem_edges.mp (show e∈edges A x y from he)
    have b:=mem_edges.mp (show f∈edges A x y from hf)
    change e.1=f.1 at same
    refine Prod.ext same ?_
    exact unique e.1 e.2 f.2 ((outer_spec _ _).mp a.1).1 ((outer_spec _ _).mp a.2.1).1
      ((outer_spec _ _).mp b.2.1).1 a.2.2 (same ▸ b.2.2)
  have dis : Disjoint P T := by
    apply Finset.disjoint_left.mpr
    intro i hi ti
    obtain ⟨e,he,eq⟩:=Finset.mem_image.mp hi
    subst i
    have a:=mem_edges.mp (show e∈edges A x y from he)
    have b:=Finset.mem_filter.mp ti
    exact ((outer_spec _ _).mp a.2.1).2 (unique _ _ _ ((outer_spec _ _).mp a.1).1
      ((outer_spec _ _).mp a.2.1).1 (rest_last _) a.2.2 b.2)
  have all : P∪T=outer x := by
    ext i
    constructor
    · intro h
      rcases Finset.mem_union.mp h with h|h
      · obtain ⟨e,he,eq⟩:=Finset.mem_image.mp h
        exact eq ▸ (mem_edges.mp (show e∈edges A x y from he)).1
      · exact (Finset.mem_filter.mp h).1
    · intro hi
      obtain ⟨h1,h2⟩:=(outer_spec _ _).mp hi
      obtain ⟨j,hj,hbit⟩:=cover _ h1 h2
      by_cases special : j=y 3
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi,special ▸ hbit⟩)
      · apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨(i,j),mem_edges.mpr ⟨hi,(outer_spec _ _).mpr ⟨hj,special⟩,hbit⟩,rfl⟩
  have g:=Finset.card_union_of_disjoint dis
  rw [all,hp] at g
  exact g.symm

theorem flip_count {n m} (A : Fin n → Fin m → Bool) (x : Fin 4 ↪ Fin n) (y : Fin 4 ↪ Fin m) :
    (edges (fun j i=>A i j) y x).card=(edges A x y).card := by
  classical
  apply Finset.card_bij (fun p _ => p.swap)
  · intro p hp
    obtain ⟨a,b,c⟩:=mem_edges.mp hp
    exact mem_edges.mpr ⟨b,a,c⟩
  · intro p hp q hq eq
    exact Prod.swap_injective eq
  · intro p hp
    obtain ⟨a,b,c⟩:=mem_edges.mp hp
    exact ⟨p.swap,mem_edges.mpr ⟨b,a,c⟩,rfl⟩

end PEqualNP.Outside.L_meta_29722_aux


namespace PEqualNP.Outside.L_meta_29722_aux

def profile {n m} (A : Fin n → Fin m → Bool) (x : Fin 4 ↪ Fin n) (y : Fin 4 ↪ Fin m)
    (i : Fin n) (j : Fin m) : Prop :=
  ((i=x 2 ∨ j=y 2) ∧ ¬(i=x 1 ∨ j=y 1)) ∨
  ((i=x 3 ∨ j=y 3) ∧ (i=x 1 ∨ j=y 1 ∨ i∈extra A x y ∨ j∈extra (fun c r=>A r c) y x)) ∨
  (i,j)∈edges A x y

theorem classes {n} (x : Fin 4 ↪ Fin n) (i : Fin n) :
    i=x 0 ∨ i=x 1 ∨ i=x 2 ∨ i=x 3 ∨ rest x i ∧ i≠x 3 := by
  unfold rest
  tauto

theorem table {n m} (A : Fin n → Fin m → Bool) (x : Fin 4 ↪ Fin n) (y : Fin 4 ↪ Fin m)
    (rows : ∀j,A (x 0) j=decide (j=y 2) ∧ A (x 1) j=decide (j=y 3) ∧ A (x 2) j=decide (j≠y 1))
    (cols : ∀i,A i (y 0)=decide (i=x 2) ∧ A i (y 1)=decide (i=x 3) ∧ A i (y 2)=decide (i≠x 1))
    (corner : A (x 3) (y 3)=false) (i : Fin n) (j : Fin m) :
    profile A x y i j ↔ A i j=true := by
  classical
  have row0:=fun j=>(rows j).1
  have row1:=fun j=>(rows j).2.1
  have row2:=fun j=>(rows j).2.2
  have col0:=fun i=>(cols i).1
  have col1:=fun i=>(cols i).2.1
  have col2:=fun i=>(cols i).2.2
  rcases classes x i with rfl|rfl|rfl|rfl|⟨⟨i0,i1,i2⟩,i3⟩ <;>
    rcases classes y j with rfl|rfl|rfl|rfl|⟨⟨j0,j1,j2⟩,j3⟩ <;>
    simp_all [profile,extra,mem_edges,outer_spec,rest,x.injective.eq_iff,y.injective.eq_iff]

end PEqualNP.Outside.L_meta_29722_aux


namespace PEqualNP.Outside.L_meta_29722_aux

def pushOr {k} {α : Type} (f : α → Expr k) (l : List α) (base : Expr k) : Expr k :=
  l.foldl (fun acc a=>Expr.node false acc (f a)) base

theorem push_count {k} {α : Type} (f : α → Expr k) (l : List α) (base : Expr k)
    (d : Nat) (constant : ∀ a,nodes (f a)=d) :
    nodes (pushOr f l base)=nodes base+l.length*(d+1) := by
  induction l generalizing base with
  | nil => simp [pushOr]
  | cons a l ih =>
    change nodes (pushOr f l (.node false base (f a)))=_
    rw [ih]
    simp [nodes,constant,Nat.succ_mul]
    omega

theorem push_true {k} {α : Type} (v : Fin k → Bool) (f : α → Expr k) (l : List α) (base : Expr k) :
    meaning v (pushOr f l base)=true ↔ meaning v base=true ∨ ∃ a∈l,meaning v (f a)=true := by
  induction l generalizing base with
  | nil => simp [pushOr]
  | cons a l ih =>
    change meaning v (pushOr f l (.node false base (f a)))=true ↔ _
    rw [ih]
    simp [meaning,applyBit,or_assoc]

def rowPin {n} (m : Nat) (r : Fin n) : Fin (n+m+2) := ⟨r.val,by omega⟩
def colPin (n : Nat) {m} (c : Fin m) : Fin (n+m+2) := ⟨n+c.val,by omega⟩
def bankPin (n m : Nat) : Fin (n+m+2) := ⟨n+m,by omega⟩
def invPin (n m : Nat) : Fin (n+m+2) := ⟨n+m+1,by omega⟩

noncomputable def form {n m} (A : Fin n → Fin m → Bool) (x : Fin 4 ↪ Fin n) (y : Fin 4 ↪ Fin m) :
    Expr (n+m+2) :=
  let r := fun i => Expr.pin (rowPin m i)
  let c := fun j => Expr.pin (colPin n j)
  let h := pushOr c (extra (fun j i=>A i j) y x).toList
    (pushOr r (extra A x y).toList (.pin (bankPin n m)))
  let a := Expr.node true (.node false (r (x 2)) (c (y 2))) (.pin (invPin n m))
  let b := Expr.node true (.node false (r (x 3)) (c (y 3))) h
  pushOr (fun e : Fin n × Fin m => Expr.node true (r e.1) (c e.2)) (edges A x y).toList (.node false a b)

theorem form_count {n m} (A : Fin n → Fin m → Bool) (x : Fin 4 ↪ Fin n) (y : Fin 4 ↪ Fin m) :
    nodes (form A x y)=5+(extra A x y).card+(extra (fun j i=>A i j) y x).card+2*(edges A x y).card := by
  unfold form
  rw [push_count _ _ _ 1 (by intro;rfl)]
  simp only [nodes]
  rw [push_count _ _ _ 0 (by intro;rfl),push_count _ _ _ 0 (by intro;rfl)]
  simp [nodes,Nat.mul_comm]
  omega

theorem form_true {n m} (A : Fin n → Fin m → Bool) (x : Fin 4 ↪ Fin n) (y : Fin 4 ↪ Fin m)
    (i : Fin n) (j : Fin m) (v : Fin (n+m+2) → Bool)
    (vr : ∀r,v (rowPin m r)=true ↔ i=r) (vc : ∀c,v (colPin n c)=true ↔ j=c)
    (vh : v (bankPin n m)=true ↔ i=x 1 ∨ j=y 1)
    (vi : v (invPin n m)=true ↔ ¬(i=x 1 ∨ j=y 1)) :
    meaning v (form A x y)=true ↔ profile A x y i j := by
  classical
  have hit {α : Type} [DecidableEq α] (s : Finset α) (u : α) :
      (∃ p∈s,u=p) ↔ u∈s := by simp
  have pairHit (s : Finset (Fin n × Fin m)) :
      (∃ p∈s,i=p.1 ∧ j=p.2) ↔ (i,j)∈s := by
    constructor
    · rintro ⟨⟨a,b⟩,h,rfl,rfl⟩
      exact h
    · intro h
      exact ⟨(i,j),h,rfl,rfl⟩
  unfold form profile
  simp only [push_true,meaning,applyBit,Bool.and_eq_true,Bool.or_eq_true,
    Bool.false_eq_true,ite_true,ite_false,Finset.mem_toList,vr,vc,vh,vi,hit,pairHit,or_assoc]

end PEqualNP.Outside.L_meta_29722_aux


namespace PEqualNP.Outside.L_meta_29722_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem hot_len {n m} (i : Fin n) (j : Fin m) : (oneEach i j).length=n+m := by simp [oneEach]

theorem hot_row {n m} (i r : Fin n) (j : Fin m) : (oneEach i j).getD r.val false=decide (i=r) := by
  unfold oneEach
  rw [List.getD_eq_getElem?_getD,List.getElem?_append_left (by simp)]
  simp [List.getElem?_ofFn,eq_comm]

theorem hot_col {n m} (i : Fin n) (j c : Fin m) : (oneEach i j).getD (n+c.val) false=decide (j=c) := by
  unfold oneEach
  rw [List.getD_eq_getElem?_getD,List.getElem?_append_right (by simp)]
  simp [List.getElem?_ofFn,eq_comm]

def first {n m} (r : Fin n) (c : Fin m) : List Gate :=
  [⟨.or,[r.val,n+c.val]⟩,⟨.not,[n+m]⟩]

theorem first_back {n m} (r : Fin n) (c : Fin m) : Back (n+m) (first r c) := by
  intro k hk i hi
  have h : k<2 := by simpa [first] using hk
  interval_cases k <;> simp [first] at hi <;> omega

theorem first_vals {n m} (i r : Fin n) (j c : Fin m) :
    run (first r c) (oneEach i j)=oneEach i j++[decide (i=r ∨ j=c),!decide (i=r ∨ j=c)] := by
  let W:=oneEach i j
  let h:=decide (i=r ∨ j=c)
  have bh : (W.getD r.val false || W.getD (n+c.val) false)=h := by
    change ((oneEach i j).getD _ _ || (oneEach i j).getD _ _) = _
    rw [hot_row,hot_col]
    simp [h]
  have get : (W++[h]).getD (n+m) false=h := by rw [←hot_len i j];simp [W]
  change ((W++[GateOp.or.eval ([r.val,n+c.val].map fun a=>W.getD a false)])++
    [GateOp.not.eval ([n+m].map fun a=>(W++[GateOp.or.eval ([r.val,n+c.val].map fun b=>W.getD b false)]).getD a false)])=_
  simp only [List.map_cons,List.map_nil,GateOp.eval,List.any_cons,List.any_nil,id_eq,Bool.or_false,
    List.headD_cons,bh,get]
  simp [W,h]

theorem physical {n m} (A : Fin n → Fin m → Bool) (x : Fin 4 ↪ Fin n) (y : Fin 4 ↪ Fin m)
    (sem : ∀ i j, profile A x y i j ↔ A i j=true) (price : 2+nodes (form A x y)=n+m-1) :
    ∃ C : Circuit,FanInTwo C ∧ NestedCover.ReadsBack (n+m) C ∧ Represents A C ∧
      C.size=n+m-1 ∧ ∃! j : Fin C.gates.length,(C.gates.get j).op=GateOp.not := by
  classical
  let t:=form A x y
  let gs:=first (x 1) (y 1)
  have len : gs.length=2 := rfl
  obtain ⟨hs,o,size,bound,back,mono,correct⟩:=realize t (n+m+2) (by omega)
  let C : Circuit:=⟨gs++hs,o⟩
  have valid : Back (n+m) C.gates:=back_cat (first_back _ _) (by simpa only [len] using back)
  refine ⟨C,?_,?_,?_,?_,?_⟩
  · intro g mem
    rcases List.mem_append.mp mem with he|he
    · simp [gs,first] at he
      rcases he with rfl|rfl <;> simp
    · obtain ⟨h,length⟩:=mono g he
      rcases h with e|e <;> simp [e,length]
  · intro k hk a ha
    apply valid k hk a
    simpa only [NestedCover.gateAt,List.getD_eq_getElem _ _ hk] using ha
  · intro i j
    let W:=oneEach i j
    let S:=run gs W
    have lW : W.length=n+m:=hot_len _ _
    have lS : S.length=n+m+2:=by simp [S,run_len,lW,len]
    let f:=fun k : Fin (n+m+2)=>S.getD k.val false
    have vr (r : Fin n) : f (rowPin m r)=true ↔ i=r := by
      change (run gs W).getD r.val false=true ↔ _
      rw [run_old _ _ _ (by omega),hot_row]
      simp
    have vc (c : Fin m) : f (colPin n c)=true ↔ j=c := by
      change (run gs W).getD (n+c.val) false=true ↔ _
      rw [run_old _ _ _ (by omega),hot_col]
      simp
    have out : S=W++[decide (i=x 1 ∨ j=y 1),!decide (i=x 1 ∨ j=y 1)] := first_vals _ _ _ _
    have vh : f (bankPin n m)=true ↔ i=x 1 ∨ j=y 1 := by
      change S.getD (n+m) false=true ↔ _
      rw [out,←lW]
      simp [List.getD_eq_getElem?_getD]
    have vi : f (invPin n m)=true ↔ ¬(i=x 1 ∨ j=y 1) := by
      change S.getD (n+m+1) false=true ↔ _
      rw [out,←lW]
      simp [List.getD_eq_getElem?_getD]
    change (run (gs++hs) W).getD o false=_
    rw [run_cat,correct S lS]
    have hh:=(form_true A x y i j f vr vc vh vi).trans (sem i j)
    change meaning f (form A x y)=_
    cases ha : A i j
    · have no : meaning f (form A x y)≠true:=by simpa [ha] using hh.not.mpr (by simp [ha])
      cases hv : meaning f (form A x y) <;> simp_all
    · exact hh.mpr ha
  · change (gs++hs).length=_
    rw [List.length_append,len,size]
    exact price
  · have low : 1<C.gates.length := by change 1<(gs++hs).length;simp [len];omega
    refine ⟨⟨1,low⟩,by rfl,?_⟩
    rintro ⟨k,hk⟩ val
    apply Fin.ext
    change k=1
    by_cases small : k<2
    · interval_cases k
      · contradiction
      · rfl
    · have late : gs.length≤k:=by omega
      change (gs++hs)[k].op=GateOp.not at val
      rw [List.getElem_append_right late] at val
      have hk' : k-gs.length<hs.length:=by change k<(gs++hs).length at hk;simp at hk;omega
      have ok:=mono hs[k-gs.length] (List.getElem_mem hk')
      rcases ok.1 with a|a <;> rw [a] at val <;> contradiction

end PEqualNP.Outside.L_meta_29722_aux


open PEqualNP.Outside.L_meta_29722_aux in
theorem PEqualNP.Outside.L_meta_29722 : ∀ (n m : Nat) (A : Fin n → Fin m → Bool) (x : Fin 4 ↪ Fin n) (y : Fin 4 ↪ Fin m),
  (
  let R := fun i : Fin n => i ≠ x 0 ∧ i ≠ x 1 ∧ i ≠ x 2
  let T := fun j : Fin m => j ≠ y 0 ∧ j ≠ y 1 ∧ j ≠ y 2
  (∀ j, A (x 0) j = decide (j = y 2) ∧ A (x 1) j = decide (j = y 3) ∧
    A (x 2) j = decide (j ≠ y 1)) ∧
  (∀ i, A i (y 0) = decide (i = x 2) ∧ A i (y 1) = decide (i = x 3) ∧
    A i (y 2) = decide (i ≠ x 1)) ∧ A (x 3) (y 3) = false ∧
  (∀ i j l, R i → T j → T l → A i j = true → A i l = true → j = l) ∧
  (∀ j i k, T j → R i → R k → A i j = true → A k j = true → i = k) ∧
  (∀ i, R i → i ≠ x 3 → ∃ j, T j ∧ A i j = true) ∧
  (∀ j, T j → j ≠ y 3 → ∃ i, R i ∧ A i j = true)) →
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C ∧ PEqualNP.Represents.Represents A C ∧
    C.size = n+m-1 ∧ ∃! j : Fin C.gates.length, (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not := by
  classical
  intro n m A x y hypotheses
  dsimp only at hypotheses
  obtain ⟨rows,cols,corner,rowUnique,colUnique,rowCover,colCover⟩:=hypotheses
  apply physical A x y (table A x y rows cols corner)
  have h1:=half_count A x y rowUnique rowCover
  have h2:=half_count (fun j i=>A i j) y x colUnique colCover
  rw [flip_count] at h2
  rw [outer_card] at h1 h2
  have xn : 4 ≤ n := by simpa using Fintype.card_le_of_injective x x.injective
  have ym : 4 ≤ m := by simpa using Fintype.card_le_of_injective y y.injective
  rw [form_count]
  omega
