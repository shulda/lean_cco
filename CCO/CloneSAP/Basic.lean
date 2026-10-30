import CCO.PairHomogeneity
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Fintype

/-! The actual infinite pure clone source. Logical equality remains separate
from both the old diversity atoms and the new same-owner diversity atom. -/
universe u v w
namespace CCO.CloneSAP
variable {ι : Type u} {X : ι → Type v}

abbrev Carrier (X : ι → Type v) (i : ι) := X i × ℕ
abbrev Atom (S : AtomicSource ι X) (i j : ι) := S.Atom i j ⊕ PLift (i = j)

/-- Reassociation retains literal original sort and owner. -/
def pointEquiv : Sigma (Carrier X) ≃ (Sigma X) × ℕ where
  toFun p := (⟨p.1,p.2.1⟩,p.2.2)
  invFun p := ⟨p.1.1,(p.1.2,p.2)⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p with | mk p n => cases p; rfl

noncomputable def colour (S : AtomicSource ι X) {i j : ι}
    (x : Carrier X i) (y : Carrier X j) : Option (Atom S i j) := by
  classical
  exact if h : S.colour x.1 y.1 = none then
    if x.2 = y.2 then none else
      some (.inr ⟨congrArg Sigma.fst ((S.colour_none_iff x.1 y.1).mp h)⟩)
  else (S.colour x.1 y.1).map Sum.inl

@[simp] theorem colour_old_iff (S : AtomicSource ι X) {i j : ι}
    (x : Carrier X i) (y : Carrier X j) (a : S.Atom i j) :
    colour S x y = some (.inl a) ↔ S.colour x.1 y.1 = some a := by
  classical
  unfold colour
  split_ifs with h hindex
  · simp [h]
  · simp [h]
  · cases hc : S.colour x.1 y.1 with
    | none => exact (h hc).elim
    | some b => simp

@[simp] theorem colour_clone_iff (S : AtomicSource ι X) {i j : ι}
    (x : Carrier X i) (y : Carrier X j) (e : PLift (i = j)) :
    colour S x y = some (.inr e) ↔
      (⟨i,x.1⟩ : Sigma X) = ⟨j,y.1⟩ ∧ x.2 ≠ y.2 := by
  classical
  unfold colour
  split_ifs with h hindex
  · simp [hindex]
  · simp only [Option.some.injEq, Sum.inr.injEq]
    exact ⟨fun _ => ⟨(S.colour_none_iff _ _).mp h,hindex⟩,
      fun _ => trivial⟩
  · constructor
    · cases hc : S.colour x.1 y.1 with
      | none => exact (h hc).elim
      | some a => simp [hc]
    · rintro ⟨he,_⟩
      exact (h ((S.colour_none_iff _ _).mpr he)).elim

@[simp] theorem colour_none_iff (S : AtomicSource ι X) {i j : ι}
    (x : Carrier X i) (y : Carrier X j) :
    colour S x y = none ↔ (⟨i,x⟩ : Sigma (Carrier X)) = ⟨j,y⟩ := by
  classical
  unfold colour
  split_ifs with h hindex
  · have he := (S.colour_none_iff _ _).mp h
    refine ⟨fun _ => ?_,fun _ => rfl⟩
    have htag : ((⟨i,x.1⟩ : Sigma X),x.2) = ((⟨j,y.1⟩ : Sigma X),y.2) := Prod.ext he hindex
    exact pointEquiv.injective htag
  · constructor
    · simp
    · intro he
      cases he
      exact (hindex rfl).elim
  · constructor
    · intro he
      have hh : S.colour x.1 y.1 = none := Option.map_eq_none_iff.mp he
      exact (h hh).elim
    · intro he
      cases he
      exact (h ((S.colour_none_iff _ _).mpr rfl)).elim

noncomputable def source (S : AtomicSource ι X) : AtomicSource ι (Carrier X) where
  Atom := Atom S
  finiteSort := S.finiteSort
  finiteAtom i j := by
    classical
    letI := S.finiteAtom i j
    exact inferInstance
  nonemptySort i := by
    haveI := S.nonemptySort i
    infer_instance
  conv := fun a => match a with
    | .inl b => .inl (S.conv b)
    | .inr e => .inr ⟨e.down.symm⟩
  conv_invol := by
    intro i j a
    cases a with
    | inl a => simp [S.conv_invol]
    | inr e => rfl
  symmetricLoop := by
    intro i a
    cases a with
    | inl a => simp [S.symmetricLoop]
    | inr e => rfl
  colour := colour S
  colour_none_iff := colour_none_iff S
  colour_swap := by
    intro i j x y a
    cases a with
    | inl a => simpa only [colour_old_iff] using S.colour_swap x.1 y.1 a
    | inr e =>
      simp only [colour_clone_iff]
      exact ⟨fun h => ⟨h.1.symm,h.2.symm⟩,fun h => ⟨h.1.symm,h.2.symm⟩⟩
  realized := by
    intro i j a
    cases a with
    | inl a =>
      obtain ⟨x,y,h⟩ := S.realized a
      exact ⟨(x,0),(y,0),(colour_old_iff S _ _ a).mpr h⟩
    | inr e =>
      rcases e with ⟨e⟩
      subst j
      obtain ⟨x⟩ := S.nonemptySort i
      exact ⟨(x,0),(x,1),(colour_clone_iff S _ _ ⟨rfl⟩).mpr ⟨rfl,Nat.zero_ne_one⟩⟩

/-- Literal projection to the original named real point. -/
def owner (p : Sigma (Carrier X)) : Sigma X := ⟨p.1,p.2.1⟩

/-- The equality-inclusive kernel, independently of CCO or amalgamation. -/
def Kernel (p q : Sigma (Carrier X)) : Prop := owner p = owner q

@[simp] theorem kernel_same_sort {i : ι} (x y : Carrier X i) :
    Kernel ⟨i,x⟩ ⟨i,y⟩ ↔ x.1 = y.1 := by
  simp [Kernel,owner]

/-- The actual new diversity relation on one original sort. -/
def cloneRel {i : ι} (x y : Carrier X i) : Prop := x.1 = y.1 ∧ x.2 ≠ y.2

@[simp] theorem source_clone_iff (S : AtomicSource ι X) {i : ι}
    (x y : Carrier X i) :
    (source S).colour x y = some (.inr ⟨rfl⟩) ↔ cloneRel x y := by
  simp [source,colour_clone_iff,cloneRel]

/-- C23--C25: FULL represented multiplication includes the actual diagonal. -/
theorem clone_comp_eq_kernel {i : ι} :
    TRel.comp (X := Carrier X) (@cloneRel ι X i) cloneRel =
      fun x y => x.1 = y.1 := by
  funext x y
  apply propext
  constructor
  · rintro ⟨z,hxz,hzy⟩
    exact hxz.1.trans hzy.1
  · intro h
    refine ⟨(x.1,max x.2 y.2 + 1),⟨rfl,?_⟩,⟨h,?_⟩⟩
    · exact Nat.ne_of_lt (Nat.lt_succ_of_le (Nat.le_max_left _ _))
    · exact (Nat.ne_of_lt (Nat.lt_succ_of_le (Nat.le_max_right _ _))).symm

/-- The logical diagonal plus c is precisely equality of old owners. -/
theorem kernel_eq_identity_union_clone {i : ι} (x y : Carrier X i) :
    x.1 = y.1 ↔ x = y ∨ cloneRel x y := by
  classical
  constructor
  · intro h
    by_cases hi : x.2 = y.2
    · exact Or.inl (Prod.ext h hi)
    · exact Or.inr ⟨h,hi⟩
  · rintro (rfl | h)
    · rfl
    · exact h.1

end CCO.CloneSAP
