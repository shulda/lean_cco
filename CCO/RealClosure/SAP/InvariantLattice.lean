import CCO.RealClosure.SAP.Source
import Mathlib.Order.Atoms.Finite
import Mathlib.Order.Preorder.Finite

/-! The FULL original ambient-action invariant-equivalence lattice.
Finiteness uses BOTH ordered original pair colours, not symmetry. Joins are
intersections of common upper bounds; no represented commutation or
distributivity is assumed. -/
universe v w t z
namespace CCO.RealClosure.SAP
variable {M : Type v} {G : Type t} [Group G] [MulAction G M]

def Invariant (E : Setoid M) : Prop :=
  ∀ g : G, ∀ x y : M, E x y → E (g • x) (g • y)

abbrev InvariantEq (G : Type t) [Group G] (M : Type v) [MulAction G M] :=
  {E : Setoid M // Invariant (G := G) E}

namespace InvariantEq
instance : PartialOrder (InvariantEq G M) := inferInstanceAs (PartialOrder {E : Setoid M // _})
instance : CoeFun (InvariantEq G M) (fun _ => M → M → Prop) := ⟨fun E => E.val.r⟩

@[ext] theorem ext {E F : InvariantEq G M} (h : ∀ x y, E x y ↔ F x y) : E = F :=
  Subtype.ext (Setoid.ext h)

instance : OrderBot (InvariantEq G M) where
  bot := ⟨⊥,fun _ _ _ h => congrArg _ h⟩
  bot_le := fun E _ _ h => h ▸ E.val.refl _
instance : OrderTop (InvariantEq G M) where
  top := ⟨⊤,fun _ _ _ _ => trivial⟩
  le_top := fun _ _ _ _ => trivial
instance : SemilatticeInf (InvariantEq G M) where
  inf E F := ⟨E.val ⊓ F.val,fun g x y h => ⟨E.property g x y h.1,F.property g x y h.2⟩⟩
  inf_le_left := fun _ _ _ _ h => h.1
  inf_le_right := fun _ _ _ _ h => h.2
  le_inf := fun _ _ _ hE hF _ _ h => ⟨hE h,hF h⟩

@[simp] theorem bot_apply (x y : M) : (⊥ : InvariantEq G M) x y ↔ x = y := Iff.rfl
@[simp] theorem top_apply (x y : M) : (⊤ : InvariantEq G M) x y ↔ True := Iff.rfl
@[simp] theorem inf_apply (E F : InvariantEq G M) (x y : M) :
    (E ⊓ F) x y ↔ E x y ∧ F x y := Iff.rfl

def familyMeet {I : Type z} (E : I → InvariantEq G M) : InvariantEq G M :=
  ⟨{ r := fun x y => ∀ k, E k x y
     iseqv := ⟨fun x k => (E k).val.refl x,
       fun h k => (E k).val.symm (h k),
       fun h h' k => (E k).val.trans (h k) (h' k)⟩ },
   fun g x y h k => (E k).property g x y (h k)⟩

@[simp] theorem familyMeet_apply {I : Type z} (E : I → InvariantEq G M) (x y : M) :
    familyMeet E x y ↔ ∀ k, E k x y := Iff.rfl

theorem familyMeet_le {I : Type z} (E : I → InvariantEq G M) (k : I) :
    familyMeet E ≤ E k := fun _ _ h => h k
theorem le_familyMeet {I : Type z} {E : I → InvariantEq G M} {F : InvariantEq G M}
    (h : ∀ k, F ≤ E k) : F ≤ familyMeet E := fun _ _ hxy k => h k hxy

def join (E F : InvariantEq G M) : InvariantEq G M :=
  familyMeet (fun K : {K : InvariantEq G M // E ≤ K ∧ F ≤ K} => K.val)

instance : Lattice (InvariantEq G M) where
  inf := (· ⊓ ·)
  inf_le_left := fun _ _ => inf_le_left
  inf_le_right := fun _ _ => inf_le_right
  le_inf := fun _ _ _ hE hF => le_inf hE hF
  sup := join
  le_sup_left := fun _ _ _ _ h K => K.property.1 h
  le_sup_right := fun _ _ _ _ h K => K.property.2 h
  sup_le := fun _ _ K hE hF _ _ h => h ⟨K,hE,hF⟩

theorem apply_smul_iff (E : InvariantEq G M) (g : G) (x y : M) :
    E (g • x) (g • y) ↔ E x y := by
  refine ⟨fun h => ?_,E.property g x y⟩
  simpa only [inv_smul_smul] using E.property g⁻¹ (g • x) (g • y) h

/-- The finite COMPLETE palette separates all invariant equivalences even
when no individual original orbital is symmetric. -/
theorem finite (S : Source.{v,w} M) (H : S.Homogeneous (G := G)) :
    Finite (InvariantEq G M) := by
  letI := S.finiteColour
  let support : InvariantEq G M → Set (S.Colour × S.Colour) :=
    fun E => {c | ∃ x y, E x y ∧ (S.colour x y,S.colour y x) = c}
  apply Finite.of_injective support
  intro E F h
  apply ext
  intro x y
  constructor
  · intro hxy
    have hs : (S.colour x y,S.colour y x) ∈ support F := by
      rw [← h]
      exact ⟨x,y,hxy,rfl⟩
    obtain ⟨a,b,hab,hcol⟩ := hs
    obtain ⟨g,hg,hg'⟩ := Source.Homogeneous.pair S H (congrArg Prod.fst hcol) (congrArg Prod.snd hcol)
    simpa only [hg,hg'] using F.property g a b hab
  · intro hxy
    have hs : (S.colour x y,S.colour y x) ∈ support E := by
      rw [h]
      exact ⟨x,y,hxy,rfl⟩
    obtain ⟨a,b,hab,hcol⟩ := hs
    obtain ⟨g,hg,hg'⟩ := Source.Homogeneous.pair S H (congrArg Prod.fst hcol) (congrArg Prod.snd hcol)
    simpa only [hg,hg'] using E.property g a b hab

theorem exists_neighbour (S : Source.{v,w} M) (H : S.Homogeneous (G := G))
    {E : InvariantEq G M} (hE : E ≠ ⊥) (x : M) :
    ∃ y, y ≠ x ∧ E x y := by
  have hex : ∃ a b, E a b ∧ a ≠ b := by
    by_contra hn
    apply hE
    apply le_antisymm ?_ bot_le
    intro a b hab
    by_contra hne
    exact hn ⟨a,b,hab,hne⟩
  obtain ⟨a,b,hab,hne⟩ := hex
  obtain ⟨g,hg⟩ := Source.Homogeneous.transitive S H a x
  refine ⟨g • b,?_,?_⟩
  · intro he
    exact hne ((MulAction.injective g) (hg.trans he.symm))
  · simpa only [hg] using E.property g a b hab

/-- C20: the FIXED class of x is infinite, using its complete anchor
{y,z}; the proof allows y=z and never switches to unrelated classes. -/
theorem infinite_meet_class (S : Source.{v,w} M) (H : S.Homogeneous (G := G))
    (sap : S.AgeSAP) {E F : InvariantEq G M}
    (hE : E ≠ ⊥) (hF : F ≠ ⊥) (x : M) :
    Set.Infinite {y | (E ⊓ F) x y} := by
  classical
  obtain ⟨y,hy,he⟩ := exists_neighbour S H hE x
  obtain ⟨z,hz,hf⟩ := exists_neighbour S H hF x
  let A : Finset M := {y,z}
  have hxA : x ∉ A := by simpa only [A,Finset.mem_insert,Finset.mem_singleton] using
    (not_or.mpr ⟨Ne.symm hy,Ne.symm hz⟩)
  apply (S.infinite_orbit H sap A x hxA).mono
  rintro u ⟨g,hg,rfl⟩
  have hgy : g • y = y := hg y (by simp [A])
  have hgz : g • z = z := hg z (by simp [A])
  constructor
  · have hgu : E (g • x) y := by simpa only [hgy] using E.property g x y he
    exact E.val.trans he (E.val.symm hgu)
  · have hgu : F (g • x) z := by simpa only [hgz] using F.property g x z hf
    exact F.val.trans hf (F.val.symm hgu)

end InvariantEq
end CCO.RealClosure.SAP
