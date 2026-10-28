import CCO.ParityHasse.Original.OrbitalAlgebra
import CCO.RealHull.Geometry.ClassHomogeneity
import CCO.RealHull.Geometry.ClassSizes
import CCO.FinitePackets.Geometry.Sigma
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.SetTheory.Cardinal.Finite

/-! The greatest finite-class ORIGINAL equivalence. Its existence uses only
the finite full invariant lattice and represented permutability. No CCO or
exactness of this packet is assumed. All cardinal estimates follow actual
finiteness proofs. -/

universe v w t
namespace CCO.RealClosure.Bounds
open ParityHasse.Original RealHull.Geometry

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))

def FiniteClasses (E : ColourEq S ()) : Prop :=
  ∀ x : M, Finite (ClassPoint S () E x)

theorem finiteClasses_bot : FiniteClasses S (⊥ : ColourEq S ()) := by
  intro x
  letI : Subsingleton (ClassPoint S () (⊥ : ColourEq S ()) x) := ⟨by
    intro p q
    exact Subtype.ext (p.property.symm.trans q.property)⟩
  infer_instance

theorem finiteClasses_of_le {E F : ColourEq S ()} (hle : E ≤ F)
    (hF : FiniteClasses S F) : FiniteClasses S E := by
  intro x
  letI := hF x
  exact Finite.of_injective
    (fun y : ClassPoint S () E x => (⟨y.val, hle y.property⟩ : ClassPoint S () F x))
    (fun _ _ h => Subtype.ext (congrArg (fun z : ClassPoint S () F x => z.val) h))

variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)

def classTranslate (E : ColourEq S ()) (x : M) (g : G) :
    ClassPoint S () E x ≃ ClassPoint S () E (g • x) where
  toFun y := ⟨g • y.val, (class_group_invariant S () H E g x y.val).mpr y.property⟩
  invFun y := ⟨g⁻¹ • y.val, by
    have hh := (class_group_invariant S () H E g⁻¹ (g • x) y.val).mpr y.property
    simpa only [inv_smul_smul] using hh⟩
  left_inv y := Subtype.ext (inv_smul_smul g y.val)
  right_inv y := Subtype.ext (smul_inv_smul g y.val)

noncomputable def classEquiv (E : ColourEq S ()) (x y : M) :
    ClassPoint S () E x ≃ ClassPoint S () E y := by
  let g := Classical.choose (S.original_sort_transitive_of_homogeneous H () x y)
  have hg : g • x = y := Classical.choose_spec
    (S.original_sort_transitive_of_homogeneous H () x y)
  exact hg ▸ classTranslate S H E x g

include H in
theorem finiteClasses_iff_at (E : ColourEq S ()) (x : M) :
    FiniteClasses S E ↔ Finite (ClassPoint S () E x) := by
  constructor
  · exact fun h => h x
  · intro hx y
    letI := hx
    exact Finite.of_equiv (ClassPoint S () E x) (classEquiv S H E x y)

include H in
theorem class_card_eq (E : ColourEq S ()) (x y : M) :
    Nat.card (ClassPoint S () E x) = Nat.card (ClassPoint S () E y) :=
  Nat.card_congr (classEquiv S H E x y)

def classJoinAssembly (E F : ColourEq S ()) (x : M) :
    (Σ y : ClassPoint S () E x, ClassPoint S () F y.val) →
      ClassPoint S () (ColourEq.join S H E F) x :=
  fun p => ⟨p.2.val, (sup_relation_iff S H E F x p.2.val).mpr
    ⟨p.1.val, p.1.property, p.2.property⟩⟩

theorem classJoinAssembly_surjective (E F : ColourEq S ()) (x : M) :
    Function.Surjective (classJoinAssembly S H E F x) := by
  intro z
  obtain ⟨y, hxy, hyz⟩ := (sup_relation_iff S H E F x z.val).mp z.property
  exact ⟨⟨⟨y, hxy⟩, ⟨z.val, hyz⟩⟩, rfl⟩

theorem finite_classes_sup (E F : ColourEq S ())
    (hE : FiniteClasses S E) (hF : FiniteClasses S F) :
    FiniteClasses S (ColourEq.join S H E F) := by
  intro x
  letI := hE x
  letI : Fintype (ClassPoint S () E x) := Fintype.ofFinite (ClassPoint S () E x)
  letI : ∀ y : ClassPoint S () E x, Fintype (ClassPoint S () F y.val) := fun y => by
    letI := hF y.val
    exact Fintype.ofFinite _
  exact Finite.of_surjective (classJoinAssembly S H E F x)
    (classJoinAssembly_surjective S H E F x)

theorem class_sup_card_le_product (E F : ColourEq S ())
    (hE : FiniteClasses S E) (hF : FiniteClasses S F) (x : M) :
    Nat.card (ClassPoint S () (ColourEq.join S H E F) x) ≤
      Nat.card (ClassPoint S () E x) * Nat.card (ClassPoint S () F x) := by
  classical
  letI := hE x
  letI : Fintype (ClassPoint S () E x) := Fintype.ofFinite _
  letI : ∀ y : ClassPoint S () E x, Fintype (ClassPoint S () F y.val) := fun y => by
    letI := hF y.val
    exact Fintype.ofFinite _
  let W := Σ y : ClassPoint S () E x, ClassPoint S () F y.val
  let e : W ≃ ClassPoint S () E x × ClassPoint S () F x := {
    toFun p := (p.1, classEquiv S H F p.1.val x p.2)
    invFun p := ⟨p.1, (classEquiv S H F p.1.val x).symm p.2⟩
    left_inv p := by
      cases p
      simp only [Equiv.symm_apply_apply]
    right_inv p := by
      cases p
      simp only [Equiv.apply_symm_apply]
  }
  calc
    _ ≤ Nat.card W := Nat.card_le_card_of_surjective _
      (classJoinAssembly_surjective S H E F x)
    _ = Nat.card (ClassPoint S () E x × ClassPoint S () F x) := Nat.card_congr e
    _ = _ := Nat.card_prod _ _

noncomputable def finitePacket : ColourEq S () := by
  exact FinitePackets.Geometry.sigma S H (⊥ : ColourEq S ())

theorem finitePacket_finite : FiniteClasses S (finitePacket S H) := by
  intro x
  letI : Finite (RelativeClass (⊥ : ColourEq S ()).val (finitePacket S H).val x) :=
    FinitePackets.Geometry.finiteIndex_sigma S H (⊥ : ColourEq S ()) x
  exact Finite.of_equiv _ (bottomClassEquiv S () (finitePacket S H) x)

theorem le_finitePacket (E : ColourEq S ()) (hE : FiniteClasses S E) :
    E ≤ finitePacket S H := by
  have hfin : FinitePackets.Geometry.FiniteIndex S (⊥ : ColourEq S ()) E := by
    intro x
    letI := hE x
    exact Finite.of_equiv _ (bottomClassEquiv S () E x).symm
  exact FinitePackets.Geometry.sigma_greatest S H bot_le hfin

theorem finiteClasses_iff_le_packet (E : ColourEq S ()) :
    FiniteClasses S E ↔ E ≤ finitePacket S H :=
  ⟨le_finitePacket S H E, fun h => finiteClasses_of_le S h (finitePacket_finite S H)⟩

theorem packet_class_card (x y : M) :
    Nat.card (ClassPoint S () (finitePacket S H) x) =
      Nat.card (ClassPoint S () (finitePacket S H) y) :=
  class_card_eq S H _ x y

end CCO.RealClosure.Bounds
