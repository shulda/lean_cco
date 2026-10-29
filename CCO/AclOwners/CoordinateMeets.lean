import CCO.AclOwners.CorrespondenceGeometry
import Mathlib.Data.List.OfFn

/-! Exhaustive ORIGINAL correspondence coordinates. The index type is the
ENTIRE finite collection of minimal infinite directions, not an arbitrary
selected subfamily. The packet F is never claimed exact. -/

universe v w t z
namespace CCO.AclOwners
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Geometry FinitePackets.Normalization RawExact
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))

/-- Literal all-family intersection, including an empty indexed family. -/
def colourFamilyMeet {I : Type z} (E : I → ColourEq S ()) : ColourEq S () :=
  ⟨⟨fun x y => ∀ i, E i x y,
    ⟨fun x i => (E i).val.refl x,
      fun h i => (E i).val.symm (h i),
      fun h h' i => (E i).val.trans (h i) (h' i)⟩⟩,
    fun x y x' y' hc => ⟨fun h i => ((E i).property x y x' y' hc).mp (h i),
      fun h i => ((E i).property x y x' y' hc).mpr (h i)⟩⟩

@[simp] theorem colourFamilyMeet_apply {I : Type z} (E : I → ColourEq S ()) (x y : M) :
    colourFamilyMeet S E x y ↔ ∀ i, E i x y := Iff.rfl

/-- Finite meets of actual exact equivalences have a full exact word
presentation. Their common diagonal supplies nonemptiness, including the
empty family (the empty restriction list denotes actual Top). -/
theorem colourFamilyMeet_exact {I : Type z} [Finite I] (E : I → ColourEq S ())
    (hE : ∀ i, ExactCRT.IsExactEq S (i := ()) (E i).val) :
    ExactCRT.IsExactEq S (i := ()) (colourFamilyMeet S E).val := by
  classical
  letI : Fintype I := Fintype.ofFinite _
  let D : I → NonemptyExact S () () := fun i => (hE i).choose
  have hD : ∀ i, evaluate S (D i).words = (E i).val.r := fun i => (hE i).choose_spec
  let P : Presentation S () () := Finset.univ.toList.flatMap (fun i => (D i).words)
  have hP : evaluate S P = (colourFamilyMeet S E).val.r := by
    funext x y
    apply propext
    constructor
    · intro h i
      have hh : evaluate S (D i).words x y := by
        intro word hw
        exact h word (List.mem_flatMap.mpr ⟨i,by simp,hw⟩)
      rwa [hD i] at hh
    · intro h word hw
      obtain ⟨i,_,hwi⟩ := List.mem_flatMap.mp hw
      have hh : evaluate S (D i).words x y := by
        rw [hD i]
        exact h i
      exact hh word hwi
  obtain ⟨x⟩ := S.nonemptySort ()
  exact ⟨⟨P,⟨x,x,by rw [hP]⟩⟩,hP⟩

variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (cco : SemanticCCO.{0,v,0,w} S)

noncomputable def allCorrespondence : ColourEq S () :=
  colourFamilyMeet S (oldCorrespondence S H cco)

noncomputable def allOldCore : ColourEq S () :=
  colourFamilyMeet S (oldCore S H cco)

/-- C15: every ORIGINAL correspondence is used. Their whole intersection
is exactly the full, possibly nonexact finite packet. -/
theorem allCorrespondence_eq_packet (normalized : NoFiniteExactKernel S) :
    allCorrespondence S H cco = finitePacket S H := by
  apply le_antisymm
  · apply le_finitePacket S H
    by_contra hn
    obtain ⟨D,hD⟩ := exists_direction_le S hn
    have hcut : RealClosure.Bounds.FiniteClasses S
        (D.val ⊓ oldCorrespondence S H cco D) := by
      apply finiteClasses_of_le S (F := finitePacket S H) ?_ (finitePacket_finite S H)
      intro x y hxy
      exact ((correspondence_inf_eq_packet S H cco normalized D.val).mp hxy).2
    have hle : D.val ≤ D.val ⊓ oldCorrespondence S H cco D := by
      intro x y hxy
      exact ⟨hxy,hD hxy D⟩
    exact D.property.1 (finiteClasses_of_le S hle hcut)
  · intro x y hxy D
    exact packet_le_correspondence S H normalized D.val hxy

/-- All original core coordinates have exact common kernel. -/
theorem allOldCore_exact : ExactCRT.IsExactEq S (i := ()) (allOldCore S H cco).val :=
  colourFamilyMeet_exact S (oldCore S H cco) (fun D => core_exact S H _)

/-- C15: normalization collapses the finite exact common kernel to actual
identity. It does not collapse the NONEXACT full packet itself. -/
theorem allOldCore_eq_bot (normalized : NoFiniteExactKernel S) :
    allOldCore S H cco = ⊥ := by
  apply normalized_exact_finite S normalized _ (allOldCore_exact S H cco)
  apply finiteClasses_of_le S (F := finitePacket S H) ?_ (finitePacket_finite S H)
  rw [← allCorrespondence_eq_packet S H cco normalized]
  intro x y hxy D
  exact core_le S (oldCorrespondence S H cco D) (hxy D)

/-- The source's exact all-coordinate correspondence equation. -/
theorem all_correspondence_iff_packet (normalized : NoFiniteExactKernel S) (x y : M) :
    (∀ D : Direction S, oldCorrespondence S H cco D x y) ↔ finitePacket S H x y := by
  change allCorrespondence S H cco x y ↔ _
  rw [allCorrespondence_eq_packet S H cco normalized]

/-- The literal original core meet equation, for use as an actual joint
quotient kernel. -/
theorem all_oldCore_iff_eq (normalized : NoFiniteExactKernel S) (x y : M) :
    (∀ D : Direction S, oldCore S H cco D x y) ↔ x = y := by
  change allOldCore S H cco x y ↔ _
  rw [allOldCore_eq_bot S H cco normalized]
  rfl

end CCO.AclOwners
