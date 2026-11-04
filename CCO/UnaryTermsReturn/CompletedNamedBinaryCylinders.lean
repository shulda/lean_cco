import CCO.UnaryTermsReturn.CompletedNamedFullAdmissible
import CCO.TransitionClosure.OriginalCylinderAdmissiblePairs

/-!
# B052 D05/C14: actual finite full hidden binary semantic cylinders

The terminal hidden binary predicates must be the COMPLETE semantic
cylinders of the actual represented full original quotient coordinates,
NOT an arbitrary old-G-orbital subpartition. B049 C41-C43 has already
proved that the full OLD representative spectrum of a literal quotient
class pair is a finite named cylinder, unique whenever its endpoints
have a diversity representative. It also handles all real/proper
mixed endpoint cases and excludes same-hidden-sort diagonal colours.

We construct the genuine finite binary name type, a typed reading of
every actual real/hidden vertex in its exact old quotient coordinate,
and the interpreted binary cylinder relation on the source10 actual
completed carrier. No hidden homogeneity, hidden SAP, new atom, or
quotient-to-real operation is assumed.
-/

universe u v w t

namespace CCO.UnaryTermsReturn

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open CCO.TransitionClosure
open CCO.ParityHasse.Original

/-- A TRUE named original hidden sort is either the original REAL
equality coordinate or an existing represented proper FULL MI.
The identity case is not declared a hidden positive STRONG atom. -/
abbrev OriginalCompletedCoordinateCode (H : HomogeneousSource S G) :=
  Σ i : ι, Unit ⊕ OriginalNamedHiddenCoordinate S H i

/-- Literal full original kernel of one actual real/hidden
coordinate code; REAL code means logical identity on that sort. -/
def originalCompletedCoordinateKernel
    (H : HomogeneousSource S G)
    (C : OriginalCompletedCoordinateCode S H) :
    ColourEq S C.1 :=
  match C with
  | ⟨_, .inl _⟩ => ⊥
  | ⟨_, .inr D⟩ => D.val

/-- One finite hidden binary relation name is a pair of genuine
coordinate-sort tags together with ONE full B049 finite semantic
cylinder name on that exact pair of original full kernels. -/
abbrev OriginalCompletedCylinderBinaryName
    (H : HomogeneousSource S G) :=
  Σ C : OriginalCompletedCoordinateCode S H,
    Σ D : OriginalCompletedCoordinateCode S H,
      ↑(originalTypedCylinderNames S
        (originalCompletedCoordinateKernel S H C)
        (originalCompletedCoordinateKernel S H D))

/-- Finiteness is inherited from finitely many original sorts,
finitely many represented FULL proper MI coordinates, and the
accepted B049 finite distinct cylinder spectra, not an assumed
finite actual quotient carrier or finite class-pair set. -/
theorem original_completed_cylinder_binary_names_finite
    (H : HomogeneousSource S G) :
    Finite (OriginalCompletedCylinderBinaryName S H) := by
  letI : Fintype ι := S.finiteSort
  haveI (i : ι) :
      Finite (OriginalNamedHiddenCoordinate S H i) :=
    original_named_hidden_coordinates_finite S H
  haveI : Finite (OriginalCompletedCoordinateCode S H) := by
    infer_instance
  haveI (C D : OriginalCompletedCoordinateCode S H) :
      Finite ↑(originalTypedCylinderNames S
        (originalCompletedCoordinateKernel S H C)
        (originalCompletedCoordinateKernel S H D)) :=
    (originalTypedCylinderNames_finite S
      (originalCompletedCoordinateKernel S H C)
      (originalCompletedCoordinateKernel S H D)).to_subtype
  infer_instance

/-- Canonical real/represented-hidden VERTEX reading on the
old quotient carrier. All source and target old tags are literal.
This relation does not adjoin an ambient real representative
to a finite orphan hidden induced member. -/
inductive OriginalCompletedCoordinateReading
    (H : HomogeneousSource S G) :
    (v : OriginalCompletedNamedCarrier S H) →
    (C : OriginalCompletedCoordinateCode S H) →
    Quotient (originalCompletedCoordinateKernel S H C).val → Prop where
  | real {i : ι} (x : X i) :
      OriginalCompletedCoordinateReading H
        (.inl (⟨i,x⟩ : Sigma X)) ⟨i,.inl ()⟩
        (Quotient.mk (⊥ : ColourEq S i).val x)
  | hidden {i : ι} (D : OriginalNamedHiddenCoordinate S H i)
      (q : Quotient D.val.val) :
      OriginalCompletedCoordinateReading H
        (originalCompletedNamedHiddenNode S H D q)
        ⟨i,.inr D⟩ q

/-- Every ACTUAL completed vertex has one genuine source-facing
typed representation. It is a real equality class or one actual
represented FULL MI quotient class, with no extra real member. -/
theorem original_completed_coordinate_reading_exists
    (H : HomogeneousSource S G)
    (v : OriginalCompletedNamedCarrier S H) :
    ∃ (C : OriginalCompletedCoordinateCode S H)
      (q : Quotient (originalCompletedCoordinateKernel S H C).val),
      OriginalCompletedCoordinateReading S H v C q := by
  cases v with
  | inl x =>
      rcases x with ⟨i,x⟩
      exact ⟨⟨i,.inl ()⟩, Quotient.mk (⊥ : ColourEq S i).val x,
        .real x⟩
  | inr x =>
      obtain ⟨i,D,q,hEq⟩ :=
        original_completed_hidden_value_has_named_witness S H x
      refine ⟨⟨i,.inr D⟩,q,?_⟩
      rw [hEq]
      exact .hidden D q

/-- Interpretation of ONE actual complete binary cylinder name
on the original real/represented-hidden carrier. The real/hidden
sort tags and quotient classes must match the name, the vertices
are LITERALLY distinct, and their entire representative spectrum
is exactly its B049 canonical finite cylinder palette. -/
def originalCompletedCylinderBinaryPredicate
    (H : HomogeneousSource S G)
    (name : OriginalCompletedCylinderBinaryName S H)
    (a b : OriginalCompletedNamedCarrier S H) : Prop :=
  a ≠ b ∧
    ∃ (q : Quotient
          (originalCompletedCoordinateKernel S H name.1).val)
      (r : Quotient
          (originalCompletedCoordinateKernel S H name.2.1).val),
      OriginalCompletedCoordinateReading S H a name.1 q ∧
      OriginalCompletedCoordinateReading S H b name.2.1 r ∧
      originalTypedCylinderSemanticRelation S
        (originalCompletedCoordinateKernel S H name.1)
        (originalCompletedCoordinateKernel S H name.2.1)
        name.2.2.val q r

/-- No complete binary DIVERSITY cylinder is placed on the
literal hidden diagonal, whatever representative spectrum
the corresponding old quotient class pair might have. -/
theorem original_completed_cylinder_binary_irreflexive
    (H : HomogeneousSource S G)
    (name : OriginalCompletedCylinderBinaryName S H)
    (v : OriginalCompletedNamedCarrier S H) :
    ¬ originalCompletedCylinderBinaryPredicate S H name v v := by
  rintro ⟨hne,_⟩
  exact hne rfl

/-- A concrete source-facing C14 binary interpretation that may
be plugged into the labelled full-diagram isomorphism interface.
Every name is a genuine B049 canonical cylinder, not a finer
unverified original-G pair atom or a hypothetical quotient chart. -/
def originalCompletedActualBinary
    (H : HomogeneousSource S G) :
    OriginalCompletedCylinderBinaryName S H →
      OriginalCompletedNamedCarrier S H →
      OriginalCompletedNamedCarrier S H → Prop :=
  originalCompletedCylinderBinaryPredicate S H

end CCO.UnaryTermsReturn
