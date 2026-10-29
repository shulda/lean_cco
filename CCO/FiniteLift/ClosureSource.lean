import CCO.FiniteLift.Closure
import CCO.FiniteLift.ClosureFull
import CCO.RealClosure.Bounds.SortRestriction

/-! B029 C01 and closure corollaries. The displayed quotient is the actual
canonical K-sort with all old-group orbitals, not an abstract imaginary.
Its full automorphism stabilizers remain the group used in quotient acl. -/

universe v w t z
namespace CCO.FiniteLift
open RawExact CanonicalQuotients
variable {A : Type v} {G : Type t} [Group G] [MulAction G A]
variable {S : AtomicSource.{0,v,w} Unit (fun _ => A)}
namespace ExactKernel
variable (K : ExactKernel S G)

def quotientData : ExactData S ({K.rel} : Finset (Setoid A)) :=
  singletonData S K.rel K.exact K.represents

/-- The inherited actual finite complete symmetric canonical orbital source,
viewed as ONE sort while keeping the actual original witness group. -/
noncomputable def quotientSource (H : HomogeneousSource S G) :
    AtomicSource.{0,v,v} Unit (fun _ => K.Q) := by
  letI : ∀ k : Index ({K.rel} : Finset (Setoid A)), MulAction G (Carrier k) :=
    action S H K.quotientData
  exact RealClosure.Bounds.sortSource (source S H K.quotientData) (singletonIndex K.rel)

/-- C28 source properties are consumed as the accepted proved theorem,
including actual orbital names, countability, homogeneity, AP and CCO. -/
theorem standing_source [Countable A]
    (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S) :
    SourceProperties.{v,w,t,z} S H K.quotientData :=
  singleton_source_properties S H cco K.rel K.exact K.represents

theorem quotientSource_homogeneous [Countable A]
    (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S) :
    HomogeneousSource (K.quotientSource H) G := by
  letI : ∀ k : Index ({K.rel} : Finset (Setoid A)), MulAction G (Carrier k) :=
    action S H K.quotientData
  exact RealClosure.Bounds.sortSource_homogeneous
    (source S H K.quotientData) (singletonIndex K.rel)
    (homogeneous S H cco K.quotientData)

theorem quotientSource_cco (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,v,w} S) :
    SemanticCCO.{0,v,z,v} (K.quotientSource H) := by
  letI : ∀ k : Index ({K.rel} : Finset (Setoid A)), MulAction G (Carrier k) :=
    action S H K.quotientData
  exact RealClosure.Bounds.sortSource_semanticCCO
    (source S H K.quotientData) (singletonIndex K.rel)
    (semanticCCO S H cco K.quotientData)

theorem quotientSource_colour_orbital (H : HomogeneousSource S G)
    (x y x' y' : K.Q) :
    (K.quotientSource H).colour (i := ()) (j := ()) x y =
      (K.quotientSource H).colour x' y' ↔
        GroupActions.orbital (G := G) x y x' y' := by
  letI : ∀ k : Index ({K.rel} : Finset (Setoid A)), MulAction G (Carrier k) :=
    action S H K.quotientData
  exact source_colour_eq_iff_orbital S H K.quotientData
    (k := singletonIndex K.rel) (l := singletonIndex K.rel) x y x' y'

theorem quotientSource_countable [Countable A] : Countable K.Q := K.onto.countable

/-- C13 exact boundary: arbitrary full witnesses are closed precisely when
the supplied quotient witness is, not merely because they contain the input acl. -/
theorem fullPreimage_closed_iff [Countable A]
    (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
    (finiteK : K.FiniteClasses) (B : Set K.Q) (finiteB : B.Finite) :
    aclSet G (K.proj ⁻¹' B) = K.proj ⁻¹' B ↔
      aclSet (FullAut G K.Q) B = B := by
  constructor
  · intro h
    have he := congrArg (Set.image K.proj)
      (K.acl_pullback H cco finiteK _ (K.fullPreimage_finite finiteK B finiteB))
    rw [h, Set.image_preimage_eq B K.onto, Set.image_preimage_eq _ K.onto] at he
    exact he.symm
  · exact K.fullPreimage_closed H cco finiteK B finiteB

/-- The displayed source closure also has its literal FULL original-group
meaning; this is a finite-homogeneity identification, not a quotient section. -/
theorem acl_pullback_full [Countable A]
    (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
    (finiteK : K.FiniteClasses) (B : Set A) (finiteB : B.Finite) :
    aclSet (FullAut G A) B = K.proj ⁻¹' aclSet (FullAut G K.Q) (K.proj '' B) := by
  rw [aclSet_full_eq S H B finiteB]
  exact K.acl_pullback H cco finiteK B finiteB

end ExactKernel
end CCO.FiniteLift
