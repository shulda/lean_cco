import CCO.AclOwners.UnaryTransfer
import CCO.AclOwners.QuotientSource
import CCO.RealClosure.Bounds.Singleton

/-! Canonical quotient finite bottoms and unary real closure. The upper
interval is the FULL invariant interval, and the quotient is the actual
complete old-group orbital source. No finite-exact normalization or safe
palette is assumed by this general source bridge. -/

universe v w t
namespace CCO.AclOwners
open ParityHasse.Original FinitePackets.Geometry FinitePackets.Normalization
open RealClosure.Bounds RealHull.Geometry

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable (C R : ColourEq S ()) (hCR : C ≤ R)

/-- A sigma-closed original upper endpoint becomes the genuine greatest
finite-class relation of the actual quotient, not a selected sublattice. -/
theorem quotient_greatest_finite
    (hsigma : sigma S H C = R) :
    RealClosure.Bounds.FiniteClasses (actualQuotientSource S H C)
      (quotientColourEq S H C R hCR) ∧
    ∀ E : ColourEq (actualQuotientSource S H C) (),
      RealClosure.Bounds.FiniteClasses (actualQuotientSource S H C) E →
        E ≤ quotientColourEq S H C R hCR := by
  refine ⟨(quotient_finiteClasses_iff S H C R hCR).mpr ?_,?_⟩
  · rw [← hsigma]
    exact finiteIndex_sigma S H C
  · intro E hE
    let P := (quotientColourInterval S H C).symm E
    have hPE : quotientColourEq S H C P.val P.property = E :=
      (quotientColourInterval S H C).apply_symm_apply E
    have hfin : FinitePackets.Geometry.FiniteIndex S C P.val := by
      apply (quotient_finiteClasses_iff S H C P.val P.property).mp
      rw [hPE]
      exact hE
    have hPR : P.val ≤ R := by
      rw [← hsigma]
      exact sigma_greatest S H P.property hfin
    have hle : P ≤ (⟨R,hCR⟩ : Set.Ici C) := hPR
    have hmap := (quotientColourInterval S H C).monotone hle
    change quotientColourEq S H C P.val P.property ≤ quotientColourEq S H C R hCR at hmap
    rwa [hPE] at hmap

/-- A least strict original coarsening is preserved by the FULL quotient
interval order isomorphism. -/
theorem quotient_least_strict (D : ColourEq S ()) (hRD : R < D)
    (hleast : ∀ E : ColourEq S (), R < E → D ≤ E) :
    quotientColourEq S H C R hCR <
      quotientColourEq S H C D (hCR.trans hRD.le) ∧
    ∀ E : ColourEq (actualQuotientSource S H C) (),
      quotientColourEq S H C R hCR < E →
      quotientColourEq S H C D (hCR.trans hRD.le) ≤ E := by
  have hlt : (⟨R,hCR⟩ : Set.Ici C) < ⟨D,hCR.trans hRD.le⟩ := hRD
  refine ⟨(quotientColourInterval S H C).strictMono hlt,?_⟩
  intro E hE
  let P := (quotientColourInterval S H C).symm E
  have hR : R < P.val := by
    have hh := (quotientColourInterval S H C).symm.strictMono hE
    have heR : (quotientColourInterval S H C).symm (quotientColourEq S H C R hCR) =
        (⟨R,hCR⟩ : Set.Ici C) := (quotientColourInterval S H C).symm_apply_apply ⟨R,hCR⟩
    rw [heR] at hh
    exact hh
  have hDP : (⟨D,hCR.trans hRD.le⟩ : Set.Ici C) ≤ P := hleast P.val hR
  have hmap := (quotientColourInterval S H C).monotone hDP
  have heP : (quotientColourInterval S H C) P = E :=
    (quotientColourInterval S H C).apply_symm_apply E
  rw [heP] at hmap
  exact hmap

/-- The actual full colour-invariant equivalences form their literal
sublattice of the ambient equivalence lattice. -/
def fullColourSublattice : Sublattice (Setoid M) where
  carrier := {E | ColourInvariant S () E}
  infClosed' := by
    intro E hE F hF x y x' y' hc
    exact and_congr (hE x y x' y' hc) (hF x y x' y' hc)
  supClosed' := by
    intro E hE F hF
    exact (ColourEq.join S H ⟨E,hE⟩ ⟨F,hF⟩).property

include H in
/-- C19 specialized to a genuine homogeneous finite orbital language.
The abstract proof remains independent of this source instance. -/
theorem directionCount_eq_one_of_finite_bottom
    (F D : ColourEq S ()) (hF : RealClosure.Bounds.FiniteClasses S F)
    (greatest : ∀ E : ColourEq S (), RealClosure.Bounds.FiniteClasses S E → E ≤ F)
    (strict : F < D) (least : ∀ E : ColourEq S (), F < E → D ≤ E) :
    directionCount S = 1 := by
  let L := fullColourSublattice S H
  letI : Finite L := inferInstanceAs (Finite (ColourEq S ()))
  have hcomm : ExactCRT.Abstract.Commutes L := by
    intro E F
    exact invariant_relations_commute S H E.property F.property
  have hu : ∃! U : ColourEq S (), IsDirection S U :=
    Unary.unique_minimal_infinite L hcomm F D hF greatest strict least
  obtain ⟨U,hU,huniq⟩ := hu
  letI : Unique (Direction S) := {
    default := ⟨U,hU⟩
    uniq := fun V => Subtype.ext (huniq V.val V.property) }
  exact Nat.card_unique

/-- A finite greatest relation with a strict upper member forces the actual
carrier to be infinite; no separate infinitude premise is hidden here. -/
theorem infinite_of_finite_bottom_strict
    (F D : ColourEq S ())
    (greatest : ∀ E : ColourEq S (), RealClosure.Bounds.FiniteClasses S E → E ≤ F)
    (strict : F < D) : Infinite M := by
  apply not_finite_iff_infinite.mp
  intro hf
  letI := hf
  have hD : RealClosure.Bounds.FiniteClasses S D :=
    fun _ => Finite.of_injective Subtype.val Subtype.val_injective
  exact strict.not_ge (greatest D hD)

variable [Countable M]
variable (B : RawExact.NonemptyExact S () ())
variable (hB : RawExact.evaluate S B.words = C.val.r)
variable (cco : SemanticCCO.{0,v,0,w} S)
include B hB cco hCR

/-- C18: the original sigma endpoint is exactly the quotient's actual finite
packet, and its least strict upper relation is an actual quotient relation. -/
theorem quotient_finite_bottom (hsigma : sigma S H C = R)
    (D : ColourEq S ()) (hRD : R < D)
    (hleast : ∀ E : ColourEq S (), R < E → D ≤ E) :
    letI := originalQuotientAction S H C
    let qH := actualQuotient_homogeneous S H C B hB cco
    quotientColourEq S H C R hCR = finitePacket (actualQuotientSource S H C) qH ∧
      quotientColourEq S H C R hCR < quotientColourEq S H C D (hCR.trans hRD.le) ∧
      (∀ E : ColourEq (actualQuotientSource S H C) (),
        quotientColourEq S H C R hCR < E →
        quotientColourEq S H C D (hCR.trans hRD.le) ≤ E) := by
  letI := originalQuotientAction S H C
  let qH := actualQuotient_homogeneous S H C B hB cco
  have hg := quotient_greatest_finite S H C R hCR hsigma
  have hl := quotient_least_strict S H C R hCR D hRD hleast
  refine ⟨?_,hl.1,hl.2⟩
  exact le_antisymm (le_finitePacket _ qH _ hg.1)
    (hg.2 _ (finitePacket_finite _ qH))

/-- C18/C19: one actual minimal infinite direction in the quotient FULL
invariant lattice. -/
theorem quotient_directionCount_one (hsigma : sigma S H C = R)
    (D : ColourEq S ()) (hRD : R < D)
    (hleast : ∀ E : ColourEq S (), R < E → D ≤ E) :
    directionCount (actualQuotientSource S H C) = 1 := by
  letI := originalQuotientAction S H C
  let qH := actualQuotient_homogeneous S H C B hB cco
  have hg := quotient_greatest_finite S H C R hCR hsigma
  have hl := quotient_least_strict S H C R hCR D hRD hleast
  exact directionCount_eq_one_of_finite_bottom (actualQuotientSource S H C) qH
    _ _ hg.1 hg.2 hl.1 hl.2

/-- C20: EVERY finite quotient input has unary closure in the literal
R/C packet. No palette or quotient normalization is an input. -/
theorem quotient_acl_iff_relation (hsigma : sigma S H C = R)
    (D : ColourEq S ()) (hRD : R < D)
    (hleast : ∀ E : ColourEq S (), R < E → D ≤ E)
    (U : Finset (Quotient C.val)) (x : Quotient C.val) :
    letI := originalQuotientAction S H C
    x ∈ Acl G U ↔ ∃ u ∈ U, quotientColourEq S H C R hCR u x := by
  classical
  letI := originalQuotientAction S H C
  let T := actualQuotientSource S H C
  let qH := actualQuotient_homogeneous S H C B hB cco
  have hg := quotient_greatest_finite S H C R hCR hsigma
  have hl := quotient_least_strict S H C R hCR D hRD hleast
  letI : Infinite (Quotient C.val) :=
    infinite_of_finite_bottom_strict T _ _ hg.2 hl.1
  have hc : directionCount T = 1 :=
    quotient_directionCount_one S H C R hCR B hB cco hsigma D hRD hleast
  have he := quotient_finite_bottom S H C R hCR B hB cco hsigma D hRD hleast
  rw [acl_rank_one T qH (actualQuotient_CCO S H C B hB cco) hc U]
  change (∃ u ∈ U, finitePacket T qH u x) ↔ _
  rw [← he.1]

end CCO.AclOwners
