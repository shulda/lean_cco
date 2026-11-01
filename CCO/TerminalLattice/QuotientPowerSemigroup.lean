import CCO.TerminalLattice.FibreSAP
import CCO.ParityHasse.Original.ParitySeed

/-!
# B050 C12: all positive quotient relation powers lifted to OLD diversity

No quotient-cover, symmetry, CCO, NR2 or exactness is assumed. The
`FreshFibre` interface is used only in the abstract lemma, and the
actual original homogeneous AgeSAP source discharges it below.

Positive power n is indexed as n+1: there is deliberately NO
strong identity/diversity power of length zero. The quotient side
retains its real diagonal when an honest positive walk returns.
-/

universe u v w t
namespace CCO.TerminalLattice
variable {A : Type u}

/-- Positive compositions of an OLD diversity relation using genuine
three-distinct-vertex STRONG composition, indexed by length n+1. -/
def strongDiversityPower (R : A → A → Prop) : Nat → A → A → Prop
  | 0 => R
  | n+1 => strongCompose R (strongDiversityPower R n)

/-- Arbitrary-length source-09 semigroup formula on ACTUAL quotient
classes: at every positive length, distinct old endpoint pairs are
exactly those whose J-classes admit a literal quotient walk of that
length. Quotient diagonal returns give OLD J-diversity, NOT old Id. -/
theorem quotientDiversity_strongPower (J : Setoid A)
    (fresh : FreshFibre J)
    (R : Quotient J → Quotient J → Prop) :
    ∀ n : Nat,
      strongDiversityPower (quotientDiversity J R) n =
        quotientDiversity J
          (ParityHasse.Original.relPow R (n+1)) := by
  intro n
  induction n with
  | zero =>
      funext x y
      apply propext
      change (x ≠ y ∧ R (Quotient.mk J x) (Quotient.mk J y)) ↔
        (x ≠ y ∧
          ParityHasse.Original.relPow R 1
            (Quotient.mk J x) (Quotient.mk J y))
      rw [ParityHasse.Original.relPow_one]
  | succ n ih =>
      change strongCompose (quotientDiversity J R)
          (strongDiversityPower (quotientDiversity J R) n) =
        quotientDiversity J
          (RawSymmetric.compose R
            (ParityHasse.Original.relPow R (n+1)))
      rw [ih]
      exact quotientDiversity_strong_comp J fresh R _

/-- The reverse inclusion for every positive power is K-transitivity.
Both the diversity restriction and K-containment of the INPUT are
necessary. This is not a proof of the converse without the cover
hypothesis. -/
theorem strongDiversityPower_subset (K : Setoid A)
    (R : A → A → Prop)
    (hR : ∀ x y, R x y → x ≠ y ∧ K x y) :
    ∀ n x y, strongDiversityPower R n x y → x ≠ y ∧ K x y := by
  intro n
  induction n with
  | zero =>
      exact hR
  | succ n ih =>
      rintro x y ⟨hne, z, _, _, hxz, hzy⟩
      exact ⟨hne, K.trans (hR x z hxz).2 (ih z y hzy).2⟩

end CCO.TerminalLattice

namespace CCO.TerminalLattice
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- Entire original source-09 positive-power semigroup law, with the
infinite-fibre hypothesis proved from ORIGINAL AgeSAP. This theorem
does not create a quotient automorphism group or add a cover assumption. -/
theorem original_quotient_strongPower
    (H : HomogeneousSource S G) (sap : AgeSAP S) {i : ι}
    (J : ParityHasse.Original.ColourEq S i)
    (hJ : (⊥ : ParityHasse.Original.ColourEq S i) < J)
    (R : Quotient J.val → Quotient J.val → Prop)
    (n : Nat) :
    strongDiversityPower (quotientDiversity J.val R) n =
      quotientDiversity J.val
        (ParityHasse.Original.relPow R (n+1)) :=
  quotientDiversity_strongPower J.val
    (freshFibre_of_original_SAP S H sap J hJ) R n

end CCO.TerminalLattice
