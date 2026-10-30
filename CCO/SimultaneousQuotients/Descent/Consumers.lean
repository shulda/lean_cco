import CCO.SimultaneousQuotients.Descent.OneSort

/-! Identity-kernel source consumer. EVERY nonempty old exact relation
descends, including old diversity relations which do not contain equality. -/

universe v w t
namespace CCO.SimultaneousQuotients.Descent
open RawExact

variable {X : Unit → Type v} (S : AtomicSource.{0,v,w} Unit X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)

def identitySetoid (i : Unit) : Setoid (X i) := ⊥

def identityData (i : Unit) : NonemptyExact S i i := exactIdentityAtom S i

theorem identity_represents (i : Unit) :
    evaluate S (identityData S i).words = (identitySetoid i).r := by
  rw [identityData,exactIdentityAtom_relation]
  rfl

include cco in
/-- A complete actual source instance, with all identity-kernel data and
saturation supplied by proofs; no false Id≤D condition is passed. -/
theorem every_old_exact_descends {i : Unit} (D : NonemptyExact S i i) :
    ∃ F : NonemptyExact
      (ExactCRT.CanonicalTyped.source S H identitySetoid (identityData S) (identity_represents S)) i i,
      evaluate (ExactCRT.CanonicalTyped.source S H identitySetoid (identityData S)
        (identity_represents S)) F.words =
      ExactCRT.quotientRelation (ExactCRT.CanonicalTyped.projection identitySetoid i)
        (ExactCRT.CanonicalTyped.projection identitySetoid i) (evaluate S D.words) := by
  apply exact_descent S H identitySetoid (identityData S) (identity_represents S) cco D
  rw [identityData,exactIdentityAtom_relation]
  unfold saturate
  rw [TRel.ident_comp,TRel.comp_ident]

end CCO.SimultaneousQuotients.Descent
