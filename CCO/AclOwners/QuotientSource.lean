import CCO.AclOwners.QuotientInterval
import CCO.AclOwners.QuotientColourTransport
import CCO.RawExact.CanonicalQuotientInheritance
import CCO.RealClosure.Bounds.SortRestriction

/-! Actual exact quotients retain the standing source in their literal
one-sort old-group orbital language. Countability stays explicit. -/
universe v w t z
namespace CCO.AclOwners
open ParityHasse.Original FinitePackets.Normalization
open RawExact RawExact.CanonicalQuotients RealClosure.Bounds
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable (K : ColourEq S ()) (B : NonemptyExact S () ())
variable (hB : evaluate S B.words = K.val.r)

private noncomputable def singletonUnitSource : AtomicSource.{0,v,v} Unit (fun _ => Quotient K.val) :=
  sortSource (source S H (singletonData S K.val B hB)) (singletonIndex K.val)

private noncomputable def quotientAtomEquiv (i j : Unit) :
    (actualQuotientSource S H K).Atom i j ≃ (singletonUnitSource S H K B hB).Atom i j := by
  cases i; cases j
  refine {
    toFun := fun a => ⟨a.val,a.property.1,?_⟩
    invFun := fun a => ⟨a.val,a.property.1,?_⟩
    left_inv := fun a => Subtype.ext rfl
    right_inv := fun a => Subtype.ext rfl }
  · intro x y hxy he
    apply a.property.2 x y hxy
    have hv : x = y := eq_of_heq (Sigma.mk.inj he).2
    exact congrArg (Sigma.mk ()) hv
  · intro x y hxy he
    apply a.property.2 x y hxy
    have hv : x = y := eq_of_heq (Sigma.mk.inj he).2
    exact congrArg (Sigma.mk (singletonIndex K.val)) hv

private theorem quotientAtomEquiv_colour (i j : Unit) (x y : Quotient K.val) :
    Option.map (quotientAtomEquiv S H K B hB i j)
      ((actualQuotientSource S H K).colour (i := i) (j := j) x y) =
      (singletonUnitSource S H K B hB).colour x y := by
  cases i; cases j
  letI := originalQuotientAction S H K
  let Q := fun _ : Unit => Quotient K.val
  let R := fun k : Index ({K.val} : Finset (Setoid M)) => Carrier k
  letI : ∀ k : Index ({K.val} : Finset (Setoid M)), MulAction G (Carrier k) :=
    action S H (singletonData S K.val B hB)
  change Option.map (quotientAtomEquiv S H K B hB () ())
    (QuotientPalette.colour (G := G) Q x y) =
      QuotientPalette.colour (G := G) R x y
  cases hc : QuotientPalette.colour (G := G) Q x y with
  | none =>
    have he : x = y := by
      simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using
        (QuotientPalette.colour_none_iff (G := G) Q x y).mp hc
    subst y
    exact ((QuotientPalette.colour_none_iff (G := G) R (k := singletonIndex K.val) (l := singletonIndex K.val) x x).mpr rfl).symm
  | some a =>
    change some (quotientAtomEquiv S H K B hB () () a) = _
    apply Eq.symm
    apply (QuotientPalette.colour_some_iff R (k := singletonIndex K.val) (l := singletonIndex K.val) x y _).mpr
    exact (QuotientPalette.colour_some_iff Q x y a).mp hc

include B hB in
theorem actualQuotient_homogeneous [Countable M]
    (cco : SemanticCCO.{0,v,0,w} S) :
    letI := originalQuotientAction S H K
    HomogeneousSource (actualQuotientSource S H K) G := by
  letI := originalQuotientAction S H K
  apply actual_quotient_homogeneous_of_CCO S H (semanticCCO_change_universe S cco)
    (fun _ : Unit => Quotient K.val) (fun _ => ())
    (fun _ => Quotient.mk'') (fun _ => Quotient.mk''_surjective)
    (fun _ => quotient_projection_equivariant S H K) (fun _ => B)
  · intro _
    funext x y
    exact propext (Quotient.eq.trans (Iff.of_eq (congrFun (congrFun hB x) y)).symm)
  · exact actualQuotientSource_colour_orbital S H K

include B hB in
/-- Source CCO is inherited without an extra quotient-cycle provider. -/
theorem actualQuotient_CCO (cco : SemanticCCO.{0,v,0,w} S) :
    SemanticCCO.{0,v,z,v} (actualQuotientSource S H K) := by
  apply semanticCCO_of_colourEquiv (actualQuotientSource S H K)
    (singletonUnitSource S H K B hB) (quotientAtomEquiv S H K B hB)
  · intro i j a
    cases i; cases j
    rw [(actualQuotientSource S H K).symmetricLoop,
      (singletonUnitSource S H K B hB).symmetricLoop]
  · exact quotientAtomEquiv_colour S H K B hB
  · exact sortSource_semanticCCO (source S H (singletonData S K.val B hB))
      (singletonIndex K.val)
      (RawExact.CanonicalQuotients.semanticCCO S H (semanticCCO_change_universe S cco)
        (singletonData S K.val B hB))

end CCO.AclOwners
