import CCO.AclOwners.QuotientSource
import CCO.ExactCRT.ExactLattice
import CCO.ExactCRT.TypedPullback
import CCO.ExactCRT.SameSortDescent

/-! BOTH exact directions for the literal complete orbital quotient source.
The interval covers all invariant equivalences, not only a selected list. -/
universe v w t
namespace CCO.MIGeometry
open ParityHasse.Original RawExact AclOwners FinitePackets.Normalization
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable (cco : SemanticCCO.{0,v,0,w} S)
variable (K : ColourEq S ()) (B : NonemptyExact S () ())
variable (hB : evaluate S B.words = K.val.r)

include cco B hB in
/-- A quotient exact equivalence has an original exact pullback, including
nil words, whose pullback is K rather than real equality. -/
theorem quotientPullback_exact
    (E : ColourEq (actualQuotientSource S H K) ())
    (hE : ExactCRT.IsExactEq (actualQuotientSource S H K) (i := ()) E.val) :
    ExactCRT.IsExactEq S (i := ()) (quotientPullback S H K E).val := by
  letI := originalQuotientAction S H K
  obtain ⟨D,hD⟩ := hE
  let π : ∀ _ : Unit, M → Quotient K.val := fun _ => Quotient.mk''
  have hker : ∀ i : Unit, GroupActions.kernel (π i) = evaluate S B.words := by
    intro i
    funext x y
    exact propext (Quotient.eq.trans (Iff.of_eq (congrFun (congrFun hB x) y)).symm)
  refine ⟨ExactCRT.liftQuotientExact S (actualQuotientSource S H K) H
    (semanticCCO_change_universe S cco) π (fun _ => Quotient.mk''_surjective)
    (fun _ => quotient_projection_equivariant S H K) (fun _ => B) hker
    (actualQuotientSource_colour_orbital S H K) D,?_⟩
  rw [ExactCRT.liftQuotientExact_relation,hD]
  rfl

/-- Equivalence transitivity supplies the saturation needed by descent. -/
theorem equivalence_saturated (E : ColourEq S ()) (hKE : K ≤ E) :
    saturate (X := fun _ : Unit => M) (i := ()) (j := ()) K.val.r E.val.r K.val.r = E.val.r := by
  funext x y
  apply propext
  constructor
  · rintro ⟨b,⟨a,hxa,hab⟩,hby⟩
    exact E.val.trans (E.val.trans (hKE hxa) hab) (hKE hby)
  · intro hxy
    exact ⟨y,⟨x,K.val.refl x,hxy⟩,K.val.refl y⟩

include cco B hB in
/-- Every original exact equivalence above K descends exactly in the actual
old-group orbital language; one-sort TI is proved by the accepted calculus. -/
theorem quotientColourEq_exact (E : ColourEq S ()) (hKE : K ≤ E)
    (hE : ExactCRT.IsExactEq S (i := ()) E.val) :
    ExactCRT.IsExactEq (actualQuotientSource S H K) (i := ())
      (quotientColourEq S H K E hKE).val := by
  letI := originalQuotientAction S H K
  obtain ⟨D,hD⟩ := hE
  let π : ∀ _ : Unit, M → Quotient K.val := fun _ => Quotient.mk''
  have hker : ∀ i : Unit, GroupActions.kernel (π i) = evaluate S B.words := by
    intro i
    funext x y
    exact propext (Quotient.eq.trans (Iff.of_eq (congrFun (congrFun hB x) y)).symm)
  have hSat : saturate (evaluate S B.words) (evaluate S D.words)
      (evaluate S B.words) = evaluate S D.words := by
    rw [hB,hD]
    exact equivalence_saturated S K E hKE
  let hTI := fun word (_hw : word ∈ D.words) => ExactCRT.oneSort_wordTI S H (fun _ => B) word
  refine ⟨ExactCRT.descendExact S (actualQuotientSource S H K) H
    (semanticCCO_change_universe S cco) π (fun _ => Quotient.mk''_surjective)
    (fun _ => quotient_projection_equivariant S H K) (fun _ => B) hker
    (actualQuotientSource_colour_orbital S H K) D hSat hTI,?_⟩
  rw [ExactCRT.descendExact_relation,hD]
  funext q r
  apply propext
  induction q using Quotient.inductionOn with | _ x =>
    induction r using Quotient.inductionOn with | _ y =>
      rw [quotientColourEq_projection]
      constructor
      · rintro ⟨a,b,ha,hb,hab⟩
        exact E.val.trans (E.val.trans (hKE (K.val.symm (Quotient.exact ha))) hab)
          (hKE (Quotient.exact hb))
      · intro hxy
        exact ⟨x,y,rfl,rfl,hxy⟩

include cco B hB in
/-- C05: exactness agrees in BOTH directions of the full invariant interval. -/
theorem quotientColourEq_exact_iff (E : ColourEq S ()) (hKE : K ≤ E) :
    ExactCRT.IsExactEq (actualQuotientSource S H K) (i := ())
      (quotientColourEq S H K E hKE).val ↔ ExactCRT.IsExactEq S (i := ()) E.val := by
  constructor
  · intro h
    have hp := quotientPullback_exact S H cco K B hB _ h
    have he : quotientPullback S H K (quotientColourEq S H K E hKE) = E :=
      congrArg Subtype.val ((quotientColourInterval S H K).symm_apply_apply ⟨E,hKE⟩)
    rwa [he] at hp
  · exact quotientColourEq_exact S H cco K B hB E hKE

end CCO.MIGeometry
