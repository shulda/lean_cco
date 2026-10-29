import CCO.OwnerTransversal.TypedLifting
import CCO.Owners.Product.SparseDescent
import CCO.Owners.Provider.FiniteBase
import CCO.Owners.Provider.ExactLift
import CCO.AclOwners.QuotientSource

/-! Conditional transfer retains BOTH source assumptions: ordinary EPPA
of the actual exact quotient, and common-witness Gamma_B-EPPA for every
finite actual named-owner age.  It asserts no unconditional source EPPA. -/
universe v w t
namespace CCO.OwnerTransversal
noncomputable section
open ParityHasse.Original FinitePackets.Normalization Owners.Product Owners.Provider
open AclOwners
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable (E : ColourEq S ())

/-- The actual quotient of an arbitrary sparse finite real input.
Neither its partial domain nor its range is replaced by a full preimage. -/
def actualOwnerProjection (A : Set M) :
    letI := originalQuotientAction S H E
    OrbitalQuotient (G := G) (Subtype.val : A → M)
      (Subtype.val : (Quotient.mk'' '' A : Set (Quotient E.val)) → Quotient E.val) := by
  letI := originalQuotientAction S H E
  exact {
  ambient := Quotient.mk''
  equivariant := quotient_projection_equivariant S H E
  projection x := ⟨Quotient.mk'' x.val,⟨x.val,x.property,rfl⟩⟩
  surjective y := by
    obtain ⟨x,hx,hxy⟩ := y.property
    exact ⟨⟨x,hx⟩,Subtype.ext hxy⟩
  target_injective := Subtype.val_injective
  commutes _ := rfl }

/-- C17: the descended domain is EXACTLY the image of the original
partial domain, and the induced partial map is injective and orbital. -/
theorem projected_domain_exact (A : Set M)
    (p : OrbitalPartial (G := G) (Subtype.val : A → M)) :
    letI := originalQuotientAction S H E
    ((actualOwnerProjection S H E A).projectedPartial p).domain =
      (actualOwnerProjection S H E A).projection '' p.domain := rfl

/-- Gamma_B fixes every literal original colour and permutes only the
actual owner predicates. One common W precedes ALL (p,gamma) requests,
including empty real domains with their ENTIRE prescribed gamma. -/
def GammaEPPA (B : Set (Quotient E.val)) : Prop :=
  letI := originalQuotientAction S H E
  ∀ (A : Set M), A.Finite → ∀ overA : ∀ x : A, (Quotient.mk'' x.val : Quotient E.val) ∈ B,
    ∃ W : Set M, W.Finite ∧ ∃ overW : ∀ w : W, (Quotient.mk'' w.val : Quotient E.val) ∈ B,
      ∃ e : A ↪ W,
        (∀ x y : A, GroupActions.orbital (G := G) x.val y.val (e x).val (e y).val) ∧
        (∀ x : A, (Quotient.mk'' (e x).val : Quotient E.val) = Quotient.mk'' x.val) ∧
        ∀ (p : OrbitalPartial (G := G) (Subtype.val : A → M))
          (gamma : OrbitalAut G (Quotient E.val) (Subtype.val : B → Quotient E.val)),
          (∀ x : p.domain, (Quotient.mk'' (p.map x).val : Quotient E.val) =
            (gamma.val ⟨Quotient.mk'' x.val.val,overA x.val⟩).val) →
          ∃ beta : OrbitalAut G M (Subtype.val : W → M),
            (∀ x : p.domain, beta.val (e x.val) = e (p.map x)) ∧
            (∀ w : W, (Quotient.mk'' (beta.val w).val : Quotient E.val) =
              (gamma.val ⟨Quotient.mk'' w.val,overW w⟩).val)

/-- C18: first choose ONE quotient witness B, then its gamma_p choices,
then ONE typed witness W extending ALL compatible requests. -/
theorem conditional_eppa_transfer [Countable M]
    (cco : SemanticCCO.{0,v,0,w} S)
    (hE : ExactCRT.IsExactEq S (i := ()) E.val)
    (quotientEPPA : letI := originalQuotientAction S H E
      OrdinaryEPPA G (Quotient E.val))
    (typedEPPA : ∀ B : Set (Quotient E.val), B.Finite → GammaEPPA S H E B) :
    OrdinaryEPPA G M := by
  classical
  letI := originalQuotientAction S H E
  intro A hA
  obtain ⟨presentation,hpresentation⟩ := hE
  have QH := actualQuotient_homogeneous S H E presentation hpresentation cco
  have qhom : OrbitalHomogeneous G (Quotient E.val) :=
    source_orbital_homogeneous (actualQuotientSource S H E) QH
  obtain ⟨B,hB,hAB,hall⟩ := eppa_over_original qhom quotientEPPA
    (Quotient.mk'' '' A : Set (Quotient E.val)) (hA.image Quotient.mk'')
  have overA (x : A) : (Quotient.mk'' x.val : Quotient E.val) ∈ B := hAB ⟨x.val,x.property,rfl⟩
  obtain ⟨W,hW,overW,e,he,_,hext⟩ := typedEPPA B hB A hA overA
  refine ⟨W,hW,e,he,?_⟩
  intro p
  let Q := actualOwnerProjection S H E A
  obtain ⟨gamma,hgamma⟩ := hall (Q.projectedPartial p)
  have compatible (x : p.domain) : (Quotient.mk'' (p.map x).val : Quotient E.val) =
      (gamma.val ⟨Quotient.mk'' x.val.val,overA x.val⟩).val := by
    have hh := hgamma ⟨Q.projection x.val,⟨x.val,x.property,rfl⟩⟩
    have hp := Q.partial_projection p x
    exact (congrArg Subtype.val hp).symm.trans hh.symm
  obtain ⟨beta,hbeta,_⟩ := hext p gamma compatible
  exact ⟨beta,hbeta⟩

end
end CCO.OwnerTransversal
