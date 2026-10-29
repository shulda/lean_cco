import CCO.Owners.Master.SourceCRT

/-! The source-level simultaneous master interface.  Its clauses refer
directly to every actual exact quotient of one finite REAL carrier; no
finite-diagram callback or source representation remains in the output. -/

universe v w t z
namespace CCO.Owners.Master
noncomputable section
open RawExact ExactCRT Provider Product

section ImageQuotients
variable {A : Type v} {G : Type t} [Group G] [MulAction G A]
variable (B : Set A) (E F : Setoid A)
variable [CanonicalQuotients.Invariant G E] [CanonicalQuotients.Invariant G F]

def exactImageOver (hEF : E ≤ F)
    (x : (Quotient.mk'' : A → Quotient E) '' B) :
    Abstract.quotientMap hEF x.val ∈ (Quotient.mk'' : A → Quotient F) '' B := by
  obtain ⟨a,ha,he⟩ := x.property
  exact ⟨a,ha,congrArg (Abstract.quotientMap hEF) he⟩

theorem exactImageOnto (hEF : E ≤ F) :
    Function.Surjective (ownerProjection (Abstract.quotientMap hEF)
      ((Quotient.mk'' : A → Quotient E) '' B)
      ((Quotient.mk'' : A → Quotient F) '' B) (exactImageOver B E F hEF)) := by
  intro y
  obtain ⟨a,ha,he⟩ := y.property
  exact ⟨⟨Quotient.mk'' a,⟨a,ha,rfl⟩⟩,Subtype.ext he⟩

/-- Natural full finite quotient action on actual projection images.
The proof applies also to empty images. -/
def exactImageQuotient (hEF : E ≤ F) :
    OrbitalQuotient (G := G)
      (Subtype.val : ((Quotient.mk'' : A → Quotient E) '' B) → Quotient E)
      (Subtype.val : ((Quotient.mk'' : A → Quotient F) '' B) → Quotient F) :=
  inducedQuotient (Abstract.quotientMap hEF) (Product.quotientMap_equivariant hEF)
    _ _ (exactImageOver B E F hEF) (exactImageOnto B E F hEF)

theorem exactImage_m3_of_carriers (hEF : E ≤ F)
    (D : Set (Quotient E)) (C : Set (Quotient F))
    (hD : (Quotient.mk'' : A → Quotient E) '' B = D)
    (hC : (Quotient.mk'' : A → Quotient F) '' B = C)
    (over : ∀ x : D, Abstract.quotientMap hEF x.val ∈ C)
    (onto : Function.Surjective (ownerProjection (Abstract.quotientMap hEF) D C over))
    (m3 : Function.Surjective
        (inducedQuotient (G := G) (Abstract.quotientMap hEF) (Product.quotientMap_equivariant hEF)
          D C over onto).action ∧
      GroupActions.FibreTransitive
        (inducedQuotient (G := G) (Abstract.quotientMap hEF) (Product.quotientMap_equivariant hEF)
          D C over onto).action (ownerProjection (Abstract.quotientMap hEF) D C over)) :
    Function.Surjective (exactImageQuotient (G := G) B E F hEF).action ∧
      GroupActions.FibreTransitive (exactImageQuotient (G := G) B E F hEF).action
        (exactImageQuotient (G := G) B E F hEF).projection := by
  subst D
  subst C
  exact m3
end ImageQuotients

variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A] [Countable A]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)

local instance actualInvariant (E : Exact S H cco) : CanonicalQuotients.Invariant G E.val :=
  Product.exactInvariant S H cco E

structure ActualMaster (T : Set A) where
  carrier : Set A
  finite : carrier.Finite
  contains : T ⊆ carrier
  nonempty : carrier.Nonempty
  eppa : ∀ E : Exact S H cco,
    EPPAFor (G := G)
      (ι := (Subtype.val : ((Quotient.mk'' : A → Quotient E.val) '' carrier) → Quotient E.val))
      {x | x.val ∈ (Quotient.mk'' : A → Quotient E.val) '' T}
  closed : ∀ E : Exact S H cco,
    FullPacketClosed (quotientSource S H cco E) (quotientSource_homogeneous S H cco E)
      ((Quotient.mk'' : A → Quotient E.val) '' carrier)
  m3 : ∀ (E F : Exact S H cco) (hEF : E ≤ F),
    Function.Surjective (exactImageQuotient (G := G) carrier E.val F.val hEF).action ∧
      GroupActions.FibreTransitive (exactImageQuotient (G := G) carrier E.val F.val hEF).action
        (exactImageQuotient (G := G) carrier E.val F.val hEF).projection
  m4 : ∀ {I : Type z} [Fintype I] (E : I → Exact S H cco),
    Function.Bijective (FiniteImages.coordinates carrier (fun i => (E i).val))

variable {T : Set A} (D : SourceStage.{v,w,t,z} S H cco T Finset.univ)

/-- Final exact-image export C24. The existence proof of the complete
stage supplies its hypotheses separately; none is hidden in `ActualMaster`. -/
def SourceStage.actualMaster : ActualMaster.{v,w,t,z} S H cco T where
  carrier := realCarrier S H cco D
  finite := realCarrier_finite S H cco D
  contains := realCarrier_contains S H cco D
  nonempty := realCarrier_nonempty S H cco D
  eppa E := by
    obtain ⟨V,hV,hE⟩ : ∃ V, IsUpset V ∧ coordinateKernel S H cco V = E :=
      ⟨exactPositions S H cco E,exactPositions_upset S H cco E,
        coordinateKernel_exactPositions S H cco E⟩
    subst E
    change EPPAFor (G := G)
      (ι := (Subtype.val :
        (coordinateProjection S H cco V '' realCarrier S H cco D) → Coordinate S H cco V))
      {x | x.val ∈ originalShadow S H cco T V}
    rw [realCarrier_image S H cco D V hV]
    exact D.decorations.eppa V hV (Finset.subset_univ _)
  closed E := by
    obtain ⟨V,hV,hE⟩ : ∃ V, IsUpset V ∧ coordinateKernel S H cco V = E :=
      ⟨exactPositions S H cco E,exactPositions_upset S H cco E,
        coordinateKernel_exactPositions S H cco E⟩
    subst E
    change FullPacketClosed (quotientSource S H cco (coordinateKernel S H cco V))
      (quotientSource_homogeneous S H cco (coordinateKernel S H cco V))
      (coordinateProjection S H cco V '' realCarrier S H cco D)
    rw [realCarrier_image S H cco D V hV]
    exact D.decorations.closed V hV (Finset.subset_univ _)
  m3 E F hEF := by
    obtain ⟨V,hV,hE⟩ : ∃ V, IsUpset V ∧ coordinateKernel S H cco V = E :=
      ⟨exactPositions S H cco E,exactPositions_upset S H cco E,
        coordinateKernel_exactPositions S H cco E⟩
    obtain ⟨W,hW,hF⟩ : ∃ W, IsUpset W ∧ coordinateKernel S H cco W = F :=
      ⟨exactPositions S H cco F,exactPositions_upset S H cco F,
        coordinateKernel_exactPositions S H cco F⟩
    subst E
    subst F
    have hWV : W ⊆ V := (coordinateKernel_le_iff S H cco V W hV hW).mp hEF
    have hVI : (Quotient.mk'' : A → Quotient (coordinateKernel S H cco V).val) ''
        realCarrier S H cco D = D.finite.B V := realCarrier_image S H cco D V hV
    have hWI : (Quotient.mk'' : A → Quotient (coordinateKernel S H cco W).val) ''
        realCarrier S H cco D = D.finite.B W := realCarrier_image S H cco D W hW
    apply exactImage_m3_of_carriers (realCarrier S H cco D) _ _ hEF
      (D.finite.B V) (D.finite.B W) hVI hWI
      (fun x => D.finite.mapsTo hV hW (Finset.subset_univ V) hWV x.val x.property)
      (D.finite.r_surjective hV hW (Finset.subset_univ V) hWV)
    exact D.decorations.m3 hV hW (Finset.subset_univ V) hWV
  m4 E := realCarrier_family_bijective S H cco D E

end
end CCO.Owners.Master
