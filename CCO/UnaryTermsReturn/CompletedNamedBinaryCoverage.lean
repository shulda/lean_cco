import CCO.UnaryTermsReturn.CompletedNamedBinaryCylinders

/-!
# B052 D05/C14: actual exhaustive real/hidden binary cylinder reading

Every ordered pair of DISTINCT vertices in the literal original real or
represented-proper-FULL-MI quotient carrier receives an actual B049 finite
semantic-cylinder label. The old-real diagonal is logical equality, not a
diversity cylinder. All mixed-sort and orphan hidden quotient cases use
the same literal source coordinate and the actual old SAP (only where
needed for a proper quotient fibre). No quotient-age SAP, hidden
homogeneity, artificial equality atom or unrelated group orbit is used.

The final theorem specializes the full one-generated diagram transfer
to this CONCRETE finite cylinder language. The partial-source witness
still has to preserve ALL these actual binary predicates; it is not
silently reduced to a cardinality-only or unary-only hypothesis.
-/

universe u v w t p

namespace CCO.UnaryTermsReturn

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open CCO.TransitionClosure
open CCO.ParityHasse.Original

/-- Every pair of distinct original REAL points receives a genuine
full old representative-cylinder name. Both endpoints may belong to
different named original sorts. -/
theorem original_completed_real_real_binary_exists
    (H : HomogeneousSource S G)
    {i j : ι} (x : X i) (y : X j)
    (hne : (Sum.inl (⟨i,x⟩ : Sigma X) :
        OriginalCompletedNamedCarrier S H) ≠
        Sum.inl (⟨j,y⟩ : Sigma X)) :
    ∃ name : OriginalCompletedCylinderBinaryName S H,
      originalCompletedActualBinary S H name
        (.inl (⟨i,x⟩ : Sigma X))
        (.inl (⟨j,y⟩ : Sigma X)) := by
  have hTag : (⟨i,x⟩ : Sigma X) ≠ ⟨j,y⟩ := by
    intro e
    exact hne (congrArg
      (fun z : Sigma X => (Sum.inl z : OriginalCompletedNamedCarrier S H)) e)
  obtain ⟨a,ha⟩ := S.some_colour_of_ne x y hTag
  let q : Quotient (⊥ : ColourEq S i).val :=
    Quotient.mk (⊥ : ColourEq S i).val x
  let r : Quotient (⊥ : ColourEq S j).val :=
    Quotient.mk (⊥ : ColourEq S j).val y
  have hSpectrum : (originalTypedQuotientPairSpectrum S
        (⊥ : ColourEq S i) (⊥ : ColourEq S j) q r).Nonempty := by
    exact ⟨a,x,y,rfl,rfl,ha⟩
  obtain ⟨P, ⟨hP,hSem⟩, _⟩ :=
    originalTypedCylinderSemanticRelation_unique S H
      (⊥ : ColourEq S i) (⊥ : ColourEq S j) q r hSpectrum
  let name : OriginalCompletedCylinderBinaryName S H :=
    ⟨⟨i, .inl ()⟩, ⟨j, .inl ()⟩, ⟨P,hP⟩⟩
  refine ⟨name, ?_⟩
  exact ⟨hne, q, r, .real x, .real y, hSem⟩

/-- A genuine old real source and an actual represented hidden
quotient target receive the correct finite B049 mixed cylinder. -/
theorem original_completed_real_hidden_binary_exists
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι} (x : X i)
    (D : OriginalNamedHiddenCoordinate S H j)
    (r : Quotient D.val.val) :
    ∃ name : OriginalCompletedCylinderBinaryName S H,
      originalCompletedActualBinary S H name
        (.inl (⟨i,x⟩ : Sigma X))
        (originalCompletedNamedHiddenNode S H D r) := by
  let q : Quotient (⊥ : ColourEq S i).val :=
    Quotient.mk (⊥ : ColourEq S i).val x
  obtain ⟨P, ⟨hP,hSem⟩, _⟩ :=
    original_real_hidden_pair_cylinder_unique S H sap D q r
  let name : OriginalCompletedCylinderBinaryName S H :=
    ⟨⟨i, .inl ()⟩, ⟨j, .inr D⟩, ⟨P,hP⟩⟩
  have hne : (Sum.inl (⟨i,x⟩ : Sigma X) :
      OriginalCompletedNamedCarrier S H) ≠
      originalCompletedNamedHiddenNode S H D r := by
    intro e
    cases e
  refine ⟨name, ?_⟩
  exact ⟨hne, q, r, .real x, .hidden D r, hSem⟩

/-- The reverse mixed direction keeps the genuine old hidden
quotient source and the literal real equality target. -/
theorem original_completed_hidden_real_binary_exists
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι}
    (D : OriginalNamedHiddenCoordinate S H i)
    (q : Quotient D.val.val) (y : X j) :
    ∃ name : OriginalCompletedCylinderBinaryName S H,
      originalCompletedActualBinary S H name
        (originalCompletedNamedHiddenNode S H D q)
        (.inl (⟨j,y⟩ : Sigma X)) := by
  let r : Quotient (⊥ : ColourEq S j).val :=
    Quotient.mk (⊥ : ColourEq S j).val y
  obtain ⟨P, ⟨hP,hSem⟩, _⟩ :=
    original_hidden_real_pair_cylinder_unique S H sap D q r
  let name : OriginalCompletedCylinderBinaryName S H :=
    ⟨⟨i, .inr D⟩, ⟨j, .inl ()⟩, ⟨P,hP⟩⟩
  have hne : originalCompletedNamedHiddenNode S H D q ≠
      (Sum.inl (⟨j,y⟩ : Sigma X) :
        OriginalCompletedNamedCarrier S H) := by
    intro e
    cases e
  refine ⟨name, ?_⟩
  exact ⟨hne, q, r, .hidden D q, .real y, hSem⟩

/-- Two DISTINCT actual represented quotient vertices always
receive an old full-spectrum cylinder, including different original
sorts and the same original sort at different proper kernels. -/
theorem original_completed_hidden_hidden_binary_exists
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι}
    (D : OriginalNamedHiddenCoordinate S H i)
    (q : Quotient D.val.val)
    (E : OriginalNamedHiddenCoordinate S H j)
    (r : Quotient E.val.val)
    (hne : originalCompletedNamedHiddenNode S H D q ≠
      originalCompletedNamedHiddenNode S H E r) :
    ∃ name : OriginalCompletedCylinderBinaryName S H,
      originalCompletedActualBinary S H name
        (originalCompletedNamedHiddenNode S H D q)
        (originalCompletedNamedHiddenNode S H E r) := by
  obtain ⟨P, ⟨hP,hSem⟩, _⟩ :=
    original_named_hidden_pair_cylinder_unique S H sap D E q r
  let name : OriginalCompletedCylinderBinaryName S H :=
    ⟨⟨i, .inr D⟩, ⟨j, .inr E⟩, ⟨P,hP⟩⟩
  refine ⟨name, ?_⟩
  exact ⟨hne, q, r, .hidden D q, .hidden E r, hSem⟩

/-- Source10 full actual terminal binary coverage for EVERY
ordered pair of distinct real/represented-hidden vertices.
This is the genuine finite cylinder language, not the strictly
finer original-G-orbital language on quotient pairs. -/
theorem original_completed_distinct_pair_binary_exists
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (a b : OriginalCompletedNamedCarrier S H) (hne : a ≠ b) :
    ∃ name : OriginalCompletedCylinderBinaryName S H,
      originalCompletedActualBinary S H name a b := by
  cases a with
  | inl v =>
      obtain ⟨i,x⟩ := v
      cases b with
      | inl w =>
          obtain ⟨j,y⟩ := w
          exact original_completed_real_real_binary_exists S H x y hne
      | inr w =>
          obtain ⟨j,D,q,hw⟩ :=
            original_completed_hidden_value_has_named_witness S H w
          rw [hw]
          exact original_completed_real_hidden_binary_exists S H sap x D q
  | inr v =>
      obtain ⟨i,D,q,hv⟩ :=
        original_completed_hidden_value_has_named_witness S H v
      rw [hv] at hne ⊢
      cases b with
      | inl w =>
          obtain ⟨j,y⟩ := w
          exact original_completed_hidden_real_binary_exists S H sap D q y
      | inr w =>
          obtain ⟨j,E,r,hw⟩ :=
            original_completed_hidden_value_has_named_witness S H w
          rw [hw] at hne ⊢
          exact original_completed_hidden_hidden_binary_exists
            S H sap D q E r hne

/-- The concrete actual cylinder palette discharges the BINARY
interpretation parameter of C14. Unary-admissibility must still
supply for EVERY root an isomorphism of the FULL one-generated
induced diagram, preserving every cylinder, every named unary
symbol and literal equality. No arbitrary partial source obtains
this witness automatically. -/
theorem original_completed_cylinder_admissible_uniform
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    {P : Type p}
    (partialStep : OriginalCompletedPrimitiveSymbol S H → P → P → Prop)
    (partialBinary : OriginalCompletedCylinderBinaryName S H →
      P → P → Prop)
    (hAdmissible : OriginalCompletedFullyUnaryAdmissible S H sap nr2
      partialStep partialBinary (originalCompletedActualBinary S H))
    (x : P) :
    (partialNamedClosure partialStep x).ncard ≤
      originalSourceUniformNormalCodeBudget S H := by
  exact original_completed_fully_unary_admissible_uniform
    S H sap nr2 partialStep partialBinary
    (originalCompletedActualBinary S H) hAdmissible x

end CCO.UnaryTermsReturn
