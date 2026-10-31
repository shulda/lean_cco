import CCO.ExactEPGeometry.MarkedEquivalences

/-!
# B062 / C30: actual one-character-step exact-equivalence joins

An original pair of equality-inclusive RAW exact equivalences has a
represented exact product by the accepted ORIGINAL CCO convolution provider.
The old symmetric homogeneous group action makes that product the actual
original equivalence join. In the real marked-age child, the marked trace
of that product is EXACTLY the product of the two marked traces: the
input trace nonemptiness needed for C22 is proved by the real current
reflexive diagonal. No SAP, hypothetical child action or arbitrary
quotient exact-descent assumption is used.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter RigidGroupoid.Geometry
noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G)

/-- C30 exact one-step TP on actual child carrier. In a real nonempty
marked child, reflexivity witnesses BOTH input trace nonemptiness
hypotheses required by the genuine AP-only source C22. -/
theorem markedChild_exact_comp_iff
    {C : ExactCalculus S} {r : ι} {A : Kernel S r}
    (P : SourcePhase S H C A)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i : ι} (D E : RawExact.NonemptyExact S i i)
    (hD : RawSymmetric.EquivRel (RawExact.evaluate S D.words))
    (hE : RawSymmetric.EquivRel (RawExact.evaluate S E.words))
    (ε : Bit)
    (a c : MarkedChild S H (P.completion_property cco) i ε) :
    markedChildRelation S H (P.completion_property cco)
        (TRel.comp (RawExact.evaluate S D.words)
          (RawExact.evaluate S E.words)) ε a c ↔
      ∃ b : MarkedChild S H (P.completion_property cco) i ε,
        markedChildRelation S H (P.completion_property cco)
          (RawExact.evaluate S D.words) ε a b ∧
        markedChildRelation S H (P.completion_property cco)
          (RawExact.evaluate S E.words) ε b c := by
  have hCurrentD : RawSymmetric.EquivRel
      (markedChildRelation S H (P.completion_property cco)
        (RawExact.evaluate S D.words) ε) :=
    markedChild_exact_equiv S H P cco D hD ε
  have hCurrentE : RawSymmetric.EquivRel
      (markedChildRelation S H (P.completion_property cco)
        (RawExact.evaluate S E.words) ε) :=
    markedChild_exact_equiv S H P cco E hE ε
  have hInputD : ∃ x y : Age.Limit S H (P.completion_property cco),
      markedTrace S H (P.completion_property cco) (RawExact.evaluate S D.words)
        ε ε x y := ⟨a.val, a.val, hCurrentD.refl a⟩
  have hInputE : ∃ x y : Age.Limit S H (P.completion_property cco),
      markedTrace S H (P.completion_property cco) (RawExact.evaluate S E.words)
        ε ε x y := ⟨a.val, a.val, hCurrentE.refl a⟩
  have hTP :=
    marked_trace_product S H P cco D E ε ε ε hInputD hInputE a.val c.val
  constructor
  · intro h
    obtain ⟨b, hAB, hBC⟩ := hTP.mpr h
    exact ⟨⟨b,hAB.2.1⟩,hAB,hBC⟩
  · rintro ⟨b,hAB,hBC⟩
    exact hTP.mp ⟨b.val,hAB,hBC⟩

/-- The OLD full exact product is an equivalence and its universal
original join, by original invariant pair flips, not a quotient action. -/
section OriginalJoin
include H

theorem original_exact_comp_join
    {i : ι} (D E : RawExact.NonemptyExact S i i)
    (hD : RawSymmetric.EquivRel (RawExact.evaluate S D.words))
    (hE : RawSymmetric.EquivRel (RawExact.evaluate S E.words)) :
    RawSymmetric.EquivRel
      (TRel.comp (RawExact.evaluate S D.words) (RawExact.evaluate S E.words)) ∧
    (∀ x y, RawExact.evaluate S D.words x y →
      TRel.comp (RawExact.evaluate S D.words) (RawExact.evaluate S E.words) x y) ∧
    (∀ x y, RawExact.evaluate S E.words x y →
      TRel.comp (RawExact.evaluate S D.words) (RawExact.evaluate S E.words) x y) ∧
    (∀ K : X i → X i → Prop, RawSymmetric.EquivRel K →
      (∀ x y, RawExact.evaluate S D.words x y → K x y) →
      (∀ x y, RawExact.evaluate S E.words x y → K x y) →
      ∀ x y, TRel.comp (RawExact.evaluate S D.words)
        (RawExact.evaluate S E.words) x y → K x y) := by
  have h := S.same_sort_join_of_homogeneous H
    (RawExact.evaluate S D.words) (RawExact.evaluate S E.words)
    hD hE (RawExact.presentation_invariant_of_homogeneous S H D.words)
    (RawExact.presentation_invariant_of_homogeneous S H E.words)
  exact h

end OriginalJoin

/-- A complete actual one-stage current child has the genuine product
of two old exact equivalence traces as its LEAST upper equivalence bound.
The result is not a postulated current lattice homomorphism: the
minimality follows from an actual marked middle point and (TP).
Exactness of the *current* resulting profile is a separate source
C23–C27 obligation and is NOT inserted into this conclusion. -/
theorem markedChild_exact_comp_join
    {C : ExactCalculus S} {r : ι} {A : Kernel S r}
    (P : SourcePhase S H C A)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i : ι} (D E : RawExact.NonemptyExact S i i)
    (hD : RawSymmetric.EquivRel (RawExact.evaluate S D.words))
    (hE : RawSymmetric.EquivRel (RawExact.evaluate S E.words))
    (ε : Bit) :
    let R := markedChildRelation S H (P.completion_property cco)
      (RawExact.evaluate S D.words) ε
    let T := markedChildRelation S H (P.completion_property cco)
      (RawExact.evaluate S E.words) ε
    let J := markedChildRelation S H (P.completion_property cco)
      (TRel.comp (RawExact.evaluate S D.words)
        (RawExact.evaluate S E.words)) ε
    RawSymmetric.EquivRel J ∧
      (∀ a b, R a b → J a b) ∧
      (∀ a b, T a b → J a b) ∧
      (∀ K, RawSymmetric.EquivRel K →
        (∀ a b, R a b → K a b) →
        (∀ a b, T a b → K a b) →
        ∀ a b, J a b → K a b) := by
  dsimp
  have hOld := original_exact_comp_join S H D E hD hE
  have hFull : FullExact S
      (TRel.comp (RawExact.evaluate S D.words)
        (RawExact.evaluate S E.words)) :=
    C.comp ⟨D, rfl⟩ ⟨E, rfl⟩
  obtain ⟨F,hF⟩ := hFull
  have hEqF : RawSymmetric.EquivRel (RawExact.evaluate S F.words) := by
    rw [hF]
    exact hOld.1
  have hCurrentF :
      RawSymmetric.EquivRel
        (markedChildRelation S H (P.completion_property cco)
          (TRel.comp (RawExact.evaluate S D.words)
            (RawExact.evaluate S E.words)) ε) := by
    rw [← hF]
    exact markedChild_exact_equiv S H P cco F hEqF ε
  refine ⟨hCurrentF, ?_, ?_, ?_⟩
  · intro a b h
    obtain ⟨ha,hb,x,y,hxy,hcode⟩ := h
    exact ⟨ha,hb,x,y,hOld.2.1 x y hxy,hcode⟩
  · intro a b h
    obtain ⟨ha,hb,x,y,hxy,hcode⟩ := h
    exact ⟨ha,hb,x,y,hOld.2.2.1 x y hxy,hcode⟩
  · intro K hK hR hT a c hJ
    obtain ⟨b,hAB,hBC⟩ :=
      (markedChild_exact_comp_iff S H P cco D E hD hE ε a c).mp hJ
    exact hK.trans a b c (hR a b hAB) (hT b c hBC)

end
end CCO.ExactEPGeometry
