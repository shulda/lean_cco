import CCO.ExactEPGeometry.TraceProduct

/-!
# B062 / C44, C47: genuinely realized AP-character type supports

A support is existential over real pairs in the homogeneous marked age.
The phase mask is not baked into its definition.  Its legality is recovered
from the real finite-age pair code, including the logical diagonal.

The exact-meet theorem is guarded by a NONEMPTY original exact intersection
and realizes both endpoint child names in the ACTUAL marked limit. It is the
one-step C47 instance; arbitrary-prefix iteration remains separate.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter RigidGroupoid.Geometry
noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G)

/-- The support of an actual old relation between two genuine child types,
read using the FULL unary/old-orbital coding of the marked Fraïssé limit. -/
def stageSupport
    {C : ExactCalculus S} {r : ι} {A : Kernel S r}
    (P : SourcePhase S H C A) (cco : SemanticCCO.{u,v,max u v,w} S)
    {i j : ι} (R : TRel X i j) (ε η : Bit) : Prop :=
  ∃ a b : Age.Limit S H (P.completion_property cco),
    markedTrace S H (P.completion_property cco) R ε η a b

/-- Realized child labels satisfy exactly the ACTUAL character validity
predicate. Derive it from the original diagonal of a real marked point
and the finite source-chart mask legality, not from an assumed label. -/
theorem validBit_of_realized_child
    {C : ExactCalculus S} {r : ι} {A : Kernel S r}
    (P : SourcePhase S H C A) (cco : SemanticCCO.{u,v,max u v,w} S)
    (i : ι) (ε : Bit)
    (a : Age.Limit S H (P.completion_property cco))
    (hOwner : (Age.limitCoding S H (P.completion_property cco)).table.owner a =
      Age.ownerEquiv S (i,ε)) :
    P.validBit i ε := by
  have hdiag :=
    marked_diagonal_of_owner S H (P.completion_property cco) a i ε hOwner
  have hallowed : P.allows (S.colour (Classical.choice (S.nonemptySort i))
      (Classical.choice (S.nonemptySort i))) ε ε := by
    have hn : S.colour (Classical.choice (S.nonemptySort i))
        (Classical.choice (S.nonemptySort i)) = none :=
      (S.colour_none_iff _ _).mpr rfl
    rw [hn]
    exact limit_pair_colour_allowed S H (P.completion_property cco)
      a a ε ε none hOwner hOwner hdiag
  exact hallowed.1

/-- Monotonicity retains the old actual orbital witness and both real
marked endpoints, without postulating a new current orbit action. -/
theorem stageSupport_mono
    {C : ExactCalculus S} {r : ι} {A : Kernel S r}
    (P : SourcePhase S H C A) (cco : SemanticCCO.{u,v,max u v,w} S)
    {i j : ι} {R T : TRel X i j} (ε η : Bit)
    (hRT : ∀ x y, R x y → T x y) :
    stageSupport S H P cco R ε η → stageSupport S H P cco T ε η := by
  rintro ⟨a,b,ha,hb,x,y,hxy,hcode⟩
  exact ⟨a,b,ha,hb,x,y,hRT x y hxy,hcode⟩

/-- Union of source relations is exactly union of the ACTUAL marked pair
supports; no exactness/CCO theorem is needed beyond defining the genuine age. -/
theorem stageSupport_union
    {C : ExactCalculus S} {r : ι} {A : Kernel S r}
    (P : SourcePhase S H C A) (cco : SemanticCCO.{u,v,max u v,w} S)
    {i j : ι} (R T : TRel X i j) (ε η : Bit) :
    stageSupport S H P cco (fun x y => R x y ∨ T x y) ε η ↔
      stageSupport S H P cco R ε η ∨
      stageSupport S H P cco T ε η := by
  constructor
  · rintro ⟨a,b,ha,hb,x,y,hxy,hcode⟩
    rcases hxy with h | h
    · exact Or.inl ⟨a,b,ha,hb,x,y,h,hcode⟩
    · exact Or.inr ⟨a,b,ha,hb,x,y,h,hcode⟩
  · rintro (⟨a,b,ha,hb,x,y,hxy,hcode⟩ | ⟨a,b,ha,hb,x,y,hxy,hcode⟩)
    · exact ⟨a,b,ha,hb,x,y,Or.inl hxy,hcode⟩
    · exact ⟨a,b,ha,hb,x,y,Or.inr hxy,hcode⟩

/-- A genuine real marked pair witnesses the opposite old relation in
reverse: its reversed colour is forced by the SAME real old chart and
original symmetric fine-colour involution. -/
theorem markedTrace_reverse
    {M : MaskData S} (completion : Age.CompletionProperty S M)
    {i j : ι} (R : TRel X i j) (ε η : Bit)
    (a b : Age.Limit S H completion)
    (h : markedTrace S H completion R ε η a b) :
    markedTrace S H completion (TRel.converse R) η ε b a := by
  obtain ⟨ha,hb,x,y,hxy,hCode⟩ := h
  obtain ⟨p,q,hPQ,hQP⟩ := marked_pair_chart_codes S H completion a b
  have hSame : taggedColour S p q =
      taggedColour S (⟨i,x⟩ : Sigma X) ⟨j,y⟩ :=
    (Age.colourEquiv S).injective (hPQ.symm.trans hCode)
  have hSwap := tagged_colour_reverse_eq S p q
    (⟨i,x⟩ : Sigma X) ⟨j,y⟩ hSame
  exact ⟨hb,ha,y,x,hxy,
    hQP.trans (congrArg (Age.colourEquiv S) hSwap)⟩

/-- Actual marked type support respects converse for arbitrary old
relations, even if the chosen pairs are on their genuine diagonal. -/
theorem stageSupport_converse
    {C : ExactCalculus S} {r : ι} {A : Kernel S r}
    (P : SourcePhase S H C A) (cco : SemanticCCO.{u,v,max u v,w} S)
    {i j : ι} (R : TRel X i j) (ε η : Bit) :
    stageSupport S H P cco (TRel.converse R) η ε ↔
      stageSupport S H P cco R ε η := by
  constructor
  · rintro ⟨b,a,h⟩
    exact ⟨a,b,markedTrace_reverse S H (P.completion_property cco)
      (TRel.converse R) η ε b a h⟩
  · rintro ⟨a,b,h⟩
    exact ⟨b,a,markedTrace_reverse S H (P.completion_property cco)
      R ε η a b h⟩

/-- Guarded exact finite meet support on two REALIZED marked child types.
The whole original old intersection must have an actual pair; nothing is
asserted for empty old atomic meets. This is the one-step C47 instance. -/
theorem stageSupport_exactFamily_iff
    {C : ExactCalculus S} {r : ι} {A : Kernel S r}
    (P : SourcePhase S H C A) (cco : SemanticCCO.{u,v,max u v,w} S)
    {i j : ι} (L : List (RawExact.NonemptyExact S i j))
    (ε η : Bit)
    (hOld : TRel.Nonempty (rawExactFamily S L))
    (ha : ∃ a : Age.Limit S H (P.completion_property cco),
      (Age.limitCoding S H (P.completion_property cco)).table.owner a =
        Age.ownerEquiv S (i,ε))
    (hb : ∃ b : Age.Limit S H (P.completion_property cco),
      (Age.limitCoding S H (P.completion_property cco)).table.owner b =
        Age.ownerEquiv S (j,η)) :
    stageSupport S H P cco (rawExactFamily S L) ε η ↔
      ∀ d ∈ L, stageSupport S H P cco
        (RawExact.evaluate S d.words) ε η := by
  constructor
  · intro h d hd
    apply stageSupport_mono S H P cco ε η _ h
    intro x y hxy
    exact hxy d hd
  · intro h
    obtain ⟨a,hA⟩ := ha
    obtain ⟨b,hB⟩ := hb
    have hv : P.validBit i ε :=
      validBit_of_realized_child S H P cco i ε a hA
    have hw : P.validBit j η :=
      validBit_of_realized_child S H P cco j η b hB
    exact marked_exact_meet_prime (S := S) (H := H) P cco L ε η
      hv hw hOld h

end
end CCO.ExactEPGeometry
