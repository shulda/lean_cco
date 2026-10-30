import CCO.FullPhaseLift.BinarySource.MarkedComparisonAge

/-! The chosen B047 marked pair source supplies genuine whole tuple
motions for the literal old-name/bit code table. The group used here is
the whole marked PAIR limit group; no full-language motion is inferred. -/

universe m t
namespace CCO.FullPhaseLift.BinarySource.MarkedComparison
open Canonical APCharacter OwnerTransversal.CountableColour RigidGroupoid.Geometry
open APCharacter.SourceAge.UnarySource
noncomputable section
variable {L : Signature} {M : Type m} (U : BoolTable L M) (hsym : SameSortSymmetric U)
variable {G : Type t} [Group G] [∀ i, MulAction G (Canonical.Carrier U i)]
variable {H : HomogeneousSource (Canonical.source U hsym) G}
variable {C : ExactCalculus (Canonical.source U hsym)} {a : UnaryName U}
variable {K : Kernel (Canonical.source U hsym) a}
variable (P : SourcePhase (Canonical.source U hsym) H C K)
variable (cco : SemanticCCO.{0,m,m,0} (Canonical.source U hsym))
variable (I : Identification (Canonical.source U hsym) H (P.completion_property cco))

theorem childLabel_of_target_owner {p q : NewPoint I}
    (h : (targetTable U hsym P cco I).owner p = (targetTable U hsym P cco I).owner q) :
    childLabel I p.1 = childLabel I q.1 := by
  rw [target_owner,target_owner] at h
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun s : Profile L 1 × Bit => s.1) h
  · exact congrArg (fun s : Profile L 1 × Bit => s.2) h

theorem oldColours_of_target_colour {p q r s : NewPoint I}
    (h : (targetTable U hsym P cco I).colour p q = (targetTable U hsym P cco I).colour r s) :
    taggedColour (Canonical.source U hsym) (oldEquiv I p) (oldEquiv I q) =
      taggedColour (Canonical.source U hsym) (oldEquiv I r) (oldEquiv I s) := by
  apply tagCode_injective U
  simpa only [target_colour] using h

theorem target_motions : TupleMotions (targetTable U hsym P cco I) := by
  intro n p q ho hc
  let coding := Age.limitCoding (Canonical.source U hsym) H (P.completion_property cco)
  let left : Fin n → Age.Limit (Canonical.source U hsym) H (P.completion_property cco) :=
    newEquiv I ∘ p
  let right : Fin n → Age.Limit (Canonical.source U hsym) H (P.completion_property cco) :=
    newEquiv I ∘ q
  have heq : ∀ x y, left x = left y ↔ right x = right y := by
    intro x y
    change newEquiv I (p x) = newEquiv I (p y) ↔ newEquiv I (q x) = newEquiv I (q y)
    rw [(newEquiv I).injective.eq_iff,(newEquiv I).injective.eq_iff,
      p.injective.eq_iff,q.injective.eq_iff]
  have howner : ∀ x, coding.table.owner (left x) = coding.table.owner (right x) := by
    intro x
    change coding.table.owner (newEquiv I (p x)) = coding.table.owner (newEquiv I (q x))
    rw [new_owner,new_owner,childLabel_of_target_owner U hsym P cco I (ho x)]
  have hcolour : ∀ x y, coding.table.colour (left x) (left y) = coding.table.colour (right x) (right y) := by
    intro x y
    change coding.table.colour (newEquiv I (p x)) (newEquiv I (p y)) =
      coding.table.colour (newEquiv I (q x)) (newEquiv I (q y))
    rw [new_colour,new_colour,erase_tagged,erase_tagged,
      oldColours_of_target_colour U hsym P cco I (hc x y)]
  obtain ⟨g,hg⟩ := Age.tuple_homogeneous (Canonical.source U hsym) H (P.completion_property cco)
    left right heq howner hcolour
  let e : NewPoint I ≃ NewPoint I := ((newEquiv I).trans g.toEquiv).trans (newEquiv I).symm
  have image (x : NewPoint I) : newEquiv I (e x) = g (newEquiv I x) :=
    (newEquiv I).apply_symm_apply _
  have names := coding.embedding_preserves coding g.toEmbedding
  refine ⟨e,?_,?_,?_⟩
  · intro x
    have h := names.1 (newEquiv I x)
    change coding.table.owner (g (newEquiv I x)) = coding.table.owner (newEquiv I x) at h
    rw [← image,new_owner,new_owner] at h
    have hh := (Age.ownerEquiv (Canonical.source U hsym)).injective h
    rw [target_owner,target_owner,hh]
  · intro x y
    have h := names.2 (newEquiv I x) (newEquiv I y)
    change coding.table.colour (g (newEquiv I x)) (g (newEquiv I y)) =
      coding.table.colour (newEquiv I x) (newEquiv I y) at h
    rw [← image,← image,new_colour,new_colour,erase_tagged,erase_tagged] at h
    have hh := (Age.colourEquiv (Canonical.source U hsym)).injective h
    rw [target_colour,target_colour,hh]
  · intro x
    apply (newEquiv I).injective
    exact (image (p x)).trans (hg x)

end
end CCO.FullPhaseLift.BinarySource.MarkedComparison
