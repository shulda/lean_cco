import CCO.ExactCRT.SameSortDescent
import CCO.RawExact.CanonicalQuotients

/-! A source-complete actual quotient instantiation. Every carrier is the
literal quotient of its original carrier by its displayed full exact setoid;
the quotient actions, equivariance and all kernel identities are constructed. -/
universe u v w t
namespace CCO.ExactCRT.CanonicalTyped
open RawExact
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀i, MulAction G (X i)]
variable (H : HomogeneousSource S G)
variable (J : ∀i, Setoid (X i)) (E : ∀i, NonemptyExact S i i)
variable (represents : ∀i, evaluate S (E i).words = (J i).r)

/-- Exactness itself supplies kernel invariance under every original motion. -/
def invariant (i : ι) : RawExact.CanonicalQuotients.Invariant G (J i) where
  invariant g x y hxy := by
    rw [← represents i] at hxy ⊢
    exact presentation_invariant_of_homogeneous S H (E i).words g x y hxy

@[instance_reducible] def action (i : ι) : MulAction G (Quotient (J i)) := by
  letI : RawExact.CanonicalQuotients.Invariant G (J i) := invariant S H J E represents i
  infer_instance

def projection (i : ι) : X i → Quotient (J i) := Quotient.mk''

theorem projection_surjective (i : ι) : Function.Surjective (projection J i) :=
  Quotient.mk''_surjective

include represents in
theorem projection_kernel (i : ι) :
    GroupActions.kernel (projection J i) = evaluate S (E i).words := by
  rw [represents i]
  funext x y
  exact propext Quotient.eq

theorem projection_equivariant :
    letI : ∀i, MulAction G (Quotient (J i)) := action S H J E represents
    ∀i (g : G) x, projection J i (g • x) = g • projection J i x := by
  intro i g x
  rfl

/-- The actual finite complete orbital language of the literal quotients. -/
noncomputable def source : AtomicSource ι (fun i => Quotient (J i)) := by
  letI := S.finiteSort
  letI : ∀i, MulAction G (Quotient (J i)) := action S H J E represents
  exact TypedPalette.source (fun i => Quotient (J i)) S H id (projection J)
    (projection_surjective J) (projection_equivariant S H J E represents)

/-- C24 over literal quotient carriers. The only additional criterion is
TI on the supplied old presentation; all action/palette providers are proved. -/
theorem typed_exact_descent (cco : SemanticCCO.{u,v,max u v,w} S)
    {i j : ι} (D : NonemptyExact S i j)
    (hSat : saturate (evaluate S (E i).words) (evaluate S D.words)
      (evaluate S (E j).words) = evaluate S D.words)
    (hTI : ∀ word, word ∈ D.words → WordTI S (fun i => evaluate S (E i).words) word) :
    ∃ F : NonemptyExact (source S H J E represents) i j,
      evaluate (source S H J E represents) F.words =
        quotientRelation (projection J i) (projection J j) (evaluate S D.words) := by
  letI : ∀i, MulAction G (Quotient (J i)) := action S H J E represents
  exact actual_typed_exact_descent S H cco (projection J) (projection_surjective J)
    (projection_equivariant S H J E represents) E
    (projection_kernel S J E represents) D hSat hTI

/-- The converse literal quotient full exact pullback is unconditional on
TI and uses the same constructed actions and actual orbital language. -/
noncomputable def exactPullback (cco : SemanticCCO.{u,v,max u v,w} S)
    {i j : ι} (D : NonemptyExact (source S H J E represents) i j) :
    NonemptyExact S i j := by
  letI : ∀i, MulAction G (Quotient (J i)) := action S H J E represents
  exact actualQuotientExactPullback S H cco (projection J) (projection_surjective J)
    (projection_equivariant S H J E represents) E
    (projection_kernel S J E represents) D

theorem exactPullback_relation (cco : SemanticCCO.{u,v,max u v,w} S)
    {i j : ι} (D : NonemptyExact (source S H J E represents) i j) :
    evaluate S (exactPullback S H J E represents cco D).words =
      GroupActions.pullback (projection J i) (projection J j)
        (evaluate (source S H J E represents) D.words) := by
  letI : ∀i, MulAction G (Quotient (J i)) := action S H J E represents
  exact actualQuotientExactPullback_relation S H cco (projection J) (projection_surjective J)
    (projection_equivariant S H J E represents) E
    (projection_kernel S J E represents) D

end CCO.ExactCRT.CanonicalTyped

namespace CCO.ExactCRT.CanonicalTyped
open RawExact

/-- C22 over literal one-sort quotients. Original invariant commutation
supplies TI, while the source containment and saturation are retained. -/
theorem same_sort_exact_descent {Y : Unit → Type v}
    (S : AtomicSource.{0,v,w} Unit Y)
    {G : Type t} [Group G] [∀i, MulAction G (Y i)]
    (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
    (J : ∀i, Setoid (Y i)) (E : ∀i, NonemptyExact S i i)
    (represents : ∀i, evaluate S (E i).words = (J i).r)
    {i : Unit} (D : NonemptyExact S i i)
    (_hContainment : ∀ x y, evaluate S (E i).words x y → evaluate S D.words x y)
    (hSat : saturate (evaluate S (E i).words) (evaluate S D.words)
      (evaluate S (E i).words) = evaluate S D.words) :
    ∃ F : NonemptyExact (source S H J E represents) i i,
      evaluate (source S H J E represents) F.words =
        quotientRelation (projection J i) (projection J i) (evaluate S D.words) := by
  apply typed_exact_descent S H J E represents cco D hSat
  intro word _
  exact oneSort_wordTI S H E word

end CCO.ExactCRT.CanonicalTyped
