import CCO.RawExact.AtomicExact
import CCO.RawExact.ConvolutionFromHelly
import CCO.RawExact.Saturation

/-!
# B002 C14: full-exact saturation from actual RAW convolution

Convolving exact equivalences with a genuinely realized atomic orbital
preserves exact word-presentability, but this needs the real C09
convolution theorem. We keep the C13 heterogeneous ball-Helly provider
visible until its original CCO proof is fully discharged. All predicates
are equality-inclusive; the original identity orbital is available as
a genuine zero-letter exact word.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- The finite exact presentation of E ; R ; K is built by TWO real
word convolutions, without inventing a formal quotient atom. -/
def exactSaturation
    {G : Type*} [Group G] [∀ p : ι, MulAction G (X p)]
    (H : HomogeneousSource S G)
    {i j : ι}
    (E : NonemptyExact S i i) (R : NonemptyExact S i j)
    (K : NonemptyExact S j j) :
    NonemptyExact S i j :=
  convolutionExact S H (convolutionExact S H E R) K

theorem exactSaturation_relation
    {G : Type*} [Group G] [∀ p : ι, MulAction G (X p)]
    (H : HomogeneousSource S G)
    (hHelly : HeterogeneousExactBallHelly S)
    {i j : ι}
    (E : NonemptyExact S i i) (R : NonemptyExact S i j)
    (K : NonemptyExact S j j) :
    evaluate S (exactSaturation S H E R K).words =
      saturate (evaluate S E.words) (evaluate S R.words)
        (evaluate S K.words) := by
  change evaluate S (convolutionExact S H
      (convolutionExact S H E R) K).words =
    TRel.comp
      (TRel.comp (evaluate S E.words) (evaluate S R.words))
      (evaluate S K.words)
  rw [convolutionExact_represents S H hHelly
        (convolutionExact S H E R) K]
  rw [convolutionExact_represents S H hHelly E R]

/-- C14 actual quotient-orbital exactness with no conditional
representation theorem hidden: the ONLY remaining providers are
the genuine exact presentations of both actual kernel equivalences,
the original realized pair orbit, and real heterogeneous ball Helly.
The accompanying orbit equality uses B001's actual diagonal action. -/
theorem exact_actual_orbit_pullback_of_helly
    {G : Type*} [Group G] [∀ p : ι, MulAction G (X p)]
    {i j : ι} {Q R : Type*}
    [MulAction G Q] [MulAction G R]
    (H : HomogeneousSource S G)
    (hHelly : HeterogeneousExactBallHelly S)
    (τ : X i → Q) (σ : X j → R)
    (equivτ : ∀ (g : G) x, τ (g • x) = g • τ x)
    (equivσ : ∀ (g : G) y, σ (g • y) = g • σ y)
    (E : NonemptyExact S i i) (K : NonemptyExact S j j)
    (hE : GroupActions.kernel τ = evaluate S E.words)
    (hK : GroupActions.kernel σ = evaluate S K.words)
    (a : X i) (b : X j)
    (A : NonemptyExact S i j)
    (hA : evaluate S A.words =
      GroupActions.orbital (G := G) a b) :
    ∃ D : NonemptyExact S i j,
      evaluate S D.words =
        GroupActions.pullback τ σ
          (GroupActions.orbital (G := G) (τ a) (σ b)) := by
  let D := exactSaturation S H E A K
  refine ⟨D, ?_⟩
  calc
    evaluate S D.words =
        saturate (evaluate S E.words) (evaluate S A.words)
          (evaluate S K.words) :=
      exactSaturation_relation S H hHelly E A K
    _ = saturate (GroupActions.kernel τ)
          (GroupActions.orbital (G := G) a b)
          (GroupActions.kernel σ) := by rw [hE, hK, hA]
    _ = GroupActions.pullback τ σ
          (GroupActions.orbital (G := G) (τ a) (σ b)) :=
      (equivariant_orbit_pullback τ σ equivτ equivσ a b).symm

end CCO.RawExact
