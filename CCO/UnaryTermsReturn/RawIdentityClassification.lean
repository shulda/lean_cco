import CCO.UnaryTermsReturn.NormalizedKernels
import CCO.TransitionClosure.OriginalIdentityTransport

/-!
# B052 C10/C39: source-tight original RAW identity dichotomy

An original old-G invariant nonempty typed RAW relation either
contains a genuine old diversity fine atom, or every one of its
actual edges is the *logical* original tagged diagonal. The
latter cannot link two distinct named original sorts. If it
contains one same-sort diagonal edge, transitivity makes the
ENTIRE original diagonal part present.

These facts concern the WHOLE literal RAW relation (including
equality), not an artificial STRONG equality atom. They are the
exact two cases in which the NORMAL canonical B040 map will
be realized by one genuine named atomic transition or the
ALREADY NAMED quotient identity, respectively.
-/

universe u v w t

namespace CCO.UnaryTermsReturn

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open CCO.TransitionClosure
open CCO.ParityHasse.Original

/-- No actually realized OLD fine diversity atom in an
original RAW invariant relation means every actual R-edge
is the literal tagged original identity. No original age
assumption, hidden quotient SAP, or positivity argument
enters this elementary diversity/identity classification. -/
theorem original_raw_no_diversity_edges_are_real_identity
    {i j : ι}
    (R : OriginalNonemptyInvariantTypedRel
      (X := X) (G := G) i j)
    (hNo : ¬ (S.diversityGuard R.val.val).Nonempty) :
    ∀ x : X i, ∀ y : X j,
      R.val.val x y →
        (⟨i,x⟩ : Sigma X) = ⟨j,y⟩ := by
  intro x y hR
  by_contra hneq
  obtain ⟨a,hAtom⟩ := S.some_colour_of_ne x y hneq
  exact hNo ⟨a,x,y,hR,hAtom⟩

/-- A genuinely NONEMPTY original RAW relation with no diversity
edges can exist only on one and the same ORIGINAL named sort.
Its existence is not inferred from an empty product. -/
theorem original_raw_no_diversity_same_sort
    {i j : ι}
    (R : OriginalNonemptyInvariantTypedRel
      (X := X) (G := G) i j)
    (hNo : ¬ (S.diversityGuard R.val.val).Nonempty) :
    i = j := by
  obtain ⟨x,y,hxy⟩ := R.property
  exact congrArg Sigma.fst
    (original_raw_no_diversity_edges_are_real_identity
      S R hNo x y hxy)

/-- A single actual diagonal pair of a same-sort invariant RAW
relation forces EVERY real diagonal pair by the ACTUAL original
homogeneous ambient group. This uses transitivity on the
original sort, not quotient-reduct homogeneity. -/
theorem original_raw_one_diagonal_implies_all
    (H : HomogeneousSource S G)
    {i : ι}
    (R : OriginalNonemptyInvariantTypedRel
      (X := X) (G := G) i i)
    (hSome : ∃ x : X i, R.val.val x x) :
    ∀ y : X i, R.val.val y y := by
  obtain ⟨x,hxx⟩ := hSome
  intro y
  obtain ⟨g,hg⟩ :=
    S.original_sort_transitive_of_homogeneous H i x y
  have hMoved := R.val.property g x x hxx
  simpa only [hg] using hMoved

end CCO.UnaryTermsReturn
