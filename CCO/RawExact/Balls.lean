import CCO.RawExact.Presentations
import CCO.RawSource

/-!
# RAW C11: the exact orientation of heterogeneous balls

All relations are actual equality-inclusive typed predicates. The pair
criterion is unconditional: exactness and CCO enter only when upgrading
pairwise nonempty balls to a single common point (RAW C13).
-/

universe u v

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}

/-- A ball has its centre on the RIGHT of a typed RAW relation. -/
def ball {i j : ι} (D : TRel X i j) (b : X j) : Set (X i) :=
  {x | D x b}

/-- RAW C11: the witness is a point of the common target sort.
Neither converse factor may be omitted, even when centre sorts differ. -/
theorem ball_pair_criterion {i j k : ι}
    (D : TRel X i j) (F : TRel X i k)
    (b : X j) (c : X k) :
    (ball D b ∩ ball F c).Nonempty ↔
      TRel.comp (TRel.converse D) F b c :=
  Iff.rfl

/-- A heterogeneous indexed family: the exact pairwise condition that
the later C13 Helly theorem needs to consume. No common witness is claimed. -/
theorem pairwise_ball_criterion {I : Type*} {i : ι}
    (centreSort : I → ι)
    (D : ∀ t : I, TRel X i (centreSort t))
    (centres : ∀ t : I, X (centreSort t)) :
    (∀ s t : I, s ≠ t →
      (ball (D s) (centres s) ∩ ball (D t) (centres t)).Nonempty) ↔
    (∀ s t : I, s ≠ t →
      TRel.comp (TRel.converse (D s)) (D t)
        (centres s) (centres t)) := by
  constructor
  · intro h s t hst
    exact (ball_pair_criterion (D s) (D t)
      (centres s) (centres t)).mp (h s t hst)
  · intro h s t hst
    exact (ball_pair_criterion (D s) (D t)
      (centres s) (centres t)).mpr (h s t hst)

/-- C11 singleton boundary: every nonempty invariant RAW relation
has a nonempty ball at every actual centre in a homogeneous source. -/
theorem ball_nonempty_of_homogeneous
    (S : AtomicSource ι X)
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {i j : ι} (D : TRel X i j)
    (hD : TRel.Nonempty D)
    (hInv : TRel.Invariant (G := G) D)
    (b : X j) :
    (ball D b).Nonempty := by
  obtain ⟨x, hx⟩ := S.raw_coserial_of_homogeneous H D hD hInv b
  exact ⟨x, hx⟩

end CCO.RawExact
