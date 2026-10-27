import CCO.PairHomogeneity
import CCO.StrongExact.CycleCompletion

/-!
# Independent triangle-fullness preparation: homogeneous fan extension

This lemma uses literal fine-colour pair homogeneity of the ACTUAL
source, rather than SAP, a selected quotient, an assumed generic
triangle completion, or any STRONG identity. It supplies the atomic
one-step extension used by the classical AP cycle-fan proof.

The general triangle-fullness statement from AP+CCO is not asserted
here until its finite cycle-fan induction is formalized.
-/

universe u v w

namespace CCO.AtomicSource

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u, v, w} ι X)
variable {i j k : ι}
variable {G : Type*} [Group G] [∀ q : ι, MulAction G (X q)]

/-- Gluing one triangle onto an ALREADY REALIZED complete root edge
without changing either endpoint. Homogeneity alone (in particular no
SAP) transports a triangle witness to those two literal root points.
The third point must be distinct from each because its two incident
edges are genuine diversity atoms, even for repeated named sorts. -/
theorem triangle_fan_step_of_homogeneous
    (H : HomogeneousSource S G)
    (a : S.Atom i j) (b : S.Atom j k) (c : S.Atom i k)
    (htri : S.Triangle a b c)
    (root : X i) (last : X j)
    (hroot : S.colour root last = some a) :
    ∃ next : X k,
      S.colour last next = some b ∧
      S.colour root next = some c := by
  obtain ⟨x, y, z, hxy, hyz, hxz⟩ := htri
  obtain ⟨g, hgx, hgy⟩ :=
    (S.pair_homogeneous_of_homogeneous H)
      x root y last (hxy.trans hroot.symm)
  refine ⟨g • z, ?_, ?_⟩
  · calc
      S.colour last (g • z) =
          S.colour (g • y) (g • z) := by rw [hgy]
      _ = S.colour y z :=
        S.colourInvariant_of_homogeneous H g y z
      _ = some b := hyz
  · calc
      S.colour root (g • z) =
          S.colour (g • x) (g • z) := by rw [hgx]
      _ = S.colour x z :=
        S.colourInvariant_of_homogeneous H g x z
      _ = some c := hxz

end CCO.AtomicSource
