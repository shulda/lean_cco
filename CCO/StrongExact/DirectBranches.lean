import CCO.StrongExact.ThetaVertices
import CCO.StrongExact.HellyConvolution

/-!
# C07: duplicate direct branches in the strong theta construction

A one-letter positive profile is a literal atomic singleton. If the
whole family of positive profiles is pairwise intersecting, ALL
one-letter branches therefore have the same original typed fine atom.
The theta graph must record only ONE root-to-root edge for these
repeated direct branches: separate parallel coloured edges or
artificial two-cycles are not legal in the B001 simple-diagram API.

This small fact is fully independent of SAP, CCO, and unproved word
Helly. The remaining cycle classification concerns two different
simple private paths in the merged graph.
-/

universe u v a

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u, v, a} ι X)
variable {i j : ι}

/-- Pairwise profile intersection, including self-pairs, with one
fixed and genuinely typed ordered pair of endpoint sorts. -/
def PairwiseWordProfiles (ws : List (PositiveWord S i j)) : Prop :=
  ∀ p ∈ ws, ∀ q ∈ ws,
    (PositiveWord.profile S p ∩
      PositiveWord.profile S q).Nonempty

/-- The last needed edge-unicity fact before encoding the theta
diagram as a simple (not parallel-edge) partial diversity diagram:
any two literal direct root-to-root branches have the same atom. -/
theorem pairwise_direct_branch_atoms_equal
    (ws : List (PositiveWord S i j))
    (hPair : PairwiseWordProfiles S ws)
    (a b : S.Atom i j)
    (ha : (PositiveWord.single a : PositiveWord S i j) ∈ ws)
    (hb : (PositiveWord.single b : PositiveWord S i j) ∈ ws) :
    a = b := by
  obtain ⟨c, hcA, hcB⟩ := hPair (.single a) ha (.single b) hb
  have hca : c = a := by
    simpa only [PositiveWord.profile, Set.mem_singleton_iff] using hcA
  have hcb : c = b := by
    simpa only [PositiveWord.profile, Set.mem_singleton_iff] using hcB
  exact hca.symm.trans hcb

/-- The root direct-edge atom is an actual survivor of every positive
profile whenever it occurs as a one-letter path in a pairwise
intersecting family. This lets the graph constructor choose that
edge consistently with every longer private path. -/
theorem direct_branch_atom_in_every_profile
    (ws : List (PositiveWord S i j))
    (hPair : PairwiseWordProfiles S ws)
    (a : S.Atom i j)
    (ha : (PositiveWord.single a : PositiveWord S i j) ∈ ws)
    (w : PositiveWord S i j) (hw : w ∈ ws) :
    a ∈ PositiveWord.profile S w := by
  obtain ⟨c, hcA, hcW⟩ := hPair (.single a) ha w hw
  have hca : c = a := by
    simpa only [PositiveWord.profile, Set.mem_singleton_iff] using hcA
  simpa only [hca] using hcW

/-- A full C07 Helly subcase: whenever one of the pairwise-
intersecting positive word profiles is a SINGLE old atom, that atom
already belongs to every other profile. Thus their finite total
intersection is nonempty, without invoking CCO or SAP. For the hard
theta argument one may hence restrict to branches of length at least
two; there are then no duplicate direct edges at all. -/
theorem wordHelly_of_direct_branch
    (ws : List (PositiveWord S i j))
    (hPair : PairwiseWordProfiles S ws)
    (a : S.Atom i j)
    (ha : (PositiveWord.single a : PositiveWord S i j) ∈ ws) :
    (present S ws).Nonempty := by
  refine ⟨a, ?_⟩
  intro w hw
  exact direct_branch_atom_in_every_profile S ws hPair a ha w hw

end CCO.StrongExact
