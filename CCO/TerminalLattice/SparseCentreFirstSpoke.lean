import CCO.TerminalLattice.PositiveFiniteChain
import CCO.TerminalLattice.ProjectedOrientedWords
import CCO.TerminalLattice.SparseCycleUsedWords

/-!
# B050 C27: a genuine centre spoke before the closing projected edge

The true B002 compression is an injectively enumerated cyclic list of
actual marked roots. When the unique LAST centre occurs among these
marked vertices, some incidence with it is necessarily among the
first n edges of any n+1 cyclic numbering (n>=2), independently of
the location of the centre. There is no need to silently rotate a
cycle or insert a missing graph pair.

The actual source sparse-word selection then forces this very used
edge to be labelled by the genuine ORIGINAL positive K° spoke, and
its original same-sort STRONG profile is unchanged when traversed
in reverse. This is the exact combinatorial input to the verified
centre-spoke path saturation theorem.
-/

universe u v w t

namespace CCO.TerminalLattice

/-- Exact finite cyclic geometry: if the centre is visited by a
nontrivial cyclic numbering of length n+1, one of the FIRST n
successor edges is incident with it. For a centre not at the last
index, use the outgoing edge; for a centre at the last index, use
its genuine predecessor edge. The latter requires n>0, not an
invented cycle orientation. -/
theorem original_finite_centre_incident_before_last
    {α : Type*} {n : Nat} (hn : 0 < n)
    (vertices : Fin (n+1) → α) (centre : α)
    (hCentre : ∃ p : Fin (n+1), vertices p = centre) :
    ∃ k : Fin n,
      vertices k.castSucc = centre ∨
      vertices (CCO.cyclicNext (Nat.succ_pos n) k.castSucc) = centre := by
  obtain ⟨p,hp⟩ := hCentre
  by_cases hLast : p = Fin.last n
  · let k : Fin n := ⟨n-1, by omega⟩
    refine ⟨k, Or.inr ?_⟩
    rw [original_cyclicNext_castSucc hn k]
    have hk : k.succ = (Fin.last n) := Fin.ext (by
      dsimp [k]
      omega)
    rw [hk]
    simpa only [hLast] using hp
  · have hNotLast : p.val ≠ n := by
      intro hv
      exact hLast (Fin.ext hv)
    let k : Fin n := ⟨p.val, by have hpLt := p.isLt; omega⟩
    have hIndex : k.castSucc = p := Fin.ext rfl
    exact ⟨k, Or.inl (by rw [hIndex]; exact hp)⟩

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

/-- C27 ACTUAL original sparse-star projective geometry. Given an
actual B002 compressed marked projection of the ONE constructed OLD
finite private-word network, if the centre is present, at least one
edge among the first n of its n+1 genuine consecutive edges has
exactly the source-prescribed positive centre-spoke word.

Every index/edge here is an actual B002 marked-edge identifier,
not a synthetic W edge. The length equality only reindexes the
true projected finite cycle as n+1 so its LAST closing edge can be
removed for a separate STRONG path spectrum. -/
theorem oldSparseWordDiagram_projected_prior_spoke
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {q r g n : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (spoke : PositiveWord S i i)
    (words : Fin r → PositiveWord S i i)
    (C : SimpleCycle (oldSparseWordDiagram S H sap W spoke words))
    (B : CCO.RawExact.QuotientExpansion.MarkedProjection
      S (fun _ : Fin (W.size+1) => i)
      (oldOptionalPositivePresentations S
        (oldSparseWordSelection S W spoke words))
      (oldOptionalPositivePresentations_nonempty S H sap
        (oldSparseWordSelection S W spoke words)) C)
    (hLength : B.length = n+1)
    (hCentre : ∃ p : Fin B.length,
      B.vertices p = oldSparseCentre W) :
    ∃ k : Fin n,
      oldSparseWordSelection S W spoke words
        (B.edges (Fin.cast hLength.symm k.castSucc)) = some spoke := by
  let vertices : Fin (n+1) → Fin (W.size+1) :=
    fun p => B.vertices (Fin.cast hLength.symm p)
  have hVisit : ∃ p : Fin (n+1),
      vertices p = oldSparseCentre W := by
    obtain ⟨p,hp⟩ := hCentre
    refine ⟨Fin.cast hLength p, ?_⟩
    change B.vertices
        (Fin.cast hLength.symm (Fin.cast hLength p)) =
          oldSparseCentre W
    simpa only [Fin.cast_cast, Fin.cast_refl] using hp
  have hn : 0 < n := by
    have hh := B.length_ge_three
    omega
  obtain ⟨k,hInc⟩ :=
    original_finite_centre_incident_before_last hn
      vertices (oldSparseCentre W) hVisit
  let t : Fin B.length := Fin.cast hLength.symm k.castSucc
  have hIncident :
      B.vertices t = oldSparseCentre W ∨
      B.vertices (CCO.cyclicNext B.length_pos t) = oldSparseCentre W := by
    rcases hInc with hHere | hAfter
    · exact Or.inl hHere
    · right
      have hNext :
          CCO.cyclicNext B.length_pos t =
            Fin.cast hLength.symm
              (CCO.cyclicNext (Nat.succ_pos n) k.castSucc) := by
        apply Fin.ext
        change (k.val+1) % B.length = (k.val+1) % (n+1)
        rw [hLength]
      rw [hNext]
      exact hAfter
  exact ⟨k, oldSparseWordDiagram_projected_centre_step_word
    S H sap W spoke words C B t hIncident⟩

/-- The previously proved original word reversal preserves the exact
old STRONG spectrum of this specifically selected centre spoke.
Thus at least one complementary projected edge has precisely the
original spoke's entire menu, even when the cyclic traversal uses
the opposite orientation of its canonical root-to-centre word.

This does not yet assert every OTHER projected menu lies in K°;
the original label-specific positive words supply that separately.
-/
theorem oldSparseWordDiagram_projected_prior_spoke_profile
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {q r g n : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (spoke : PositiveWord S i i)
    (words : Fin r → PositiveWord S i i)
    (C : SimpleCycle (oldSparseWordDiagram S H sap W spoke words))
    (B : CCO.RawExact.QuotientExpansion.MarkedProjection
      S (fun _ : Fin (W.size+1) => i)
      (oldOptionalPositivePresentations S
        (oldSparseWordSelection S W spoke words))
      (oldOptionalPositivePresentations_nonempty S H sap
        (oldSparseWordSelection S W spoke words)) C)
    (hLength : B.length = n+1)
    (hCentre : ∃ p : Fin B.length,
      B.vertices p = oldSparseCentre W) :
    ∃ k : Fin n,
      PositiveWord.profile S
        (oldProjectedOrientedWord S H sap
          (oldSparseWordSelection S W spoke words) C B
          (Fin.cast hLength.symm k.castSucc)) =
        PositiveWord.profile S spoke := by
  obtain ⟨k,hSelected⟩ :=
    oldSparseWordDiagram_projected_prior_spoke
      S H sap W spoke words C B hLength hCentre
  let t : Fin B.length := Fin.cast hLength.symm k.castSucc
  have hCanonical :
      oldProjectedCanonicalWord S H sap
        (oldSparseWordSelection S W spoke words) C B t = spoke := by
    apply Option.some.inj
    calc
      some (oldProjectedCanonicalWord S H sap
          (oldSparseWordSelection S W spoke words) C B t) =
          oldSparseWordSelection S W spoke words (B.edges t) :=
        (oldProjectedCanonicalWord_selected S H sap
          (oldSparseWordSelection S W spoke words) C B t).symm
      _ = some spoke := hSelected
  refine ⟨k, ?_⟩
  calc
    PositiveWord.profile S
        (oldProjectedOrientedWord S H sap
          (oldSparseWordSelection S W spoke words) C B t) =
      PositiveWord.profile S
        (oldProjectedCanonicalWord S H sap
          (oldSparseWordSelection S W spoke words) C B t) :=
      oldProjectedOrientedWord_profile S H sap
        (oldSparseWordSelection S W spoke words) C B t
    _ = PositiveWord.profile S spoke := by rw [hCanonical]

end CCO.TerminalLattice
