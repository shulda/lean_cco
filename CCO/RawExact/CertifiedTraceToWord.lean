import CCO.RawExact.LabelledRealTrace
import CCO.RawExact.TypedChain

/-!
# B002 RAW C12/C13: recover a genuine represented word from a certified trace

The exact diversity-step certificate of a RAW word, together with
its literal original-sort trace, determines an actual `WordPath`.
Conversely, every already-realized word supplies that certificate.

This bridge is crucial after source CCO completes an anchored
private fan: the CCO homomorphism gives a real point at every
formal position and preserves all recorded genuine atomic letters.
The bridge then recovers the equality-inclusive RAW relation at
the two endpoints WITHOUT assuming its output pair is diverse.

All original logical identity LETTERS contribute zero edges and
are retained by the word's inductive semantics.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- A true colour-certified trace with the original RAW word's
named sort sequence reconstructs exactly one actual path witness,
including genuine identity letters and possibly diagonal outputs. -/
theorem wordPath_of_certified_sort_trace
    {i j : ι}
    (word : RawWord S i j)
    (points : List (Sigma X))
    (hCert : TypedWalkCertificate S points (rawAtomicSteps S word))
    (hSort : points.map Sigma.fst = wordSortTrace S word) :
    ∃ (x : X i) (y : X j)
      (path : WordPath S word x y),
      realWalkTrace S path = points := by
  induction word generalizing points with
  | nil i =>
      cases hCert with
      | singleton p =>
          rcases p with ⟨k, z⟩
          have hk : k = i := by
            have hList : [k] = [i] := by
              simpa only [List.map_cons, List.map_nil, wordSortTrace] using hSort
            exact (List.cons.inj hList).1
          subst k
          exact ⟨z, z, WordPath.nil z, rfl⟩
  | identity tail ih =>
      obtain ⟨x, y, path, hTrace⟩ :=
        ih points hCert (by simpa only [wordSortTrace] using hSort)
      refine ⟨x, y, WordPath.identity path, ?_⟩
      simpa only [realWalkTrace] using hTrace
  | atom a tail ih =>
      cases hCert with
      | step x middle b hEdge hRest =>
          obtain ⟨y, z, path, hTrace⟩ :=
            ih _ hRest (by
              simpa only [List.map_cons, wordSortTrace,
                List.cons.injEq, true_and] using hSort)
          have hTraceKeep := hTrace
          obtain ⟨remaining, hCons⟩ := realWalkTrace_cons S path
          rw [hCons] at hTrace
          have hMiddle : middle = y := by
            have hFirst := (List.cons.inj hTrace).1
            have hEq : (⟨_, middle⟩ : Sigma X) = ⟨_, y⟩ :=
              hFirst.symm
            simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using hEq
          subst middle
          refine ⟨x, z, WordPath.atom a hEdge path, ?_⟩
          simpa only [realWalkTrace, hTraceKeep]

end CCO.RawExact
