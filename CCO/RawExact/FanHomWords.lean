import CCO.RawExact.FanHomTraceColours
import CCO.RawExact.FanHomTraceEndpoints
import CCO.RawExact.WalkColourReconstruction
import Lean.Elab.Tactic.Omega

/-!
# Genuine RAW words in a completed private fan

The source homomorphism's points along each private path carry the same
sort trace and atomic letters as a real reference walk. Reconstruction
therefore gives the original RAW relation between the displayed root
and centre images, including all logical identity letters and possible
diagonal outputs of positive words.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {root : ι} {I : Type (max u v)} [Finite I]
variable {sort : I → ι}

/-- Every positive-diversity word occurrence is realized from the
single completed root to its marked centre image. -/
theorem privateFanHom_word_relation
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (hPair : ∀ p q : I,
      (ball (evaluate S (D p).words) (centres p) ∩
        ball (evaluate S (D q).words) (centres q)).Nonempty)
    (f : DiagramHom (privateFanFullDiagram S H D centres))
    (o : WordOccurrence S D)
    (hPositive : 0 < diversityLength S (occurrenceWord S D o)) :
    RawWord.relation S (occurrenceWord S D o)
      (f.point (privateFanRoot S D centres))
      (f.point (privateFanCentre S D centres (toDistinctCentre sort centres o.1))) := by
  obtain ⟨x, y, path, hTrace⟩ := wordPath_of_same_real_trace_colours S
    (occurrenceWord S D o) (referenceOccurrenceWalk S H D centres o).2
    (privateFanHomWordTrace S H D centres f o)
    (privateFanHomWordTrace_sorts S H D centres f o)
    (privateFanHomWordTrace_colours S H D centres hPair f o)
  have hStart := realWalkTrace_first_tagged S path
  rw [hTrace] at hStart
  have hStartBound : 0 < (privateFanHomWordTrace S H D centres f o).length := by
    rw [privateFanHomWordTrace_length S H D centres f o]
    omega
  rw [List.getElem?_eq_getElem hStartBound] at hStart
  have hxTag : (⟨root, x⟩ : Sigma X) =
      ⟨root, f.point (privateFanRoot S D centres)⟩ :=
    (Option.some.inj hStart).symm.trans
      (privateFanHomWordTrace_start S H D centres f o)
  have hx : x = f.point (privateFanRoot S D centres) :=
    eq_of_heq (Sigma.mk.inj hxTag).2
  have hFinish := realWalkTrace_last_tagged S path
  rw [hTrace] at hFinish
  have hFinishBound : diversityLength S (occurrenceWord S D o) <
      (privateFanHomWordTrace S H D centres f o).length := by
    rw [privateFanHomWordTrace_length S H D centres f o]
    omega
  rw [List.getElem?_eq_getElem hFinishBound] at hFinish
  have hyTag : (⟨sort o.1, y⟩ : Sigma X) =
      ⟨sort o.1,
        f.point (privateFanCentre S D centres (toDistinctCentre sort centres o.1))⟩ :=
    (Option.some.inj hFinish).symm.trans
      (privateFanHomWordTrace_finish S H D centres f o hPositive)
  have hy : y = f.point
      (privateFanCentre S D centres (toDistinctCentre sort centres o.1)) :=
    eq_of_heq (Sigma.mk.inj hyTag).2
  have hRelation := (wordPath_iff_relation S (occurrenceWord S D o) x y).mp ⟨path⟩
  simpa only [hx, hy] using hRelation

end CCO.RawExact
