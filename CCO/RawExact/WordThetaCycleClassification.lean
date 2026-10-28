import CCO.RawExact.WordThetaCycleClassificationExhaustion

/-!
# C06: exact whole-cycle/two-private-path classification of the actual RAW theta

Every literal simple cycle in the already constructed source-coloured theta
is EXACTLY the union of two DISTINCT positive original word occurrences,
including every position and every traversed edge of BOTH whole paths.
Logical identity letters contribute no edges. Duplicate direct paths are
already merged, so they never produce a parallel two-cycle. Empty and
singleton families, and families consisting only of short paths, have no cycles.
-/

universe u v w
namespace CCO.RawExact
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {I : Type (max u v)} [Finite I] {i j : ι}

/-- All marked endpoints of a word theta are literally the same actual centre. -/
theorem wordTheta_centres_eq (centre : X j)
    (c d : DistinctCentres (fun _ : I => j) (fun _ => centre)) : c = d := by
  apply Subtype.ext
  obtain ⟨t, ht⟩ := c.property
  obtain ⟨u, hu⟩ := d.property
  exact ht.symm.trans hu

/-- A singleton word menu has exactly its original indexed occurrence. -/
theorem wordThetaOccurrence_exhaustive
    (words : I → RawWord S i j)
    (hNonempty : ∀ t, TRel.Nonempty (RawWord.relation S (words t)))
    (o : WordOccurrence S (wordThetaMenus S words hNonempty)) :
    wordThetaOccurrence S words hNonempty o.1 = o := by
  rcases o with ⟨t, p⟩
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Fin.ext
    have hp := p.isLt
    change p.val < 1 at hp
    change 0 = p.val
    omega

/-- A literal position on the t-th original reduced RAW path. -/
def wordThetaPathVertex (words : I → RawWord S i j)
    (hNonempty : ∀ t, TRel.Nonempty (RawWord.relation S (words t)))
    (centre : X j) (t : I) (p : PathPosition S (words t)) :
    PrivateFanVertex S (wordThetaMenus S words hNonempty) (fun _ => centre) :=
  privateFanAtWordPosition S (wordThetaMenus S words hNonempty) (fun _ => centre)
    (wordThetaOccurrence S words hNonempty t) p

/-- A literal edge on the t-th original reduced RAW path. -/
abbrev wordThetaPathEdge (words : I → RawWord S i j)
    (hNonempty : ∀ t, TRel.Nonempty (RawWord.relation S (words t))) (centre : X j) (t : I) :=
  PrivateOccurrenceEdge S (wordThetaMenus S words hNonempty) (fun _ => centre)
    (wordThetaOccurrence S words hNonempty t)

/-- Source N03/C06, with literal equality of complete cycle vertex AND edge supports.
No CCO, Helly, SAP, path-injectivity-of-real-walks or all-positive-family premise is used. -/
theorem wordTheta_cycle_two_whole_paths
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G) (words : I → RawWord S i j)
    (hNonempty : ∀ t, TRel.Nonempty (RawWord.relation S (words t))) (centre : X j)
    (C : SimpleCycle (privateFanFullDiagram S H (wordThetaMenus S words hNonempty) (fun _ => centre))) :
    ∃ t u : I, t ≠ u ∧ 0 < diversityLength S (words t) ∧ 0 < diversityLength S (words u) ∧
      (∀ v, CycleVertex C v ↔
        (∃ p, wordThetaPathVertex S words hNonempty centre t p = v) ∨
        (∃ p, wordThetaPathVertex S words hNonempty centre u p = v)) ∧
      (∀ v w, CycleEdge C v w ↔
        wordThetaPathEdge S words hNonempty centre t v w ∨
        wordThetaPathEdge S words hNonempty centre u v w) := by
  obtain ⟨left, right, hne, hPosLeft, hPosRight, hVertices, hEdges⟩ :=
    privateFan_one_centre_cycle_two_whole_paths S (wordThetaMenus S words hNonempty) (fun _ => centre) C
      (privateFanFull_cycle_adjacent S H _ _ C) (wordTheta_centres_eq (I := I) centre)
  let t := left.1
  let u := right.1
  have hLeft : wordThetaOccurrence S words hNonempty t = left := wordThetaOccurrence_exhaustive S words hNonempty left
  have hRight : wordThetaOccurrence S words hNonempty u = right := wordThetaOccurrence_exhaustive S words hNonempty right
  have htu : t ≠ u := by
    intro h
    exact hne (hLeft.symm.trans ((congrArg (wordThetaOccurrence S words hNonempty) h).trans hRight))
  refine ⟨t, u, htu, ?_, ?_, ?_, ?_⟩
  · simpa only [← hLeft, wordThetaOccurrence_word] using hPosLeft
  · simpa only [← hRight, wordThetaOccurrence_word] using hPosRight
  · have hLeftV (v) :
        (∃ p, wordThetaPathVertex S words hNonempty centre t p = v) ↔
        (∃ p, privateFanAtWordPosition S (wordThetaMenus S words hNonempty) (fun _ => centre) left p = v) := by
      change (∃ p, privateFanAtWordPosition S (wordThetaMenus S words hNonempty) (fun _ => centre)
        (wordThetaOccurrence S words hNonempty t) p = v) ↔ _
      rw [hLeft]
    have hRightV (v) :
        (∃ p, wordThetaPathVertex S words hNonempty centre u p = v) ↔
        (∃ p, privateFanAtWordPosition S (wordThetaMenus S words hNonempty) (fun _ => centre) right p = v) := by
      change (∃ p, privateFanAtWordPosition S (wordThetaMenus S words hNonempty) (fun _ => centre)
        (wordThetaOccurrence S words hNonempty u) p = v) ↔ _
      rw [hRight]
    intro v
    exact (hVertices v).trans (or_congr (hLeftV v).symm (hRightV v).symm)
  · simpa only [← hLeft, ← hRight, wordThetaPathEdge] using hEdges

/-- A family with at most one private word path cannot contain a simple theta cycle. -/
theorem wordTheta_no_cycle_of_subsingleton [Subsingleton I]
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G) (words : I → RawWord S i j)
    (hNonempty : ∀ t, TRel.Nonempty (RawWord.relation S (words t))) (centre : X j) :
    ¬ Nonempty (SimpleCycle (privateFanFullDiagram S H (wordThetaMenus S words hNonempty) (fun _ => centre))) := by
  rintro ⟨C⟩
  obtain ⟨t, u, hne, _⟩ := wordTheta_cycle_two_whole_paths S H words hNonempty centre C
  exact hne (Subsingleton.elim t u)

/-- Merged duplicate direct edges and zero-length reduced words have no fake two-cycle. -/
theorem wordTheta_no_cycle_of_short_words
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G) (words : I → RawWord S i j)
    (hNonempty : ∀ t, TRel.Nonempty (RawWord.relation S (words t))) (centre : X j)
    (hShort : ∀ t, diversityLength S (words t) ≤ 1) :
    ¬ Nonempty (SimpleCycle (privateFanFullDiagram S H (wordThetaMenus S words hNonempty) (fun _ => centre))) := by
  rintro ⟨C⟩
  obtain ⟨o, p, _⟩ := privateFan_one_centre_cycle_has_interior S
    (wordThetaMenus S words hNonempty) (fun _ => centre) C (wordTheta_centres_eq (I := I) centre)
  have hlen : diversityLength S (occurrenceWord S (wordThetaMenus S words hNonempty) o) ≤ 1 := by
    rw [← wordThetaOccurrence_exhaustive S words hNonempty o, wordThetaOccurrence_word]
    exact hShort o.1
  have hpBound := p.1.isLt
  have hp0 := p.property.1
  have hpEnd := p.property.2
  omega

end CCO.RawExact
