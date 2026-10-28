import CCO.RawExact.PrivateFanAdjacency

/-!
# B002 C12: the private-word fan graph is actually SIMPLE

Two adjacent positions of a single RAW word stay distinct after
endpoints are glued to the one root and the appropriate old centre.
Every interior position of every occurrence is still private.
The old centre graph has edges only between genuinely different
actual tagged centres. Therefore the union graph is symmetric and
irreflexive, without fake equality edges or parallel 2-cycles.

This is a purely combinatorial source theorem; it does NOT prove
the remaining C12 cycle decomposition or colour labelling.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {root : ι} {I : Type (max u v)} [Finite I]
variable {sort : I → ι}

/-- The positions of any *single* word occurrence embed into the
formal private fan, including positive-length and zero-length words.
The latter have just one position, mapped to the formal root; no
false equality edge is introduced. -/
theorem privateFanAtWordPosition_injective
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D) :
    Function.Injective (privateFanAtWordPosition S D centres o) := by
  classical
  intro p q heq
  have hVal : p.val = q.val := by
    by_cases hp0 : p.val = 0 <;>
    by_cases hpend : p.val = diversityLength S (occurrenceWord S D o) <;>
    by_cases hq0 : q.val = 0 <;>
    by_cases hqend : q.val = diversityLength S (occurrenceWord S D o) <;>
      simp_all [privateFanAtWordPosition, privateFanRoot,
        privateFanCentre, privateFanInterior]
  exact Fin.ext hVal

theorem privateFanOldCentreAdjacent_irrefl
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (v : PrivateFanVertex S D centres) :
    ¬ privateFanOldCentreAdjacent S D centres v v := by
  rintro ⟨c, d, hcd, hv, hw⟩
  have hEq : privateFanCentre S D centres c =
      privateFanCentre S D centres d := hv.symm.trans hw
  exact hcd ((privateFanCentre_injective S D centres) hEq)

theorem privateFanPathAdjacent_irrefl
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (v : PrivateFanVertex S D centres) :
    ¬ privateFanPathAdjacent S D centres v v := by
  rintro ⟨o, p, q, hpq, hv, hw⟩
  have hpEq : privateFanAtWordPosition S D centres o p =
      privateFanAtWordPosition S D centres o q :=
    hv.symm.trans hw
  have hpqEq : p = q :=
    privateFanAtWordPosition_injective S D centres o hpEq
  subst q
  exact (pathAdjacent_irrefl S (occurrenceWord S D o) p) hpq

/-- The finite ROOT/centre/private-word graph is a simple undirected
graph in the precise source sense. Atomic colours and oriented
diversity labels must still be supplied separately. -/
theorem privateFanAdjacent_irrefl
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (v : PrivateFanVertex S D centres) :
    ¬ privateFanAdjacent S D centres v v := by
  intro h
  rcases h with hOld | hPath
  · exact privateFanOldCentreAdjacent_irrefl S D centres v hOld
  · exact privateFanPathAdjacent_irrefl S D centres v hPath

end CCO.RawExact
