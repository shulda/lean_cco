import CCO.RawExact.FanFullDiagram
import CCO.RawExact.FanSortCompatibility
import Mathlib.Tactic

/-!
# B002 C13: actual old point trace of one completed RAW private word

A homomorphism of the full finite old-coloured private fan assigns
one real original-sort point to every formal vertex. Restricting to
the finite positions of a specific actual RAW word occurrence gives
a list of precisely one real point per genuine diversity position.

Identity LETTERS create no list entry. Repeated actual word
occurrences keep independent formal interiors and share only their
correctly glued original endpoints. A later proof will recover
the represented RAW word from these displayed points and their
old atomic-edge colours.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- The actual original point list along one specific occurrence
in a completed `DiagramHom` of the source private fan. -/
def privateFanHomWordTrace
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {root : ι} {I : Type (max u v)} [Finite I]
    {sort : I → ι}
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (f : DiagramHom (privateFanFullDiagram S H D centres))
    (o : WordOccurrence S D) : List (Sigma X) :=
  List.ofFn (fun p : PathPosition S (occurrenceWord S D o) =>
    (⟨privateFanSort S D centres
        (privateFanAtWordPosition S D centres o p),
      f.point (privateFanAtWordPosition S D centres o p)⟩ : Sigma X))

/-- The trace contains EXACTLY the genuine-diversity positions
of this one equality-inclusive typed RAW word. -/
theorem privateFanHomWordTrace_length
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {root : ι} {I : Type (max u v)} [Finite I]
    {sort : I → ι}
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (f : DiagramHom (privateFanFullDiagram S H D centres))
    (o : WordOccurrence S D) :
    (privateFanHomWordTrace S H D centres f o).length =
      diversityLength S (occurrenceWord S D o) + 1 := by
  simp [privateFanHomWordTrace]

/-- A numbered trace entry is literally the old point assigned
by the full source diagram homomorphism to that formal private
path position, with its ORIGINAL named sort retained. -/
theorem privateFanHomWordTrace_get
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {root : ι} {I : Type (max u v)} [Finite I]
    {sort : I → ι}
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (f : DiagramHom (privateFanFullDiagram S H D centres))
    (o : WordOccurrence S D)
    (p : PathPosition S (occurrenceWord S D o)) :
    (privateFanHomWordTrace S H D centres f o)[p.val]'(by
      rw [privateFanHomWordTrace_length S H D centres f o]
      exact p.isLt) =
      (⟨privateFanSort S D centres
        (privateFanAtWordPosition S D centres o p),
        f.point (privateFanAtWordPosition S D centres o p)⟩ : Sigma X) := by
  simp only [privateFanHomWordTrace, List.getElem_ofFn]

/-- Every trace point has exactly the original sort at its typed
RAW word position, not a quotient sort or an invented colour. -/
theorem privateFanHomWordTrace_sorts
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {root : ι} {I : Type (max u v)} [Finite I]
    {sort : I → ι}
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (f : DiagramHom (privateFanFullDiagram S H D centres))
    (o : WordOccurrence S D) :
    (privateFanHomWordTrace S H D centres f o).map Sigma.fst =
      wordSortTrace S (occurrenceWord S D o) := by
  have hSort : ∀ p : PathPosition S (occurrenceWord S D o),
      privateFanSort S D centres
        (privateFanAtWordPosition S D centres o p) =
          pathSortAt S (occurrenceWord S D o) p :=
    privateFanAtWordPosition_sort S D centres o
  rw [privateFanHomWordTrace, List.map_ofFn]
  simp only [Function.comp_def]
  simp_rw [hSort]
  simpa only [pathSortAt, wordSortTrace_length S
      (occurrenceWord S D o), List.get_eq_getElem] using
    (List.ofFn_getElem (xs := wordSortTrace S (occurrenceWord S D o)))

end CCO.RawExact
