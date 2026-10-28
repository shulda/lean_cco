import Mathlib.Basic.Finite.Sigma
import CCO.RawExact.DistinctCentres
import CCO.RawExact.PrivatePaths
import CCO.RawExact.Balls

/-!
# B002 C12: every private RAW word occurrence in a finite exact-ball fan

A finite exact-ball family is a finite array of finite actual RAW
word menus. An occurrence keeps BOTH its outer ball index and its
position in that ball's list, so two identical words remain distinct
private paths, with disjoint interiors in the later graph.

Pairwise ball intersections give ACTUAL simultaneous represented
walks for EVERY chosen pair of word occurrences, including
two occurrences in one menu or two menus with the same centre.
This is exactly the local semantic input to the C12 cycle proof.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {root : ι}
variable {I : Type (max u v)} [Finite I]
variable {sort : I → ι}

/-- Occurrences, not just distinct syntactic words: (menu, list slot). -/
abbrev WordOccurrence (D : ∀ t : I, NonemptyExact S root (sort t)) :=
  Σ t : I, Fin (D t).words.length

instance wordOccurrence_finite
    (D : ∀ t : I, NonemptyExact S root (sort t)) :
    Finite (WordOccurrence S D) := by
  unfold WordOccurrence
  infer_instance

/-- Correctly typed RAW word in this list occurrence. -/
def occurrenceWord
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (o : WordOccurrence S D) : RawWord S root (sort o.1) :=
  (D o.1).words.get o.2

/-- Every listed word belongs to the exact menu that owns it. -/
theorem occurrenceWord_mem
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (o : WordOccurrence S D) :
    occurrenceWord S D o ∈ (D o.1).words :=
  List.get_mem _ _

/-- A point in an exact ball satisfies each individual original
word occurrence at that actual centre. -/
theorem occurrenceWord_of_ball
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D)
    (x : X root)
    (hx : evaluate S (D o.1).words x (centres o.1)) :
    RawWord.relation S (occurrenceWord S D o) x (centres o.1) :=
  hx (occurrenceWord S D o) (occurrenceWord_mem S D o)

/-- Local C12 lemma: any two named private paths have ACTUAL
simultaneous realizations based at ONE source point, with their
old real centres kept literally fixed. A witnessed walk is not
required to be injective; identity OUTPUTS are preserved. -/
theorem pair_private_walks_of_pairwise_balls
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (hPair : ∀ p q : I,
      (ball (evaluate S (D p).words) (centres p) ∩
        ball (evaluate S (D q).words) (centres q)).Nonempty)
    (p q : WordOccurrence S D) :
    Nonempty
      (Σ x : X root,
        WordPath S (occurrenceWord S D p) x (centres p.1) ×
        WordPath S (occurrenceWord S D q) x (centres q.1)) := by
  obtain ⟨x, hp, hq⟩ := hPair p.1 q.1
  have hWordP :=
    occurrenceWord_of_ball S D centres p x hp
  have hWordQ :=
    occurrenceWord_of_ball S D centres q x hq
  obtain ⟨wp⟩ := (wordPath_iff_relation S
    (occurrenceWord S D p) x (centres p.1)).mpr hWordP
  obtain ⟨wq⟩ := (wordPath_iff_relation S
    (occurrenceWord S D q) x (centres q.1)).mpr hWordQ
  exact ⟨⟨x, wp, wq⟩⟩

/-- Distinct occurrences in the SAME exact menu are included: this
is the case needed for cycles through two different private paths
ending at one actual old centre, without requiring two distinct
ball indices. -/
theorem two_private_walks_same_menu
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (hPair : ∀ p q : I,
      (ball (evaluate S (D p).words) (centres p) ∩
        ball (evaluate S (D q).words) (centres q)).Nonempty)
    (t : I) (p q : Fin (D t).words.length) :
    Nonempty
      (Σ x : X root,
        WordPath S (occurrenceWord S D ⟨t,p⟩) x (centres t) ×
        WordPath S (occurrenceWord S D ⟨t,q⟩) x (centres t)) :=
  pair_private_walks_of_pairwise_balls S D centres hPair ⟨t,p⟩ ⟨t,q⟩

end CCO.RawExact
