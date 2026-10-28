import CCO.StrongExact.ThetaVertices

/-!
# C07 theta graph: the genuine directed atomic edges of each private path

For any genuinely positive typed word, its finite line has one
directed diversity-coloured edge per atomic letter. These edges
retain the original palette types, including repeated sort labels,
and every formal edge has distinct endpoints.

Every branch edge is embedded in the shared-root theta vertex type,
using literal endpoints and indexed private internal positions.
This is the exact preparatory edge API for proving that all theta
simple cycles consist of two different private paths (merging
duplicate singleton direct edges when necessary).
-/

universe u v a

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u, v, a} ι X)

/-- Finite edge indices along the positive word's formal line.
For a cons word, the first edge is new and the remaining edges
belong to its typed tail. -/
def wordEdgeIndex {i j : ι} :
    PositiveWord S i j → Type
  | .single _ => PUnit
  | .cons _ tail => PUnit ⊕ wordEdgeIndex tail

def wordEdgeSource {i j : ι} :
    (w : PositiveWord S i j) → wordEdgeIndex S w → wordPositions S w
  | .single _, _ => false
  | .cons _ tail, e =>
      match e with
      | .inl _ => none
      | .inr t => some (wordEdgeSource tail t)

def wordEdgeTarget {i j : ι} :
    (w : PositiveWord S i j) → wordEdgeIndex S w → wordPositions S w
  | .single _, _ => true
  | .cons _ tail, e =>
      match e with
      | .inl _ => some (wordSource S tail)
      | .inr t => some (wordEdgeTarget tail t)

/-- Each formal line edge has its literal old fine atomic diversity
colour, with exact types given by the two formal endpoint sorts. -/
def wordEdgeAtom {i j : ι} :
    (w : PositiveWord S i j) → (e : wordEdgeIndex S w) →
      S.Atom
        (wordPositionSort S w (wordEdgeSource S w e))
        (wordPositionSort S w (wordEdgeTarget S w e))
  | .single b, _ => b
  | .cons b tail, e =>
      match e with
      | .inl _ => (wordSource_sort S tail).symm ▸ b
      | .inr e => wordEdgeAtom tail e

theorem finite_wordEdgeIndex {i j : ι}
    (w : PositiveWord S i j) : Finite (wordEdgeIndex S w) := by
  induction w with
  | single _ =>
      change Finite PUnit
      infer_instance
  | cons _ tail ih =>
      change Finite (PUnit ⊕ wordEdgeIndex S tail)
      infer_instance

/-- A genuine positive word edge never joins a formal position to
itself, even if the two original named sorts are the same. -/
theorem wordEdge_distinct {i j : ι}
    (w : PositiveWord S i j) :
    ∀ e : wordEdgeIndex S w,
      wordEdgeSource S w e ≠ wordEdgeTarget S w e := by
  induction w with
  | single _ =>
      intro e h
      cases e
      change (false : Bool) = true at h
      cases h
  | cons b tail ih =>
      intro e h
      cases e with
      | inl _ =>
          change (none : Option (wordPositions S tail)) =
            some (wordSource S tail) at h
          cases h
      | inr e =>
          change some (wordEdgeSource S tail e) =
            some (wordEdgeTarget S tail e) at h
          exact (ih e) (Option.some.inj h)

/-- The literal source of any private branch edge inside the global
theta vertex type. The first/last endpoints may map to shared roots. -/
noncomputable def thetaBranchEdgeSource {i j : ι}
    (ws : List (PositiveWord S i j)) (b : Fin ws.length)
    (e : wordEdgeIndex S (ws.get b)) : thetaVertices S ws :=
  thetaBranchPosition S ws b (wordEdgeSource S (ws.get b) e)

noncomputable def thetaBranchEdgeTarget {i j : ι}
    (ws : List (PositiveWord S i j)) (b : Fin ws.length)
    (e : wordEdgeIndex S (ws.get b)) : thetaVertices S ws :=
  thetaBranchPosition S ws b (wordEdgeTarget S (ws.get b) e)

/-- Exact typed fine colour of a branch edge in the global shared-root
theta graph. It is transported by the PROVED sort preservation of
the branch embedding, not by an unproved extra colour axiom. -/
noncomputable def thetaBranchEdgeAtom {i j : ι}
    (ws : List (PositiveWord S i j)) (b : Fin ws.length)
    (e : wordEdgeIndex S (ws.get b)) :
    S.Atom
      (thetaVertexSort S ws (thetaBranchEdgeSource S ws b e))
      (thetaVertexSort S ws (thetaBranchEdgeTarget S ws b e)) :=
  (thetaBranchPosition_sort S ws b (wordEdgeSource S (ws.get b) e)).symm ▸
    ((thetaBranchPosition_sort S ws b (wordEdgeTarget S (ws.get b) e)).symm ▸
      wordEdgeAtom S (ws.get b) e)

theorem thetaBranchEdgeAtom_cast {i j : ι}
    (ws : List (PositiveWord S i j)) (b : Fin ws.length)
    (e : wordEdgeIndex S (ws.get b)) :
    thetaBranchEdgeAtom S ws b e =
      (thetaBranchPosition_sort S ws b (wordEdgeSource S (ws.get b) e)).symm ▸
      ((thetaBranchPosition_sort S ws b (wordEdgeTarget S (ws.get b) e)).symm ▸
        wordEdgeAtom S (ws.get b) e) := rfl

end CCO.StrongExact
