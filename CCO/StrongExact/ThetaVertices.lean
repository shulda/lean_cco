import CCO.PositiveWords
import CCO.StrongExact.ExactMenus

/-!
# C07 theta construction: finite private positions of typed positive words

Every genuine positive word defines a finite formal *line* with two
distinguished roots and private intermediate vertex positions. A family
of words with the SAME typed endpoint sorts receives ONE shared left
root, ONE shared right root, and separately tagged interiors. The
interiors of different branches cannot coincide.

This is the exact combinatorial vertex universe for the human theta
diagram. It is only the checked vertex/sort encoding; assigning all
word edges and proving the simple-cycle classification remain separate
obligations. No CCO, SAP, or new word identity is postulated here.
-/

universe u v a

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u, v, a} ι X)

/-- Finite formal line positions: the single letter has Boolean
left/right endpoints; a cons letter adds one new source before
the previous line. -/
def wordPositions {i j : ι} :
    PositiveWord S i j → Type
  | .single _ => Bool
  | .cons _ tail => Option (wordPositions tail)

/-- The literal first formal position of a positive word. -/
def wordSource {i j : ι} :
    (w : PositiveWord S i j) → wordPositions S w
  | .single _ => false
  | .cons _ _ => none

/-- The literal last formal position of a positive word. -/
def wordTarget {i j : ι} :
    (w : PositiveWord S i j) → wordPositions S w
  | .single _ => true
  | .cons _ tail => some (wordTarget tail)

/-- The genuinely typed named sort of every formal position. -/
def wordPositionSort {i j : ι} :
    (w : PositiveWord S i j) → wordPositions S w → ι
  | .single _ => fun b => cond b j i
  | .cons _ tail => fun p =>
      match p with
      | none => i
      | some q => wordPositionSort tail q

theorem wordSource_sort {i j : ι} (w : PositiveWord S i j) :
    wordPositionSort S w (wordSource S w) = i := by
  cases w <;> rfl

theorem wordTarget_sort {i j : ι} (w : PositiveWord S i j) :
    wordPositionSort S w (wordTarget S w) = j := by
  induction w with
  | single _ => rfl
  | cons _ tail ih =>
      simpa only [wordPositionSort, wordTarget] using ih

/-- Even on a positive loop word, the two FORMAL endpoints of
its path are distinct; their named sorts may nevertheless agree. -/
theorem wordSource_ne_target {i j : ι} (w : PositiveWord S i j) :
    wordSource S w ≠ wordTarget S w := by
  intro h
  cases w with
  | single _ =>
      change (false : Bool) = true at h
      cases h
  | cons _ tail =>
      change (none : Option (wordPositions S tail)) =
        some (wordTarget S tail) at h
      cases h

/-- Formal word positions are finite independently of the sizes of
their actual original-sort carriers. -/
theorem finite_wordPositions {i j : ι} (w : PositiveWord S i j) :
    Finite (wordPositions S w) := by
  induction w with
  | single _ =>
      change Finite Bool
      infer_instance
  | cons _ tail ih =>
      change Finite (Option (wordPositions S tail))
      infer_instance

/-- Only the genuinely internal positions. No single-letter word
has any interior vertices; endpoints cannot be identified with one
another or with private interiors. -/
def wordInterior {i j : ι} (w : PositiveWord S i j) :
    Type :=
  {p : wordPositions S w //
    p ≠ wordSource S w ∧ p ≠ wordTarget S w}

theorem finite_wordInterior {i j : ι} (w : PositiveWord S i j) :
    Finite (wordInterior S w) := by
  letI : Finite (wordPositions S w) := finite_wordPositions S w
  exact Finite.of_injective (fun p : wordInterior S w => p.val)
    Subtype.val_injective

/-- One shared pair of roots and a PRIVATE copy of every internal
position of every profile word. The branch index prevents collisions
of interiors even for syntactically identical positive words. -/
def thetaVertices {i j : ι} (ws : List (PositiveWord S i j)) :
    Type :=
  Bool ⊕ (Σ b : Fin ws.length, wordInterior S (ws.get b))

theorem finite_thetaVertices {i j : ι}
    (ws : List (PositiveWord S i j)) :
    Finite (thetaVertices S ws) := by
  classical
  letI (b : Fin ws.length) :
      Fintype (wordInterior S (ws.get b)) := by
    letI : Finite (wordInterior S (ws.get b)) :=
      finite_wordInterior S (ws.get b)
    exact Fintype.ofFinite _
  change Finite (Bool ⊕
    (Σ b : Fin ws.length, wordInterior S (ws.get b)))
  infer_instance

/-- The original sort of a theta vertex, with both shared roots
specified literally by the common typed endpoints. -/
def thetaVertexSort {i j : ι}
    (ws : List (PositiveWord S i j)) :
    thetaVertices S ws → ι
  | .inl false => i
  | .inl true => j
  | .inr ⟨b, p⟩ => wordPositionSort S (ws.get b) p.val

def thetaLeft {i j : ι} (ws : List (PositiveWord S i j)) :
    thetaVertices S ws := .inl false

def thetaRight {i j : ι} (ws : List (PositiveWord S i j)) :
    thetaVertices S ws := .inl true

theorem thetaLeft_ne_right {i j : ι}
    (ws : List (PositiveWord S i j)) :
    thetaLeft S ws ≠ thetaRight S ws := by
  intro h
  cases h

theorem thetaLeft_sort {i j : ι}
    (ws : List (PositiveWord S i j)) :
    thetaVertexSort S ws (thetaLeft S ws) = i := rfl

theorem thetaRight_sort {i j : ι}
    (ws : List (PositiveWord S i j)) :
    thetaVertexSort S ws (thetaRight S ws) = j := rfl

/-- Embed one branch's formal vertex, identifying ONLY its two
endpoints with the global theta roots. Every other position retains
a private (branch index, interior position) tag. -/
noncomputable def thetaBranchPosition {i j : ι}
    (ws : List (PositiveWord S i j)) (b : Fin ws.length)
    (p : wordPositions S (ws.get b)) : thetaVertices S ws := by
  classical
  exact if h0 : p = wordSource S (ws.get b) then thetaLeft S ws
    else if h1 : p = wordTarget S (ws.get b) then thetaRight S ws
    else .inr ⟨b, ⟨p, h0, h1⟩⟩

theorem thetaBranchPosition_source {i j : ι}
    (ws : List (PositiveWord S i j)) (b : Fin ws.length) :
    thetaBranchPosition S ws b (wordSource S (ws.get b)) =
      thetaLeft S ws := by
  classical
  simp [thetaBranchPosition]

theorem thetaBranchPosition_target {i j : ι}
    (ws : List (PositiveWord S i j)) (b : Fin ws.length) :
    thetaBranchPosition S ws b (wordTarget S (ws.get b)) =
      thetaRight S ws := by
  classical
  have h : wordTarget S (ws.get b) ≠ wordSource S (ws.get b) :=
    (wordSource_ne_target S (ws.get b)).symm
  unfold thetaBranchPosition
  split_ifs with h0 h1
  · exact (h h0).elim
  · simp
  · exact (h1 rfl).elim

/-- Every private interior maps to its uniquely tagged theta point. -/
theorem thetaBranchPosition_interior {i j : ι}
    (ws : List (PositiveWord S i j)) (b : Fin ws.length)
    (p : wordInterior S (ws.get b)) :
    thetaBranchPosition S ws b p.val = (.inr ⟨b, p⟩) := by
  classical
  unfold thetaBranchPosition
  split_ifs with h0 h1
  · exact (p.property.1 h0).elim
  · exact (p.property.2 h1).elim
  · split_ifs <;> simp_all
    cases p
    rfl

/-- No typed sort changes when mapping a formal path into theta:
only its literal same-sort root positions are identified. -/
theorem thetaBranchPosition_sort {i j : ι}
    (ws : List (PositiveWord S i j)) (b : Fin ws.length)
    (p : wordPositions S (ws.get b)) :
    thetaVertexSort S ws (thetaBranchPosition S ws b p) =
      wordPositionSort S (ws.get b) p := by
  classical
  by_cases h0 : p = wordSource S (ws.get b)
  · subst p
    rw [thetaBranchPosition_source S ws b]
    rw [thetaLeft_sort S ws]
    exact (wordSource_sort S (ws.get b)).symm
  · by_cases h1 : p = wordTarget S (ws.get b)
    · subst p
      rw [thetaBranchPosition_target S ws b]
      simpa only [thetaRight_sort] using
        (wordTarget_sort S (ws.get b)).symm
    · let inner : wordInterior S (ws.get b) := ⟨p, h0, h1⟩
      change thetaVertexSort S ws
          (thetaBranchPosition S ws b inner.val) =
        wordPositionSort S (ws.get b) inner.val
      rw [thetaBranchPosition_interior S ws b inner]
      rfl

end CCO.StrongExact
