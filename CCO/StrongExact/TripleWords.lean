import CCO.StrongExact.ExactEndpointSemantics

/-!
# Three distinct formal roots and private word branches on their sides

This is the literal finite typed vertex universe used for C09. Each side
retains its own original positive-word presentation and separately tagged
private interiors. The three formal roots remain distinct even when some
or all original named sort labels agree.
-/

universe u v w
namespace CCO.StrongExact

inductive TripleRoot where
  | left | middle | right
  deriving DecidableEq

inductive TripleSide where
  | left | right | across
  deriving DecidableEq

instance : Fintype TripleRoot :=
  ⟨{.left,.middle,.right}, by intro r; cases r <;> simp⟩

instance : Fintype TripleSide :=
  ⟨{.left,.right,.across}, by intro s; cases s <;> simp⟩

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j k : ι}

structure TripleWords (i j k : ι) where
  left : List (PositiveWord S i j)
  right : List (PositiveWord S j k)
  across : List (PositiveWord S i k)

def tripleRootSort (i j k : ι) : TripleRoot → ι
  | .left => i
  | .middle => j
  | .right => k

def tripleSideSource : TripleSide → TripleRoot
  | .left => .left
  | .right => .middle
  | .across => .left

def tripleSideTarget : TripleSide → TripleRoot
  | .left => .middle
  | .right => .right
  | .across => .right

def TripleWords.side (W : TripleWords S i j k) :
    (s : TripleSide) → List (PositiveWord S
      (tripleRootSort i j k (tripleSideSource s))
      (tripleRootSort i j k (tripleSideTarget s)))
  | .left => W.left
  | .right => W.right
  | .across => W.across

/-- One separately tagged private interior for every original side word. -/
def tripleVertices (W : TripleWords S i j k) : Type :=
  TripleRoot ⊕ (Σ s : TripleSide, Σ b : Fin (TripleWords.side S W s).length,
    wordInterior S ((TripleWords.side S W s).get b))

def tripleVertexSort (W : TripleWords S i j k) : tripleVertices S W → ι
  | .inl r => tripleRootSort i j k r
  | .inr ⟨s,b,t⟩ => wordPositionSort S ((TripleWords.side S W s).get b) t.val

theorem finite_tripleVertices (W : TripleWords S i j k) :
    Finite (tripleVertices S W) := by
  let (s : TripleSide) (b : Fin (TripleWords.side S W s).length) :
      Finite (wordInterior S ((TripleWords.side S W s).get b)) :=
    finite_wordInterior S ((TripleWords.side S W s).get b)
  change Finite (TripleRoot ⊕ (Σ s : TripleSide, Σ b : Fin (TripleWords.side S W s).length,
    wordInterior S ((TripleWords.side S W s).get b)))
  infer_instance

/-- Include one complete private theta side, identifying exactly its
endpoints with the corresponding pair of the three global roots. -/
def thetaIntoTriple (W : TripleWords S i j k) (s : TripleSide) :
    thetaVertices S (TripleWords.side S W s) → tripleVertices S W
  | .inl false => .inl (tripleSideSource s)
  | .inl true => .inl (tripleSideTarget s)
  | .inr ⟨b,t⟩ => .inr ⟨s,b,t⟩

theorem thetaIntoTriple_sort (W : TripleWords S i j k) (s : TripleSide)
    (z : thetaVertices S (TripleWords.side S W s)) :
    tripleVertexSort S W (thetaIntoTriple S W s z) =
      thetaVertexSort S (TripleWords.side S W s) z := by
  cases z with
  | inl r => cases r <;> cases s <;> rfl
  | inr tag => rcases tag with ⟨b,t⟩; rfl

theorem thetaIntoTriple_injective (W : TripleWords S i j k) (s : TripleSide) :
    Function.Injective (thetaIntoTriple S W s) := by
  intro a b h
  cases a with
  | inl r =>
      cases b with
      | inl t =>
          cases s <;> cases r <;> cases t <;>
            simp only [thetaIntoTriple, tripleSideSource, tripleSideTarget] at h <;>
            cases h <;> rfl
      | inr tag => cases r <;> cases h
  | inr tag =>
      cases b with
      | inl r => cases r <;> cases h
      | inr tag' =>
          change (Sum.inr ⟨s,tag⟩ : tripleVertices S W) = .inr ⟨s,tag'⟩ at h
          have hh : (⟨s,tag⟩ : Σ t : TripleSide,
              Σ b : Fin (TripleWords.side S W t).length,
                wordInterior S ((TripleWords.side S W t).get b)) = ⟨s,tag'⟩ :=
            Sum.inr.inj h
          have ht : tag = tag' := eq_of_heq (Sigma.mk.inj hh).2
          exact congrArg Sum.inr ht

/-- Root values of one actual old-colour triangle, with all named sorts
retained. No distinctness is asserted until its diversity atoms are given. -/
def tripleRootPoint (x : X i) (y : X j) (z : X k) :
    ∀ r : TripleRoot, X (tripleRootSort i j k r)
  | .left => x
  | .middle => y
  | .right => z

structure TripleLiteralLines (W : TripleWords S i j k)
    (x : X i) (y : X j) (z : X k) where
  left : ∀ b : Fin W.left.length, LiteralLine S (W.left.get b) x y
  right : ∀ b : Fin W.right.length, LiteralLine S (W.right.get b) y z
  across : ∀ b : Fin W.across.length, LiteralLine S (W.across.get b) x z

def TripleLiteralLines.side {W : TripleWords S i j k}
    {x : X i} {y : X j} {z : X k}
    (lines : TripleLiteralLines S W x y z) :
    (s : TripleSide) → (b : Fin (TripleWords.side S W s).length) →
      LiteralLine S ((TripleWords.side S W s).get b)
        (tripleRootPoint x y z (tripleSideSource s))
        (tripleRootPoint x y z (tripleSideTarget s))
  | .left => lines.left
  | .right => lines.right
  | .across => lines.across

/-- Glue all three private line families at their shared three roots. -/
def tripleLinePoint (W : TripleWords S i j k)
    (x : X i) (y : X j) (z : X k)
    (lines : TripleLiteralLines S W x y z) :
    ∀ a : tripleVertices S W, X (tripleVertexSort S W a)
  | .inl r => tripleRootPoint x y z r
  | .inr ⟨s,b,t⟩ => (TripleLiteralLines.side S lines s b).point t.val

theorem tripleLinePoint_side_image (W : TripleWords S i j k)
    (x : X i) (y : X j) (z : X k)
    (lines : TripleLiteralLines S W x y z) (s : TripleSide)
    (a : thetaVertices S (TripleWords.side S W s)) :
    (⟨tripleVertexSort S W (thetaIntoTriple S W s a),
      tripleLinePoint S W x y z lines (thetaIntoTriple S W s a)⟩ : Sigma X) =
      ⟨thetaVertexSort S (TripleWords.side S W s) a,
        thetaFamilyLinePoint S (TripleWords.side S W s)
          (tripleRootPoint x y z (tripleSideSource s))
          (tripleRootPoint x y z (tripleSideTarget s)) (TripleLiteralLines.side S lines s) a⟩ := by
  cases a with
  | inl r => cases r <;> cases s <;> rfl
  | inr tag => rcases tag with ⟨b,t⟩; rfl

end CCO.StrongExact
