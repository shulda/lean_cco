import CCO.StrongExact.ThetaWordLineWitness
import CCO.StrongExact.PrescribedPathWitness

/-!
# C07: two pairwise-compatible original words have literal common roots

When two STRONG positive profiles intersect, source homogeneity and
genuine SAP give represented walks for both old diversity words over
the SAME two real endpoints of one common atomic colour. The purely
typed word-line witness theorem converts these to actual position-
indexed lines without changing their endpoints. No CCO or global
word Helly provider is used.
-/

universe u v w
namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

structure LiteralLine (word : PositiveWord S i j) (x : X i) (y : X j) where
  point : ∀ p : wordPositions S word, X (wordPositionSort S word p)
  edges : ∀ e : wordEdgeIndex S word,
    S.colour (point (wordEdgeSource S word e))
      (point (wordEdgeTarget S word e)) =
      some (wordEdgeAtom S word e)
  source : (wordSource_sort S word) ▸ point (wordSource S word) = x
  target : (wordTarget_sort S word) ▸ point (wordTarget S word) = y

theorem LiteralLine.of_represented
    (word : PositiveWord S i j) (x : X i) (y : X j)
    (h : PositiveWord.represented S word x y) :
    LiteralLine S word x y := by
  obtain ⟨point, hEdges, hSource, hTarget⟩ :=
    literal_word_line_of_represented S word x y h
  exact ⟨point, hEdges, hSource, hTarget⟩

/-- A common atomic survivor produces TWO actual original-colour
word-line witnesses with LITERALLY the same endpoint real points.
No injectivity of the walks is required by a cycle homomorphism. -/
theorem two_literal_lines_of_intersecting_profiles
    {G : Type*} [Group G] [∀ q : ι, MulAction G (X q)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (w v : PositiveWord S i j)
    (hInter :
      (PositiveWord.profile S w ∩ PositiveWord.profile S v).Nonempty) :
    ∃ (a : S.Atom i j) (x : X i) (y : X j),
      ∃ (lineW : LiteralLine S w x y)
        (lineV : LiteralLine S v x y),
        S.colour x y = some a := by
  obtain ⟨a, x, y, hxy, hw, hv⟩ :=
    intersecting_profiles_common_root_walks_of_SAP S H sap w v hInter
  exact ⟨a, x, y,
    LiteralLine.of_represented S w x y hw,
    LiteralLine.of_represented S v x y hv, hxy⟩

end CCO.StrongExact
