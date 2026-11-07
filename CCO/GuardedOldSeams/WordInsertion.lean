import CCO.Injectivization
import CCO.StrongExact.ThetaCompatibleLines

/-!
# Literal original-word insertion over an arbitrary finite old base

The input is the specified positive word, its actual endpoint colour, and
membership of that colour in that word's strong profile.  Visible SAP is
used through its proved finite-diagram injectivisation theorem.  No CCO,
terminality, idempotence, replacement word or equality-labelled edge occurs.
-/

universe u v a t

namespace CCO.GuardedOldSeams

open StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,a} ι X)
variable {i j : ι}

def lineImage {w : PositiveWord S i j} {x : X i} {y : X j}
    (line : LiteralLine S w x y) (p : wordPositions S w) : Sigma X :=
  ⟨wordPositionSort S w p, line.point p⟩

private theorem sigma_eq_of_cast_eq {i j : ι} {x : X i} {y : X j}
    (h : i = j) (hxy : h ▸ x = y) :
    (⟨i, x⟩ : Sigma X) = ⟨j, y⟩ := by
  cases h
  cases hxy
  rfl

theorem lineImage_source {w : PositiveWord S i j} {x : X i} {y : X j}
    (line : LiteralLine S w x y) :
    lineImage S line (wordSource S w) = ⟨i, x⟩ :=
  sigma_eq_of_cast_eq (wordSource_sort S w) line.source

theorem lineImage_target {w : PositiveWord S i j} {x : X i} {y : X j}
    (line : LiteralLine S w x y) :
    lineImage S line (wordTarget S w) = ⟨j, y⟩ :=
  sigma_eq_of_cast_eq (wordTarget_sort S w) line.target

/-- All formal vertices of this exact word are distinct.  Every interior
avoids the supplied whole old base; the endpoints are the literal inputs. -/
structure FreshWordLine (w : PositiveWord S i j) (x : X i) (y : X j)
    (Z : Set (Sigma X)) extends LiteralLine S w x y where
  injective : Function.Injective (lineImage S toLiteralLine)
  fresh : ∀ p : wordPositions S w,
    p ≠ wordSource S w → p ≠ wordTarget S w →
    lineImage S toLiteralLine p ∉ Z

/-- The complete old colours of a given walk can be retained as a finite
partial diversity diagram.  Coincident nonadjacent positions contribute
no fake equality edge. -/
def wordWalkDiagram {w : PositiveWord S i j} {x : X i} {y : X j}
    (line : LiteralLine S w x y) : PartialDiagram S (wordPositions S w) where
  finite_type := finite_wordPositions S w
  vertexSort := wordPositionSort S w
  edge p q _ := S.colour (line.point p) (line.point q)
  edge_reverse p q _ b := S.colour_swap (line.point p) (line.point q) b

def wordWalkHom {w : PositiveWord S i j} {x : X i} {y : X j}
    (line : LiteralLine S w x y) : DiagramHom (wordWalkDiagram S line) where
  point := line.point
  preserves_edge _ _ _ _ h := h

/-- A literal original word can be made simple and private while fixing
its prescribed distinct actual endpoints. -/
theorem fresh_word_line_of_represented
    {G : Type t} [Group G] [∀ q : ι, MulAction G (X q)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (w : PositiveWord S i j) (x : X i) (y : X j)
    (hne : (⟨i, x⟩ : Sigma X) ≠ ⟨j, y⟩)
    (hw : PositiveWord.represented S w x y)
    (Z : Set (Sigma X)) (hZ : Z.Finite) :
    Nonempty (FreshWordLine S w x y Z) := by
  classical
  let line := LiteralLine.of_represented S w x y hw
  let f₀ := wordWalkHom S line
  let pins : Set (wordPositions S w) := {wordSource S w, wordTarget S w}
  have hPin : ∀ p ∈ pins, ∀ q ∈ pins, f₀.image p = f₀.image q → p = q := by
    intro p hp q hq heq
    change lineImage S line p = lineImage S line q at heq
    simp only [pins, Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · rfl
    · exact False.elim (hne ((lineImage_source S line).symm.trans
        (heq.trans (lineImage_target S line))))
    · exact False.elim (hne ((lineImage_source S line).symm.trans
        (heq.symm.trans (lineImage_target S line))))
    · rfl
  obtain ⟨f, hinj, hfixed, hfresh⟩ :=
    DiagramHom.injectivize_of_SAP H sap f₀ pins hPin Z hZ
  have hpoint (p : wordPositions S w) (hp : p ∈ pins) :
      f.point p = line.point p := by
    have h := hfixed p hp
    change f.point p = f₀.point p
    simpa only [DiagramHom.image, Sigma.mk.injEq, heq_eq_eq, true_and] using h
  let out : LiteralLine S w x y := {
    point := f.point
    edges := fun e => f.preserves_edge _ _ (wordEdge_distinct S w e) _ (line.edges e)
    source := by
      rw [hpoint (wordSource S w) (by simp [pins])]
      exact line.source
    target := by
      rw [hpoint (wordTarget S w) (by simp [pins])]
      exact line.target }
  refine ⟨{ toLiteralLine := out, injective := hinj, fresh := ?_ }⟩
  intro p hs ht
  exact hfresh p (by simpa only [pins, Set.mem_insert_iff,
    Set.mem_singleton_iff, not_or] using And.intro hs ht)

/-- C55--C58 without the unnecessary idempotence specialization: the
actual fine endpoint atom in this particular word's profile suffices. -/
theorem fresh_word_line_of_profile
    {G : Type t} [Group G] [∀ q : ι, MulAction G (X q)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (w : PositiveWord S i j) (b : S.Atom i j)
    (hb : b ∈ PositiveWord.profile S w) (x : X i) (y : X j)
    (hxy : S.colour x y = some b)
    (Z : Set (Sigma X)) (hZ : Z.Finite) :
    Nonempty (FreshWordLine S w x y Z) := by
  exact fresh_word_line_of_represented S H sap w x y (S.atomRel_ne hxy)
    (profile_realizes_prescribed_pair_of_SAP S H sap w b hb x y hxy) Z hZ

end CCO.GuardedOldSeams
