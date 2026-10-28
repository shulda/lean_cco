import CCO.RawExact.QuotientExpansionReadout
import CCO.GroupActions

/-!
# Project one completed original expansion to the actual quotient diagram

Every expanded menu is the full pullback of its specified quotient
orbital. The proved whole-menu readout therefore makes the marked images
satisfy every actual quotient atom. Reverse orientations use the actual
source converse law. This is the C27 readout step; original CCO and the
cycle-witness/compression proof must still construct the given expansion
homomorphism before a final source inheritance theorem is asserted.
-/

universe u v w z q r

namespace CCO.RawExact.QuotientExpansion

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {K : Type z} {Q : K → Type q} (T : AtomicSource.{z,q,r} K Q)
variable {n : Nat} (D : PartialDiagram T (Fin n))
variable (root : K → ι) (π : ∀ k, X (root k) → Q k)

/-- Original-sort assignment of the marked quotient vertices. -/
def markedOriginalSort : Fin n → ι := fun m => root (D.vertexSort m)

variable (P : Menus S (markedOriginalSort T D root))
variable (hNonempty : ∀ e, TRel.Nonempty (evaluate S (P e)))

/-- Every specified quotient diversity edge has its true full represented
pullback menu. Missing edges may have an empty Top menu. -/
def RepresentsEdges : Prop :=
  ∀ (e : Edge n) (a : T.Atom (D.vertexSort (left e)) (D.vertexSort (right e))),
    D.edge (left e) (right e) (left_ne_right e) = some a →
    evaluate S (P e) =
      GroupActions.pullback (π (D.vertexSort (left e))) (π (D.vertexSort (right e)))
        (T.atomRel a)

/-- One actual completed original diagram induces a quotient diagram
homomorphism on the marked images, retaining every specified original
quotient atom. No injective representative choice or section is needed. -/
def project_expansion_hom
    (hRepresents : RepresentsEdges S T D root π P)
    (hPositive : ∀ o, 0 < diversityLength S (word S (markedOriginalSort T D root) P o))
    (f : DiagramHom (diagram S (markedOriginalSort T D root) P hNonempty)) :
    DiagramHom D := by
  let point : ∀ m, Q (D.vertexSort m) := fun m =>
    π (D.vertexSort m) (f.point (mark S (markedOriginalSort T D root) P m))
  refine ⟨point, ?_⟩
  intro m l hml a hEdge
  by_cases hlt : m < l
  · let e : Edge n := ⟨(m, l), hlt⟩
    have hCanonical : D.edge (left e) (right e) (left_ne_right e) = some a := hEdge
    have hMenu := hom_all_menus S (markedOriginalSort T D root) P hNonempty f hPositive e
    rw [hRepresents e a hCanonical] at hMenu
    exact hMenu
  · have hlt' : l < m := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hml)
    let e : Edge n := ⟨(l, m), hlt'⟩
    have hReverse : D.edge (left e) (right e) (left_ne_right e) = some (T.conv a) :=
      (D.edge_reverse m l hml a).mp hEdge
    have hMenu := hom_all_menus S (markedOriginalSort T D root) P hNonempty f hPositive e
    rw [hRepresents e (T.conv a) hReverse] at hMenu
    exact (T.colour_swap (point m) (point l) a).mpr hMenu

end CCO.RawExact.QuotientExpansion
