import CCO.ResetOrder.Hierarchy.Structures

/-! The one-task reversal is itself functorial on actual induced diagrams.
Every later parent-lex comparison is recomputed by the SAME recursion. -/
universe u v w
namespace CCO.ResetOrder.Hierarchy.Charting
variable {R : Type u} {J : R → Type u} {H : Schedule (Sigma J)}
variable {X : Sigma J → Type v} {Y : Sigma J → Type w}
variable {S : System H X} {T : System H Y} {representative : ∀ r, J r}
variable {C : Charting S representative} {D : Charting T representative}
variable {L : OldLanguage (Sigma J)}

namespace OrderedStructure
noncomputable def reverseOrbit (A : OrderedStructure C L) (r : R) : OrderedStructure C L :=
  ⟨A.data, C.reverseOrbit A.orders r⟩

theorem reverseOrbit_data (A : OrderedStructure C L) (r : R) : (A.reverseOrbit r).data = A.data := rfl

theorem reverseOrbit_coarser (A : OrderedStructure C L) (r : R) (i : Sigma J)
    (hi : H.rank i < H.rank ⟨r,representative r⟩) :
    (A.reverseOrbit r).orders i = A.normalize.orders i := C.reverseOrbit_coarser A.orders r i hi
end OrderedStructure

namespace OrderedEmbedding
variable {A : OrderedStructure C L} {B : OrderedStructure D L}

theorem reversedTasks_preserve (f : OrderedEmbedding C D L A B) (r : R)
    (i : Sigma J) (x y : X i)
    (h : (S.reverseTasks (C.localTasks A.orders) (fun i => i.1 = r) i).lt x y) :
    (T.reverseTasks (D.localTasks B.orders) (fun i => i.1 = r) i).lt
      (f.old.point i x) (f.old.point i y) := by
  classical
  by_cases hi : i.1 = r
  · have hs := (S.reverseTasks_selected _ (fun i : Sigma J => i.1 = r) i hi x y).1 h
    exact (T.reverseTasks_selected _ (fun i : Sigma J => i.1 = r) i hi _ _).2
      (f.localTasks_preserve i y x hs)
  · have hs : (C.localTasks A.orders i).lt x y := by simpa only [System.reverseTasks, if_neg hi] using h
    have ht := f.localTasks_preserve i x y hs
    simpa only [System.reverseTasks, if_neg hi] using ht

noncomputable def reverseOrbit (f : OrderedEmbedding C D L A B) (r : R) :
    OrderedEmbedding C D L (A.reverseOrbit r) (B.reverseOrbit r) where
  old := f.old
  up_commute := f.up_commute
  chart_commute := f.chart_commute
  order_preserve := f.geometryMap.normalize_preserves _ _ (f.reversedTasks_preserve r)

theorem reverseOrbit_identity (A : OrderedStructure C L) (r : R) :
    (identity A).reverseOrbit r = identity (A.reverseOrbit r) := by
  apply ext
  rfl

theorem reverseOrbit_compose {Z : Sigma J → Type*} {U : System H Z} {E : Charting U representative}
    {B : OrderedStructure D L} {F : OrderedStructure E L}
    (g : OrderedEmbedding D E L B F) (f : OrderedEmbedding C D L A B) (r : R) :
    (g.compose f).reverseOrbit r = (g.reverseOrbit r).compose (f.reverseOrbit r) := by
  apply ext
  rfl
end OrderedEmbedding
end CCO.ResetOrder.Hierarchy.Charting
