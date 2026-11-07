import CCO.UnfilteredEP.NormalizedTaskProvider

/-! Exact-map equivalence between the full task provider and the SAME
complete normalized hidden class. All old unary domains are retained. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 1200000
universe u v w
namespace CCO.UnfilteredEP
open CCO CCO.FullCode CCO.APRamseyReadout CCO.CloneTupleGeometry
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal) (n : Nat)
variable (D : HiddenCut B) (m : ActualResetMenu B (fullMIOfNamed B D.1 D.2))
variable (priority : LinearOrder (Sig B ht).Sorts)
local notation "P" => actualTaskFibres B ht n D m
local notation "X" => normalizedTaskExtra B ht n
variable {A C : ResetOrder.Unary.FullObject (actualTaskFibres B ht n D m)
  (normalizedTaskExtra B ht n)}

/-- Every full task map decodes to its complete hidden map. -/
def normalizedTaskDecodeMap (f : ResetOrder.Unary.FullHom A C) :
    Structure.Embedding (normalizedTaskDecode B ht n D m A)
      (normalizedTaskDecode B ht n D m C) where
  point := f.point
  injective := f.task.old.injective
  sort_eq := f.task.old.sort_eq
  map_func := f.task.old.map_func
  reflect_func := f.task.old.reflect_func
  unary_iff U := PEmpty.elim U
  binary_iff R x y := by
    cases R with
    | inl R => exact (resetUnaryDecodeEmbedding (PrefixFullCodeLanguage B ht n) f.task.old).binary_iff (.inl R) x y
    | inr p =>
      change C.rel p (taskPair (f.point x) (f.point y)) ↔ A.rel p (taskPair x y)
      have same : taskPair (f.point x) (f.point y) = f.point ∘ taskPair x y := by
        funext i
        dsimp only [taskPair,Function.comp_apply]
        split <;> rfl
      rw [same]
      exact f.rel_iff p (taskPair x y)

/-- The old prefix map of a complete hidden embedding is recovered on
the same points from the two exact prefix equations. -/
def normalizedTaskOldMap
    (hA : normalizedTaskFullAge B ht n D m priority A)
    (hC : normalizedTaskFullAge B ht n D m priority C)
    (f : Structure.Embedding (normalizedTaskDecode B ht n D m A)
      (normalizedTaskDecode B ht n D m C)) : A.task.old.Emb C.task.old :=
  resetUnaryEmbeddingOfDecode (PrefixFullCodeLanguage B ht n)
    (((taskPrefixEmbedding B ht n f).sourceCongr hA.prefix_eq.symm).targetCongr hC.prefix_eq.symm)

/-- Complete hidden embeddings give full task embeddings exactly, with
no map choice and with all full comparison relations reflected. -/
def normalizedTaskMapOfDecode
    (hA : normalizedTaskFullAge B ht n D m priority A)
    (hC : normalizedTaskFullAge B ht n D m priority C)
    (f : Structure.Embedding (normalizedTaskDecode B ht n D m A)
      (normalizedTaskDecode B ht n D m C)) : ResetOrder.Unary.FullHom A C where
  task := {
    old := normalizedTaskOldMap B ht n D m priority hA hC f
    order_iff := by
      intro x y
      rw [hC.comparison,hA.comparison]
      exact and_congr ((actualParentFormula B ht D).same_natural
        (taskOldBaseEmbedding B ht n (normalizedTaskOldMap B ht n D m priority hA hC f)) x y)
        (f.binary_iff (.inr (hiddenCutSort B ht D,hiddenCutSort B ht D)) x y) }
  map_func F := PEmpty.elim F
  reflect_func F := PEmpty.elim F
  rel_iff p xs := by
    have hh := f.binary_iff (.inr p) (xs 0) (xs 1)
    change C.rel p (taskPair ((f.point ∘ xs) 0) ((f.point ∘ xs) 1)) ↔
      A.rel p (taskPair (xs 0) (xs 1)) at hh
    rw [taskPair_eta,taskPair_eta] at hh
    exact hh

/-- Both sides retain literally the same old vertex map. -/
def normalizedTaskMapEquiv
    (hA : normalizedTaskFullAge B ht n D m priority A)
    (hC : normalizedTaskFullAge B ht n D m priority C) :
    ResetOrder.Unary.FullHom A C ≃
      Structure.Embedding (normalizedTaskDecode B ht n D m A)
        (normalizedTaskDecode B ht n D m C) where
  toFun := normalizedTaskDecodeMap B ht n D m
  invFun := normalizedTaskMapOfDecode B ht n D m priority hA hC
  left_inv _ := ResetOrder.Unary.fullHom_ext (fun _ => rfl)
  right_inv _ := Structure.Embedding.ext (fun _ => rfl)

end
end CCO.UnfilteredEP
