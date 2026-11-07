import CCO.APRamseyReadout.OwnerAction
import CCO.APRamseyReadout.TupleScheme
import CCO.FullCode.EmbeddingBijection

/-! The actual owner action is a full embedding of the literal partial
hidden target and its faithful binary view. In particular the tuple action
uses these proved maps, not an additional equivariance/provider input. -/

universe u v w l k
namespace CCO.APRamseyReadout
open CCO.UnaryFreshFrames CCO.HiddenSAPReadings CCO.TerminalPowers
open CCO.CloneTupleGeometry CCO.UnaryTermsReturn
noncomputable section

section Partial
variable {L : CCO.UnaryFreshFrames.Language.{l}}
variable [Finite L.Sorts] [Finite L.Func] [Finite L.Rel]
variable {V : Type k} (P : CCO.UnaryFreshFrames.Structure L V)

private theorem partial_aut_func_iff (g : P.Aut) (F : L.Func) (x y : V) :
    y ∈ (partialTarget P).func F x ↔
      g • y ∈ (partialTarget P).func F (g • x) := by
  classical
  change y ∈ (if P.sort x = L.input F then {P.func F x} else ∅) ↔
    g • y ∈ (if P.sort (g • x) = L.input F then {P.func F (g • x)} else ∅)
  rw [P.aut_sort g x]
  by_cases hx : P.sort x = L.input F
  · simp only [if_pos hx,Set.mem_singleton_iff]
    rw [← P.aut_func g F x]
    exact ⟨fun h => congrArg (fun v => g • v) h,fun h => MulAction.injective g h⟩
  · simp only [if_neg hx,Set.mem_empty_iff_false]

/-- A genuine automorphism reflects the WHOLE prescribed partial unary
domain, rather than just edges whose output happened to be in the image. -/
def partialAutEmbedding (g : P.Aut) :
    CCO.UnarySupport.Structure.Embedding (partialTarget P) (partialTarget P) where
  point x := g • x
  injective := MulAction.injective g
  sort_eq x := P.aut_sort g x
  map_func F x y h := (partial_aut_func_iff P g F x y).mp h
  reflect_func F x y h := by
    refine ⟨g⁻¹ • y,?_,smul_inv_smul g y⟩
    apply (partial_aut_func_iff P g F x (g⁻¹ • y)).mpr
    simpa only [smul_inv_smul] using h
  map_rel R xs h := (P.aut_rel g R xs).mpr h
  reflect_rel R xs h := (P.aut_rel g R xs).mp h

end Partial

variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

/-- The canonical owner action in the SAME binary hidden target. -/
def ownerCoordinateMotion (g : FullAut B.source) :
    CCO.FullCode.Structure.Embedding (CoordinateTarget B ht) (CoordinateTarget B ht) :=
  TerminalHiddenHN.binaryEmbedding (Sig B ht)
    (TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B)
      (cloneSAP B) (fullCovers B ht))
    (partialAutEmbedding (Hidden B ht) (ownerHiddenHom B ht g))

@[simp] theorem ownerCoordinateMotion_point (g : FullAut B.source) (x : Values B) :
    (ownerCoordinateMotion B ht g).point x = ownerHiddenHom B ht g • x := rfl

variable (F : Charts.{u,v,w,l} B)

/-- Literal fixed-chart tuples are equivariant under this actual full
hidden embedding. Every coordinate is marked and keeps its original name. -/
theorem ownerRoot_equivariant (g : FullAut B.source) (x : Sigma B.Point) :
    (ownerRoot B ht F x).map (ownerCoordinateMotion B ht g) =
      ownerRoot B ht F (g • x) := by
  rcases x with ⟨i,x⟩
  apply CCO.FullCode.Root.ext_coordinates rfl
  intro j
  exact ownerHidden_named_node_zero B ht g (chartCoordinate B ht F i j) x

end
end CCO.APRamseyReadout
