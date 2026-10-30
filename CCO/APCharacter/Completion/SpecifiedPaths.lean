import CCO.APCharacter.Completion.Walks
import CCO.StrongExact.FinLinePath

/-! The pre-existing literal positive simple-path datatype is identified with
its actual graph walk. Only represented words are used, with no SAP input. -/
universe u v w z
namespace CCO.APCharacter.Completion
open StrongPC
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {V : Type z} (D : PartialDiagram S V)

noncomputable def specifiedWalk {x y : V} : SpecifiedPath D x y → (graph D).Walk x y
  | .edge h a ha => .cons ⟨h,a,ha⟩ .nil
  | .cons h _ a ha tail => .cons ⟨h,a,ha⟩ (specifiedWalk tail)

theorem specifiedWalk_support {x y : V} (p : SpecifiedPath D x y) :
    (specifiedWalk D p).support = p.vertexList := by
  induction p with
  | edge => rfl
  | cons _ _ _ _ p ih =>
    change _ :: (specifiedWalk D p).support = _ :: p.vertexList
    rw [ih]

theorem specifiedWalk_word {x y : V} (p : SpecifiedPath D x y) :
    walkWord D (specifiedWalk D p) = PositiveWord.toRawWord S p.word := by
  induction p with
  | edge h a ha =>
    change RawWord.atom (edgeAtom D ⟨h,a,ha⟩) (.nil _) = RawWord.atom a (.nil _)
    rw [edgeAtom_unique D ⟨h,a,ha⟩ h a ha]
  | cons h _ a ha p ih =>
    change RawWord.atom (edgeAtom D ⟨h,a,ha⟩) (walkWord D (specifiedWalk D p)) =
      RawWord.atom a (PositiveWord.toRawWord S p.word)
    rw [edgeAtom_unique D ⟨h,a,ha⟩ h a ha,ih]

noncomputable def simpleSpecifiedWalk {x y : V} (p : SimpleSpecifiedPath D x y) :
    (graph D).Path x y :=
  ⟨specifiedWalk D p.val,SimpleGraph.Walk.IsPath.mk' (by
    rw [specifiedWalk_support]
    exact p.property)⟩

/-- A common actual RAW endpoint atom for ALL graph paths also serves every
literal simple specified path, with identity outputs retained. -/
theorem graph_bound_specified_bound {x y : V}
    (a : X (D.vertexSort x)) (b : X (D.vertexSort y))
    (h : ∀ p : (graph D).Path x y, RawWord.relation S (walkWord D p.val) a b)
    (p : SimpleSpecifiedPath D x y) : PositiveWord.represented S p.val.word a b := by
  have hp := h (simpleSpecifiedWalk D p)
  change RawWord.relation S (walkWord D (specifiedWalk D p.val)) a b at hp
  rw [specifiedWalk_word] at hp
  rwa [PositiveWord.represented_toRawWord S]

end CCO.APCharacter.Completion
