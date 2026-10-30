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

/-- Every nonempty genuine simple graph path is the literal specified-path
object, with the SAME vertex list and the SAME RAW word. -/
noncomputable def specifiedOfWalk {x y : V} (p : (graph D).Walk x y)
    (hp : p.IsPath) (hne : x ≠ y) :
    {t : SpecifiedPath D x y // t.vertexList = p.support ∧
      PositiveWord.toRawWord S t.word = walkWord D p} := by
  induction p with
  | nil => exact False.elim (hne rfl)
  | @cons x z y h r ih =>
    by_cases he : z = y
    · subst y
      have hr : r.Nil := (hp.of_cons.nil_iff_eq).mpr rfl
      cases hr
      refine ⟨SpecifiedPath.edge h.choose (edgeAtom D h) (edgeAtom_spec D h),rfl,rfl⟩
    · obtain ⟨t,hSupport,hWord⟩ := ih hp.of_cons he
      refine ⟨SpecifiedPath.cons h.choose hne (edgeAtom D h) (edgeAtom_spec D h) t,?_,?_⟩
      · change _ :: t.vertexList = _ :: r.support
        rw [hSupport]
      · change RawWord.atom _ (PositiveWord.toRawWord S t.word) = RawWord.atom _ (walkWord D r)
        rw [hWord]

noncomputable def graphToSpecified {x y : V} (p : (graph D).Path x y) (hne : x ≠ y) :
    SimpleSpecifiedPath D x y :=
  ⟨(specifiedOfWalk D p.val p.property hne).val,by
    rw [(specifiedOfWalk D p.val p.property hne).property.1]
    exact p.property.support_nodup⟩

theorem graphToSpecified_word {x y : V} (p : (graph D).Path x y) (hne : x ≠ y) :
    PositiveWord.toRawWord S (graphToSpecified D p hne).val.word = walkWord D p.val :=
  (specifiedOfWalk D p.val p.property hne).property.2

 theorem walkWord_append {x y z : V} (p : (graph D).Walk x y)
    (r : (graph D).Walk y z) :
    walkWord D (p.append r) = RawWord.append S (walkWord D p) (walkWord D r) := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    change RawWord.atom _ (walkWord D (p.append r)) =
      RawWord.atom _ (RawWord.append S (walkWord D p) (walkWord D r))
    rw [ih]

 theorem walkWord_reverse_relation {x y : V} (p : (graph D).Walk x y) :
    RawWord.relation S (walkWord D p.reverse) =
      TRel.converse (RawWord.relation S (walkWord D p)) := by
  induction p with
  | nil =>
    funext a b
    exact propext eq_comm
  | @cons x z y h p ih =>
    rw [SimpleGraph.Walk.reverse_cons,walkWord_append,RawWord.relation_append,ih]
    have edgeReverse : edgeAtom D h.symm = S.conv (edgeAtom D h) :=
      edgeAtom_unique D h.symm _ _ ((D.edge_reverse _ _ h.choose _).mp (edgeAtom_spec D h))
    change TRel.comp (TRel.converse (RawWord.relation S (walkWord D p)))
      (TRel.comp (S.atomRel (edgeAtom D h.symm)) (TRel.ident X _)) =
      TRel.converse (TRel.comp (S.atomRel (edgeAtom D h)) (RawWord.relation S (walkWord D p)))
    rw [TRel.comp_ident,edgeReverse,RawWord.atomRel_flip,TRel.converse_comp]

/-- Reversing the ALL-simple-path output test retains the SAME actual real
endpoint pair in reverse order, including literal identity outputs. -/
theorem graph_bound_reverse {x y : V}
    (a : X (D.vertexSort x)) (b : X (D.vertexSort y))
    (bound : ∀ p : (graph D).Path x y, RawWord.relation S (walkWord D p.val) a b) :
    ∀ p : (graph D).Path y x, RawWord.relation S (walkWord D p.val) b a := by
  intro p
  have h := bound ⟨p.val.reverse,p.property.reverse⟩
  rw [walkWord_reverse_relation] at h
  exact h

end CCO.APCharacter.Completion
