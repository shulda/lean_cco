import CCO.ExactEPGeometry.ActualPrefixSupport
import CCO.APCharacter.Towers.CurrentSource

/-! B063 D01–D04: one ORIGINAL transitive sort, actual realized prefix
labels and their old-atom support. Logical equality is distinct from every
old diversity atom. Finite and zero-step sources are included. -/

universe u v w t
namespace CCO.AutomaticEPCore

open CCO.ParityHasse.Original CCO.APCharacter.Towers CCO.ExactEPGeometry

noncomputable section

/-- The unique original real carrier, identified by literal sort equalities. -/
def originalPointEquiv (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i) :
    Sigma A.Point ≃ A.Point base where
  toFun p := (hOne p.1).symm ▸ p.2
  invFun x := ⟨base,x⟩
  left_inv p := by
    rcases p with ⟨i,x⟩
    cases hOne i
    rfl
  right_inv _ := rfl

/-- Original diversity rank counts actual old atoms, never the diagonal. -/
def originalDiversityRank (A : CurrentSource.{u,v,w,t}) (base : A.Sorts) : Nat := by
  letI := A.source.finiteAtom base base
  exact Fintype.card (A.source.Atom base base)

/-- A literal relation on the original carrier, with both old sort tags retained. -/
def originalRelation (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (R : A.Point base → A.Point base → Prop) :
    Sigma A.Point → Sigma A.Point → Prop :=
  fun x y => R (originalPointEquiv A base hOne x) (originalPointEquiv A base hOne y)

/-- The actual old-atom table on EVERY realized prefix type. No predicate
names an individual newly created label. -/
def originalAtomTable (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (a : A.source.Atom base base) (s t : B.Sorts) : Prop :=
  prefixSupport P (originalRelation A base hOne (A.source.atomRel a)) s t

/-- Phi(Id) is the literal identity on ALL realized types, using real
point equality rather than a new diversity name. -/
theorem original_identity_support (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (s t : B.Sorts) :
    prefixSupport P (originalRelation A base hOne Eq) s t ↔ s = t := by
  constructor
  · rintro ⟨x,y,hxy⟩
    have hOld : P.project ⟨s,x⟩ = P.project ⟨t,y⟩ :=
      (originalPointEquiv A base hOne).injective hxy
    exact congrArg Sigma.fst (P.bijective.1 hOld)
  · intro hst
    subst t
    obtain ⟨x⟩ := B.source.nonemptySort s
    exact ⟨x,x,rfl⟩

/-- A diversity loop in the table witnesses TWO DISTINCT original points
of one prefix type. It never denotes the logical real identity. -/
theorem original_atom_table_diversity (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (a : A.source.Atom base base) {s t : B.Sorts}
    (hst : originalAtomTable A B P base hOne a s t) :
    ∃ (x : B.Point s) (y : B.Point t),
      originalPointEquiv A base hOne (P.project ⟨s,x⟩) ≠
        originalPointEquiv A base hOne (P.project ⟨t,y⟩) ∧
      A.source.atomRel a
        (originalPointEquiv A base hOne (P.project ⟨s,x⟩))
        (originalPointEquiv A base hOne (P.project ⟨t,y⟩)) := by
  obtain ⟨x,y,hxy⟩ := hst
  refine ⟨x,y,?_,hxy⟩
  intro heq
  change A.source.atomRel a
    (originalPointEquiv A base hOne (P.project ⟨s,x⟩))
    (originalPointEquiv A base hOne (P.project ⟨t,y⟩)) at hxy
  rw [heq] at hxy
  have hNone := (A.source.colour_none_iff
    (originalPointEquiv A base hOne (P.project ⟨t,y⟩))
    (originalPointEquiv A base hOne (P.project ⟨t,y⟩))).mpr rfl
  change A.source.colour
    (originalPointEquiv A base hOne (P.project ⟨t,y⟩))
    (originalPointEquiv A base hOne (P.project ⟨t,y⟩)) = some a at hxy
  rw [hNone] at hxy
  cases hxy

/-- The entire original point set is still in bijection with the entire
prefix carrier; this is not a section of an imaginary quotient. -/
def prefixOriginalPointEquiv (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i) :
    Sigma B.Point ≃ A.Point base :=
  (Equiv.ofBijective P.project P.bijective).trans (originalPointEquiv A base hOne)

/-- Every current type is an actual nonempty named sort, even for finite M. -/
theorem realized_prefix_type (B : CurrentSource.{u,v,w,t}) (s : B.Sorts) :
    Nonempty (B.Point s) := B.source.nonemptySort s

/-- In a true zero-step prefix over one original sort there cannot be two
label names. No infinite-source or positive rank assumption is needed. -/
theorem initial_type_unique (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (s t : A.Sorts) : s = t := (hOne s).symm.trans (hOne t)

end
end CCO.AutomaticEPCore
