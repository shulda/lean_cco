import CCO.CloneTupleGeometry.MarkedChildSourceEquiv

/-!
# B060 N02: transport of entire tagged finite diagrams across source equivalence

A genuine typed atomic source equivalence transports not only each pair
colour but the complete dependent sort-indexed code on pairs of points.
This is the general readout needed to move actual whole-source
homogeneity and CCO between the B047 marked child and its B045
owner-by-clone presentation. No replacement source is hypothesized.
-/

universe u v w
namespace CCO.CloneTupleGeometry.TypedAtomicSourceEquiv

variable {ι : Type u} {X Y : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X}
variable {T : AtomicSource.{u,v,w} ι Y}

/-- Concrete dependent-sum point isomorphism of two ACTUAL sources. -/
noncomputable def sigmaPoint (E : TypedAtomicSourceEquiv S T) :
    Sigma X ≃ Sigma Y where
  toFun p := ⟨p.1, E.point p.1 p.2⟩
  invFun p := ⟨p.1, (E.point p.1).symm p.2⟩
  left_inv := by
    rintro ⟨i,x⟩
    change (⟨i,(E.point i).symm (E.point i x)⟩ : Sigma X) = ⟨i,x⟩
    rw [Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨i,y⟩
    change (⟨i,E.point i ((E.point i).symm y)⟩ : Sigma Y) = ⟨i,y⟩
    rw [Equiv.apply_symm_apply]

/-- The typed pair-code transport retains BOTH sort coordinates
and maps the full optional atom, including the genuine none diagonal. -/
def taggedCodeMap (E : TypedAtomicSourceEquiv S T)
    (code : Σ i, Σ j, Option (S.Atom i j)) :
    Σ i, Σ j, Option (T.Atom i j) :=
  ⟨code.1,code.2.1,code.2.2.map (E.atom code.1 code.2.1)⟩

/-- Exact whole tagged-colour transport, including all ordered mixed
sort pairs, repeated points and the true logical diagonal. -/
theorem taggedColour_sigmaPoint (E : TypedAtomicSourceEquiv S T)
    (p q : Sigma X) :
    taggedColour T (sigmaPoint E p) (sigmaPoint E q) =
      taggedCodeMap E (taggedColour S p q) := by
  rcases p with ⟨i,x⟩
  rcases q with ⟨j,y⟩
  change
    (⟨i,j,T.colour (E.point i x) (E.point j y)⟩ :
      Σ i, Σ j, Option (T.Atom i j)) =
    (⟨i,j,(S.colour x y).map (E.atom i j)⟩ :
      Σ i, Σ j, Option (T.Atom i j))
  exact congrArg
    (fun z : Option (T.Atom i j) =>
      (⟨i,j,z⟩ : Σ i, Σ j, Option (T.Atom i j)))
    (E.colour x y)

/-- A complete finite old diagram of the original source
becomes a complete finite diagram of the target source with the
SAME indexing set and repeated-point equality pattern. -/
theorem finite_diagram_map (E : TypedAtomicSourceEquiv S T)
    {V : Type (max u v)} (f h : V → Sigma X)
    (hc : ∀ a b, taggedColour S (f a) (f b) =
      taggedColour S (h a) (h b)) :
    ∀ a b, taggedColour T (sigmaPoint E (f a)) (sigmaPoint E (f b)) =
      taggedColour T (sigmaPoint E (h a)) (sigmaPoint E (h b)) := by
  intro a b
  rw [taggedColour_sigmaPoint E,taggedColour_sigmaPoint E,hc]

end CCO.CloneTupleGeometry.TypedAtomicSourceEquiv
