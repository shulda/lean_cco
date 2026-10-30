import CCO.APCharacter.Age.Alignment

/-! Finite images of genuine marked homomorphisms. The kernel quotient is
on a small finite formal carrier; collisions are retained, rather than
replaced by an injectivity or strong-amalgamation assumption. -/
universe u v w
namespace CCO.APCharacter.Age
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
noncomputable section
variable {V : Type} {D : PartialDiagram S V}

/-- Any homomorphism is injective on a complete leg, not necessarily on
its whole (possibly incomplete) domain. -/
theorem leg_injective (F : DiagramHom D) {Y : Type} (j : Y ↪ V)
    (complete : ∀ x y (h : x ≠ y),
      ∃ a, D.edge (j x) (j y) (j.injective.ne h) = some a) :
    Function.Injective (F.image ∘ j) := by
  intro x y hxy
  by_contra hne
  obtain ⟨a,ha⟩ := complete x y hne
  exact (S.atomRel_ne (F.preserves_edge _ _ _ _ ha)) hxy

/-- Completeness of the leg upgrades specified-edge preservation to full
literal optional-colour preservation, including all repeated pairs. -/
theorem leg_names (F T : DiagramHom D) {Y : Type} (j : Y ↪ V)
    (complete : ∀ x y (h : x ≠ y),
      ∃ a, D.edge (j x) (j y) (j.injective.ne h) = some a) :
    ∀ x y, taggedColour S (F.image (j x)) (F.image (j y)) =
      taggedColour S (T.image (j x)) (T.image (j y)) := by
  intro x y
  by_cases hxy : x = y
  · subst y
    have hF := (S.colour_none_iff (F.point (j x)) (F.point (j x))).mpr rfl
    have hT := (S.colour_none_iff (T.point (j x)) (T.point (j x))).mpr rfl
    change (⟨D.vertexSort (j x),D.vertexSort (j x),
      S.colour (F.point (j x)) (F.point (j x))⟩ : Colour S) =
      ⟨D.vertexSort (j x),D.vertexSort (j x),S.colour (T.point (j x)) (T.point (j x))⟩
    rw [hF,hT]
  · obtain ⟨a,ha⟩ := complete x y hxy
    have hF := F.preserves_edge _ _ _ _ ha
    have hT := T.preserves_edge _ _ _ _ ha
    exact congrArg (fun c => (⟨D.vertexSort (j x),D.vertexSort (j y),c⟩ : Colour S))
      (hF.trans hT.symm)

variable {S}
namespace FiniteImage
variable (F : DiagramHom D)
abbrev Carrier := Quotient (Setoid.ker F.image)
def point : Carrier F → Sigma X := Quotient.lift F.image (by intro a b h; exact h)
theorem point_mk (x : V) : point F (Quotient.mk _ x) = F.image x := rfl
theorem injective : Function.Injective (point F) := by
  intro x y
  induction x using Quotient.inductionOn with
  | _ a =>
    induction y using Quotient.inductionOn with
    | _ b => exact fun h => Quotient.sound h

variable {M : MaskData S}
def table (mark : Sigma X → Bit) : Age.Table S (Carrier F) :=
  Age.table S (point F) (fun x => mark (point F x))
theorem realized (mark : Sigma X → Bit) (hm : M.GlobalMarking mark) :
    Realized S M (table F mark) :=
  ⟨point F,fun x => mark (point F x),injective F,
    ⟨fun x => hm.1 _,fun x y => hm.2 _ _⟩,rfl⟩

def inclusion {Y : Type} (j : Y ↪ V)
    (complete : ∀ x y (h : x ≠ y),
      ∃ a, D.edge (j x) (j y) (j.injective.ne h) = some a) : Y ↪ Carrier F where
  toFun x := Quotient.mk _ (j x)
  inj' := by
    intro x y hxy
    apply leg_injective S F j complete
    exact congrArg (point F) hxy

/-- The complete marked legs embed into the actual finite image, with
full unary and optional-binary names. No condition compares the two legs. -/
def embedding {Y : Type} (T : Age.Table S Y) (j : Y ↪ V)
    (complete : ∀ x y (h : x ≠ y),
      ∃ a, D.edge (j x) (j y) (j.injective.ne h) = some a)
    (old : DiagramHom D) (bits : V → Bit) (mark : Sigma X → Bit)
    (hmark : ∀ x, mark (F.image x) = bits x)
    (howner : ∀ x, T.owner x = ownerEquiv S (D.vertexSort (j x),bits (j x)))
    (hcolour : ∀ x y, T.colour x y = colourEquiv S
      (taggedColour S (old.image (j x)) (old.image (j y)))) :
    @FirstOrder.Language.Embedding (Language S) Y (Carrier F)
      T.toStructure (table F mark).toStructure :=
  T.embedding (table F mark) (inclusion F j complete)
    (fun x => by
      change ownerEquiv S (D.vertexSort (j x),mark (F.image (j x))) = T.owner x
      rw [hmark,howner])
    (fun x y => by
      change colourEquiv S (taggedColour S (F.image (j x)) (F.image (j y))) = _
      rw [leg_names S F old j complete,hcolour])

end FiniteImage
end
end CCO.APCharacter.Age
