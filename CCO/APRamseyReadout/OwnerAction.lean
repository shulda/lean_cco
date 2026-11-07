import CCO.APRamseyReadout.ActualSource
import CCO.TypedOrbitFrames.CompletedStructureAction
import CCO.UnaryFreshFrames.Quotient.Named

/-! The actual owner automorphism group acts diagonally on its pure
clone source, and hence on the entire canonical hidden interpretation.
The fibre permutations are identities. No hidden homogeneity, choice of
coordinate chart, or bound on the length of a term is assumed. -/

universe u v w
namespace CCO.APRamseyReadout
open CCO.CloneTupleGeometry CCO.CloneTupleGeometry.OwnerStage
open CCO.TerminalPowers CCO.TypedOrbitFrames CCO.UnaryFreshFrames
open CCO.UnaryTermsReturn CCO.TransitionClosure
noncomputable section

variable (B : OwnerStage.{u,v,w})

/-- The owner structure is homogeneous in its actual full-colour
language, including the safe sort labels recorded in `B.Sorts`. -/
abbrev ownerHomogeneous : HomogeneousSource B.source (FullAut B.source) :=
  B.homogeneous

/-- Lift an owner automorphism by the identity bijection on every
countably infinite clone fibre. This is a genuine group homomorphism. -/
def ownerCloneHom : FullAut B.source →* FullAut (cloneSource B) where
  toFun g := CloneSAP.liftAut B.source g (fun _ _ => Equiv.refl ℕ)
  map_one' := by
    apply Subtype.ext
    funext i
    apply Equiv.ext
    intro x
    rfl
  map_mul' g h := by
    apply Subtype.ext
    funext i
    apply Equiv.ext
    intro x
    rfl

@[simp] theorem ownerCloneHom_apply (g : FullAut B.source)
    {i : B.Sorts} (x : B.Point i) (n : ℕ) :
    ownerCloneHom B g • (x,n) = (g • x,n) := rfl

/-- The same actual owner map preserves every fine clone colour. -/
theorem ownerCloneHom_colour (g : FullAut B.source)
    {i j : B.Sorts} (x : CloneSAP.Carrier B.Point i)
    (y : CloneSAP.Carrier B.Point j) :
    (cloneSource B).colour (ownerCloneHom B g • x) (ownerCloneHom B g • y) =
      (cloneSource B).colour x y :=
  (ownerCloneHom B g).property i j x y

variable (ht : B.Terminal)

/-- The owner action on ALL actual real and represented hidden values.
The canonical full source action used to construct `Hidden` is retained
literally; no separately supplied imaginary action occurs here. -/
def ownerHiddenHom : FullAut B.source →* (Hidden B ht).Aut :=
  (originalCompletedMotionHom (cloneSource B) (HF B) (cloneSAP B)
    (TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht))).comp
      (ownerCloneHom B)

@[simp] theorem ownerHiddenHom_apply (g : FullAut B.source) (x : Values B) :
    ownerHiddenHom B ht g • x =
      originalCompletedNamedAct (cloneSource B) (HF B) (ownerCloneHom B g) x := rfl

@[simp] theorem ownerHidden_real (g : FullAut B.source)
    {i : B.Sorts} (x : B.Point i) (n : ℕ) :
    ownerHiddenHom B ht g • (Sum.inl ⟨i,(x,n)⟩ : Values B) =
      Sum.inl ⟨i,(g • x,n)⟩ := rfl

/-- A canonical named quotient node is moved using the SAME named
coordinate and the literal diagonal image of its representative. This
holds for every actual coordinate, not just the selected visible chart. -/
@[simp] theorem ownerHidden_named_node (g : FullAut B.source)
    {i : B.Sorts} (D : OriginalNamedHiddenCoordinate (cloneSource B) (HF B) i)
    (x : B.Point i) (n : ℕ) :
    ownerHiddenHom B ht g • originalCompletedNamedHiddenNode (cloneSource B) (HF B) D
        (Quotient.mk D.val.val (x,n)) =
      originalCompletedNamedHiddenNode (cloneSource B) (HF B) D
        (Quotient.mk D.val.val (g • x,n)) := rfl

theorem ownerHidden_named_node_zero (g : FullAut B.source)
    {i : B.Sorts} (D : OriginalNamedHiddenCoordinate (cloneSource B) (HF B) i)
    (x : B.Point i) :
    ownerHiddenHom B ht g • originalCompletedNamedHiddenNode (cloneSource B) (HF B) D
        (Quotient.mk D.val.val (x,0)) =
      originalCompletedNamedHiddenNode (cloneSource B) (HF B) D
        (Quotient.mk D.val.val (g • x,0)) :=
  ownerHidden_named_node B ht g D x 0

/-- Every actual named function, including its off-sort identity
bookkeeping, commutes with the owner action. -/
theorem ownerHidden_func (g : FullAut B.source) (F : (Lang B ht).Func)
    (x : Values B) :
    ownerHiddenHom B ht g • (Hidden B ht).func F x =
      (Hidden B ht).func F (ownerHiddenHom B ht g • x) :=
  (Hidden B ht).aut_func (ownerHiddenHom B ht g) F x

/-- Every actual hidden relation is preserved and reflected by the
lifted owner map. In particular all mixed quotient cylinders survive. -/
theorem ownerHidden_rel (g : FullAut B.source) (R : (Lang B ht).Rel)
    (xs : Fin ((Lang B ht).arity R) → Values B) :
    (Hidden B ht).rel R ((fun x => ownerHiddenHom B ht g • x) ∘ xs) ↔
      (Hidden B ht).rel R xs :=
  (Hidden B ht).aut_rel (ownerHiddenHom B ht g) R xs

/-- Evaluation equivariance for an arbitrary actual named term and
arbitrary actual input value, including orphan quotient values. -/
theorem ownerHidden_eval (g : FullAut B.source)
    {s t : (Lang B ht).Sorts} (word : Term (Lang B ht) s t) (x : Values B) :
    ownerHiddenHom B ht g • (Hidden B ht).eval word x =
      (Hidden B ht).eval word (ownerHiddenHom B ht g • x) :=
  (Hidden B ht).aut_eval (ownerHiddenHom B ht g) word x

theorem ownerHidden_typedEval (g : FullAut B.source)
    {s t : (Lang B ht).Sorts} (word : Term (Lang B ht) s t)
    (x : (Hidden B ht).Carrier s) :
    ownerHiddenHom B ht g • (Hidden B ht).typedEval word x =
      (Hidden B ht).typedEval word (ownerHiddenHom B ht g • x) := by
  apply Subtype.ext
  exact ownerHidden_eval B ht g word x.val

/-- Any term starting at any actual proper named coordinate has the
literal owner-equivariant value at its canonical representative. The
target may be any actual hidden output sort and the term is unrestricted. -/
theorem ownerHidden_named_term (g : FullAut B.source)
    {i : B.Sorts} (D : OriginalNamedHiddenCoordinate (cloneSource B) (HF B) i)
    {s : (Lang B ht).Sorts}
    (word : Term (Lang B ht) ⟨⟨i,Sum.inr D⟩⟩ s)
    (x : B.Point i) (n : ℕ) :
    ownerHiddenHom B ht g • (Hidden B ht).eval word
        (originalCompletedNamedHiddenNode (cloneSource B) (HF B) D
          (Quotient.mk D.val.val (x,n))) =
      (Hidden B ht).eval word
        (originalCompletedNamedHiddenNode (cloneSource B) (HF B) D
          (Quotient.mk D.val.val (g • x,n))) :=
  (ownerHidden_eval B ht g word _).trans
    (congrArg ((Hidden B ht).eval word) (ownerHidden_named_node B ht g D x n))

end
end CCO.APRamseyReadout
