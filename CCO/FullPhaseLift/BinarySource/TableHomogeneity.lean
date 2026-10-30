import CCO.APCharacter.SourceAge.BackAndForth
import Mathlib.Data.Set.Finite.Range

/-! Countable actual table homogeneity from the proved finite extension
property. Repeated tuple entries and finite or empty carriers are retained.
Applications must derive the finite extension property from full factors. -/

open scoped FirstOrder
open FirstOrder FirstOrder.Language
universe u v w z
namespace CCO.FullPhaseLift.BinarySource
open OwnerTransversal.CountableColour
open APCharacter.SourceAge
noncomputable section

/-- Actual finite table isomorphisms, including their full equality
pattern, extend to automorphisms once both finite extensions are proved. -/
theorem table_tuple_homogeneous {B : Type u} {C : Type v} {Y : Type w}
    [Countable Y] (T : Table B C Y) (ext : FiniteExtension T T)
    {V : Type z} [Finite V] (p q : V → Y)
    (heq : ∀ x y, p x = p y ↔ q x = q y)
    (ho : ∀ x, T.owner (p x) = T.owner (q x))
    (hc : ∀ x y, T.colour (p x) (p y) = T.colour (q x) (q y)) :
    ∃ e : Y ≃ Y,
      (∀ x, T.owner (e x) = T.owner x) ∧
      (∀ x y, T.colour (e x) (e y) = T.colour x y) ∧
      ∀ x, e (p x) = q x := by
  classical
  letI := T.toStructure
  let A : (language B C).Substructure Y := {
    carrier := Set.range p
    fun_mem := by intro n f; exact Empty.elim f }
  letI : Finite A := (Set.finite_range p).to_subtype
  let choose : A → V := fun a => a.property.choose
  have choose_spec (a : A) : p (choose a) = a.val := a.property.choose_spec
  let k : A ↪ Y := ⟨fun a => q (choose a),by
    intro a b hab
    apply Subtype.ext
    exact (choose_spec a).symm.trans (((heq _ _).mpr hab).trans (choose_spec b))⟩
  have hko (a : A) : T.owner (k a) = T.owner a.val := by
    change T.owner (q (choose a)) = T.owner a.val
    rw [← ho,choose_spec]
  have hkc (a b : A) : T.colour (k a) (k b) = T.colour a.val b.val := by
    change T.colour (q (choose a)) (q (choose b)) = T.colour a.val b.val
    rw [← hc,choose_spec,choose_spec]
  let f : A ↪[language B C] Y := {
    toFun := k
    inj' := k.injective
    map_fun' F := Empty.elim F
    map_rel' := by
      intro n R xs
      cases R with
      | owner b =>
        change (T.owner (k (xs 0)) = b) ↔ T.owner (xs 0).val = b
        rw [hko]
      | colour c =>
        change (T.colour (k (xs 0)) (k (xs 1)) = c) ↔
          T.colour (xs 0).val (xs 1).val = c
        rw [hkc] }
  have hfinite : OwnerTransversal.PacketBackAndForth.LocallyFinite (language B C) Y := by
    intro D hD
    exact hD.finite
  obtain ⟨e,he⟩ := OwnerTransversal.PacketBackAndForth.equiv_extending
    (language B C) Y Y hfinite hfinite
    (finiteExtension_firstOrder T T ext) (finiteExtension_firstOrder T T ext) A f
  have hnames := Table.embedding_preserves T T e.toEmbedding
  refine ⟨e.toEquiv,hnames.1,hnames.2,?_⟩
  intro x
  let a : A := ⟨p x,⟨x,rfl⟩⟩
  have hx := DFunLike.congr_fun he a
  change e (p x) = q (choose a) at hx
  exact hx.trans ((heq _ _).mp (choose_spec a))

end
end CCO.FullPhaseLift.BinarySource
