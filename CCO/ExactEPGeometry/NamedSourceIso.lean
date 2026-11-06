import CCO.ExactEPGeometry.SelectedSortSource
import CCO.SimultaneousQuotients.Towers.SourceIso

/-!
# Actual complete source isomorphisms with equivalent named sorts

A genuine tagged-point bijection over a genuine sort equivalence, preserving
and reflecting the complete pair-colour partition, gives an AtomicIso after
that exact reindexing. Atom maps come from realized diversity relations;
logical equality is preserved separately by the actual point bijection.
The resulting iso transports every whole induced diagram in both directions.
-/

universe u v w q z t
namespace CCO.ExactEPGeometry

open APCharacter.Towers
open CCO.SimultaneousQuotients.Towers

noncomputable section

variable {ι κ : Type u} {X : ι → Type v} {Y : κ → Type q}
variable (e : ι ≃ κ) (F : Sigma X ≃ Sigma Y)
variable (hOwner : ∀ p : Sigma X, (F p).1 = e p.1)

/-- Restrict a true tagged-point equivalence to its precise actual sort
fibres, using only its proved owner map. -/
def namedPointEquiv (i : ι) : X i ≃ Y (e i) :=
  (Equiv.sigmaSubtype i).symm.trans
    ((F.subtypeEquiv (fun p => by rw [hOwner]; exact e.injective.eq_iff.symm)).trans
      (Equiv.sigmaSubtype (e i)))

/-- The fibre equivalence is the SAME original tagged-point map. -/
theorem namedPointEquiv_tagged (i : ι) (x : X i) :
    (⟨e i,namedPointEquiv e F hOwner i x⟩ : Sigma Y) = F ⟨i,x⟩ := by
  change (⟨e i,(hOwner ⟨i,x⟩) ▸ (F ⟨i,x⟩).2⟩ : Sigma Y) = F ⟨i,x⟩
  have transport (p : Sigma Y) (h : p.1 = e i) :
      (⟨e i,h ▸ p.2⟩ : Sigma Y) = p := by
    rcases p with ⟨j,y⟩
    cases h
    rfl
  exact transport (F ⟨i,x⟩) (hOwner ⟨i,x⟩)

variable (S : AtomicSource.{u,v,w} ι X) (T : AtomicSource.{u,q,z} κ Y)
variable (hPalette : ∀ p s p' s' : Sigma X,
  taggedColour S p s = taggedColour S p' s' ↔
    taggedColour T (F p) (F s) = taggedColour T (F p') (F s'))

/-- A whole source isomorphism, including ALL actual diversity atoms,
after reindexing by the specified equivalent sort names. -/
def namedAtomicIso :
    letI := S.finiteSort
    AtomicIso S (selectedSortAtomicSource T e.toEmbedding) := by
  letI := S.finiteSort
  apply atomicIso S (selectedSortAtomicSource T e.toEmbedding)
    (namedPointEquiv e F hOwner)
  intro i j x x' y y'
  have h := hPalette ⟨i,x⟩ ⟨j,y⟩ ⟨i,x'⟩ ⟨j,y'⟩
  have hp (i : ι) (x : X i) := namedPointEquiv_tagged e F hOwner i x
  rw [←hp i x,←hp j y,←hp i x',←hp j y'] at h
  constructor
  · intro hc
    have hh := h.mp (congrArg (fun c =>
      (⟨i,j,c⟩ : Σ i : ι, Σ j : ι, Option (S.Atom i j))) hc)
    exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj hh).2)).2
  · intro hc
    have hh := h.mpr (congrArg (fun c =>
      (⟨e i,e j,c⟩ : Σ i : κ, Σ j : κ, Option (T.Atom i j))) hc)
    exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj hh).2)).2

end

noncomputable section

variable {ι : Type u} {X : ι → Type v} {Y : ι → Type q}
variable {S : AtomicSource.{u,v,w} ι X} {T : AtomicSource.{u,q,z} ι Y}

/-- A complete AtomicIso transports the ENTIRE induced diagram, in both
directions, with the same formal vertices and actual logical identities.
This applies in particular to every finite age diagram; no local-only
triangle test or quotient SAP is substituted for a full realization. -/
theorem atomicIso_inducedDiagram_iff
    (I : AtomicIso S T) {V : Type t}
    (owner : V → ι) (colour : ∀ a b, Option (S.Atom (owner a) (owner b))) :
    (∃ point : ∀ a, X (owner a),
      Function.Injective (fun a => (⟨owner a,point a⟩ : Sigma X)) ∧
      ∀ a b, S.colour (point a) (point b) = colour a b) ↔
    (∃ point : ∀ a, Y (owner a),
      Function.Injective (fun a => (⟨owner a,point a⟩ : Sigma Y)) ∧
      ∀ a b, T.colour (point a) (point b) = (colour a b).map (I.atom _ _)) := by
  let f : Sigma X ≃ Sigma Y := Equiv.sigmaCongrRight I.point
  constructor
  · rintro ⟨p,hp,hColour⟩
    refine ⟨fun a => I.point (owner a) (p a),f.injective.comp hp,?_⟩
    intro a b
    exact (I.colours _ _ _ _).symm.trans (congrArg (Option.map (I.atom _ _)) (hColour a b))
  · rintro ⟨p,hp,hColour⟩
    let old : ∀ a, X (owner a) := fun a => (I.point (owner a)).symm (p a)
    refine ⟨old,f.symm.injective.comp hp,?_⟩
    intro a b
    apply Option.map_injective (I.atom _ _).injective
    have h := I.colours (owner a) (owner b) (old a) (old b)
    dsimp only [old] at h
    rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply] at h
    exact h.trans (hColour a b)

end
end CCO.ExactEPGeometry
