import CCO.Owners.Product.FullGeometry
import CCO.ExactCRT.AbstractFibreProduct
import CCO.ExactCRT.ExactLattice
import CCO.RawExact.CanonicalQuotients

/-! C14 and C16 on literal original exact quotients. Every action,
set-realization and equality-inclusive fine readout is constructed. -/
universe u v w t
namespace CCO.Owners.Product
open RawExact ExactCRT
open RawExact.CanonicalQuotients

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{u,v,max u v,w} S)

/-- Exactness supplies original-action invariance. -/
def exactInvariant {i : ι} (E : ExactEq S H cco i) : Invariant G E.val where
  invariant := ParityHasse.Original.colourInvariant_groupInvariant S H
    (isExactEq_colourInvariant S H E.property)

section QuotientMaps
variable {A : Type*} [MulAction G A] {E F : Setoid A}
variable [Invariant G E] [Invariant G F]

theorem quotientMap_equivariant (h : E ≤ F) (g : G) (q : Quotient E) :
    Abstract.quotientMap h (g • q) = g • Abstract.quotientMap h q := by
  induction q using Quotient.inductionOn with
  | _ x => rfl
end QuotientMaps

/-- The actual product geometry. C14 uses only original symmetric
commutation; C16 separately invokes B002's discharged fine-orbital law.
The logical diagonal is retained through optional original atoms. -/
noncomputable def sourceGeometry {i : ι} (E F : ExactEq S H cco i) :
    letI := exactInvariant S H cco E
    letI := exactInvariant S H cco F
    letI := exactInvariant S H cco (E ⊓ F)
    letI := exactInvariant S H cco (E ⊔ F)
    ProductGeometry (G := G) (K := Quotient (E.val ⊓ F.val))
      (ED := Quotient E.val) (JC := Quotient F.val) (O := Quotient (E.val ⊔ F.val)) := by
  letI := exactInvariant S H cco E
  letI := exactInvariant S H cco F
  letI := exactInvariant S H cco (E ⊓ F)
  letI := exactInvariant S H cco (E ⊔ F)
  refine {
    pD := Abstract.quotientMap inf_le_left
    pC := Abstract.quotientMap inf_le_right
    rD := Abstract.quotientMap le_sup_left
    rC := Abstract.quotientMap le_sup_right
    equiv_pD := quotientMap_equivariant _
    equiv_pC := quotientMap_equivariant _
    equiv_rD := quotientMap_equivariant _
    equiv_rC := quotientMap_equivariant _
    full := Abstract.fibreProductEquiv E.val F.val (exactEq_commutes S H cco i E F)
    full_fst := ?_
    full_snd := ?_
    fine := ?_ }
  · intro q
    induction q using Quotient.inductionOn with | _ x => rfl
  · intro q
    induction q using Quotient.inductionOn with | _ x => rfl
  · intro a b x y
    induction a using Quotient.inductionOn with | _ a =>
      induction b using Quotient.inductionOn with | _ b =>
        induction x using Quotient.inductionOn with | _ x =>
          induction y using Quotient.inductionOn with | _ y =>
            obtain ⟨e,he⟩ := E.property
            obtain ⟨f,hf⟩ := F.property
            let Q : Bool → Type v := fun z => if z then Quotient F.val else Quotient E.val
            letI : ∀ z, MulAction G (Q z) := fun z => by cases z <;> dsimp [Q] <;> infer_instance
            let L : Bool → NonemptyExact S i i := fun z =>
              if z then f else e
            let π : ∀ z, X i → Q z := fun z => by cases z <;> exact Quotient.mk''
            have eqπ : ∀ z (g : G) x, π z (g • x) = g • π z x := by
              intro z g x; cases z <;> rfl
            have kerπ : ∀ z, GroupActions.kernel (π z) = evaluate S (L z).words := by
              intro z
              cases z
              · dsimp [π,L]
                rw [he]
                funext u v
                exact propext Quotient.eq
              · dsimp [π,L]
                rw [hf]
                funext u v
                exact propext Quotient.eq
            have kerκ : GroupActions.kernel (Quotient.mk'' : X i → Quotient (E.val ⊓ F.val)) =
                RawExact.familyMeet (fun z => evaluate S (L z).words) := by
              funext u v
              apply propext
              change (Quotient.mk'' u = Quotient.mk'' v) ↔ _
              rw [Quotient.eq]
              change (E.val u v ∧ F.val u v) ↔ (∀ z, evaluate S (L z).words u v)
              simp only [Bool.forall_bool,L,Bool.false_eq_true,↓reduceIte,
                he,hf]
            have h := actual_fine_pair_orbit_of_CCO S H cco L Q π
              (Quotient.mk'' : X i → Quotient (E.val ⊓ F.val)) eqπ
              (fun _ _ => rfl) kerπ kerκ a b x y
            change (GroupActions.orbital (G := G)
              (Quotient.mk E.val a) (Quotient.mk E.val b) (Quotient.mk E.val x) (Quotient.mk E.val y) ∧
              GroupActions.orbital (G := G)
              (Quotient.mk F.val a) (Quotient.mk F.val b) (Quotient.mk F.val x) (Quotient.mk F.val y)) ↔
              GroupActions.orbital (G := G)
              (Quotient.mk (E.val ⊓ F.val) a) (Quotient.mk (E.val ⊓ F.val) b)
              (Quotient.mk (E.val ⊓ F.val) x) (Quotient.mk (E.val ⊓ F.val) y)
            simpa only [Bool.forall_bool,π] using h

end CCO.Owners.Product
