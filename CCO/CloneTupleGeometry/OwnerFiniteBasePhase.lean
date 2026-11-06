import CCO.CloneTupleGeometry.OwnerFiniteBaseTypes
import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

/-! N09: one genuine safe phase preserves nonalgebraic owner types over
the FULL marked finite base. The entire anchored diagram receives one
global compatible seed, embeds once, and its marked base is aligned once. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w t
namespace CCO.CloneTupleGeometry
open APCharacter APCharacter.SourceAge RigidGroupoid.Geometry TerminalPowers
noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G) (ap : AgeAP S)
variable (C : ExactCalculus (CloneSAP.source S))
variable {r : ι} {A : Kernel (CloneSAP.source S) r}
variable (P : SourcePhase (CloneSAP.source S) (CloneSAP.homogeneous S H) C A)
variable (cco : SemanticCCO.{u,v,max u v,w} S)
variable (I : CloneMarkedIdentification S H C P cco)

/-- Arbitrarily many distinct owner realizations of the same actual child
type over all marked anchors, from an infinite original parent type. -/
theorem owner_child_type_finite_embeddings {m : ℕ}
    (base : Fin m ↪ Sigma (OwnerChild S H C P cco I))
    {c : Rank.Child (UnarySource.β
      (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I)}
    (x : OwnerChild S H C P cco I c)
    (hparent : (ownerTypeOver S
      ((ownerProjection S H ap C P cco I).project ∘ base) x.val).Infinite)
    (n : ℕ) :
    Nonempty (Fin n ↪ ownerTypeOver (owner_child_source S H ap C P cco I) base x) := by
  classical
  let pr := ownerProjection S H ap C P cco I
  let oldBase : Fin m → Sigma X := pr.project ∘ base
  obtain ⟨a,hTri,g,hmem,hmono⟩ := actual_infinite_old_mono_atom_subset S
    (ownerTypeOver S oldBase x.val) hparent
  let point : Fin m ⊕ Fin n → Sigma X :=
    Sum.elim oldBase (fun j => ⟨c.1,g j.val⟩)
  let bits : Fin m ⊕ Fin n → Bit :=
    Sum.elim (fun j => (base j).1.2.val) (fun _ => c.2.val)
  have hpoint : Function.Injective point := by
    intro z z' he
    cases z with
    | inl j =>
      cases z' with
      | inl k => exact congrArg Sum.inl (base.injective (pr.bijective.1 he))
      | inr k =>
        exact False.elim (infinite_ownerType_avoids_base S oldBase x.val hparent
          (hmem k.val) j he.symm)
    | inr j =>
      cases z' with
      | inl k =>
        exact False.elim (infinite_ownerType_avoids_base S oldBase x.val hparent
          (hmem j.val) k he)
      | inr k =>
        have he' : g j.val = g k.val := by
          simpa only [point,Sum.elim_inr,Sigma.mk.injEq,heq_eq_eq,true_and] using he
        exact congrArg Sum.inr (Fin.ext (g.injective he'))
  have hglobal (p q : Sigma (OwnerChild S H C P cco I)) :
      P.allows ((CloneSAP.source S).colour
        (zeroClonePoint (pr.project p)).2 (zeroClonePoint (pr.project q)).2)
        p.1.2.val q.1.2.val := by
    have hh := (UnarySource.global_marking
      (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I).2
      (zeroClonePoint (pr.project p)) (zeroClonePoint (pr.project q))
    rw [owner_zero_bit S H ap C P cco I p,owner_zero_bit S H ap C P cco I q] at hh
    exact hh
  have hlegal : Age.Legal (CloneSAP.source S) P.masks (zeroClonePoint ∘ point) bits := by
    constructor
    · intro z
      cases z with
      | inl j => exact (base j).1.2.property
      | inr j => exact c.2.property
    · intro z z'
      cases z with
      | inl j =>
        cases z' with
        | inl k => exact hglobal (base j) (base k)
        | inr k =>
          exact phase_allowed_of_tagged (CloneSAP.source S) P.masks
            (zeroClonePoint_tagged S ((hmem k.val) j)) _ _
            (hglobal (base j) ⟨c,x⟩)
      | inr j =>
        cases z' with
        | inl k =>
          exact phase_allowed_of_tagged (CloneSAP.source S) P.masks
            (zeroClonePoint_tagged S
              (RawExact.taggedColour_reverse_eq_of_eq S _ _ _ _ ((hmem j.val) k))) _ _
            (hglobal ⟨c,x⟩ (base k))
        | inr k =>
          change P.allows ((CloneSAP.source S).colour (g j.val,0) (g k.val,0)) c.2.val c.2.val
          by_cases hjk : j = k
          · subst k
            rw [show (CloneSAP.source S).colour (g j.val,0) (g j.val,0) = none from
              ((CloneSAP.source S).colour_none_iff _ _).mpr rfl]
            exact (P.allows_identity c.1 c.2.val c.2.val).mpr ⟨rfl,c.2.property⟩
          · have hc : (CloneSAP.source S).colour (g j.val,0) (g k.val,0) = some (Sum.inl a) :=
              (CloneSAP.colour_old_iff S _ _ a).mpr
                (hmono j.val k.val (Fin.val_injective.ne hjk))
            rw [hc]
            exact phase_loop_atom_same_bit_allowed (CloneSAP.source S)
              (CloneSAP.homogeneous S H) C P (Sum.inl a)
              (pure_clone_old_loop_triangle S a hTri) c.2.val c.2.property
  -- One actual global marking certifies the WHOLE anchored finite seed.
  obtain ⟨mark,hmark,hseed⟩ := Age.finite_seed_small (CloneSAP.source S)
    P.masks P.finite_seed_extension (zeroClonePoint ∘ point) bits hlegal
  have hglobalLegal : Age.Legal (CloneSAP.source S) P.masks (zeroClonePoint ∘ point) bits := by
    constructor
    · intro z
      have hh := hmark.1 ((zeroClonePoint ∘ point) z)
      rw [hseed z] at hh
      exact hh
    · intro z z'
      have hh := hmark.2 ((zeroClonePoint ∘ point) z) ((zeroClonePoint ∘ point) z')
      rw [hseed z,hseed z'] at hh
      exact hh
  obtain ⟨f,hfO,hfC⟩ := owner_marked_age_embeds S H ap C P cco I point bits hpoint hglobalLegal
  let T := owner_child_source S H ap C P cco I
  let HT := actual_marked_owner_homogeneous S H ap C P cco I
  have hlabelBase (j : Fin m) : ownerFiniteBaseLabel S H C P cco I (f (Sum.inl j)) =
      ownerFiniteBaseLabel S H C P cco I (base j) := hfO (Sum.inl j)
  have hlabelNew (j : Fin n) : ownerFiniteBaseLabel S H C P cco I (f (Sum.inr j)) =
      ownerFiniteBaseLabel S H C P cco I ⟨c,x⟩ := hfO (Sum.inr j)
  have hbaseC (j k : Fin m) : taggedColour T (f (Sum.inl j)) (f (Sum.inl k)) =
      taggedColour T (base j) (base k) :=
    owner_tagged_of_old_and_labels S H ap C P cco I (hlabelBase j) (hlabelBase k)
      (hfC (Sum.inl j) (Sum.inl k))
  obtain ⟨k,hk⟩ := HT.extends_finite_diagram
    (fun j : ULift.{max u v} (Fin m) => f (Sum.inl j.down))
    (fun j : ULift.{max u v} (Fin m) => base j.down)
    (fun j l => hbaseC j.down l.down)
  have hfix (j : Fin m) : k • f (Sum.inl j) = base j := hk ⟨j⟩
  let moved (j : Fin n) : Sigma (OwnerChild S H C P cco I) := k • f (Sum.inr j)
  have hsort (j : Fin n) : (moved j).1 = c := by
    change (f (Sum.inr j)).1 = c
    exact UnarySource.childLabel_injective I (hlabelNew j)
  let out (j : Fin n) : OwnerChild S H C P cco I c :=
    cast (congrArg (OwnerChild S H C P cco I) (hsort j)) (moved j).2
  have hout (j : Fin n) : (⟨c,out j⟩ : Sigma (OwnerChild S H C P cco I)) = moved j :=
    UnarySource.sigma_cast (hsort j) (moved j).2
  have houtInj : Function.Injective out := by
    intro j l he
    have hh : moved j = moved l := (hout j).symm.trans ((congrArg (Sigma.mk c) he).trans (hout l))
    have hh' : f (Sum.inr j) = f (Sum.inr l) := smul_left_cancel k hh
    exact Sum.inr.inj (f.injective hh')
  have htype (j : Fin n) : out j ∈ ownerTypeOver T base x := by
    intro l
    have hOld := (hfC (Sum.inl l) (Sum.inr j)).trans ((hmem j.val) l)
    have hnew := owner_tagged_of_old_and_labels S H ap C P cco I
      (hlabelBase l) (hlabelNew j) hOld
    have hh := HT.preserves_colours k (f (Sum.inl l)) (f (Sum.inr j))
    change taggedColour T (k • f (Sum.inl l)) (moved j) = _ at hh
    rw [hfix l,← hout j] at hh
    exact hh.trans hnew
  exact ⟨⟨fun j => ⟨out j,htype j⟩,fun j l he => houtInj (congrArg Subtype.val he)⟩⟩

/-- A nonalgebraic parent type remains nonalgebraic in EVERY realized
actual child type over the same FULL marked base, including empty bases. -/
theorem owner_child_type_infinite {m : ℕ}
    (base : Fin m ↪ Sigma (OwnerChild S H C P cco I))
    {c : Rank.Child (UnarySource.β
      (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I)}
    (x : OwnerChild S H C P cco I c)
    (hparent : (ownerTypeOver S
      ((ownerProjection S H ap C P cco I).project ∘ base) x.val).Infinite) :
    (ownerTypeOver (owner_child_source S H ap C P cco I) base x).Infinite := by
  classical
  intro hf
  let Y := ownerTypeOver (owner_child_source S H ap C P cco I) base x
  letI : Finite Y := hf.to_subtype
  letI : Fintype Y := Fintype.ofFinite Y
  obtain ⟨f⟩ := owner_child_type_finite_embeddings S H ap C P cco I base x hparent
    (Fintype.card Y + 1)
  have hc : Fintype.card Y + 1 ≤ Fintype.card Y := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f f.injective
  omega

end
end CCO.CloneTupleGeometry
