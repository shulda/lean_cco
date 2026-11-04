import CCO.CloneTupleGeometry.MarkedOwnerLimit
import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

/-!
# B060 N03: infinitely many real owners survive an actual B047 split

For each actual reached old clone sort, an infinite set of original owners
provides a SINGLE old fine atom with a real loop triangle and arbitrarily
large monochromatic cliques. Those finite cliques embed into the ACTUAL
B047 marked Fraisse limit with ANY valid bit. The real old-reduct
identification and the proved clone-gate saturation produce distinct
members of the corresponding original owner CHILD. Thus that child
owner type is infinite, not just its product with the clone index.

Inactive B047 sorts have one forced zero bit, so the owner child is
an injective copy of the entire infinite original sort. All actual
child types are covered. This establishes the single-phase owner
infinitude step, not yet the finite terminal tower.
-/

universe u v w t
namespace CCO.CloneTupleGeometry

open APCharacter
open APCharacter.SourceAge
open RigidGroupoid.Geometry
noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G) (ap : AgeAP S)
variable (C : ExactCalculus (CloneSAP.source S))
variable {r : ι} {A : Kernel (CloneSAP.source S) r}
variable (P : SourcePhase (CloneSAP.source S) (CloneSAP.homogeneous S H) C A)
variable (cco : SemanticCCO.{u,v,max u v,w} S)

include ap in
/-- The genuine B045/B047 finite marked cliques yield injective maps
of EVERY finite size into the original owner child of a reached sort.
The target is the OWNER subtype, not the already infinite marked
point type or a clone fibre. -/
theorem marked_reached_owner_child_finite_embeddings
    (I : CloneMarkedIdentification S H C P cco)
    (b : Reached (CloneSAP.source S) A)
    [Infinite (X b.val)]
    (ε : Bit) (hε : P.validBit b.val ε)
    (n : ℕ) :
    Nonempty (Fin n ↪ OwnerChild S H C P cco I
      ⟨b.val,(⟨ε,hε⟩ : UnarySource.β
        (completion := P.completion_property
          (CloneSAP.CCO.cco_forward S cco)) I b.val)⟩) := by
  classical
  obtain ⟨a,hTri,hall⟩ :=
    actual_clone_old_mono_marked_age_unbounded S H C P cco b ε hε
  obtain ⟨points,f,hbit,hcolour⟩ := hall n
  have hget (x : Fin n) :
      ∃ q : OwnerChild S H C P cco I
          ⟨b.val,(⟨ε,hε⟩ : UnarySource.β
            (completion := P.completion_property
              (CloneSAP.CCO.cco_forward S cco)) I b.val)⟩,
        CloneSAP.owner (I.equiv.symm (f x)) =
          (⟨b.val,q.val⟩ : Sigma X) := by
    apply marked_limit_point_owner_child S H ap C P cco
      I b.val ε hε (I.equiv.symm (f x))
    simpa only [Equiv.apply_symm_apply] using hbit x
  let g : Fin n → OwnerChild S H C P cco I
      ⟨b.val,(⟨ε,hε⟩ : UnarySource.β
        (completion := P.completion_property
          (CloneSAP.CCO.cco_forward S cco)) I b.val)⟩ :=
    fun x => Classical.choose (hget x)
  have hg (x : Fin n) :
      CloneSAP.owner (I.equiv.symm (f x)) =
        (⟨b.val,(g x).val⟩ : Sigma X) :=
    Classical.choose_spec (hget x)
  have hownerInj :
      Function.Injective
        (fun x : Fin n => CloneSAP.owner (I.equiv.symm (f x))) :=
    marked_limit_original_owners_injective S H C P cco
      I b.val n points f hcolour
  refine ⟨⟨g,?_⟩⟩
  intro x y hxy
  apply hownerInj
  calc
    CloneSAP.owner (I.equiv.symm (f x)) =
      (⟨b.val,(g x).val⟩ : Sigma X) := hg x
    _ = (⟨b.val,(g y).val⟩ : Sigma X) := by rw [hxy]
    _ = CloneSAP.owner (I.equiv.symm (f y)) := (hg y).symm

include ap in
/-- Genuine reached B047 child owner types are infinite: for EVERY n,
the actual marked finite-age construction produces n different original
owners of the SAME target bit. An infinite clone fibre alone would not
prove this conclusion. -/
theorem marked_reached_owner_child_infinite
    (I : CloneMarkedIdentification S H C P cco)
    (b : Reached (CloneSAP.source S) A)
    [Infinite (X b.val)]
    (ε : Bit) (hε : P.validBit b.val ε) :
    Infinite (OwnerChild S H C P cco I
      ⟨b.val,(⟨ε,hε⟩ : UnarySource.β
        (completion := P.completion_property
          (CloneSAP.CCO.cco_forward S cco)) I b.val)⟩) := by
  classical
  let B : Type v := OwnerChild S H C P cco I
    ⟨b.val,(⟨ε,hε⟩ : UnarySource.β
      (completion := P.completion_property
        (CloneSAP.CCO.cco_forward S cco)) I b.val)⟩
  change Infinite B
  by_contra hn
  haveI : Finite B := (not_infinite_iff_finite).mp hn
  letI : Fintype B := Fintype.ofFinite B
  obtain ⟨f⟩ :=
    marked_reached_owner_child_finite_embeddings
      S H ap C P cco I b ε hε (Fintype.card B + 1)
  have hcard : Fintype.card B + 1 ≤ Fintype.card B := by
    simpa only [Fintype.card_fin] using
      (Fintype.card_le_of_injective f f.injective)
  omega

include ap in
/-- The ACTUAL marked B047 successor of an all-infinite pure-clone
source has infinite original-owner child types in EVERY named sort.
Inactive source sorts use their unique forced zero bit, not a
hypothetical extra phase marking. -/
theorem marked_all_owner_children_infinite
    [∀ i : ι, Infinite (X i)]
    (I : CloneMarkedIdentification S H C P cco) :
    ∀ c : APCharacter.Rank.Child (UnarySource.β
      (completion := P.completion_property
        (CloneSAP.CCO.cco_forward S cco)) I),
      Infinite (OwnerChild S H C P cco I c) := by
  intro c
  rcases c with ⟨i,⟨ε,hε⟩⟩
  by_cases hi : Nonempty (Bridge (CloneSAP.source S) A i)
  · let b : Reached (CloneSAP.source S) A := ⟨i,hi⟩
    exact marked_reached_owner_child_infinite
      S H ap C P cco I b ε hε
  · have htag (q : X i) :
        ownerChildTag S H C P cco I i q =
          (⟨ε,hε⟩ : UnarySource.β
            (completion := P.completion_property
              (CloneSAP.CCO.cco_forward S cco)) I i) := by
      apply Subtype.ext
      have hmark : P.validBit i
          (UnarySource.mark
            (completion := P.completion_property
              (CloneSAP.CCO.cco_forward S cco)) I ⟨i,(q,0)⟩) :=
        (UnarySource.global_marking
          (completion := P.completion_property
            (CloneSAP.CCO.cco_forward S cco)) I).1 ⟨i,(q,0)⟩
      exact (hmark hi).trans (hε hi).symm
    let g : X i → OwnerChild S H C P cco I
        ⟨i,(⟨ε,hε⟩ : UnarySource.β
          (completion := P.completion_property
            (CloneSAP.CCO.cco_forward S cco)) I i)⟩ :=
      fun q => ⟨q,htag q⟩
    have hg : Function.Injective g := by
      intro x y hxy
      exact congrArg Subtype.val hxy
    exact Infinite.of_injective g hg

include ap in
/-- The real back-and-forth identification used by B047 (constructed
rather than assumed) supplies a marked successor with all original
owner child sorts infinite. The source still requires actual old AP,
homogeneity, HOM CCO and per-sort countable infinitude. -/
theorem actual_clone_marked_owner_infinitude
    [∀ i : ι, Countable (X i)]
    [∀ i : ι, Infinite (X i)] :
    ∃ I : CloneMarkedIdentification S H C P cco,
      ∀ c : APCharacter.Rank.Child (UnarySource.β
        (completion := P.completion_property
          (CloneSAP.CCO.cco_forward S cco)) I),
        Infinite (OwnerChild S H C P cco I c) := by
  let I := actualCloneIdentification S H C P cco
  exact ⟨I, marked_all_owner_children_infinite S H ap C P cco I⟩

end
end CCO.CloneTupleGeometry
