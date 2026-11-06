import CCO.CloneTupleGeometry.LoopedPhaseMarkedAge
import CCO.CloneSAP.CCO.Cycles
import CCO.CloneSAP.Homogeneity

/-!
# B060 N03: actual pure-clone instance of looped old-atom marked cliques

The B045 concrete pure clone cover of an original homogeneous AP/HOM-CCO
source carries the actual B047 reached character phase. An original
monochromatic a-clique lifts on clone-index zero to a clique of the SAME
old tagged atom; an original a-triangle is a true cloned a-triangle.
Therefore the actual B047 marked Fraisse limit realizes every such finite
clique with one prescribed valid phase bit.

This is a real original-source application, not an arbitrary unary-age
hypothesis. The extraction of DISTINCT original owner points from the
marked limit and the unlimited-size source cliques are separate steps.
-/

universe u v w t
namespace CCO.CloneTupleGeometry

open APCharacter
open RigidGroupoid.Geometry
noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G)
variable (C : ExactCalculus (CloneSAP.source S))
variable {r : ι} {A : Kernel (CloneSAP.source S) r}
variable (P : SourcePhase (CloneSAP.source S) (CloneSAP.homogeneous S H) C A)

/-- An actual original a-triangle, with genuine old diversity,
is still an a-triangle at clone-index zero in B045. -/
theorem pure_clone_old_loop_triangle
    {i : ι} (a : S.Atom i i)
    (h : S.Triangle a a a) :
    (CloneSAP.source S).Triangle (Sum.inl a) (Sum.inl a) (Sum.inl a) := by
  obtain ⟨x,y,z,hxy,hyz,hxz⟩ := h
  exact ⟨(x,0),(y,0),(z,0),
    (CloneSAP.colour_old_iff S (x,0) (y,0) a).mpr hxy,
    (CloneSAP.colour_old_iff S (y,0) (z,0) a).mpr hyz,
    (CloneSAP.colour_old_iff S (x,0) (z,0) a).mpr hxz⟩

/-- The concrete actual B045 source, with its B047 phase, realizes
any finite original old-a clique under one phase bit in the genuine
homogeneous marked limit. No clone fibre can be mistaken for an old-a
edge; these remain OLD tagged colours throughout. -/
theorem pure_clone_old_mono_marked_age_embeds
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (b : Reached (CloneSAP.source S) A)
    (a : S.Atom b.val b.val)
    (hTri : S.Triangle a a a)
    (ε : Bit) (hε : P.validBit b.val ε)
    (n : ℕ) (points : Fin n → X b.val)
    (hinj : Function.Injective points)
    (hmono : ∀ x y : Fin n, x ≠ y →
      S.colour (points x) (points y) = some a) :
    ∃ f : Fin n ↪ Age.Limit (CloneSAP.source S)
      (CloneSAP.homogeneous S H)
      (P.completion_property (CloneSAP.CCO.cco_forward S cco)),
      (∀ x : Fin n,
        (Age.ownerEquiv (CloneSAP.source S)).symm
          ((Age.limitCoding (CloneSAP.source S)
            (CloneSAP.homogeneous S H)
            (P.completion_property (CloneSAP.CCO.cco_forward S cco))).table.owner (f x)) =
            (b.val,ε)) ∧
      ∀ x y : Fin n,
        (Age.limitCoding (CloneSAP.source S) (CloneSAP.homogeneous S H)
          (P.completion_property (CloneSAP.CCO.cco_forward S cco))).table.colour (f x) (f y) =
          Age.colourEquiv (CloneSAP.source S)
            (taggedColour (CloneSAP.source S)
              (⟨b.val,(points x,0)⟩ : Sigma (CloneSAP.Carrier X))
              (⟨b.val,(points y,0)⟩ : Sigma (CloneSAP.Carrier X))) := by
  have hIndexInj : Function.Injective
      (fun j : Fin n => ((points j,0) : CloneSAP.Carrier X b.val)) := by
    intro x y h
    exact hinj (congrArg Prod.fst h)
  have hIndexMono : ∀ x y : Fin n, x ≠ y →
      (CloneSAP.source S).colour (points x,0) (points y,0) =
        some (Sum.inl a) := by
    intro x y h
    exact (CloneSAP.colour_old_iff S (points x,0) (points y,0) a).mpr
      (hmono x y h)
  exact phase_loop_mono_marked_age_embeds
    (CloneSAP.source S) (CloneSAP.homogeneous S H) C P
    (CloneSAP.CCO.cco_forward S cco) b (Sum.inl a)
    (pure_clone_old_loop_triangle S a hTri) ε hε n
    (fun j => (points j,0)) hIndexInj hIndexMono

end
end CCO.CloneTupleGeometry
