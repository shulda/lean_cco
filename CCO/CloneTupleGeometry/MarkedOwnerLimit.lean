import CCO.CloneTupleGeometry.ActualOldMonoClique
import CCO.CloneTupleGeometry.MarkedChildProduct
import CCO.APCharacter.SourceAge.UnarySourceHomogeneity

/-!
# B060 N03: distinct old owners in a real marked successor

A finite marked B047 configuration whose complete old-tagged colour
matrix comes from distinct ORIGINAL owners is still owner-injective
when decoded through the ACTUAL old-reduct back-and-forth
identification. The proof uses the B045 real owner/colour erasure
and the equality field of the full atomic source, not injectivity
of clone indices or a hypothetical quotient action.

Separately, a marked point with actual encoded child bit ε decodes
to an original owner carrying the matching real B047 child tag.
These are the two ingredients needed for finite injections into
the *owner* child of an actual homogeneous marked successor.
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

/-- B060 N03: the ACTUAL inverse B047 marking identification
cannot merge two distinct old a-clique owners, even though each
new child has infinitely many separate clone indices. The complete
literal colours, including original equality, are preserved. -/
theorem marked_limit_original_owners_injective
    (I : CloneMarkedIdentification S H C P cco)
    (i : ι) (n : ℕ)
    (points : Fin n ↪ X i)
    (f : Fin n ↪ Age.Limit (CloneSAP.source S)
      (CloneSAP.homogeneous S H)
      (P.completion_property (CloneSAP.CCO.cco_forward S cco)))
    (hcolour : ∀ x y : Fin n,
      (Age.limitCoding (CloneSAP.source S) (CloneSAP.homogeneous S H)
        (P.completion_property (CloneSAP.CCO.cco_forward S cco))).table.colour (f x) (f y) =
          Age.colourEquiv (CloneSAP.source S)
            (taggedColour (CloneSAP.source S)
              (⟨i,(points x,0)⟩ : Sigma (CloneSAP.Carrier X))
              (⟨i,(points y,0)⟩ : Sigma (CloneSAP.Carrier X)))) :
    Function.Injective
      (fun x : Fin n => CloneSAP.owner (I.equiv.symm (f x))) := by
  intro x y he
  let px : Sigma (CloneSAP.Carrier X) := I.equiv.symm (f x)
  let py : Sigma (CloneSAP.Carrier X) := I.equiv.symm (f y)
  have hClone :
      taggedColour (CloneSAP.source S) px py =
        taggedColour (CloneSAP.source S)
          (⟨i,(points x,0)⟩ : Sigma (CloneSAP.Carrier X))
          (⟨i,(points y,0)⟩ : Sigma (CloneSAP.Carrier X)) := by
    apply (Age.colourEquiv (CloneSAP.source S)).injective
    calc
      Age.colourEquiv (CloneSAP.source S)
          (taggedColour (CloneSAP.source S) px py) =
        (Age.limitCoding (CloneSAP.source S) (CloneSAP.homogeneous S H)
          (P.completion_property (CloneSAP.CCO.cco_forward S cco))).table.colour
            (I.equiv px) (I.equiv py) := by
              exact (UnarySource.colour_eq
                (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco))
                I px py).symm
      _ = (Age.limitCoding (CloneSAP.source S) (CloneSAP.homogeneous S H)
          (P.completion_property (CloneSAP.CCO.cco_forward S cco))).table.colour
            (f x) (f y) := by simp only [px,py,Equiv.apply_symm_apply]
      _ = _ := hcolour x y
  have hOld := CloneSAP.tagged_owner_eq S hClone
  change taggedColour S (CloneSAP.owner px) (CloneSAP.owner py) =
    taggedColour S (⟨i,points x⟩ : Sigma X) (⟨i,points y⟩ : Sigma X) at hOld
  have hSame : (⟨i,points x⟩ : Sigma X) = ⟨i,points y⟩ :=
    (UnarySource.equality_iff S _ _ _ _ hOld).mp he
  apply points.injective
  simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using hSame

include ap in
/-- Each ACTUAL marked-limit point with prescribed encoded child bit
descends through the true old-reduct identification to one ORIGINAL
owner in the corresponding B047 owner child. This statement does not
invent a point of a quotient carrier or assume marked-age SAP. -/
theorem marked_limit_point_owner_child
    (I : CloneMarkedIdentification S H C P cco)
    (i : ι) (ε : Bit) (hε : P.validBit i ε)
    (p : Sigma (CloneSAP.Carrier X))
    (hp :
      (Age.ownerEquiv (CloneSAP.source S)).symm
        ((Age.limitCoding (CloneSAP.source S) (CloneSAP.homogeneous S H)
          (P.completion_property (CloneSAP.CCO.cco_forward S cco))).table.owner
          (I.equiv p)) = (i,ε)) :
    ∃ q : OwnerChild S H C P cco I
        ⟨i,(⟨ε,hε⟩ : UnarySource.β
          (completion := P.completion_property
            (CloneSAP.CCO.cco_forward S cco)) I i)⟩,
      CloneSAP.owner p = (⟨i,q.val⟩ : Sigma X) := by
  have hs : p.1 = i :=
    (I.owner_sort p).symm.trans (congrArg Prod.fst hp)
  have hm :
      UnarySource.mark
        (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco))
        I p = ε := congrArg Prod.snd hp
  rcases p with ⟨j,z⟩
  change j = i at hs
  subst j
  let childbit : UnarySource.β
      (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco))
      I i := ⟨ε,hε⟩
  have ht : UnarySource.tag
      (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco))
      I i z = childbit := by
    apply Subtype.ext
    exact hm
  have hownerTag :
      ownerChildTag S H C P cco I i z.1 = childbit :=
    (marked_child_tag_fibre S H ap C P cco I i z.1 z.2).symm.trans ht
  exact ⟨⟨z.1,hownerTag⟩,rfl⟩

end
end CCO.CloneTupleGeometry
