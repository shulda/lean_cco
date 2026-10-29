import CCO.FiniteLift.OwnerCover

/-! All K/H mixed pair orbitals, including equality, are read in the
actual common join quotient. Exactness is needed later for the lift,
while the pair reduction itself is the accepted symmetric RAW algebra. -/

universe v w t
namespace CCO.FiniteLift
open RawExact OwnerCover
variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A]
variable (HS : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable (K H : ExactKernel S G)

theorem mixed_orbital (q q' : K.Q) (b b' : H.Q) :
    GroupActions.orbital (G := G) q b q' b' ↔
      GroupActions.orbital (G := G) (rK S HS cco K H q) (rH S HS cco K H b)
        (rK S HS cco K H q') (rH S HS cco K H b') := by
  apply actual_mixed_orbit_reduction_of_join S HS (i := ()) K.rel.r H.rel.r
    ⟨K.rel.refl,fun _ _ => K.rel.symm,fun _ _ _ => K.rel.trans⟩
    ⟨H.rel.refl,fun _ _ => H.rel.symm,fun _ _ _ => H.rel.trans⟩
    K.invariant H.invariant K.proj H.proj (J S HS cco K H).proj
    (rK S HS cco K H) (rH S HS cco K H) K.onto H.onto
    K.proj_smul H.proj_smul (J S HS cco K H).proj_smul
    (toJoinK_smul S HS cco K H) (toJoinH_smul S HS cco K H)
    (fun _ => rfl) (fun _ => rfl)
    (K.kernel.trans K.represents) (H.kernel.trans H.represents)
    (((J S HS cco K H).kernel.trans (J S HS cco K H).represents).trans
      (join_relation S HS K H))

end CCO.FiniteLift
