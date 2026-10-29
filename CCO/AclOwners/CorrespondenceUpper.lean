import CCO.AclOwners.CorrespondenceGeometry

/-! The ORIGINAL correspondence has exactly one least strict
coarsening. Actual relative classes, rather than division of infinite
cardinals, prove that it has no finite-index strict coarsening. -/
universe v w t
namespace CCO.AclOwners
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Geometry FinitePackets.Normalization RawExact
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (cco : SemanticCCO.{0,v,0,w} S)
variable (normalized : NoFiniteExactKernel S)
include normalized

theorem direction_le_strict_correspondence_upper (D : Direction S)
    (V : ColourEq S ()) (hV : oldCorrespondence S H cco D < V) : D.val ≤ V := by
  classical
  by_contra hle
  have hstrict : D.val ⊓ V < D.val := lt_of_le_of_ne inf_le_left (by
    intro he
    exact hle (by rw [← he]; exact inf_le_right))
  have hf : FiniteClasses S (D.val ⊓ V) := D.property.2 _ hstrict
  have hn : ¬ V ≤ oldCorrespondence S H cco D := hV.not_ge
  change ¬ ∀ ⦃x y : M⦄, V x y → oldCorrespondence S H cco D x y at hn
  push_neg at hn
  obtain ⟨x,y,hVxy,hnR⟩ := hn
  apply hnR
  have hfin : ∀ u v, D.val u v → colourSquare S (col S x y) u v → finitePacket S H u v := by
    intro u v hD huv
    obtain ⟨z,huz,hzv⟩ := huv
    have hVuz := (V.property x y u z huz.symm).mp hVxy
    have hVzv := (V.property x y z v hzv.symm).mp hVxy
    exact le_finitePacket S H _ hf ⟨hD,V.val.trans hVuz hVzv⟩
  have he := finite_exact_intersection S H cco normalized D.val
    (direction_exact S H cco D) (col S x y) hfin
  intro u v hD huv
  exact (Iff.of_eq (congrFun (congrFun he u) v)).mp ⟨hD,huv⟩

theorem direction_not_le_own_correspondence (D : Direction S) :
    ¬ D.val ≤ oldCorrespondence S H cco D := by
  intro h
  apply D.property.1
  apply finiteClasses_of_le S (F := finitePacket S H) ?_ (finitePacket_finite S H)
  intro x y hD
  exact ((correspondence_inf_eq_packet S H cco normalized D.val).mp ⟨hD,h hD⟩).2

/-- C17's least strict coarsening, in the FULL invariant lattice. -/
theorem oldCorrespondence_least_upper (D : Direction S) :
    oldCorrespondence S H cco D < ColourEq.join S H D.val (oldCorrespondence S H cco D) ∧
    ∀ V : ColourEq S (), oldCorrespondence S H cco D < V →
      ColourEq.join S H D.val (oldCorrespondence S H cco D) ≤ V := by
  letI := ColourEq.lattice S H (i := ())
  refine ⟨lt_of_le_of_ne le_sup_right ?_,?_⟩
  · intro he
    exact direction_not_le_own_correspondence S H cco normalized D
      (he ▸ (show D.val ≤ D.val ⊔ oldCorrespondence S H cco D from le_sup_left))
  · intro V hV
    exact sup_le (direction_le_strict_correspondence_upper S H cco normalized D V hV) hV.le

theorem oldCorrespondence_upper_index_infinite (D : Direction S) :
    ¬ FiniteIndex S (oldCorrespondence S H cco D)
      (ColourEq.join S H D.val (oldCorrespondence S H cco D)) := by
  letI := ColourEq.lattice S H (i := ())
  let R := oldCorrespondence S H cco D
  intro hfin
  have hRmeet : FiniteIndex S (R ⊓ D.val) D.val := by
    intro x
    have hfin' : Finite (RelativeClass R.val (ColourEq.join S H R D.val).val x) := by
      have he : ColourEq.join S H R D.val = ColourEq.join S H D.val R := sup_comm R D.val
      rw [he]
      exact hfin x
    letI := hfin'
    exact Finite.of_equiv _ (classTransposition S H R D.val x).symm
  have hmeet : FiniteClasses S (R ⊓ D.val) := by
    apply finiteClasses_of_le S (F := finitePacket S H) ?_ (finitePacket_finite S H)
    intro x y hxy
    exact ((correspondence_inf_eq_packet S H cco normalized D.val).mp ⟨hxy.2,hxy.1⟩).2
  apply D.property.1
  apply (finiteIndex_bottom_iff_finite_classes S D.val).mp
  exact finiteIndex_trans S ⊥ (R ⊓ D.val) D.val bot_le inf_le_right
    ((finiteIndex_bottom_iff_finite_classes S _).mpr hmeet) hRmeet

theorem oldCorrespondence_sigma (D : Direction S) :
    sigma S H (oldCorrespondence S H cco D) = oldCorrespondence S H cco D := by
  apply le_antisymm ?_ (le_sigma S H _)
  by_contra h
  have hstrict := lt_of_le_of_ne (le_sigma S H (oldCorrespondence S H cco D))
    (fun he => h he.symm.le)
  have hD := (oldCorrespondence_least_upper S H cco normalized D).2 _ hstrict
  exact oldCorrespondence_upper_index_infinite S H cco normalized D
    (finiteIndex_lower S hD (finiteIndex_sigma S H _))

theorem oldCore_sigma (D : Direction S) :
    sigma S H (oldCore S H cco D) = oldCorrespondence S H cco D :=
  (sigma_core S H cco _).trans (oldCorrespondence_sigma S H cco normalized D)

end CCO.AclOwners
