import CCO.AclOwners.CorrespondenceLift

/-! The global correspondence equivalence is constructed on ALL original
real points. Its transitivity is the actual finite fixed-owner lift, not
an assumed conditional-bijection composition law. -/
universe v w t
namespace CCO.AclOwners
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Geometry FinitePackets.Normalization RawExact
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)

include H in
theorem correspondence_functional_chain [Countable M] [DecidableEq M]
    (cco : SemanticCCO.{0,v,0,w} S) (E : ColourEq S ())
    (hE : ExactCRT.IsExactEq S (i := ()) E.val)
    {x y z x' : M} (hxy : correspondence S E x y) (hyz : correspondence S E y z)
    (hxx' : E x x') (hcol : col S x' z = col S x z) : x' = x := by
  classical
  by_cases hxz : x = z
  · subst z
    exact (col_none S x' x).mp (hcol.trans ((col_none S x x).mpr rfl))
  let f : M → M := fun a => if a = x then x' else a
  have hfx : f x = x' := if_pos rfl
  have hfz : f z = z := if_neg (Ne.symm hxz)
  have hpairs : ∀ a ∈ ({x,z} : Finset M), ∀ b ∈ ({x,z} : Finset M),
      col S (f a) (f b) = col S a b := by
    intro a ha b hb
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · rw [ha,hb,hfx]; exact ((col_none S x' x').mpr rfl).trans ((col_none S x x).mpr rfl).symm
    · rw [ha,hb,hfx,hfz]; exact hcol
    · rw [ha,hb,hfz,hfx,col_symm S z x',col_symm S z x]; exact hcol
    · rw [ha,hb,hfz]
  letI := originalQuotientAction S H E
  let q : M → Quotient E.val := Quotient.mk''
  obtain ⟨g,hg,howners⟩ := finite_fixed_owner_lift S H cco E hE {x,z} f hpairs
    (by
      intro a ha
      simp only [Finset.mem_insert,Finset.mem_singleton] at ha
      rcases ha with ha | ha
      · rw [ha,hfx]; exact hxx'
      · rw [ha]; simpa only [hfz] using E.val.refl z)
    {q x,q y,q z}
  have hgx : g • x = x' := (hg x (by simp)).trans hfx
  have hgz : g • z = z := (hg z (by simp)).trans hfz
  have hgyq : g • q y = q y := howners (q y) (by simp)
  have hEy : E y (g • y) := E.val.symm (Quotient.exact hgyq)
  have hgycol : col S z (g • y) = col S z y := by
    simpa only [hgz] using col_invariant S H g z y
  have hgy : g • y = y := (cutColour_functional S E (col S z y)
    (correspondence_symm S E hyz) rfl hgycol hEy).symm
  have hcolx : col S y x' = col S y x := by
    simpa only [hgy,hgx] using col_invariant S H g y x
  exact (cutColour_functional S E (col S y x)
    (correspondence_symm S E hxy) rfl hcolx hxx').symm

include H in
/-- C09: every outer actual colour is functional in every E-class.
Actual pair homogeneity transfers a realized two-edge path to each
candidate pair in the outer-colour square. -/
theorem correspondence_trans [Countable M] [DecidableEq M]
    (cco : SemanticCCO.{0,v,0,w} S) (E : ColourEq S ())
    (hE : ExactCRT.IsExactEq S (i := ()) E.val)
    {x y z : M} (hxy : correspondence S E x y) (hyz : correspondence S E y z) :
    correspondence S E x z := by
  intro a b hab hsq
  obtain ⟨c,hac,hcb⟩ := hsq
  obtain ⟨g,hgx,hgz⟩ := S.pair_homogeneous_of_homogeneous H x a z c hac.symm
  have hleft : correspondence S E a (g • y) := by
    change CutColour S E (col S a (g • y))
    have hh : col S a (g • y) = col S x y := by
      simpa only [hgx] using col_invariant S H g x y
    rw [hh]
    exact hxy
  have hright : correspondence S E (g • y) c := by
    change CutColour S E (col S (g • y) c)
    have hh : col S (g • y) c = col S y z := by
      simpa only [hgz] using col_invariant S H g y z
    rw [hh]
    exact hyz
  exact (correspondence_functional_chain S H cco E hE hleft hright hab
    ((col_symm S b c).trans (hcb.trans hac.symm))).symm

noncomputable def correspondenceEq [Countable M] [DecidableEq M]
    (cco : SemanticCCO.{0,v,0,w} S) (E : ColourEq S ())
    (hE : ExactCRT.IsExactEq S (i := ()) E.val) : ColourEq S () :=
  ⟨⟨correspondence S E,⟨correspondence_refl S E,
    fun h => correspondence_symm S E h,
    fun hxy hyz => correspondence_trans S H cco E hE hxy hyz⟩⟩,
    fun _ _ _ _ hc => by
      change col S _ _ = col S _ _ at hc
      change CutColour S E _ ↔ CutColour S E _
      rw [hc]⟩

/-- C05 derives finite-bottom thinness from the actual square regularizer.
The full finite packet may be a nonidentity NONEXACT equivalence. -/
theorem packet_le_correspondence (normalized : NoFiniteExactKernel S)
    (E : ColourEq S ()) {x y : M} (hxy : finitePacket S H x y) :
    correspondence S E x y := by
  have hc := terminal_greatest_finite_packet_thin S H normalized
    (col S x y) (fullColourBelow_at S (finitePacket S H) x y hxy)
  intro a b _ hab
  unfold colourSquare at hab
  exact (Iff.of_eq (congrFun (congrFun
    (thinColour_square_identity S (col S x y) hc) a) b)).mp hab

/-- C06: a cut edge inside E has a singleton real orbit over its first
endpoint, hence lies in the actual finite packet by accepted singleton
closure. No exactness of that packet is assumed. -/
theorem correspondence_inf_eq_packet [DecidableEq M]
    (cco : SemanticCCO.{0,v,0,w} S) (normalized : NoFiniteExactKernel S)
    (E : ColourEq S ()) {x y : M} :
    E x y ∧ correspondence S E x y ↔ E x y ∧ finitePacket S H x y := by
  constructor
  · rintro ⟨hE,hcut⟩
    refine ⟨hE,?_⟩
    have hy : y ∈ Acl G ({x} : Finset M) := by
      apply (Set.finite_singleton y).subset
      rintro z ⟨g,hg,hgz⟩
      have hgx := hg x (by simp)
      have hcol : col S x z = col S x y := by
        simpa only [hgx,hgz] using col_invariant S H g x y
      have hEz : E x z := by
        have hinv := (class_group_invariant S () H E g x y).mpr hE
        rwa [hgx,hgz] at hinv
      exact Set.mem_singleton_iff.mpr (cutColour_functional S E _ hcut rfl hcol
        (E.val.trans (E.val.symm hE) hEz)).symm
    rw [acl_singleton S H cco x] at hy
    exact hy
  · rintro ⟨hE,hF⟩
    exact ⟨hE,packet_le_correspondence S H normalized E hF⟩

end CCO.AclOwners
