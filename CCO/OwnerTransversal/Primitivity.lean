import CCO.OwnerTransversal.TransversalModel
import CCO.OwnerTransversal.ColourSupportOverlap
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! The diversity support of an invariant equivalence on one named
transversal sort is transported to a GLOBAL original equivalence.
The actual finite-age instance of TransversalModel is constructed
internally in TransversalInstance, without a source provider premise. -/
universe v w t
namespace CCO.OwnerTransversal
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization CountableColour
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) {U : Type} (L : TransversalModel S H R B U)

abbrev OwnerFibre (s : ↥B) := {x : U // L.table.owner x = s}

def fibrePerm (s : ↥B) (f : TableAut S H R B L.table) :
    Equiv.Perm (OwnerFibre S H R B L s) where
  toFun x := ⟨f.val x.val,(TableAut.owner f x.val).trans x.property⟩
  invFun x := ⟨f.val.symm x.val,(TableAut.owner f⁻¹ x.val).trans x.property⟩
  left_inv x := Subtype.ext (f.val.symm_apply_apply x.val)
  right_inv x := Subtype.ext (f.val.apply_symm_apply x.val)

/-- Invariance under the FULL fine-coloured, individually named owner
automorphism group, rather than a chosen witness subgroup. -/
structure SortEquivalence (s : ↥B) where
  eqv : Setoid (OwnerFibre S H R B L s)
  invariant : ∀ f : TableAut S H R B L.table,
    ∀ x y, eqv x y → eqv (fibrePerm S H R B L s f x) (fibrePerm S H R B L s f y)

namespace SortEquivalence
variable {S H R B L} {s : ↥B} (Q : SortEquivalence S H R B L s)

def support : Set (FullColour S) :=
  {c | ∃ x y : OwnerFibre S H R B L s,
    x ≠ y ∧ Q.eqv x y ∧ L.table.colour x.val y.val = c}

/-- C36: homogeneity makes the invariant relation depend only on the
literal fine colour of each diversity pair in this named sort. -/
theorem support_iff (x y : OwnerFibre S H R B L s) (hne : x ≠ y) :
    L.table.colour x.val y.val ∈ Q.support ↔ Q.eqv x y := by
  constructor
  · rintro ⟨a,b,_,hab,hcol⟩
    obtain ⟨f,hfa,hfb⟩ := L.pair_homogeneous a.val b.val x.val y.val
      (a.property.trans x.property.symm) (b.property.trans y.property.symm) hcol
    have hh := Q.invariant f a b hab
    have ha : fibrePerm S H R B L s f a = x := Subtype.ext hfa
    have hb : fibrePerm S H R B L s f b = y := Subtype.ext hfb
    rwa [ha,hb] at hh
  · intro hxy
    exact ⟨x,y,hne,hxy,rfl⟩

theorem support_below : ∀ c ∈ Q.support, FullColourBelow S R.E c := by
  rintro c ⟨x,y,hne,_,hcol⟩
  obtain ⟨a,b,hoa,hob,hab,_⟩ := L.realize_pair x.val y.val
    (fun he => hne (Subtype.ext he))
  have hown : owner S H R a.val = owner S H R b.val := by
    rw [hoa,hob,x.property,y.property]
  have hE : R.E a.val b.val := Quotient.exact hown
  have hc := fullColourBelow_at S R.E a.val b.val hE
  rwa [hab,hcol] at hc

theorem support_nonthin : ∀ c ∈ Q.support, ∀ x y : M,
    col S x y = c → ¬ finitePacket S H x y := by
  rintro c ⟨a,b,hne,_,hcol⟩ x y hxy hF
  obtain ⟨u,v,_,_,huv,hnF⟩ := L.realize_pair a.val b.val
    (fun he => hne (Subtype.ext he))
  have heq : col S u.val v.val = col S x y := huv.trans (hcol.trans hxy.symm)
  exact hnF (((finitePacket S H).property u.val v.val x y heq).mpr hF)

/-- C36's strong composition condition uses ACTUAL original triangles.
Original transitivity moves their common E-class to the named owner;
the exact finite age then realizes the three distinct packets in U. -/
theorem support_closed : ∀ x y z : M,
    col S x y ∈ Q.support → col S y z ∈ Q.support →
    ¬ finitePacket S H x z → col S x z ∈ Q.support := by
  intro x y z hxy hyz hxz
  have hExy := Q.support_below _ hxy x y rfl
  have hEyz := Q.support_below _ hyz y z rfl
  have hnxy := Q.support_nonthin _ hxy x y rfl
  have hnyz := Q.support_nonthin _ hyz y z rfl
  obtain ⟨g,hgx⟩ := S.original_sort_transitive_of_homogeneous H () x s.val.out
  have ho₀ : owner S H R (g • x) = s.val := by
    rw [hgx]
    exact Quotient.out_eq s.val
  have ho₁ : owner S H R (g • y) = s.val := by
    apply Eq.trans _ ho₀
    apply Quotient.sound
    exact R.E.val.symm ((class_group_invariant S () H R.E g x y).mpr hExy)
  have ho₂ : owner S H R (g • z) = s.val := by
    apply Eq.trans _ ho₀
    apply Quotient.sound
    exact R.E.val.symm ((class_group_invariant S () H R.E g x z).mpr
      (R.E.val.trans hExy hEyz))
  let a : NamedCarrier S H R B := ⟨g • x,ho₀ ▸ s.property⟩
  let b : NamedCarrier S H R B := ⟨g • y,ho₁ ▸ s.property⟩
  let c : NamedCarrier S H R B := ⟨g • z,ho₂ ▸ s.property⟩
  let p : Fin 3 → NamedCarrier S H R B := ![a,b,c]
  have hp : ∀ i j : Fin 3, i ≠ j → ¬ finitePacket S H (p i).val (p j).val := by
    intro i j hij
    have hn₀₁ : ¬ finitePacket S H a.val b.val :=
      fun h => hnxy ((class_group_invariant S () H _ g x y).mp h)
    have hn₁₂ : ¬ finitePacket S H b.val c.val :=
      fun h => hnyz ((class_group_invariant S () H _ g y z).mp h)
    have hn₀₂ : ¬ finitePacket S H a.val c.val :=
      fun h => hxz ((class_group_invariant S () H _ g x z).mp h)
    fin_cases i <;> fin_cases j <;>
      simp only [p] at *
    all_goals first | exact False.elim (hij rfl) | exact hn₀₁ | exact hn₁₂ | exact hn₀₂ |
      exact fun h => hn₀₁ ((finitePacket S H).val.symm h) |
      exact fun h => hn₁₂ ((finitePacket S H).val.symm h) |
      exact fun h => hn₀₂ ((finitePacket S H).val.symm h)
  obtain ⟨f,hfo,hfc⟩ := L.embed p hp
  have hof (i : Fin 3) : L.table.owner (f i) = s := by
    apply Subtype.ext
    have hi : owner S H R (p i).val = s.val := by
      fin_cases i <;> simp only [p]
      exact ho₀
      exact ho₁
      exact ho₂
    exact (hfo i).trans hi
  let u : Fin 3 → OwnerFibre S H R B L s := fun i => ⟨f i,hof i⟩
  have hu (i j : Fin 3) (hij : i ≠ j) : u i ≠ u j :=
    fun he => hij (f.injective (congrArg Subtype.val he))
  have h₀₁ : L.table.colour (u 0).val (u 1).val ∈ Q.support := by
    rw [hfc 0 1]
    exact (col_invariant S H g x y).symm ▸ hxy
  have h₁₂ : L.table.colour (u 1).val (u 2).val ∈ Q.support := by
    rw [hfc 1 2]
    exact (col_invariant S H g y z).symm ▸ hyz
  have hQ := Q.eqv.trans ((Q.support_iff (u 0) (u 1) (hu _ _ (by decide))).mp h₀₁)
    ((Q.support_iff (u 1) (u 2) (hu _ _ (by decide))).mp h₁₂)
  have hout := (Q.support_iff (u 0) (u 2) (hu _ _ (by decide))).mpr hQ
  rw [hfc 0 2] at hout
  exact (col_invariant S H g x z) ▸ hout

/-- C37–39 with every support condition discharged from the actual
transversal age and original singleton-orbit geometry. -/
theorem support_conditions : ColourSupportConditions S (finitePacket S H) R.E
    (G := G) Q.support :=
  colourSupportConditions_of_triangles S (finitePacket S H) R.E H R.cco rfl
    Q.support Q.support_below Q.support_nonthin Q.support_closed

/-- C40–41: the global old-colour equivalence forced by a nontrivial
sort relation is infinite, hence equals the unique full direction E. -/
theorem support_full (hne : Q.support.Nonempty) {x y : M}
    (hE : R.E x y) (hnF : ¬ finitePacket S H x y) : col S x y ∈ Q.support := by
  let J := supportEquivalence S (finitePacket S H) R.E H (R.packet_thin S H)
    Q.support Q.support_conditions
  have hJE : J ≤ R.E := supportEquivalence_le S (finitePacket S H) R.E H
    (R.packet_thin S H) Q.support Q.support_conditions
  have hJinf : ¬ FiniteClasses S J := by
    intro hfin
    let x := Classical.choice (S.nonemptySort ())
    have hinf := supportEquivalence_infinite S (finitePacket S H) R.E H
      (R.packet_thin S H) Q.support Q.support_conditions R.cco rfl hne x
    exact hinf (Set.finite_coe_iff.mp (hfin x))
  have hEq : J = R.E := by
    by_contra hne
    exact hJinf ((R.isDirection S H).2 J (lt_of_le_of_ne hJE hne))
  have hxy : J x y := hEq.symm ▸ hE
  rcases hxy with ⟨e,_,rfl⟩ | hd
  · exact False.elim (hnF (translation_in_packet S (finitePacket S H) G e x))
  · exact hd

/-- C41: every individual named owner sort is primitive under the FULL
owner/fine-colour automorphism group of the actual transversal. -/
theorem equality_or_universal :
    (∀ x y, Q.eqv x y → x = y) ∨ ∀ x y, Q.eqv x y := by
  classical
  by_cases htrivial : ∀ x y, Q.eqv x y → x = y
  · exact Or.inl htrivial
  · right
    have hnonempty : Q.support.Nonempty := by
      simp only [not_forall] at htrivial
      obtain ⟨x,y,hxy,hne⟩ := htrivial
      exact ⟨L.table.colour x.val y.val,x,y,hne,hxy,rfl⟩
    intro x y
    by_cases hxy : x = y
    · subst y
      exact Q.eqv.refl x
    · obtain ⟨a,b,hoa,hob,hab,hnF⟩ := L.realize_pair x.val y.val
        (fun he => hxy (Subtype.ext he))
      have hE : R.E a.val b.val := Quotient.exact (by
        change owner S H R a.val = owner S H R b.val
        rw [hoa,hob,x.property,y.property])
      have hd := Q.support_full hnonempty hE hnF
      rw [hab] at hd
      exact (Q.support_iff x y hxy).mp hd

theorem eqv_eq_bot_or_top : Q.eqv = ⊥ ∨ Q.eqv = ⊤ := by
  rcases Q.equality_or_universal with h | h
  · left
    apply Setoid.ext
    intro x y
    exact ⟨h x y,fun he => he ▸ Q.eqv.refl x⟩
  · right
    apply Setoid.ext
    intro x y
    exact iff_of_true (h x y) trivial

end SortEquivalence
end
end CCO.OwnerTransversal
