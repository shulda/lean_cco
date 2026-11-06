import CCO.CloneTupleGeometry.OwnerFiniteBaseSupport

/-! Complete finite-base owner types and the actual infinite monochromatic
selection inside such a type. All anchor spokes remain fixed. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w t
namespace CCO.CloneTupleGeometry
open APCharacter APCharacter.SourceAge RigidGroupoid.Geometry TerminalPowers
noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- The entire old named type over a finite actual base, including all
logical equality cases and the declared new point's original sort. -/
def ownerTypeOver {m : ℕ} (base : Fin m → Sigma X) {i : ι} (x : X i) : Set (X i) :=
  {y | ∀ a, taggedColour S (base a) ⟨i,y⟩ = taggedColour S (base a) ⟨i,x⟩}

theorem ownerType_self {m : ℕ} (base : Fin m → Sigma X) {i : ι} (x : X i) :
    x ∈ ownerTypeOver S base x := fun _ => rfl

/-- An infinite complete type cannot be the named equality type of any
anchor. Consequently every point in it lies outside the entire base. -/
theorem infinite_ownerType_avoids_base {m : ℕ} (base : Fin m → Sigma X)
    {i : ι} (x : X i) (hi : (ownerTypeOver S base x).Infinite)
    {y : X i} (hy : y ∈ ownerTypeOver S base x) (a : Fin m) :
    (⟨i,y⟩ : Sigma X) ≠ base a := by
  intro he
  have hbx : base a = (⟨i,x⟩ : Sigma X) :=
    (CloneSAP.tagged_diagonal S (hy a)).mp he.symm
  apply hi
  apply (Set.finite_singleton x).subset
  intro z hz
  have hbe : base a = (⟨i,z⟩ : Sigma X) :=
    (CloneSAP.tagged_diagonal S (hz a)).mpr hbx
  have hzx : (⟨i,z⟩ : Sigma X) = ⟨i,x⟩ := hbe.symm.trans hbx
  exact Set.mem_singleton_iff.mpr (by
    simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using hzx)

/-- The explicit infinite-tail argument is applied INSIDE one actual old
type. Its output points therefore keep every anchor spoke together. -/
theorem actual_infinite_old_mono_atom_subset {i : ι} (s : Set (X i)) (hs : s.Infinite) :
    ∃ a : S.Atom i i, S.Triangle a a a ∧
      ∃ f : ℕ ↪ X i, (∀ n, f n ∈ s) ∧
        ∀ m n : ℕ, m ≠ n → S.colour (f m) (f n) = some a := by
  classical
  letI : Infinite s := hs.to_subtype
  letI : Fintype (S.Atom i i) := S.finiteAtom i i
  have hsym (x y : s) : S.colour x.val y.val = S.colour y.val x.val := by
    cases hc : S.colour x.val y.val with
    | none =>
      have he := (S.colour_none_iff x.val y.val).mp hc
      exact ((S.colour_none_iff y.val x.val).mpr he.symm).symm
    | some a =>
      have hr := (S.colour_swap x.val y.val a).mp hc
      rw [S.symmetricLoop a] at hr
      exact hr.symm
  obtain ⟨c,g,hg⟩ := infinite_monochromatic_pairs
    (fun x y : s => S.colour x.val y.val) hsym
  let f : ℕ ↪ X i := g.trans ⟨Subtype.val,Subtype.val_injective⟩
  have hcol (m n : ℕ) (hmn : m ≠ n) : S.colour (f m) (f n) = c := hg m n hmn
  have hn : c ≠ none := by
    intro hc
    have he := (S.colour_none_iff (f 0) (f 1)).mp ((hcol 0 1 (by decide)).trans hc)
    have he' : f 0 = f 1 := by simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using he
    exact Nat.zero_ne_one (f.injective he')
  cases c with
  | none => exact (hn rfl).elim
  | some a =>
    exact ⟨a,⟨f 0,f 1,f 2,hcol 0 1 (by decide),hcol 1 2 (by decide),
      hcol 0 2 (by decide)⟩,f,fun n => (g n).property,hcol⟩

/-- A FULL typed colour equality transports the exact local mask test,
including its original endpoint tags. -/
theorem phase_allowed_of_tagged {Y : ι → Type v} (T : AtomicSource.{u,v,w} ι Y)
    (M : MaskData T) {p q x y : Sigma Y}
    (h : taggedColour T p q = taggedColour T x y) (ε η : Bit)
    (ha : M.allowed (T.colour x.2 y.2) ε η) :
    M.allowed (T.colour p.2 q.2) ε η := by
  exact Eq.mpr (congrArg (fun c : Age.Colour T => M.allowed c.2.2 ε η) h) ha

variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G) (ap : AgeAP S)
variable (C : ExactCalculus (CloneSAP.source S))
variable {r : ι} {A : Kernel (CloneSAP.source S) r}
variable (P : SourcePhase (CloneSAP.source S) (CloneSAP.homogeneous S H) C A)
variable (cco : SemanticCCO.{u,v,max u v,w} S)
variable (I : CloneMarkedIdentification S H C P cco)

/-- The actual child bit is the pulled-back marked-limit bit on a
literal zero-index clone of that owner. -/
theorem owner_zero_bit (q : Sigma (OwnerChild S H C P cco I)) :
    UnarySource.mark
      (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco))
      I (zeroClonePoint ((ownerProjection S H ap C P cco I).project q)) =
      q.1.2.val := by
  rcases q with ⟨c,q⟩
  exact congrArg Subtype.val q.property

end
end CCO.CloneTupleGeometry
