import CCO.RawExact.Convolution

/-!
# Canonical actual quotient sorts

Sort labels are actual setoids in a finite family, not word-presentation
records or independently named duplicate quotient copies. In particular
there is at most one identity quotient of the one original source sort.
This structural fact is needed by the private-path CCO expansion.

Pinned scope: raw_exact/module.json C26–C28 are `one_original_sort`;
PROOF_NOTES N09–N10 and thm:exact-sorts-source in
sections/exact_foundations/03_joint_exact_sort_lifting.tex concern M_E
for one original M. Earlier C21 typed joint lifting retains arbitrary
original-sort origins in its separate JointFamily API.
-/

universe v w t

namespace CCO.RawExact.CanonicalQuotients

variable {A : Type v}

abbrev Index (family : Finset (Setoid A)) := ↥family

abbrev Carrier {family : Finset (Setoid A)} (k : Index family) := Quotient k.val

def projection {family : Finset (Setoid A)} (k : Index family) : A → Carrier k :=
  Quotient.mk''

theorem projection_surjective {family : Finset (Setoid A)} (k : Index family) :
    Function.Surjective (projection k) := Quotient.mk''_surjective

theorem projection_kernel {family : Finset (Setoid A)} (k : Index family) :
    GroupActions.kernel (projection k) = k.val.r := by
  funext x y
  exact propext Quotient.eq

/-- Distinct canonical sorts cannot have equal actual quotient kernels. -/
theorem sort_eq_of_kernel_eq {family : Finset (Setoid A)}
    (k l : Index family)
    (h : GroupActions.kernel (projection k) = GroupActions.kernel (projection l)) :
    k = l := by
  apply Subtype.ext
  apply Setoid.ext
  intro x y
  rw [← projection_kernel k, ← projection_kernel l]
  rw [h]

/-- Two identity-kernel quotient sorts are the SAME canonical sort.
No nonduplicate-sort hypothesis is added to the source theorem. -/
theorem sort_eq_of_injective_projections {family : Finset (Setoid A)}
    (k l : Index family)
    (hk : Function.Injective (projection k))
    (hl : Function.Injective (projection l)) : k = l := by
  apply sort_eq_of_kernel_eq k l
  funext x y
  apply propext
  constructor
  · intro h
    exact congrArg (projection l) (hk h)
  · intro h
    exact congrArg (projection k) (hl h)

/-- Full-exactness is data about the actual equivalence relation.
Different presentations of that relation do not create new sort labels. -/
structure ExactData (S : AtomicSource.{0,v,w} Unit (fun _ => A))
    (family : Finset (Setoid A)) where
  exact : ∀ _ : Index family, NonemptyExact S () ()
  represents : ∀ k, evaluate S (exact k).words = k.val.r

/-- The relation is invariant under the actual original group action. -/
class Invariant (G : Type t) [Group G] [MulAction G A] (J : Setoid A) : Prop where
  invariant : ∀ (g : G) x y, J x y → J (g • x) (g • y)

instance quotientMulAction {G : Type t} [Group G] [MulAction G A]
    (J : Setoid A) [hJ : Invariant G J] : MulAction G (Quotient J) where
  smul g q := Quotient.map (fun x : A => g • x)
    (fun {x y} h => hJ.invariant g x y h) q
  one_smul q := by
    induction q using Quotient.inductionOn with
    | _ x => exact congrArg (Quotient.mk'' : A → Quotient J) (one_smul G x)
  mul_smul g h q := by
    induction q using Quotient.inductionOn with
    | _ x => exact congrArg (Quotient.mk'' : A → Quotient J) (mul_smul g h x)

theorem projection_equivariant {G : Type t} [Group G] [MulAction G A]
    {family : Finset (Setoid A)} (k : Index family) [Invariant G k.val]
    (g : G) (x : A) : projection k (g • x) = g • projection k x := rfl

/-- Exact source presentations supply actual quotient invariance;
this is proved rather than assumed as a new source provider. -/
theorem ExactData.invariant
    (S : AtomicSource.{0,v,w} Unit (fun _ => A))
    {G : Type t} [Group G] [MulAction G A]
    (H : HomogeneousSource S G)
    {family : Finset (Setoid A)} (E : ExactData S family)
    (k : Index family) : Invariant G k.val := by
  refine ⟨?_⟩
  intro g x y h
  rw [← E.represents k] at h ⊢
  exact presentation_invariant_of_homogeneous S H (E.exact k).words g x y h

end CCO.RawExact.CanonicalQuotients
