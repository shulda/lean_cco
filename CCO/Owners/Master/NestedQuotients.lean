import CCO.ExactCRT.AbstractRelations
import CCO.Owners.Provider.Enlargement
import CCO.Owners.Product.Descent
import CCO.RawExact.CanonicalQuotients

/-! Canonical nested quotients in the complete orbital language. Full
structural automorphisms preserve all coarse orbitals because their
pullbacks are unions of fine orbitals. No global automorphism lift or
source hypothesis is used. -/

namespace CCO.Owners.Master

open ExactCRT RawExact.CanonicalQuotients Product

variable {G A : Type*} [Group G] [MulAction G A]
variable {K J : Setoid A} [Invariant G K] [Invariant G J]

def nestedKernel (h : K ≤ J) : Setoid (Quotient K) :=
  Setoid.ker (Abstract.quotientMap h)

noncomputable def nestedQuotientEquiv (h : K ≤ J) :
    Quotient (nestedKernel h) ≃ Quotient J :=
  Setoid.quotientKerEquivOfSurjective (Abstract.quotientMap h)
    (Abstract.quotientMap_surjective h)

@[simp] theorem nestedQuotientEquiv_projection (h : K ≤ J) (x : Quotient K) :
    nestedQuotientEquiv h (Quotient.mk'' x) = Abstract.quotientMap h x := rfl

theorem nestedQuotientEquiv_original (h : K ≤ J) (x : A) :
    nestedQuotientEquiv h (Quotient.mk'' (Quotient.mk K x)) = Quotient.mk J x := rfl

theorem nested_projection_equivariant (h : K ≤ J) (g : G) (x : Quotient K) :
    Abstract.quotientMap h (g • x) = g • Abstract.quotientMap h x := by
  induction x using Quotient.inductionOn with | _ x => rfl

/-- Both carriers have their full original-action orbital language. -/
def nestedOrbitalQuotient (h : K ≤ J) :
    OrbitalQuotient (G := G) (id : Quotient K → Quotient K)
      (id : Quotient J → Quotient J) where
  ambient := Abstract.quotientMap h
  equivariant := nested_projection_equivariant h
  projection := Abstract.quotientMap h
  surjective := Abstract.quotientMap_surjective h
  target_injective := Function.injective_id
  commutes _ := rfl

/-- Recognition of H/K by the complete fine language, in both directions. -/
theorem nestedKernel_fullAut (h : K ≤ J)
    (f : OrbitalAut G (Quotient K) (id : Quotient K → Quotient K))
    (x y : Quotient K) :
    nestedKernel h (f.val x) (f.val y) ↔ nestedKernel h x y :=
  (nestedOrbitalQuotient h).kernel_iff f x y

instance nestedKernel_fullInvariant (h : K ≤ J) :
    Invariant (OrbitalAut G (Quotient K) (id : Quotient K → Quotient K))
      (nestedKernel h) where
  invariant f x y hxy := (nestedKernel_fullAut h f x y).mpr hxy

/-- The canonical set identification intertwines the genuine induced
full fine-automorphism action on the DOUBLE quotient. -/
theorem nestedQuotientEquiv_fullAut (h : K ≤ J)
    (f : OrbitalAut G (Quotient K) (id : Quotient K → Quotient K))
    (q : Quotient (nestedKernel h)) :
    nestedQuotientEquiv h (f • q) =
      ((nestedOrbitalQuotient h).action f).val (nestedQuotientEquiv h q) := by
  induction q using Quotient.inductionOn with
  | _ x => exact ((nestedOrbitalQuotient h).action_projection f x).symm

/-- Every full fine automorphism preserves EVERY original coarse colour. -/
theorem nested_fullAut_preserves_coarse (h : K ≤ J)
    (f : OrbitalAut G (Quotient K) (id : Quotient K → Quotient K))
    (a b : Quotient J) :
    GroupActions.orbital (G := G) a b
      (((nestedOrbitalQuotient h).action f).val a)
      (((nestedOrbitalQuotient h).action f).val b) :=
  orbitalAut_pair ((nestedOrbitalQuotient h).action f) a b

/-- The induced FULL fine-group orbitals are exactly the original coarse
orbitals. Only individual original group elements supply the converse;
there is no surjectivity assertion onto the full coarse automorphism group. -/
theorem nested_fullAut_orbital_iff (h : K ≤ J) (a b x y : Quotient J) :
    (∃ f : OrbitalAut G (Quotient K) (id : Quotient K → Quotient K),
      ((nestedOrbitalQuotient h).action f).val a = x ∧
      ((nestedOrbitalQuotient h).action f).val b = y) ↔
      GroupActions.orbital (G := G) a b x y := by
  constructor
  · rintro ⟨f,rfl,rfl⟩
    exact nested_fullAut_preserves_coarse h f a b
  · rintro ⟨g,hgx,hgy⟩
    let f : OrbitalAut G (Quotient K) (id : Quotient K → Quotient K) :=
      Provider.ambientAut g
    have hf (q : Quotient J) : ((nestedOrbitalQuotient h).action f).val q = g • q := by
      obtain ⟨z,rfl⟩ := Abstract.quotientMap_surjective h q
      exact ((nestedOrbitalQuotient h).action_projection f z).trans
        (nested_projection_equivariant h g z)
    exact ⟨f,(hf a).trans hgx,(hf b).trans hgy⟩

/-- Full canonical orbital colours on the iterated quotient are exactly
the original coarse colours, including equality. -/
theorem nestedQuotient_orbital_iff (h : K ≤ J)
    (a b x y : Quotient (nestedKernel h)) :
    GroupActions.orbital
      (G := OrbitalAut G (Quotient K) (id : Quotient K → Quotient K)) a b x y ↔
    GroupActions.orbital (G := G) (nestedQuotientEquiv h a) (nestedQuotientEquiv h b)
      (nestedQuotientEquiv h x) (nestedQuotientEquiv h y) := by
  constructor
  · rintro ⟨f,rfl,rfl⟩
    rw [nestedQuotientEquiv_fullAut,nestedQuotientEquiv_fullAut]
    exact nested_fullAut_preserves_coarse h f _ _
  · intro horb
    obtain ⟨f,hfa,hfb⟩ := (nested_fullAut_orbital_iff h _ _ _ _).mpr horb
    refine ⟨f,?_,?_⟩
    · apply (nestedQuotientEquiv h).injective
      rw [nestedQuotientEquiv_fullAut]
      exact hfa
    · apply (nestedQuotientEquiv h).injective
      rw [nestedQuotientEquiv_fullAut]
      exact hfb

end CCO.Owners.Master
