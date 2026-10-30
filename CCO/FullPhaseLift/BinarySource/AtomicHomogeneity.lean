import CCO.FullPhaseLift.BinarySource.TableHomogeneity
import CCO.TerminalPowers.FullSource

/-! Actual source homogeneity from the concrete finite pair extension
property, via countable back-and-forth and the FULL binary automorphism
group. No equality between this group and the full old-language group is
asserted or required. -/

universe u v w
namespace CCO.FullPhaseLift.BinarySource
open OwnerTransversal.CountableColour
open APCharacter.SourceAge TerminalPowers
noncomputable section
variable {ι : Type u} {X : ι → Type v}

private theorem sigma_cast {i j : ι} (h : i = j) (x : X i) :
    (⟨j,cast (congrArg X h) x⟩ : Sigma X) = ⟨i,x⟩ := by
  cases h
  rfl

def fibreMap (e : Sigma X ≃ Sigma X) (hs : ∀ p, (e p).1 = p.1)
    (i : ι) (x : X i) : X i :=
  cast (congrArg X (hs ⟨i,x⟩)) (e ⟨i,x⟩).2

theorem fibreMap_sigma (e : Sigma X ≃ Sigma X) (hs : ∀ p, (e p).1 = p.1)
    (p : Sigma X) : (⟨p.1,fibreMap e hs p.1 p.2⟩ : Sigma X) = e p :=
  sigma_cast (hs p) (e p).2

theorem fibreMap_bijective (e : Sigma X ≃ Sigma X) (hs : ∀ p, (e p).1 = p.1)
    (i : ι) : Function.Bijective (fibreMap e hs i) := by
  constructor
  · intro x y he
    have h : e ⟨i,x⟩ = e ⟨i,y⟩ := by
      rw [← fibreMap_sigma e hs,← fibreMap_sigma e hs,he]
    simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using e.injective h
  · intro y
    let p := e.symm (⟨i,y⟩ : Sigma X)
    have hp : p.1 = i := by
      have h := hs p
      rw [e.apply_symm_apply] at h
      exact h.symm
    let x : X i := cast (congrArg X hp) p.2
    have hx : (⟨i,x⟩ : Sigma X) = p := sigma_cast hp p.2
    refine ⟨x,?_⟩
    have h : (⟨i,fibreMap e hs i x⟩ : Sigma X) = ⟨i,y⟩ := by
      apply (fibreMap_sigma e hs ⟨i,x⟩).trans
      rw [hx]
      exact e.apply_symm_apply _
    simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using h

def fibreEquiv (e : Sigma X ≃ Sigma X) (hs : ∀ p, (e p).1 = p.1)
    (i : ι) : X i ≃ X i :=
  Equiv.ofBijective (fibreMap e hs i) (fibreMap_bijective e hs i)

def fibreAut (S : AtomicSource.{u,v,w} ι X)
    (e : Sigma X ≃ Sigma X) (hs : ∀ p, (e p).1 = p.1)
    (hc : ∀ p q, taggedColour S (e p) (e q) = taggedColour S p q) :
    FullAut S := by
  refine ⟨fibreEquiv e hs,?_⟩
  intro i j x y
  change S.colour (fibreMap e hs i x) (fibreMap e hs j y) = S.colour x y
  have h := hc ⟨i,x⟩ ⟨j,y⟩
  rw [← fibreMap_sigma e hs,← fibreMap_sigma e hs] at h
  simpa only [taggedColour,Sigma.mk.injEq,heq_eq_eq,true_and] using h

theorem fibreAut_sigma (S : AtomicSource.{u,v,w} ι X)
    (e : Sigma X ≃ Sigma X) (hs : ∀ p, (e p).1 = p.1)
    (hc : ∀ p q, taggedColour S (e p) (e q) = taggedColour S p q)
    (p : Sigma X) : fibreAut S e hs hc • p = e p :=
  fibreMap_sigma e hs p

def sourceTable (S : AtomicSource.{u,v,w} ι X) :
    Table ι (Σ i, Σ j, Option (S.Atom i j)) (Sigma X) where
  owner := Sigma.fst
  colour := taggedColour S

/-- The actual countable source becomes homogeneous only AFTER its finite
extension property is proved. In B048 that property uses the full A03 lift,
not full homogeneity alone. -/
theorem homogeneous_of_finiteExtension (S : AtomicSource.{u,v,w} ι X)
    [Countable (Sigma X)]
    (ext : FiniteExtension (sourceTable S) (sourceTable S)) :
    HomogeneousSource S (FullAut S) where
  preserves_sort := by intro g p; rfl
  preserves_colours := by
    rintro g ⟨i,x⟩ ⟨j,y⟩
    exact congrArg (fun c => (⟨i,j,c⟩ : Σ i, Σ j, Option (S.Atom i j)))
      (g.property i j x y)
  extends_finite_diagram := by
    intro V _ p q hc
    have heq : ∀ x y, p x = p y ↔ q x = q y := by
      intro x y
      have h := congrArg (fun c : Σ i, Σ j, Option (S.Atom i j) => c.2.2.isNone) (hc x y)
      have hp : (S.colour (p x).2 (p y).2).isNone = true ↔ p x = p y := by
        rw [Option.isNone_iff_eq_none,S.colour_none_iff]
      have hq : (S.colour (q x).2 (q y).2).isNone = true ↔ q x = q y := by
        rw [Option.isNone_iff_eq_none,S.colour_none_iff]
      exact hp.symm.trans ((congrArg (fun z => z = true) h).to_iff.trans hq)
    obtain ⟨e,ho,hcol,he⟩ := table_tuple_homogeneous (sourceTable S) ext p q heq
      (fun x => congrArg (fun c : Σ i, Σ j, Option (S.Atom i j) => c.1) (hc x x)) hc
    refine ⟨fibreAut S e ho hcol,fun x => ?_⟩
    exact (fibreAut_sigma S e ho hcol (p x)).trans (he x)

end
end CCO.FullPhaseLift.BinarySource
