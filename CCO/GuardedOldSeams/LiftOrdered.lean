import CCO.GuardedOldSeams.LiftSplitting
import CCO.GuardedTwoRoot.SourceRootSignature
import Mathlib.Data.Fintype.EquivFin

/-! One orientation for each old root pair. This finite bookkeeping
prevents duplicate direct edges in the visible simple graph; it imposes
no order or extra relation on the hidden source. -/

universe u v w r z
namespace CCO.GuardedOldSeams
open CCO.UnarySupport CCO.UnarySupport.Structure
open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames CCO.HiddenSAPReadings
open CCO.GuardedTwoRoot CCO.StrongExact
noncomputable section

def liftRootRank {P : Type z} [Finite P] (p : P) : ℕ :=
  letI : Fintype P := Fintype.ofFinite P
  ((Fintype.equivFin P) p).val

theorem liftRootRank_injective {P : Type z} [Finite P] :
    Function.Injective (liftRootRank (P := P)) := by
  letI : Fintype P := Fintype.ofFinite P
  intro p q h
  exact (Fintype.equivFin P).injective (Fin.ext h)

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
local notation "Lang" => originalCompletedLanguage S H sap nr2
local notation "Hidden" => originalCompletedStructure S H sap nr2
variable {P : Type z} [Finite P]
variable (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)

abbrev OrderedGuardedPair := {k : GuardedPair S H sap nr2 F //
  liftRootRank k.val.1 < liftRootRank k.val.2}

theorem orderedGuardedPair_unique (k l : OrderedGuardedPair S H sap nr2 F)
    (h : ({k.val.val.1,k.val.val.2} : Set P) = {l.val.val.1,l.val.val.2}) : k = l := by
  have hleft : k.val.val.1 = l.val.val.1 ∨ k.val.val.1 = l.val.val.2 := by
    have hm : k.val.val.1 ∈ ({l.val.val.1,l.val.val.2} : Set P) := h ▸ (by simp)
    exact hm
  have hright : k.val.val.2 = l.val.val.1 ∨ k.val.val.2 = l.val.val.2 := by
    have hm : k.val.val.2 ∈ ({l.val.val.1,l.val.val.2} : Set P) := h ▸ (by simp)
    exact hm
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · rcases hleft with hl | hl
    · exact hl
    · rcases hright with hr | hr
      · have hk := k.property
        have hh := l.property
        rw [hl,hr] at hk
        omega
      · exact False.elim (k.val.property.1 (hl.trans hr.symm))
  · rcases hright with hr | hr
    · rcases hleft with hl | hl
      · exact False.elim (k.val.property.1 (hl.trans hr.symm))
      · have hk := k.property
        have hh := l.property
        rw [hl,hr] at hk
        omega
    · exact hr

variable (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))
variable (tests : BoundedJoinedPairTests S H sap nr2 F)

/-- The local word family is constructed from the fixed embedding of
this same bounded support, including its mandatory positive seed. -/
def guardedPairPackage
    (hCover : ∀ i, OriginalAllFullCoversInfinite S (i := i))
    (k : GuardedPair S H sap nr2 F) :=
  oneFactorRootPackage S H sap nr2 hCover
    (F.closureStructure {k.val.1,k.val.2})
    (guardedPairEmbedding S H sap nr2 F hUnary tests k)
    (guardedPairLeft S H sap nr2 F k) (guardedPairRight S H sap nr2 F k)
    (fun he => k.property.1 (congrArg Subtype.val he))

structure OrderedRootRealization where
  point : ∀ p : P, X (F.sort p).down.1
  injective : Function.Injective (fun p => (⟨(F.sort p).down.1,point p⟩ : Sigma X))
  guarded : ∀ k : OrderedGuardedPair S H sap nr2 F,
    S.menuRel (guardedPairMenu S H sap nr2 F hUnary tests k.val)
      (point k.val.val.1) (point k.val.val.2)

def GuardedRootRealization.ordered
    (R : GuardedRootRealization S H sap nr2 F hUnary tests) :
    OrderedRootRealization S H sap nr2 F hUnary tests where
  point := R.point
  injective := R.injective
  guarded k := R.guarded k.val

/-- Swapping generators changes only their enumeration, and keeps
the complete old induced diagram and its genuine unary domains. -/
def pairSwapEmbedding {b c : P}
    (e : CCO.UnarySupport.Structure.Embedding (F.closureStructure {c,b})
      (originalPartialTarget S H sap nr2)) :
    CCO.UnarySupport.Structure.Embedding (F.closureStructure {b,c})
      (originalPartialTarget S H sap nr2) where
  point p := e.point ⟨p.val,by simpa only [Set.pair_comm] using p.property⟩
  sort_eq p := e.sort_eq _
  map_func U p q h := e.map_func U _ _ h
  map_rel R xs h := e.map_rel R (fun i => ⟨(xs i).val,by
    simpa only [Set.pair_comm] using (xs i).property⟩) h
  injective p q h := by
    have hv : p.val = q.val := congrArg
      (fun z : F.closure {c,b} => z.val) (e.injective h)
    exact Subtype.ext hv
  reflect_func U p y hy := by
    obtain ⟨q,hq,he⟩ := e.reflect_func U _ y hy
    exact ⟨⟨q.val,by simpa only [Set.pair_comm] using q.property⟩,hq,he⟩
  reflect_rel R xs h := e.reflect_rel R (fun i => ⟨(xs i).val,by
    simpa only [Set.pair_comm] using (xs i).property⟩) h

def OrderedRootRealization.localEmbeddings
    (R : OrderedRootRealization S H sap nr2 F hUnary tests) :
    RootLocalEmbeddings (C := F) (A := originalPartialTarget S H sap nr2)
      (fun p => rootMap S H sap nr2 (F.sort p) (R.point p)) where
  sort_eq p := (Hidden).eval_sort (rootBaseTerm S H sap nr2 (F.sort p)) rfl
  singleton p := canonical_singleton_embedding S H sap nr2 F hUnary p (R.point p)
  pair b c hbc hirr := by
    by_cases hlt : liftRootRank b < liftRootRank c
    · let k : OrderedGuardedPair S H sap nr2 F := ⟨⟨(b,c),hbc,hirr⟩,hlt⟩
      obtain ⟨a,ha,hxy⟩ := R.guarded k
      obtain ⟨e,hb,hc,_,_⟩ := guardedPair_every_atom S H sap nr2 F hUnary tests k.val ha hxy
      exact ⟨e,hb,hc⟩
    · have hrev : liftRootRank c < liftRootRank b := by
        have hne : liftRootRank b ≠ liftRootRank c := fun he => hbc (liftRootRank_injective he)
        omega
      have hirr' : (F.closureStructure {c,b}).Irreducible := by
        rw [← Set.pair_comm b c]
        exact hirr
      let k : OrderedGuardedPair S H sap nr2 F := ⟨⟨(c,b),Ne.symm hbc,hirr'⟩,hrev⟩
      obtain ⟨a,ha,hxy⟩ := R.guarded k
      obtain ⟨e,hc,hb,_,_⟩ := guardedPair_every_atom S H sap nr2 F hUnary tests k.val ha hxy
      exact ⟨pairSwapEmbedding S H sap nr2 F e,hb,hc⟩

def OrderedRootRealization.hiddenHom
    (R : OrderedRootRealization S H sap nr2 F hUnary tests) :
    Hom F (originalPartialTarget S H sap nr2) := R.localEmbeddings.hom (fun _ => rfl)

theorem OrderedRootRealization.hiddenHom_HE
    (R : OrderedRootRealization S H sap nr2 F hUnary tests) :
    R.hiddenHom.HomEmbedding :=
  R.localEmbeddings.homEmbedding
    (total_of_unary_admissible hUnary (originalPartialTarget_total S H sap nr2)) (fun _ => rfl)

theorem ordered_roots_iff_hidden_HE :
    Nonempty (OrderedRootRealization S H sap nr2 F hUnary tests) ↔
      ∃ f : Hom F (originalPartialTarget S H sap nr2), f.HomEmbedding := by
  constructor
  · rintro ⟨R⟩
    exact ⟨R.hiddenHom,R.hiddenHom_HE⟩
  · rintro ⟨f,_⟩
    obtain ⟨R⟩ := guardedRootRealization_of_hom S H sap nr2 F hUnary tests f
    exact ⟨R.ordered⟩

end
end CCO.GuardedOldSeams
