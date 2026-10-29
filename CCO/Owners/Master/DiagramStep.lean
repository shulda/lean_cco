import CCO.Owners.Master.Diagram
import Mathlib.Basic.Finite.Prod

/-! The actual full pullback step.  Ambient objects do not change.  No
surjectivity, coherence or CRT assertion about the new finite stage is an
input: these are proved from the old stage and the displayed binary square. -/

universe u v z
namespace CCO.Owners.Master.Diagram
variable {P : Type u} [DecidableEq P]
variable {A : Ambient.{u,v} P} {Valid : Finset P → Prop} {U : Finset P}

structure Step (B : Stage A Valid U) (p : P) (O : Finset P) where
  fresh : p ∉ U
  owner_subset : O ⊆ U
  valid_owner : Valid O
  valid_erase : ∀ V, Valid V → V ⊆ insert p U → Valid (V.erase p)
  owner_erase : ∀ V, Valid V → V ⊆ insert p U → p ∈ V → O ⊆ V.erase p
  localSet : Set (A.X (insert p O))
  local_finite : localSet.Finite
  local_over : ∀ x ∈ localSet,
    A.r (Finset.subset_insert p O) x ∈ B.B O
  local_onto : ∀ b ∈ B.B O, ∃ x ∈ localSet,
    A.r (Finset.subset_insert p O) x = b
  glue : ∀ (V : Finset P) (hV : Valid V) (hVS : V ⊆ insert p U) (hp : p ∈ V)
    (b : A.X (V.erase p)) (x : A.X (insert p O)),
    A.r (owner_erase V hV hVS hp) b = A.r (Finset.subset_insert p O) x →
      ∃! y : A.X V,
        A.r (Finset.erase_subset p V) y = b ∧
          A.r (Finset.insert_subset hp ((owner_erase V hV hVS hp).trans
            (Finset.erase_subset p V))) y = x

namespace Step
variable {B : Stage A Valid U} {p : P} {O : Finset P} (S : Step B p O)
include S

theorem erase_subset_old {V : Finset P} (hV : V ⊆ insert p U) : V.erase p ⊆ U := by
  intro x hx
  rcases Finset.mem_erase.mp hx with ⟨hne,hx⟩
  exact (Finset.mem_insert.mp (hV hx)).resolve_left hne

theorem old_subset {V : Finset P} (hV : V ⊆ insert p U) (hp : p ∉ V) : V ⊆ U := by
  intro x hx
  rcases Finset.mem_insert.mp (hV hx) with he | hu
  · exact (hp (he ▸ hx)).elim
  · exact hu

theorem principal_subset {V : Finset P} (hV : Valid V)
    (hVS : V ⊆ insert p U) (hp : p ∈ V) : insert p O ⊆ V :=
  Finset.insert_subset hp ((S.owner_erase V hV hVS hp).trans (Finset.erase_subset p V))

def newSet (V : Finset P) : Set (A.X V) :=
  {x | (p ∉ V ∧ x ∈ B.B V) ∨
    (p ∈ V ∧ ∃ h : insert p O ⊆ V,
      A.r (Finset.erase_subset p V) x ∈ B.B (V.erase p) ∧ A.r h x ∈ S.localSet)}

theorem mem_new_old {V : Finset P} (hp : p ∉ V) (x : A.X V) :
    x ∈ S.newSet V ↔ x ∈ B.B V := by simp [newSet,hp]

theorem mem_new_new {V : Finset P} (hp : p ∈ V) (h : insert p O ⊆ V)
    (x : A.X V) : x ∈ S.newSet V ↔
      A.r (Finset.erase_subset p V) x ∈ B.B (V.erase p) ∧ A.r h x ∈ S.localSet := by
  simp only [newSet, Set.mem_setOf_eq, hp, not_true_eq_false, false_and,
    true_and, false_or]
  exact ⟨fun ⟨_,h⟩ => h, fun hx => ⟨h,hx⟩⟩

theorem new_mapsTo {V W : Finset P} (hV : Valid V) (hW : Valid W)
    (hVS : V ⊆ insert p U) (hWV : W ⊆ V) (x : A.X V)
    (hx : x ∈ S.newSet V) : A.r hWV x ∈ S.newSet W := by
  have hWS := hWV.trans hVS
  by_cases hpW : p ∈ W
  · have hpV := hWV hpW
    have hPV := S.principal_subset hV hVS hpV
    have hPW := S.principal_subset hW hWS hpW
    have hv := (S.mem_new_new hpV hPV x).mp hx
    apply (S.mem_new_new hpW hPW _).mpr
    constructor
    · have he : W.erase p ⊆ V.erase p := Finset.erase_subset_erase p hWV
      have hh := B.mapsTo (S.valid_erase V hV hVS) (S.valid_erase W hW hWS)
        (S.erase_subset_old hVS) he _ hv.1
      simpa only [Ambient.project_comp] using hh
    · simpa only [Ambient.project_comp] using hv.2
  · apply (S.mem_new_old hpW _).mpr
    by_cases hpV : p ∈ V
    · have hv := (S.mem_new_new hpV (S.principal_subset hV hVS hpV) x).mp hx
      have he : W ⊆ V.erase p := by
        intro a ha
        exact Finset.mem_erase.mpr ⟨fun he => hpW (he ▸ ha),hWV ha⟩
      have hh := B.mapsTo (S.valid_erase V hV hVS) hW (S.erase_subset_old hVS)
        he _ hv.1
      simpa only [Ambient.project_comp] using hh
    · exact B.mapsTo hV hW (S.old_subset hVS hpV) hWV x ((S.mem_new_old hpV x).mp hx)

theorem new_nonempty (V : Finset P) (hV : Valid V) (hVS : V ⊆ insert p U) :
    (S.newSet V).Nonempty := by
  by_cases hpV : p ∈ V
  · obtain ⟨b,hb⟩ := B.nonempty (V.erase p) (S.valid_erase V hV hVS)
      (S.erase_subset_old hVS)
    have ho := B.mapsTo (S.valid_erase V hV hVS) S.valid_owner (S.erase_subset_old hVS)
      (S.owner_erase V hV hVS hpV) b hb
    obtain ⟨x,hx,he⟩ := S.local_onto _ ho
    obtain ⟨y,hy,-⟩ := S.glue V hV hVS hpV b x he.symm
    exact ⟨y,(S.mem_new_new hpV (S.principal_subset hV hVS hpV) y).mpr
      ⟨hy.1 ▸ hb,hy.2 ▸ hx⟩⟩
  · obtain ⟨x,hx⟩ := B.nonempty V hV (S.old_subset hVS hpV)
    exact ⟨x,(S.mem_new_old hpV x).mpr hx⟩

theorem pair_injective (V : Finset P) (hV : Valid V)
    (hVS : V ⊆ insert p U) (hpV : p ∈ V) :
    Function.Injective (fun x : A.X V =>
      (A.r (Finset.erase_subset p V) x, A.r (S.principal_subset hV hVS hpV) x)) := by
  intro x y he
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  obtain ⟨z,hz,hunique⟩ := S.glue V hV hVS hpV
    (A.r (Finset.erase_subset p V) x) (A.r (S.principal_subset hV hVS hpV) x) (by
      simp only [Ambient.project_comp])
  exact (hunique x ⟨rfl,rfl⟩).trans (hunique y ⟨h1.symm,h2.symm⟩).symm

theorem new_finite (V : Finset P) (hV : Valid V) (hVS : V ⊆ insert p U) :
    (S.newSet V).Finite := by
  by_cases hpV : p ∈ V
  · have hb := B.finite (V.erase p) (S.valid_erase V hV hVS) (S.erase_subset_old hVS)
    have hf := hb.prod S.local_finite
    apply Set.Finite.of_injOn (t := (B.B (V.erase p)) ×ˢ S.localSet)
      (f := fun x : A.X V =>
        (A.r (Finset.erase_subset p V) x,A.r (S.principal_subset hV hVS hpV) x))
    · intro x hx
      exact (S.mem_new_new hpV (S.principal_subset hV hVS hpV) x).mp hx
    · exact (S.pair_injective V hV hVS hpV).injOn
    · exact hf
  · have he : S.newSet V = B.B V := Set.ext (fun x => S.mem_new_old hpV x)
    rw [he]
    exact B.finite V hV (S.old_subset hVS hpV)

/-- Onto finite restrictions are proved by explicit old lifts and one
binary gluing, independently of the all-family CRT theorem. -/
theorem new_onto {V W : Finset P} (hV : Valid V) (hW : Valid W)
    (hVS : V ⊆ insert p U) (hWV : W ⊆ V) (y : A.X W)
    (hy : y ∈ S.newSet W) : ∃ x ∈ S.newSet V, A.r hWV x = y := by
  have hWS := hWV.trans hVS
  by_cases hpV : p ∈ V
  · have heV := S.valid_erase V hV hVS
    have hVU := S.erase_subset_old hVS
    have hPV := S.principal_subset hV hVS hpV
    by_cases hpW : p ∈ W
    · have hPW := S.principal_subset hW hWS hpW
      have heW := S.valid_erase W hW hWS
      have heWV := Finset.erase_subset_erase p hWV
      have hy' := (S.mem_new_new hpW hPW y).mp hy
      obtain ⟨b,hb,hby⟩ := B.onto heV heW hVU heWV _ hy'.1
      have howner : A.r (S.owner_erase V hV hVS hpV) b =
          A.r (Finset.subset_insert p O) (A.r hPW y) := by
        calc
          _ = A.r (S.owner_erase W hW hWS hpW) (A.r heWV b) := by
            simp only [Ambient.project_comp]
          _ = A.r (S.owner_erase W hW hWS hpW) (A.r (Finset.erase_subset p W) y) :=
            congrArg (A.r (S.owner_erase W hW hWS hpW)) hby
          _ = _ := by simp only [Ambient.project_comp]
      obtain ⟨x,hx,-⟩ := S.glue V hV hVS hpV b (A.r hPW y) howner
      refine ⟨x,(S.mem_new_new hpV hPV x).mpr ⟨hx.1 ▸ hb,hx.2 ▸ hy'.2⟩,?_⟩
      apply S.pair_injective W hW hWS hpW
      apply Prod.ext
      · change A.r (Finset.erase_subset p W) (A.r hWV x) = A.r (Finset.erase_subset p W) y
        calc
          _ = A.r heWV (A.r (Finset.erase_subset p V) x) := by
            simp only [Ambient.project_comp]
          _ = A.r heWV b := congrArg (A.r heWV) hx.1
          _ = _ := hby
      · change A.r hPW (A.r hWV x) = A.r hPW y
        simpa only [Ambient.project_comp] using hx.2
    · have hy' := (S.mem_new_old hpW y).mp hy
      have hWV' : W ⊆ V.erase p := by
        intro a ha
        exact Finset.mem_erase.mpr ⟨fun he => hpW (he ▸ ha),hWV ha⟩
      obtain ⟨b,hb,hby⟩ := B.onto heV hW hVU hWV' y hy'
      have ho := B.mapsTo heV S.valid_owner hVU (S.owner_erase V hV hVS hpV) b hb
      obtain ⟨d,hd,he⟩ := S.local_onto _ ho
      obtain ⟨x,hx,-⟩ := S.glue V hV hVS hpV b d he.symm
      refine ⟨x,(S.mem_new_new hpV hPV x).mpr ⟨hx.1 ▸ hb,hx.2 ▸ hd⟩,?_⟩
      calc
        _ = A.r hWV' (A.r (Finset.erase_subset p V) x) := by
          simp only [Ambient.project_comp]
        _ = A.r hWV' b := congrArg (A.r hWV') hx.1
        _ = y := hby
  · have hpW : p ∉ W := fun hp => hpV (hWV hp)
    have hy' := (S.mem_new_old hpW y).mp hy
    obtain ⟨x,hx,he⟩ := B.onto hV hW (S.old_subset hVS hpV) hWV y hy'
    exact ⟨x,(S.mem_new_old hpV x).mpr hx,he⟩

/-- The entire coherent, nonempty finite ONTO stage exists before CRT. -/
def stage : Stage A Valid (insert p U) where
  B := S.newSet
  finite := S.new_finite
  nonempty := S.new_nonempty
  mapsTo := S.new_mapsTo
  onto := S.new_onto

theorem stage_old (V : Finset P) (hVU : V ⊆ U) : S.stage.B V = B.B V := by
  have hpV : p ∉ V := fun hp => S.fresh (hVU hp)
  exact Set.ext (fun x => S.mem_new_old hpV x)

/-- The new finite carrier is the FULL pullback, with both literal
coordinate maps, rather than a subset having merely onto marginals. -/
def FinitePullback (V : Finset P) (hV : Valid V) (hVS : V ⊆ insert p U) (hpV : p ∈ V) :=
  {z : B.Point (V.erase p) × S.localSet //
    A.r (S.owner_erase V hV hVS hpV) z.1.val =
      A.r (Finset.subset_insert p O) z.2.val}

def split (V : Finset P) (hV : Valid V) (hVS : V ⊆ insert p U) (hpV : p ∈ V) :
    S.stage.Point V → S.FinitePullback V hV hVS hpV := fun x =>
  ⟨(⟨A.r (Finset.erase_subset p V) x.val,
      ((S.mem_new_new hpV (S.principal_subset hV hVS hpV) x.val).mp x.property).1⟩,
    ⟨A.r (S.principal_subset hV hVS hpV) x.val,
      ((S.mem_new_new hpV (S.principal_subset hV hVS hpV) x.val).mp x.property).2⟩),by
        simp only [Ambient.project_comp]⟩

theorem split_bijective (V : Finset P) (hV : Valid V) (hVS : V ⊆ insert p U)
    (hpV : p ∈ V) : Function.Bijective (S.split V hV hVS hpV) := by
  constructor
  · intro x y he
    apply Subtype.ext
    apply S.pair_injective V hV hVS hpV
    exact congrArg (fun z : S.FinitePullback V hV hVS hpV => (z.val.1.val,z.val.2.val)) he
  · intro z
    obtain ⟨x,hx,-⟩ := S.glue V hV hVS hpV z.val.1.val z.val.2.val z.property
    refine ⟨⟨x,(S.mem_new_new hpV (S.principal_subset hV hVS hpV) x).mpr
      ⟨hx.1 ▸ z.val.1.property,hx.2 ▸ z.val.2.property⟩⟩,?_⟩
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext
    · exact hx.1
    · exact hx.2

noncomputable def fullProductEquiv (V : Finset P) (hV : Valid V)
    (hVS : V ⊆ insert p U) (hpV : p ∈ V) :
    S.stage.Point V ≃ S.FinitePullback V hV hVS hpV :=
  Equiv.ofBijective (S.split V hV hVS hpV) (S.split_bijective V hV hVS hpV)

end Step
end CCO.Owners.Master.Diagram
