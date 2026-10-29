import CCO.FullRows.RowDomainNaturality
import CCO.FullRows.RowCompatibility

/-! Actual source-extension requests on the zero rows. The complete source
itself supplies the recorded clique; no row compatibility is assumed. -/
universe v w t y
namespace CCO.FullRows
noncomputable section
open AllThoseEPPA HKNReservoir ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge SafeReadings
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)
variable (Δ : Subgroup (SourceGamma S H R B))
variable (A : Set (SourceCarrier S H R B))
variable (hA : (sourceStructure S H R B hB).IsClosed A)
variable {Z : Type y} [Finite Z]
variable (E : Structure (Signature ↥B (ResidualData.PacketGroup S H) (S.Atom () ())) Z)
variable (hLocal : LocallyInSource (sourceTag S H R B Δ) (encode (finiteSourceData S H R B hB A hA)) E)
set_option quotPrecheck false
local notation "K" => ResidualData.PacketGroup S H
local notation "I" => PacketRecovery.PacketIndex E
local notation "D₀" => finiteSourceData S H R B hB A hA
local notation "tag" => sourceTag S H R B Δ
local notation "act" => sourceAction S H R B Δ
local notation "coords" => reservoirCoordinates S H R B hB Δ A hA E hLocal
local notation "P₀" => sourceOriginPattern S H R B hB Δ A hA E hLocal

def recordedPairs (i j : I) : Prop := ∃ a, (P₀).edge i j = some a

theorem recordedPairs_symmetric : Symmetric (recordedPairs S H R B hB Δ A hA E hLocal) := by
  intro i j
  rintro ⟨a,ha⟩
  exact ⟨a,((P₀).symmetric j i).trans ha⟩

theorem reservoirCoordinates_fst (x : Z) : (coords x).1 = PacketRecovery.packet E x := by
  letI := PacketRecovery.action tag D₀ E hLocal (finiteSource_regularData S H R B hB A hA)
  exact (PacketRecovery.packets tag D₀ E hLocal (finiteSource_regularData S H R B hB A hA)).coordinates_fst x

def zeroRowEmbed (j : Structure.Embedding act (encode D₀) E) (a : A) : Vertex I K :=
  (((coords (j a)).1,1),(coords (j a)).2)

theorem zeroRowEmbed_injective (j : Structure.Embedding act (encode D₀) E) :
    Function.Injective (zeroRowEmbed S H R B hB Δ A hA E hLocal j) := by
  intro a b he
  apply j.injective
  apply (coords).injective
  exact congrArg projection he

def sourceIndices (j : Structure.Embedding act (encode D₀) E) : Set I :=
  Set.range (fun a : A => (coords (j a)).1)

/-- ALL packet indices meeting the literal complete source form a recorded clique. -/
theorem sourceIndices_recorded (j : Structure.Embedding act (encode D₀) E) :
    ∀ i ∈ sourceIndices S H R B hB Δ A hA E hLocal j,
      ∀ k ∈ sourceIndices S H R B hB Δ A hA E hLocal j, i ≠ k →
        recordedPairs S H R B hB Δ A hA E hLocal i k := by
  rintro i ⟨a,rfl⟩ k ⟨b,rfl⟩ hik
  have hab : a ≠ b := fun he => hik (congrArg (fun x : A => (coords (j x)).1) he)
  obtain ⟨c,hc⟩ := (finiteSource_fineData S H R B hB A hA).complete a b hab
  have hjc : E.rel (.fine c) (![j a,j b]) := by
    have hh := (j.map_rel_iff (.fine c) (![a,b])).mpr hc
    change E.rel (.fine c) (j.toFun ∘ ![a,b]) at hh
    have hv : j.toFun ∘ ![a,b] = ![j a,j b] := by
      funext k
      refine Fin.cases rfl (fun k => ?_) k
      exact Fin.eq_zero k ▸ rfl
    rw [hv] at hh
    exact hh
  have hpk : PacketRecovery.packet E (j a) ≠ PacketRecovery.packet E (j b) := by
    simpa only [reservoirCoordinates_fst] using hik
  obtain ⟨c',hc'⟩ := PacketRecovery.origin_record_of_record tag D₀ E hLocal
    (finiteSource_regularData S H R B hB A hA) (finiteSource_fineData S H R B hB A hA)
    (j a) (j b) c hjc hpk
  change ∃ c', PacketRecovery.originEdge tag D₀ E hLocal
    (finiteSource_regularData S H R B hB A hA) ((coords (j a)).1) ((coords (j b)).1) = some c'
  rw [reservoirCoordinates_fst,reservoirCoordinates_fst]
  exact ⟨c',hc'⟩

/-- One legal correction realizes ALL prescribed real values. The structural
extension is supplied by B027; this proves, rather than assumes, its row lift. -/
theorem zeroRow_request_extension (j : Structure.Embedding act (encode D₀) E)
    (p : Request tag D₀) (s₀ : Structure.Automorphism act E)
    (hs₀ : ∀ a ∈ p.point.source, s₀ (j a) = j (p.point a)) :
    letI := TransversalPure.thinCommGroup S H R
    ∃ C : Matrix I K, Legal (recordedPairs S H R B hB Δ A hA E hLocal) C ∧
      ∀ a ∈ p.point.source,
        lift (rowStructural S H R B hB Δ A hA E hLocal s₀) C
          (zeroRowEmbed S H R B hB Δ A hA E hLocal j a) =
            zeroRowEmbed S H R B hB Δ A hA E hLocal j (p.point a) := by
  letI := TransversalPure.thinCommGroup S H R
  let s := rowStructural S H R B hB Δ A hA E hLocal s₀
  obtain ⟨C,hC,hzero,_⟩ := zero_row_requests
    (fun g => translation_square S (finitePacket S H) H (R.packet_thin S H) g) s
    (recordedPairs S H R B hB Δ A hA E hLocal)
    (recordedPairs_symmetric S H R B hB Δ A hA E hLocal)
    (sourceIndices S H R B hB Δ A hA E hLocal j)
    (sourceIndices_recorded S H R B hB Δ A hA E hLocal j)
  refine ⟨C,hC,?_⟩
  intro a ha
  have hz := hzero (coords (j a)).1 ⟨a,rfl⟩
  have he := rowStructural_coordinates S H R B hB Δ A hA E hLocal s₀ (coords (j a))
  change coords (s₀ ((coords).symm (coords (j a)))) = baseMap s (coords (j a)) at he
  rw [(coords).symm_apply_apply,hs₀ a ha] at he
  change ((s.sigma (coords (j a)).1,rowImage s C (coords (j a)).1 1),
    (coords (j a)).2 * s.offset (coords (j a)).1) = _
  have he0 := congrArg (fun f : Row I K =>
    ((s.sigma (coords (j a)).1,f),(coords (j a)).2 * s.offset (coords (j a)).1)) hz
  exact he0.trans (congrArg (fun q : I × K => ((q.1,(1 : Row I K)),q.2)) he.symm)

end
end CCO.FullRows
