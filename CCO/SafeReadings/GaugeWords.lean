import CCO.SafeReadings.EndpointGauge

universe u v w z t r
namespace CCO.SafeReadings.EndpointGauge
open Selectors
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {Γ : Type z} [Group Γ] {N : Type t} {A : PureTagAction S Γ N}
variable {K : Type r} [CommGroup K] (E : EndpointGauge S A K)

def leftWord (g : K) {i j : ι} : PositiveWord S i j → PositiveWord S (E.owner g i) j
  | .single a => .single (E.left g a)
  | .cons a rest => .cons (E.left g a) rest

def rightWord (g : K) {i j : ι} : PositiveWord S i j → PositiveWord S i (E.owner g j)
  | .single a => .single (E.right g a)
  | .cons a rest => .cons a (rightWord g rest)

theorem leftWord_profile (g : K) {i j : ι} (p : PositiveWord S i j) :
    PositiveWord.profile S (E.leftWord g p) = E.leftMenu g (PositiveWord.profile S p) := by
  cases p with
  | single a => exact (E.leftMenu_singleton g a).symm
  | cons a rest =>
    change S.product {E.left g a} (PositiveWord.profile S rest) = E.leftMenu g (S.product {a} (PositiveWord.profile S rest))
    rw [E.leftMenu_product, E.leftMenu_singleton]

theorem rightWord_profile (g : K) {i j : ι} (p : PositiveWord S i j) :
    PositiveWord.profile S (E.rightWord g p) = E.rightMenu g (PositiveWord.profile S p) := by
  induction p with
  | single a => exact (E.rightMenu_singleton g a).symm
  | cons a rest ih =>
    change S.product {a} (PositiveWord.profile S (E.rightWord g rest)) = E.rightMenu g (S.product {a} (PositiveWord.profile S rest))
    rw [ih,E.rightMenu_product]

theorem left_present (g : K) {i j : ι} (ps : List (PositiveWord S i j)) :
    StrongExact.present S (ps.map (E.leftWord g)) = E.leftMenu g (StrongExact.present S ps) := by
  induction ps with
  | nil => simp only [List.map_nil,StrongExact.present_nil,E.leftMenu_univ]
  | cons p ps ih =>
    rw [List.map_cons,StrongExact.present_cons,StrongExact.present_cons,
      E.leftMenu_inter,ih,E.leftWord_profile]

theorem right_present (g : K) {i j : ι} (ps : List (PositiveWord S i j)) :
    StrongExact.present S (ps.map (E.rightWord g)) = E.rightMenu g (StrongExact.present S ps) := by
  induction ps with
  | nil => simp only [List.map_nil,StrongExact.present_nil,E.rightMenu_univ]
  | cons p ps ih =>
    rw [List.map_cons,StrongExact.present_cons,StrongExact.present_cons,
      E.rightMenu_inter,ih,E.rightWord_profile]

theorem left_exact (g : K) {i j : ι} {D : S.Menu i j} (hD : StrongExact.Exact S D) :
    StrongExact.Exact S (E.leftMenu g D) := by
  obtain ⟨hn,ps,hp⟩ := hD
  refine ⟨hn.image (E.left g),ps.map (E.leftWord g),?_⟩
  rw [E.left_present,←hp]

theorem right_exact (g : K) {i j : ι} {D : S.Menu i j} (hD : StrongExact.Exact S D) :
    StrongExact.Exact S (E.rightMenu g D) := by
  obtain ⟨hn,ps,hp⟩ := hD
  refine ⟨hn.image (E.right g),ps.map (E.rightWord g),?_⟩
  rw [E.right_present,←hp]

end CCO.SafeReadings.EndpointGauge
