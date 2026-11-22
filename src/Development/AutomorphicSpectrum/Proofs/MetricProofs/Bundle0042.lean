import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0036
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle0001
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0006
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.LabelDegreeCommensurableBound
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0034
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0005

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HoloOnDivCongr
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem holoOn_eval {σ : Type} (A : FinHolAtlas e X) {W : Set X} {b : X → σ → ℂ}
    (hb : ∀ q, A.HoloOn W fun y => b y q) (p : MvPolynomial σ ℤ) :
    A.HoloOn W fun y => eval (b y) (map (Int.castRingHom ℂ) p) := by
  intro j
  induction p using MvPolynomial.induction_on with
  | C a =>
    simpa [Function.comp_def] using
      (analyticOnNhd_const (v := ((a : ℤ) : ℂ)) (s := (A.chart j).target ∩ (A.chart j).symm ⁻¹' W))
  | add p q hp hq =>
    convert hp.add hq using 1
    funext u
    simp [Function.comp_def]
  | mul_X p q hp =>
    simpa [Function.comp_def] using hp.mul (hb q j)

theorem continuousAt_of_holoOn (A : FinHolAtlas e X) {W : Set X} {f : X → ℂ} (hf : A.HoloOn W f) {y : X}
    (hy : y ∈ W) : ContinuousAt f y := by
  obtain ⟨j, hj⟩ := A.cover y
  have h1 : (A.chart j) y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W :=
    ⟨(A.chart j).map_source hj, by
      rw [Set.mem_preimage, (A.chart j).left_inv hj]; exact hy⟩
  have h2 : ContinuousAt (f ∘ (A.chart j).symm) ((A.chart j) y) := (hf j _ h1).continuousAt
  have h3 : ContinuousAt (fun u => (f ∘ (A.chart j).symm) ((A.chart j) u)) y :=
    ContinuousAt.comp (f := A.chart j) h2 ((A.chart j).continuousAt hj)
  refine h3.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with u hu
  simp only [Function.comp_apply, (A.chart j).left_inv hu]

theorem isOpen_inter_ne (A : FinHolAtlas e X) {W : Set X} {f : X → ℂ} (hW : IsOpen W)
    (hf : A.HoloOn W f) : IsOpen (W ∩ {y | f y ≠ 0}) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hy, h0⟩
  filter_upwards [hW.mem_nhds hy, (continuousAt_of_holoOn A hf hy).eventually_ne h0] with u h1 h2
  exact ⟨h1, h2⟩

theorem holoOn_div_congr (A : FinHolAtlas e X) {W : Set X} {f g v : X → ℂ} (hW : IsOpen W)
    (hf : A.HoloOn W f) (hg : A.HoloOn W g) (h0 : ∀ y ∈ W, g y ≠ 0) (hv : ∀ y ∈ W, v y = f y / g y) :
    A.HoloOn W v := by
  intro j
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W) :=
    (A.chart j).isOpen_inter_preimage_symm hW
  have h1 : AnalyticOnNhd ℂ (fun u => (f ∘ (A.chart j).symm) u / (g ∘ (A.chart j).symm) u)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W) := fun u hu =>
    (hf j u hu).div (hg j u hu) (h0 _ hu.2)
  exact h1.congr hO fun u hu => (hv _ hu.2).symm

theorem holoOn_valAt (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (x : (Σ k, ι k) → Ω) (s : Ω) (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (W : Set X)
    (b : X → (Σ k, ι k) → ℂ) (y₀ : X) (hW : IsOpen W) (hy₀ : y₀ ∈ W) (hb : ∀ q, A.HoloOn W fun y => b y q)
    (hpt : ∀ y ∈ W, b y ∈ mcPts (mCoordIdeal x)) (hs : RegAt x (mCoordIdeal (b y₀)) s) :
    ∃ W' : Set X, IsOpen W' ∧ y₀ ∈ W' ∧ W' ⊆ W ∧ A.HoloOn W' fun y => valAt x s (b y) := by
  obtain ⟨d, g, h, hg, hh, hQ, heq⟩ := hs
  have hz : eval (b y₀) (map (Int.castRingHom ℂ) h) ≠ 0 := by
    intro h0
    refine hQ (mem_mCoordIdeal_of_aeval_eq_zero (b y₀) hh ?_)
    rw [← h0]
    rw [aeval_def, eval_map, Subsingleton.elim (algebraMap ℤ ℂ) (Int.castRingHom ℂ)]
  have hx : aeval x h ≠ 0 := fun h0 =>
    hz (eval_eq_zero_of_mem_mcPts (hpt y₀ hy₀) (mem_mCoordIdeal_of_aeval_eq_zero x hh h0))
  have Hg := holoOn_eval A hb g
  have Hh := holoOn_eval A hb h
  refine ⟨W ∩ {y | eval (b y) (map (Int.castRingHom ℂ) h) ≠ 0}, isOpen_inter_ne A hW Hh, ⟨hy₀, hz⟩,
    Set.inter_subset_left, ?_⟩
  refine holoOn_div_congr A (isOpen_inter_ne A hW Hh) (fun j => (Hg j).mono ?_) (fun j => (Hh j).mono ?_)
    (fun y hy => hy.2) fun y hy => ?_
  · exact Set.inter_subset_inter_right _ (Set.preimage_mono Set.inter_subset_left)
  · exact Set.inter_subset_inter_right _ (Set.preimage_mono Set.inter_subset_left)
  · exact valAt_eq (hpt y hy.1) ⟨d, g, h, hg, hh, hx, heq, hy.2, rfl⟩

end GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicDegreeOneBiholomorphism
section
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Cj

theorem exists_holoMap_inverse_of_degree_one : ∀ {e : ℕ} {X Y : Type} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] (A : FinHolAtlas e X) (B : FinHolAtlas e Y)
    (h : Y → X), HoloMap B A h → IsDegreeOff A B h 1 ∅ →
    ∃ g : X → Y, (∀ y, g (h y) = y) ∧ (∀ x, h (g x) = x) ∧ HoloMap A B g := by
  intro e X Y _ _ _ _ _ A B h hh hd
  obtain ⟨-, -, -, -, hfib, hdet⟩ := hd
  have hex : ∀ x, ∃ y, h ⁻¹' {x} = {y} := fun x => Set.ncard_eq_one.1 (hfib x (by simp))
  have hinj : Function.Injective h := by
    intro a b hab
    obtain ⟨c, hc⟩ := hex (h a)
    have ha : a ∈ h ⁻¹' {h a} := rfl
    have hb : b ∈ h ⁻¹' {h a} := hab.symm
    rw [hc] at ha hb
    exact ha.trans hb.symm
  have hsurj : Function.Surjective h := by
    intro x
    obtain ⟨c, hc⟩ := hex x
    have hcx : c ∈ h ⁻¹' {x} := by rw [hc]; rfl
    exact ⟨c, hcx⟩
  let E : Y ≃ X := Equiv.ofBijective h ⟨hinj, hsurj⟩
  have hEc : Continuous E := hh.1
  obtain ⟨g, hgE⟩ : ∃ g : X → Y, g = E.symm := ⟨_, rfl⟩
  have hgc : Continuous g := by
    rw [hgE]; exact hEc.homeoOfEquivCompactToT2.symm.continuous
  have hgh : ∀ y, g (h y) = y := fun y => by rw [hgE]; exact E.symm_apply_apply y
  have hhg : ∀ x, h (g x) = x := fun x => by rw [hgE]; exact E.apply_symm_apply x
  refine ⟨g, hgh, hhg, hgc, fun j k w hw => ?_⟩
  obtain ⟨hwt, hws⟩ := hw
  have hys : g ((A.chart j).symm w) ∈ (B.chart k).source := hws
  obtain ⟨v, hv⟩ : ∃ v, v = B.chart k (g ((A.chart j).symm w)) := ⟨_, rfl⟩
  have hvt : v ∈ (B.chart k).target := hv ▸ (B.chart k).map_source hys
  have hsv : (B.chart k).symm v = g ((A.chart j).symm w) := by
    rw [hv]; exact (B.chart k).left_inv hys
  have hhv : h ((B.chart k).symm v) ∈ (A.chart j).source := by
    rw [hsv, hhg]; exact (A.chart j).map_target hwt
  obtain ⟨T, hT⟩ : ∃ T : (Fin e → ℂ) → Fin e → ℂ, T = A.chart j ∘ h ∘ (B.chart k).symm := ⟨_, rfl⟩
  have hTa : AnalyticAt ℂ T v := by
    rw [hT]; exact hh.2 k j v ⟨hvt, hhv⟩
  have hTv : T v = w := by
    rw [hT]
    simp only [Function.comp_apply]
    rw [hsv, hhg]
    exact (A.chart j).right_inv hwt
  have hdet' : (fderiv ℂ T v).det ≠ 0 := by
    rw [hT]; exact hdet k j v hvt (by simp) hhv
  have hCe := ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero (fderiv ℂ T v) hdet'
  obtain ⟨Ce, hCedef⟩ : ∃ Ce, Ce = (fderiv ℂ T v).toContinuousLinearEquivOfDetNeZero hdet' := ⟨_, rfl⟩
  rw [← hCedef] at hCe
  have hstrict : HasStrictFDerivAt T (Ce : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) v := by
    rw [hCe]; exact hTa.hasStrictFDerivAt
  set F := hstrict.toOpenPartialHomeomorph T with hF
  have hFc : (F : (Fin e → ℂ) → (Fin e → ℂ)) = T := hstrict.toOpenPartialHomeomorph_coe
  have hus : v ∈ F.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hsym : AnalyticAt ℂ F.symm w := by
    have h1 : AnalyticAt ℂ F.symm (F v) :=
      F.analyticAt_symm' (i := Ce) hus (by rw [hFc]; exact hTa) (by rw [hFc, hCe])
    rwa [hFc, hTv] at h1
  have hc2 : ContinuousAt (g ∘ (A.chart j).symm) w :=
    hgc.continuousAt.comp ((A.chart j).continuousAt_symm hwt)
  have hc : ContinuousAt (B.chart k ∘ g ∘ (A.chart j).symm) w :=
    ContinuousAt.comp (g := B.chart k) ((B.chart k).continuousAt hys) hc2
  have hus' : F.source ∈ nhds ((B.chart k ∘ g ∘ (A.chart j).symm) w) := by
    have : (B.chart k ∘ g ∘ (A.chart j).symm) w = v := hv.symm
    rw [this]; exact F.open_source.mem_nhds hus
  refine hsym.congr ?_
  filter_upwards [hc.preimage_mem_nhds hus',
    hc2.preimage_mem_nhds ((B.chart k).open_source.mem_nhds hys),
    (A.chart j).open_target.mem_nhds hwt] with w' h1 h2 h3
  have h2' : g ((A.chart j).symm w') ∈ (B.chart k).source := h2
  have e1 : T ((B.chart k ∘ g ∘ (A.chart j).symm) w') = w' := by
    rw [hT]
    simp only [Function.comp_apply]
    rw [(B.chart k).left_inv h2', hhg]
    exact (A.chart j).right_inv h3
  have e2 := F.left_inv h1
  rw [hFc, e1] at e2
  exact e2

end GlobalTheory.CompanionTheory.Ar.PB.Cj
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBaseChart
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan

section Orbit

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

structure OrbitChart (P : Ideal (MRing ι)) (e : ℕ) where

  D : Set (Fin e → ℂ)
  isOpen_D : IsOpen D

  φ : (Fin e → ℂ) → (Σ k, ι k) → ℂ
  holo : ∀ p, AnalyticOnNhd ℂ (fun w => φ w p) D
  mem : ∀ w ∈ D, φ w ∈ mcPts P

  O : Set ((Σ k, ι k) → ℂ)
  O_open : ∃ O' : Set ((Σ k, ι k) → ℂ), IsOpen O' ∧ O = O' ∩ mcPts P
  O_orbit : ∀ z ∈ O, ∀ z' ∈ mcPts P, SameOrbit z' z → z' ∈ O

  ρ : ((Σ k, ι k) → ℂ) → Fin e → ℂ
  ρ_cont : ContinuousOn ρ O
  ρ_orbit : ∀ z ∈ O, ∀ z' ∈ O, SameOrbit z' z → ρ z' = ρ z
  φ_mem_O : ∀ w ∈ D, φ w ∈ O
  ρ_φ : ∀ w ∈ D, ρ (φ w) = w
  ρ_mem : ∀ z ∈ O, ρ z ∈ D
  φ_ρ : ∀ z ∈ O, SameOrbit (φ (ρ z)) z
  immersion : ∀ w ∈ D, ∀ p : (k : K) → ι k, (∀ k, φ w ⟨k, p k⟩ ≠ 0) →
    (fderiv ℂ (fun w' => affCoord p (φ w')) w).ker = ⊥

end Orbit

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

def stepOf (N j : ℕ) (c : Fin N) : Fin N :=
  ⟨if N - j ≤ (c : ℕ) then (c : ℕ) - (N - j) else (c : ℕ) + j, by
    have := c.2
    split_ifs <;> omega⟩

def lowMat (c : LowIdx Ψ N j → ℂ) (τ : Ψ) : Matrix (Fin N) (Fin N) ℂ := fun a b =>
  if h : b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) then c ⟨(τ, a, b), h⟩ else if a = b then 1 else 0

def flagZ (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) : (Σ k, ι k) → ℂ := fun q =>
  if e : ∃ p, M.blk p = some q.1 then
    ∑ I, valAt M.x (F.u q I) zb * minorIJ (h e.choose.1) I (stepCols N j e.choose.2)
  else zb ⟨⟨q.1, fun p hp => e ⟨p, hp⟩⟩, q.2⟩

def sqZ (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (k₀ : K) (τ : Ψ) (ca cb : Fin N) (t : ℂ) :
    (Σ o : Option K, ι (o.getD k₀)) → ℂ
  | ⟨some k, m⟩ => flagZ M F zb h ⟨k, m⟩
  | ⟨none, m⟩ => flagZ M F zb (Function.update h τ (h τ * (1 + Matrix.single cb ca t))) ⟨k₀, m⟩

def pluck (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (k : K)
    (z : (Σ k, ι k) → ℂ) (I : Finset (Fin N)) : ℂ :=
  ∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) zb * z ⟨k, m⟩

def twMinor (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (i : Fin N)
    (k : K) (g : Matrix (Fin N) (Fin N) ℂ) (z : (Σ k, ι k) → ℂ) (J : Finset (Fin N)) : ℂ :=
  ∑ I ∈ Finset.univ.filter (IsStepRows N j i), minorIJ g J I * pluck M F zb k z I

def lowRead (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (z : (Σ k, ι k) → ℂ) (τ' : Ψ) (a' b' : Fin N) : ℂ :=
  (M.blk (τ', stepOf N j b')).elim 0 fun k =>
    twMinor M F zb (stepOf N j b') k (h τ')⁻¹ z (insert a' ((stepCols N j (stepOf N j b')).erase b')) /
      twMinor M F zb (stepOf N j b') k (h τ')⁻¹ z (stepCols N j (stepOf N j b'))

def baseOf (M : FlagModel y Ψ N j) (k₀ : K) (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) :
    (Σ k, baseIdx ι M.blk k) → ℂ := basePart M.blk (fstPt k₀ z)

abbrev wP (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) :
    Ideal (MRing fun o : Option K => ι (o.getD k₀)) :=
  mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)

section Param

variable {n e : ℕ} {Λ : Type}

def wB (ε : Fin n ⊕ Λ ⊕ Unit ≃ Fin e) (w : Fin e → ℂ) : Fin n → ℂ := fun i => w (ε (Sum.inl i))

def wL (ε : Fin n ⊕ Λ ⊕ Unit ≃ Fin e) (w : Fin e → ℂ) : Λ → ℂ := fun q => w (ε (Sum.inr (Sum.inl q)))

def wT (ε : Fin n ⊕ Λ ⊕ Unit ≃ Fin e) (w : Fin e → ℂ) : ℂ := w (ε (Sum.inr (Sum.inr ())))

def wD (ε : Fin n ⊕ Λ ⊕ Unit ≃ Fin e) (V : Set (Fin n → ℂ)) : Set (Fin e → ℂ) := {w | wB ε w ∈ V}

end Param

variable {n e : ℕ}

def wH (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin e) (τ' : Ψ) (w : Fin e → ℂ) :
    Matrix (Fin N) (Fin N) ℂ := h τ' * lowMat (wL ε w) τ'

def wPhi (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin e) (k₀ : K) (τ : Ψ) (ca cb : Fin N)
    (w : Fin e → ℂ) : (Σ o : Option K, ι (o.getD k₀)) → ℂ :=
  sqZ M F (bl (wB ε w)) (fun τ' => wH h ε τ' w) k₀ τ ca cb (wT ε w)

def IsBaseChart (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (F : FrameData ι Ψ N M.Ω M.blk)
    (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) : Prop :=
  IsOpen V ∧ V ⊆ (Rb.A.chart kb).target ∧ (∀ q, AnalyticOnNhd ℂ (fun w => bl w q) V) ∧
    (∀ q I, AnalyticOnNhd ℂ (fun w => valAt M.x (F.u q I) (bl w)) V) ∧
    ∀ w ∈ V, bl w ∈ mcPts (mCoordIdeal M.x) ∧ (∀ k, bl w ⟨k, F.c k⟩ = 1) ∧ M.GoodAt F (mCoordIdeal (bl w)) ∧
      SameOrbit (Rb.lift ((Rb.A.chart kb).symm w) ((Rb.A.chart kb).symm w)) (bl w)

def IsWCtx (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N)
    (d : ℕ) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
    (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  (b : ℕ) = a + 1 ∧ ((b : ℕ) < j ∨ j ≤ (a : ℕ)) ∧ M.blk (τ, a) = some k₀ ∧ (ca : ℕ) = lastCol N j a ∧
    (cb : ℕ) = ca + 1 ∧ IsArithVar (mCoordIdeal y) (d + 2) ∧ M.IsFrame F ∧ IsBaseChart M Rb F kb V bl ∧
    (∀ z ∈ mcPts (mCoordIdeal M.x), SameOrbit (Rb.lift (r z) (r z)) z) ∧ ContinuousOn r (mcPts (mCoordIdeal M.x)) ∧
    ∀ τ', IsBlockDiag j (h τ') ∧ (h τ').det ≠ 0

def wO (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N)
    (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
    (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) :
    Set ((Σ o : Option K, ι (o.getD k₀)) → ℂ) :=
  {z | z ∈ mcPts (wP M τ a k₀ ca cb) ∧ r (baseOf M k₀ z) ∈ (Rb.A.chart kb).source ∧
    Rb.A.chart kb (r (baseOf M k₀ z)) ∈ V ∧
    (∀ p k, M.blk p = some k →
      twMinor M F (baseOf M k₀ z) p.2 k (h p.1)⁻¹ (fstPt k₀ z) (stepCols N j p.2) ≠ 0) ∧
    twMinor M F (baseOf M k₀ z) a k₀ (h τ)⁻¹ (sndPt k₀ z) (stepCols N j a) ≠ 0}

def wRho (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (k₀ : K) (ca cb : Fin N)
    (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin e)
    (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) : Fin e → ℂ := fun i =>
  match ε.symm i with
  | Sum.inl l => Rb.A.chart kb (r (baseOf M k₀ z)) l
  | Sum.inr (Sum.inl q) => lowRead M F (baseOf M k₀ z) h (fstPt k₀ z) q.1.1 q.1.2.1 q.1.2.2
  | Sum.inr (Sum.inr _) =>
    lowRead M F (baseOf M k₀ z) h (sndPt k₀ z) τ cb ca - lowRead M F (baseOf M k₀ z) h (fstPt k₀ z) τ cb ca

end Flag

end GlobalTheory.CompanionTheory.Ar.PB.WMan
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsClosedSectionBoundary
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.CWeight

theorem isClosed_bdry_of_isSection : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ), IsSection A L s → IsClosed (bdry s) := by
  intro e X _ A L s hS
  exact ReciprocityTheory.AnForm.P.LeviFormBoundaryTopology.isClosed_bdry hS

end GlobalTheory.CompanionTheory.Ar.PB.CWeight
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

def flagAt {d : ℕ} (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (τ : Ψ) (ca cb : Fin N) (t : ℂ) (w : Fin d → ℂ)
    (τ' : Ψ) : Matrix (Fin N) (Fin N) ℂ :=
  if τ' = τ then H τ w * (1 + Matrix.single cb ca t) else H τ' w

def IsFibreData {M : FlagModel y Ψ N j} {n d : ℕ} {BM : BaseMetric M n} (FA : FlagAn BM d) (τ : Ψ) (a : Fin N) (ca cb : Fin N)
    {X : Type} (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q)
    (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X) : Prop :=
  (∀ τ' r s, AnalyticOnNhd ℂ (fun w => H τ' w r s) Un) ∧
    ContinuousOn bp Un ∧ (∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (Un ∩ bp ⁻¹' (BM.Rb.A.chart k).source)) ∧
    (∀ w ∈ Un, bp w ∈ BM.O l \ bdry BM.s ∧ ∀ τ', IsBlockDiag j (H τ' w) ∧ (H τ' w).det ≠ 0) ∧
    (∀ w ∈ Un, ∀ r s : Fin 2, Gn w r s =
      minorIJ ((H τ w)ᴴ * BM.G l τ (bp w) * H τ w) (insert (![ca, cb] r) ((stepCols N j a).erase ca))
          (insert (![ca, cb] s) ((stepCols N j a).erase ca)) /
        minorIJ ((H τ w)ᴴ * BM.G l τ (bp w) * H τ w) ((stepCols N j a).erase ca) ((stepCols N j a).erase ca)) ∧
    (∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ Un → ∀ x₀, FA.Re.π x₀ = ΦYn z → ∃ z₀ : (Σ k, ι k) → ℂ,
      SameOrbit (FA.Re.R.lift x₀ x₀) z₀ ∧ SameOrbit (basePart M.blk z₀) (BM.Rb.lift (bp (Fin.tail z)) (bp (Fin.tail z))) ∧
      ∀ τ' i, M.ExactAt (BM.F l) (τ', i) z₀ (flagAt H τ ca cb (z 0) (Fin.tail z) τ')) ∧
    ∀ z : Fin (d + 2) → ℂ, Fin.tail (Fin.tail z) ∈ Un →
      q 0 (ΦWn z) = ΦYn (Fin.cons (z 0) (Fin.tail (Fin.tail z))) ∧ q 1 (ΦWn z) = ΦYn (Fin.tail z)

theorem isFibreChart_iff {M : FlagModel y Ψ N j} {n d : ℕ} {BM : BaseMetric M n} (FA : FlagAn BM d) (τ : Ψ) (a : Fin N)
    (ca cb : Fin N) {X : Type} (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ))
    (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) :
    IsFibreChart FA τ a ca cb q Un Gn ΦYn ΦWn ↔ ∃ l H bp, IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp :=
  Iff.rfl

def upsVal {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) (l : Fin BM.q) (p : Ψ × Fin N) (b : BM.Rb.X) : ℂ :=
  valAt M.x ((BM.F l).υ p) (BM.Rb.lift b b)

def upsLogAt {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) (l : Fin BM.q) (p : Ψ × Fin N) (b : BM.Rb.X) : ℝ :=
  if M.blk p = none then Real.log ‖upsVal BM l p b‖ else 0

def potAt {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) (l : Fin BM.q) (p : Ψ × Fin N) (b : BM.Rb.X)
    (hf : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  blockPot j p.2 (BM.G l p.1 b) hf - upsLogAt BM l p b

def alphaOf {M : FlagModel y Ψ N j} {n d : ℕ} (BM : BaseMetric M n) (l : Fin BM.q)
    (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X) (p : Ψ × Fin N) (w : Fin d → ℂ) : ℝ :=
  potAt BM l p (bp w) (H p.1 w)

def facOf (N j : ℕ) (a : Fin N) (h : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) : ℂ :=
  if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ h (wIdx N j) (wIdx N j) else 1)
    else minorIJ h (omIdx N j) (omIdx N j)

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsImg
section
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ} {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ']
  {y' : (Σ k, ι' k) → Φ'}

def IsImg {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (z : (Σ k, ι' k) → ℂ) (w : (Σ k, ι k) → ℂ) : Prop :=
  ∀ z₁, SameOrbit z₁ z → ∀ F' F, M'.IsFrame F' → M.IsFrame F →
    M'.GoodAt F' (mCoordIdeal (basePart M'.blk z₁)) → M.GoodAt F (mCoordIdeal (basePart M'.blk z₁ ∘ Cv.v)) →
    ∀ h, M'.IsFlagOf F' z₁ h → ∃ z₀, SameOrbit z₀ w ∧ SameOrbit (basePart M.blk z₀) (basePart M'.blk z₁ ∘ Cv.v) ∧
      M.IsFlagOf F z₀ fun τ => Cv.trans F' F (basePart M'.blk z₁) τ * h τ

theorem IsImg.orbit {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} {Cv : FlagCover M' M}
    {z z₁ : (Σ k, ι' k) → ℂ} {w w₁ : (Σ k, ι k) → ℂ} (h : IsImg Cv z w) (hz : SameOrbit z₁ z)
    (hw : SameOrbit w₁ w) : IsImg Cv z₁ w₁ := by
  intro z₂ h2 F' F hF' hF hg' hg hh hfl
  obtain ⟨z₀, a, b, c⟩ := h z₂ (Cj.sameOrbit_trans h2 hz) F' F hF' hF hg' hg hh hfl
  exact ⟨z₀, Cj.sameOrbit_trans a (Cj.sameOrbit_symm hw), b, c⟩

end GlobalTheory.CompanionTheory.Ar.PB.CovMap
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsLocSec
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

def xiDeg (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) : K → ℤ := fun k => ∑ p, xiCoef τ a p * M.dy p k

def aDeg (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K) : Option K → ℤ := fun o =>
  match o with
  | none => 1
  | some k => if k = k₀ then 1 else -xiDeg M τ a k

def potA (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K) : HermLine fun o : Option K => ι (o.getD k₀) :=
  fsHerm (fun o : Option K => ι (o.getD k₀)) (aDeg M τ a k₀)

def IsPtData (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) {e : ℕ}
    (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (x : RW.X) (z₀ z₁ : (Σ k, ι k) → ℂ)
    (F : FrameData ι Ψ N M.Ω M.blk) (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) : Prop :=
  M.IsFrame F ∧ M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) ∧ SameOrbit z₀ (fstPt k₀ (RW.lift x x)) ∧
    SameOrbit z₁ (sndPt k₀ (RW.lift x x)) ∧ IsBlockDiag j h ∧ h.det ≠ 0 ∧ t ≠ 0 ∧
    (∀ i, M.ExactAt F (τ, i) z₀ h) ∧ ∀ i, M.ExactAt F (τ, i) z₁ (h * (1 + Matrix.single cb ca t))

def IsLocSec (M : FlagModel y Ψ N j) {n e : ℕ} (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K)
    (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (x : RW.X)
    (ψ : OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : Fin Rb.A.n) (σ : Fin n ↪ Fin e) (i₀ : Fin e) (V : Set RW.X)
    (u : RW.X → ℂ) : Prop :=
  (∃ F H, IsWChart M Rb τ a k₀ ca cb RW pr ψ kb σ i₀ F H) ∧ IsOpen V ∧ x ∈ V ∧ V ⊆ ψ.source ∧ V ⊆ RW.U x ∧
    RW.A.HoloOn V u ∧ (∀ y' ∈ V, u y' ≠ 0) ∧
    (∀ y' ∈ V, ψ y' i₀ = 0 ↔ SameOrbit (fstPt k₀ (RW.lift y' y')) (sndPt k₀ (RW.lift y' y'))) ∧
    ∀ y' ∈ V, ψ y' i₀ ≠ 0 → ∀ z₀ z₁ F h t, IsPtData M τ a k₀ ca cb RW y' z₀ z₁ F h t →
      Real.log ‖u y' * ψ y' i₀‖ - Real.log ((potA M τ a k₀).h (RW.lift x y')) = normRhs M τ a F z₀ z₁ h t

def diagSet (k₀ : K) {P J : Ideal (MRing fun o : Option K => ι (o.getD k₀))} {e : ℕ} (R : AnLogRes P J e) : Set R.X :=
  {x | SameOrbit (fstPt k₀ (R.lift x x)) (sndPt k₀ (R.lift x x))}

def diagSec {e : ℕ} {X : Type} [TopologicalSpace X] (ψ : X → OpenPartialHomeomorph X (Fin e → ℂ)) (i₀ : X → Fin e)
    (u : X → X → ℂ) : X → X → ℂ := fun x y' => u x y' * ψ x y' (i₀ x)

def secPot {κ : Type} [Fintype κ] {ρ : κ → Type} [∀ k, Fintype (ρ k)] {P J : Ideal (MRing ρ)} {e : ℕ}
    (R : AnLogRes P J e) (A : HermLine ρ) (V : R.X → Set R.X) (hV : ∀ x, IsOpen (V x)) (hm : ∀ x, x ∈ V x) (c : ℝ) :
    LocPot R.X where
  U := V
  isOpen_U := hV
  mem_U := hm
  φ x y' := Real.log (A.h (R.lift x y')) + c

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LabelledDegreeCommensurableBound
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.labelled_degree_commensurable_bound : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (r k : ℕ) (v : Fin r → V) (s : Ψ ⊕ Ψ) (q : Fin k → A.Λ) (F : Submodule (𝓞 L) V) (𝔞 : Ideal (𝓞 L)), A.IsAdapted s v q → 𝔞 ≠ ⊥ → 𝔞 • F ≤ A.eig s → 𝔞 • A.eig s ≤ F → |A.labDeg s F v q - A.labDeg s (A.eig s) v q| ≤ (r + k) * Real.log (Ideal.absNorm 𝔞) / Module.finrank ℚ L := by
  first | exact @LevelTowerAlt.label_degree_commensurable_bound | exact LevelTowerAlt.label_degree_commensurable_bound
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.NormalizedDegreeBoundedMapStatement
section
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalized_degree_bounded_map : ∀ (K : Type) [Field K] [NumberField K] (E E' : HermitianBundle.{0} K) (φ : E.carrier →ₗ[𝓞 K] E'.carrier) (c : ℝ), Function.Injective φ → 0 < c → (∀ (σ : K →+* ℂ) (x : Fibre σ E.carrier), sqAt E' σ (φ.lTensor (ComplexAt σ) x) ≤ c * sqAt E σ x) → (∀ F : Submodule (𝓞 K) E.carrier, E.normDegree F ≤ E'.normDegree (F.map φ) + E.rank F / 2 * Real.log c) ∧ E.slopeMax ≤ E'.slopeMax + ((Real.log c / 2 : ℝ) : EReal) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.MapCompare.main | exact GlobalTheory.CompanionTheory.Ar.MapCompare.main | (intros; apply GlobalTheory.CompanionTheory.Ar.MapCompare.main <;> assumption)
end

