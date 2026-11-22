import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0006
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0142
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0180
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0033
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0023
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0052
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0056
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0027
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0044
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0049
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0100
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0144
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0143

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticOnNhdOfDifferentiableOn
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {n : ℕ}

def sheetProj (Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (γ : (Fin n → ℂ) → (Σ k, J k) → ℂ) (t : Fin n → ℂ) : Fin n → ℂ :=
  fun i => Ψ (segre (γ t)) i.succ / Ψ (segre (γ t)) 0

def sheetReg (Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (γ : (Fin n → ℂ) → (Σ k, J k) → ℂ) (V : Set (Fin n → ℂ)) : Set (Fin n → ℂ) :=
  {t | t ∈ V ∧ Ψ (segre (γ t)) 0 ≠ 0 ∧
    LinearMap.det (fderiv ℂ (sheetProj Ψ γ) t : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0}

def sheetNorm (Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (z : (Σ k, J k) → ℂ) :
    ((k : K) → J k) → ℂ :=
  (Ψ (segre z) 0)⁻¹ • segre z

theorem analyticOnNhd_of_differentiableOn {V : Set (Fin n → ℂ)} (hV : IsOpen V)
    {γ : (Fin n → ℂ) → (Σ k, J k) → ℂ} (hγ : DifferentiableOn ℂ γ V) : AnalyticOnNhd ℂ γ V :=
  fun t ht => analyticAt_pi_iff.mpr fun p => osgood n _ _ hV (differentiableOn_pi.mp hγ p) t ht

theorem analyticAt_psi_segre (Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    {γ : (Fin n → ℂ) → (Σ k, J k) → ℂ} {t : Fin n → ℂ} (h : AnalyticAt ℂ γ t) :
    AnalyticAt ℂ (fun t' => Ψ (segre (γ t'))) t := by
  classical
  have h1 : AnalyticAt ℂ (fun t' => segre (γ t')) t :=
    analyticAt_pi_iff.mpr fun (i : (k : K) → J k) =>
      Finset.analyticAt_fun_prod _ fun k _ => analyticAt_coord h ⟨k, i k⟩
  exact ((LinearMap.toContinuousLinearMap Ψ).analyticAt _).comp h1

theorem analyticAt_sheetProj (Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    {γ : (Fin n → ℂ) → (Σ k, J k) → ℂ} {t : Fin n → ℂ} (h : AnalyticAt ℂ γ t)
    (h0 : Ψ (segre (γ t)) 0 ≠ 0) : AnalyticAt ℂ (sheetProj Ψ γ) t := by
  have hc := fun j => analyticAt_pi_iff.mp (analyticAt_psi_segre Ψ h) j
  exact analyticAt_pi_iff.mpr fun i => (hc i.succ).div (hc 0) h0

theorem isOpen_sheetReg (Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    {γ : (Fin n → ℂ) → (Σ k, J k) → ℂ} {V : Set (Fin n → ℂ)} (hV : IsOpen V)
    (hγ : AnalyticOnNhd ℂ γ V) : IsOpen (sheetReg Ψ γ V) := by
  rw [isOpen_iff_mem_nhds]
  rintro t ⟨htV, h0, hd⟩
  have hc0 := (analyticAt_pi_iff.mp (analyticAt_psi_segre Ψ (hγ t htV)) 0).continuousAt
  have hcd := (analyticAt_det_fderiv (analyticAt_sheetProj Ψ (hγ t htV) h0)).continuousAt
  filter_upwards [hV.mem_nhds htV, hc0.eventually_ne h0, hcd.eventually_ne hd] with u h1 h2 h3
  exact ⟨h1, h2, h3⟩

theorem sheetNorm_mem_fibre {P : Ideal (MRing J)} (hK : Nonempty K) (hP : IsMultiHomogIdeal P)
    (Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (γ : (Fin n → ℂ) → (Σ k, J k) → ℂ)
    {t : Fin n → ℂ} (hz : γ t ∈ mcPts P) (h0 : Ψ (segre (γ t)) 0 ≠ 0) :
    sheetNorm Ψ (γ t) ∈ fibre P Ψ (sheetProj Ψ γ t) := by
  classical
  obtain ⟨k0⟩ := hK
  set c : K → ℂ := Function.update (fun _ => 1) k0 (Ψ (segre (γ t)) 0)⁻¹ with hc
  have hc0 : ∀ k, c k ≠ 0 := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp [hc, h0]
    · simp [hc, hk]
  have hprod : ∏ k, c k = (Ψ (segre (γ t)) 0)⁻¹ := by
    rw [hc, Finset.prod_update_of_mem (Finset.mem_univ k0)]
    simp
  refine ⟨fun p => c p.1 * γ t p, mcPts_smul hP c hc0 hz, ?_, ?_⟩
  · rw [segre_smul, hprod]; rfl
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [sheetNorm, h0]
    · simp [sheetNorm, sheetProj, div_eq_inv_mul]

theorem sheetNorm_eq_torusSat (Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    {z z' : (Σ k, J k) → ℂ} (hz' : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) (h0 : Ψ (segre z) 0 ≠ 0)
    (h0' : Ψ (segre z') 0 ≠ 0) (h : sheetNorm Ψ z = sheetNorm Ψ z') : z ∈ torusSat {z'} := by
  have hs : segre z = (Ψ (segre z) 0 * (Ψ (segre z') 0)⁻¹) • segre z' := by
    have := congrArg (fun v => Ψ (segre z) 0 • v) h
    simpa [sheetNorm, smul_smul, h0] using this
  obtain ⟨c, hc, hcz⟩ := sameOrbit_of_segre hz' _ (mul_ne_zero h0 (inv_ne_zero h0')) hs
  exact ⟨z', rfl, c, hc, hcz⟩

theorem sheetProj_fibre_finite {P : Ideal (MRing J)} (hP : IsArithVar P (n + 1))
    {Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)} (hΨ : IsGoodProj P Ψ)
    {V : Set (Fin n → ℂ)} {γ : (Fin n → ℂ) → (Σ k, J k) → ℂ} (hmem : ∀ t ∈ V, γ t ∈ mcPts P)
    (hinj : ∀ t ∈ V, ∀ t' ∈ V, γ t ∈ torusSat {γ t'} → t = t') (y : Fin n → ℂ) :
    ({t | t ∈ V ∧ Ψ (segre (γ t)) 0 ≠ 0} ∩ sheetProj Ψ γ ⁻¹' {y}).Finite := by
  refine Set.Finite.of_finite_image (f := fun t => sheetNorm Ψ (γ t))
    ((fibreFinite K J P n Ψ hP hΨ y).subset ?_) ?_
  · rintro _ ⟨t, ⟨⟨htV, h0⟩, hy⟩, rfl⟩
    have := sheetNorm_mem_fibre hP.1 hP.2.1.2.1 Ψ γ (hmem t htV) h0
    rwa [show sheetProj Ψ γ t = y from hy] at this
  · rintro t ⟨⟨ht, h0⟩, -⟩ t' ⟨⟨ht', h0'⟩, -⟩ h
    exact hinj t ht t' ht' (sheetNorm_eq_torusSat Ψ (hmem t' ht').1 h0 h0' h)

theorem sheet_not_flat {P : Ideal (MRing J)} (hP : IsArithVar P (n + 1))
    {Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)} (hΨ : IsGoodProj P Ψ)
    {V : Set (Fin n → ℂ)} {γ : (Fin n → ℂ) → (Σ k, J k) → ℂ} (hV : IsOpen V)
    (hγ : AnalyticOnNhd ℂ γ V) (hmem : ∀ t ∈ V, γ t ∈ mcPts P)
    (hinj : ∀ t ∈ V, ∀ t' ∈ V, γ t ∈ torusSat {γ t'} → t = t') {O : Set (Fin n → ℂ)} (hO : IsOpen O)
    (hOV : O ⊆ V) (hne : O.Nonempty) (h0 : ∀ t ∈ O, Ψ (segre (γ t)) 0 ≠ 0)
    (hdet : ∀ t ∈ O, LinearMap.det (fderiv ℂ (sheetProj Ψ γ) t :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0) : False := by
  obtain ⟨y, hy⟩ := exists_infinite_fibre hO hne
    (fun t ht => analyticAt_sheetProj Ψ (hγ t (hOV ht)) (h0 t ht)) hdet
  exact hy ((sheetProj_fibre_finite hP hΨ hmem hinj y).subset fun t ht =>
    ⟨⟨hOV ht.1, h0 t ht.1⟩, ht.2⟩)

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseMetricPullbackFamilyStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_metric_pullback_family : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (e : ℕ) (X' : Type) [TopologicalSpace X'] (A' : FinHolAtlas e X') (U' : X' → Set X') (lf : X' → X' → (Σ k, ι k) → ℂ) (pr' : X' → BM.Rb.X) (l : Fin BM.q), HoloMap A' BM.Rb.A pr' → (∀ x, IsOpen (U' x)) → (∀ x, x ∈ U' x) → (∀ x p, A'.HoloOn (U' x) (fun y => lf x y p)) → (∀ x, ∀ y ∈ U' x, SameOrbit (lf x y) (lf y y)) → (∀ x, pr' x ∈ BM.O l → ∀ V, IsOpen V → x ∈ V → ∃ x' ∈ V, pr' x' ∈ BM.O l \ bdry BM.s ∧ ∀ p, FC.plk M (BM.F l) (FC.bvec BM l (pr' x')) (lf x' x') p ≠ 0) → IsNull A' {x | pr' x ∈ BM.O l ∧ (pr' x ∈ bdry BM.s ∨ ∃ p, FC.plk M (BM.F l) (FC.bvec BM l (pr' x)) (lf x x) p = 0)} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.isNull_off_bigCell | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.isNull_off_bigCell | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.isNull_off_bigCell <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BigZe
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ

def tz {I : Type} [Fintype I] (Z : Matrix I I ℂ) (z : I → ℂ) : I → ℂ := z - Z *ᵥ star z

abbrev Ix (Ψ : Type) (j j' : ℕ) : Type := (Fin j' ⊕ Fin j) × Ψ

def emb {E : Type} [Field E] [NumberField E] {Ψ : Type} {j j' : ℕ} (σ : Ψ → (𝓞 E →+* ℂ)) (i : Ix Ψ j j') : 𝓞 E →+* ℂ :=
  Sum.elim (fun _ => σ i.2) (fun _ => (starRingEnd ℂ).comp (σ i.2)) i.1

def bigZ {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) :
    Matrix (Ix Ψ j j') (Ix Ψ j j') ℂ :=
  blockDiagonal fun τ => fromBlocks 0 (ballMat q t τ)ᵀ (ballMat q t τ) 0

def bigZe {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} (e : Ix Ψ j j' ≃ Fin g) (q : Ψ × Fin j × Fin j' ≃ Fin n)
    (t : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  (bigZ q t).submatrix e.symm e.symm

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.EvCEqZeroIffOfSameOrbit
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.Build

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

section Forms

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem evC_torus {f : MRing ι} {b : K → ℕ} (hf : IsMultiHomog f b) (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    evC (fun p => c p.1 * z p) f = (∏ k, c k ^ b k) * evC z f := by
  classical
  simp only [evC, eval_map]
  rw [eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have h1 : ∏ p : Σ k, ι k, c p.1 ^ m p = ∏ k, c k ^ b k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, c k ^ m ⟨k, i⟩ = c k ^ b k
    rw [Finset.prod_pow_eq_pow_sum, hf m hm k]
  simp only [mul_pow, Finset.prod_mul_distrib, h1]
  ring

theorem evC_eq_zero_iff_of_sameOrbit {f : MRing ι} {b : K → ℕ} (hf : IsMultiHomog f b)
    {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : evC z f = 0 ↔ evC z' f = 0 := by
  obtain ⟨c, hc, rfl⟩ := h
  have h0 : ∏ k, c k ^ b k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  rw [evC_torus hf]
  simp [h0]

theorem evC_rename (v : (Σ k, ι k) → Σ k, ι' k) (z : (Σ k, ι' k) → ℂ) (f : MRing ι) :
    evC z (rename v f) = evC (fun p => z (v p)) f := by
  rw [evC, map_rename, eval_rename]
  rfl

theorem evC_mul (z : (Σ k, ι k) → ℂ) (f g : MRing ι) : evC z (f * g) = evC z f * evC z g := by
  simp [evC]

theorem sum_mapDomain {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hv : ∀ p, (v p).1 = κ p.1)
    [DecidableEq K'] (m : (Σ k, ι k) →₀ ℕ) (k' : K') :
    ∑ i, (Finsupp.mapDomain v m) ⟨k', i⟩ = ∑ p : Σ k, ι k, if κ p.1 = k' then m p else 0 := by
  classical
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [Finsupp.mapDomain_add]
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, hf, hg]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> simp
  | single p n =>
    have hR : (∑ q : Σ k, ι k, if κ q.1 = k' then (Finsupp.single p n) q else 0) =
        if κ p.1 = k' then n else 0 := by
      rw [Finset.sum_eq_single p]
      · simp
      · intro q _ hq
        simp [Finsupp.single_apply, Ne.symm hq]
      · simp
    have hL : ∀ q : Σ k, ι' k, ∑ i, (Finsupp.single q n) ⟨k', i⟩ = if q.1 = k' then n else 0 := by
      rintro ⟨kq, iq⟩
      by_cases h : kq = k'
      · subst h
        simp [Finsupp.single_apply]
      · simp [Finsupp.single_apply, h]
    rw [Finsupp.mapDomain_single, hL, hR, hv]

theorem isMultiHomog_rename {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hb : IsBlockMap κ v) {f : MRing ι}
    {b : K → ℕ} (hf : IsMultiHomog f b) : IsMultiHomog (rename v f) (Function.extend κ b 0) := by
  classical
  intro m hm k'
  rw [support_rename_of_injective hb.2.1, Finset.mem_image] at hm
  obtain ⟨m₀, hm₀, rfl⟩ := hm
  rw [sum_mapDomain hb.2.2.1, Fintype.sum_sigma]
  by_cases hk : ∃ k, κ k = k'
  · obtain ⟨k, rfl⟩ := hk
    rw [hb.1.extend_apply, Finset.sum_eq_single k]
    · simpa using hf m₀ hm₀ k
    · intro k₂ _ hne
      exact Finset.sum_eq_zero fun i _ => if_neg (hb.1.ne hne)
    · simp
  · rw [Function.extend_apply' _ _ _ hk]
    exact Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun i _ => if_neg fun h => hk ⟨k, h⟩

theorem isMultiHomog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, h₁, m₂, h₂, rfl⟩ := Finset.mem_add.1 (support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m₁ h₁ k, hg m₂ h₂ k]

end Forms

section Sides

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K₁ : Type} [Fintype K₁] {ι₁ : K₁ → Type} [∀ k, Fintype (ι₁ k)]

theorem exists_bdry_form {P₁ : Ideal (MRing ι₁)} {D : ℕ} {σ : Type} {S : AnSys D σ} (Re : Realis S P₁)
    (h : AlgOver Re) : ∃ (γ : MRing ι₁) (c : K₁ → ℕ), IsMultiHomog γ c ∧ γ ∉ P₁ ∧
      ∀ x, Re.π x ∈ bdry S.s → evC (Re.R.lift x x) γ = 0 := by
  obtain ⟨K₀, _, ι₀, _, κ, v, U, lam, β, b, hb, -, hor, hβ, hn, hz⟩ := h
  refine ⟨rename v β, Function.extend κ b 0, isMultiHomog_rename hb hβ, hn, fun x hx => ?_⟩
  rw [evC_rename, ← evC_eq_zero_iff_of_sameOrbit hβ (hor x)]
  exact hz _ hx

theorem side {κ₁ : K₁ → K} {v₁ : (Σ k, ι₁ k) → Σ k, ι k} (hb : IsBlockMap κ₁ v₁) {P J : Ideal (MRing ι)}
    {D : ℕ} {σ : Type} {S : AnSys D σ} {P₁ : Ideal (MRing ι₁)} (Re : Realis S P₁) (e : imageZ v₁ P = P₁)
    (R : AnLogRes P J D) (har : IsArithVar P (D + 1)) (alg : AlgOver Re) :
    ∃ (π : R.X → S.X) (hπ : HoloMap R.A S.A π),
      (∀ (x : R.X) (x₁ : Re.R.X), SameOrbit (Re.R.lift x₁ x₁) (fun p => R.lift x x (v₁ p)) → π x = Re.π x₁) ∧
      (∀ a (ref' : HermLine ι), IsPullHerm κ₁ v₁ (Re.ref a) ref' →
        SamePot R.A Set.univ (potOf R ref') ((S.th a).pullback π hπ.1)) ∧
      (∀ a t, 0 < t → t ≤ S.t₀ → ∀ x, Real.log ((Re.line a t).h fun p => R.lift x x (v₁ p)) =
        Real.log ((Re.ref a).h fun p => R.lift x x (v₁ p)) + S.phT a t (π x)) := by
  subst e
  obtain ⟨π, hπ, h1, h2, h3, -⟩ := GlobalTheory.T.algebraic_realisation_holomorphic_map K ι K₁ ι₁ κ₁ v₁ P J D σ S Re R hb har alg
  exact ⟨π, hπ, h1, h2, h3⟩

theorem evC_bdry {κ₁ : K₁ → K} {v₁ : (Σ k, ι₁ k) → Σ k, ι k} (hb : IsBlockMap κ₁ v₁) {P J : Ideal (MRing ι)}
    {D : ℕ} {σ : Type} {S : AnSys D σ} {P₁ : Ideal (MRing ι₁)} (Re : Realis S P₁) (e : imageZ v₁ P = P₁)
    (R : AnLogRes P J D) {π : R.X → S.X}
    (hπ : ∀ (x : R.X) (x₁ : Re.R.X), SameOrbit (Re.R.lift x₁ x₁) (fun p => R.lift x x (v₁ p)) → π x = Re.π x₁)
    {γ : MRing ι₁} {c : K₁ → ℕ} (hγ : IsMultiHomog γ c)
    (hz : ∀ x, Re.π x ∈ bdry S.s → evC (Re.R.lift x x) γ = 0) (x : R.X) (hx : π x ∈ bdry S.s) :
    evC (R.lift x x) (rename v₁ γ) = 0 := by
  have hmem : (fun p => R.lift x x (v₁ p)) ∈ mcPts P₁ :=
    e ▸ (GlobalTheory.T.block_pullback_herm_line K₁ ι₁ K ι κ₁ v₁ hb).2.2.1 P _ (R.mem x x (R.mem_U x))
  obtain ⟨x₁, hx₁⟩ := GlobalTheory.T.log_resolution_covers_complex_points K₁ ι₁ P₁ _ D Re.R Re.arith _ hmem
  rw [evC_rename, ← evC_eq_zero_iff_of_sameOrbit hγ hx₁]
  exact hz x₁ (hπ x x₁ hx₁ ▸ hx)

end Sides

section Assemble

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K₁ : Type} [Fintype K₁] {ι₁ : K₁ → Type} [∀ k, Fintype (ι₁ k)]
  {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

end Assemble

end GlobalTheory.CompanionTheory.Ar.Cmp.Build
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsContinuousMetricRatio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cusp.Descent

open ReciprocityTheory.AnForm.M

section General
variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem holoOn_continuousOn {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {U : Set X}
    {f : X → ℂ} (hU : IsOpen U) (h : A.HoloOn U f) : ContinuousOn f U := by
  intro t ht
  obtain ⟨j, hj⟩ := A.cover t
  have h1 : AnalyticAt ℂ (f ∘ (A.chart j).symm) (A.chart j t) :=
    h j _ ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using ht⟩
  have h2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ A.chart j) t :=
    ContinuousAt.comp h1.continuousAt ((A.chart j).continuousAt hj)
  have h3 : ((f ∘ (A.chart j).symm) ∘ A.chart j) =ᶠ[𝓝 t] f := by
    filter_upwards [(A.chart j).open_source.mem_nhds hj] with u hu
    simp [(A.chart j).left_inv hu]
  exact (h2.congr h3).continuousWithinAt

theorem exists_continuous_descent {P : Ideal (MRing J)} {d : ℕ} (M : CxModel P d)
    (F : ((Σ k, J k) → ℂ) → ℝ) (hF : ContinuousOn F {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0})
    (hinv : ∀ (c : K → ℂ), (∀ k, c k ≠ 0) → ∀ z ∈ mcPts P, F (torusSmul c z) = F z) :
    ∃ κ : M.Xc → ℝ, Continuous κ ∧ ∀ z ∈ mcPts P, κ (M.proj z) = F z := by
  choose r hr hpr using M.surj
  have key : ∀ z ∈ mcPts P, F (r (M.proj z)) = F z := by
    intro z hz
    obtain ⟨c, hc, e⟩ := (M.fibre _ (hr _) z hz).1 (hpr _)
    calc F (r (M.proj z)) = F (torusSmul c (r (M.proj z))) := (hinv c hc _ (hr _)).symm
      _ = F z := by rw [← e]
  refine ⟨fun x => F (r x), ?_, key⟩
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨U, hU, hx, s, hs, hh⟩ := M.sections x
  have hsc : ContinuousOn s U := continuousOn_pi.2 fun p => holoOn_continuousOn hU (hh p)
  have hcomp : ContinuousOn (F ∘ s) U := hF.comp hsc fun y hy => (hs y hy).1.1
  refine (hcomp.continuousAt (hU.mem_nhds hx)).congr ?_
  filter_upwards [hU.mem_nhds hx] with y hy
  have h := key (s y) (hs y hy).1
  rw [(hs y hy).2] at h
  exact h.symm

theorem log_h_torusSmul (A : HermLine J) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) {z : (Σ k, J k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (A.h (torusSmul c z)) = (∑ k, (A.a k : ℝ) * Real.log ‖c k‖) + Real.log (A.h z) := by
  have h1 : A.h (torusSmul c z) = (∏ k, ‖c k‖ ^ A.a k) * A.h z := A.smul c z hc
  have h2 : ∀ k, ‖c k‖ ^ A.a k ≠ 0 := fun k => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
  rw [h1, Real.log_mul (Finset.prod_ne_zero_iff.mpr fun k _ => h2 k) (A.pos z hz).ne',
    Real.log_prod (fun k _ => h2 k)]
  simp only [Real.log_zpow]

theorem log_h_continuousOn {A : HermLine J} (hA : IsSmoothHerm A) :
    ContinuousOn (fun z => Real.log (A.h z)) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
  ContinuousOn.log hA.continuousOn fun z hz => (A.pos z hz).ne'

end General

theorem logDiff_descends : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (B : ℕ) (Nb : HermLine J), IsSmoothHerm Nb → Nb.a = muTwDeg Hd B → ∃ κ : M.Xc → ℝ, Continuous κ ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), κ (M.proj z) = Real.log (Nb.h z) - Real.log (S.ref.h z) - ∑ p ∈ D.SB B, Real.log (D.vertFactor p z) := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D Hd M S B Nb hNb hdeg
  have hA : ∀ p, ∃ A : HermLine J, p ∈ D.SB B → A.a = D.vdeg p ∧ IsSmoothHerm A ∧
      ∀ z ∈ mcPts (mCoordIdeal D.y), A.h z = D.vertFactor p z := by
    intro p
    by_cases hp : p ∈ D.SB B
    · obtain ⟨A, h1, h2, -, h3⟩ :=
        (GlobalTheory.T.vertical_factor_smooth_hermitian_metric K J II Ψ Ω W D p (Finset.mem_of_mem_filter p hp)).1
      exact ⟨A, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨S.ref, fun h => absurd h hp⟩
  choose A hA using hA
  have hdegk : ∀ k, (Nb.a k : ℝ) = (S.ref.a k : ℝ) + ∑ p ∈ D.SB B, ((A p).a k : ℝ) := by
    intro k
    have href : S.ref.a = Hd.aMu := S.ref_deg
    have hs : ∑ p ∈ D.SB B, (A p).a k = ∑ p ∈ D.SB B, D.vdeg p k :=
      Finset.sum_congr rfl fun p hp => by rw [(hA p hp).1]
    have : Nb.a k = S.ref.a k + ∑ p ∈ D.SB B, (A p).a k := by
      rw [hdeg, href, hs]
      simp [muTwDeg, Finset.sum_apply]
    rw [this]
    push_cast
    rfl
  obtain ⟨κ, hκ, hκe⟩ := exists_continuous_descent M
    (fun z => Real.log (Nb.h z) - Real.log (S.ref.h z) - ∑ p ∈ D.SB B, Real.log ((A p).h z))
    (((log_h_continuousOn hNb).sub (log_h_continuousOn S.ref_smooth)).sub
      (continuousOn_finset_sum _ fun p hp => log_h_continuousOn (hA p hp).2.1))
    (by
      intro c hc z hz
      have hb := hz.1
      simp only [log_h_torusSmul _ hc hb, Finset.sum_add_distrib]
      rw [Finset.sum_comm (s := D.SB B)]
      simp only [hdegk, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
      ring)
  refine ⟨κ, hκ, fun z hz => ?_⟩
  rw [hκe z hz]
  congr 1
  exact Finset.sum_congr rfl fun p hp => by rw [(hA p hp).2.2 z hz]

end GlobalTheory.CompanionTheory.Ar.Cusp.Descent
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsPotentialFromSncChartsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_potential_from_snc_charts : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (M : XModel D) (P : GroundTheory.Heights₂.Heights.Regular.PotentialCharts M.atlas) (S : Fin P.N → Finset (Fin D.n)), Adapted M P S → FromSnc M P → ∃ (r : M.Xc → ℝ) (f : Fin P.N → (Fin D.n → ℂ) → ℝ) (Bf : ℝ), (∀ z ∈ D.Xo, 1 ≤ r (M.proj z)) ∧ (∀ j, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f j) (P.chart j).target ∧ ∀ y ∈ (P.chart j).target, |f j y| ≤ Bf) ∧ ∀ j, ∀ y ∈ (P.chart j).target \ ReciprocityTheory.AnForm.A.coordDiv (S j), r ((P.chart j).symm y) = Real.exp 1 + f j y + ∑ i ∈ S j, Real.log (‖y i‖ ^ 2)⁻¹ := by
  first | exact @GlobalTheory.CompanionTheory.Relay.exists_potential_from_snc_charts | exact GlobalTheory.CompanionTheory.Relay.exists_potential_from_snc_charts | (intros; apply GlobalTheory.CompanionTheory.Relay.exists_potential_from_snc_charts <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartFifthStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_chart_fifth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ z ∈ wO M Rb τ a k₀ ca cb F kb V r h, wRho M Rb τ k₀ ca cb F kb r h ε z ∈ wD ε V ∧ SameOrbit (wPhi M F bl h ε k₀ τ ca cb (wRho M Rb τ k₀ ca cb F kb r h ε z)) z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.Onto.main | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.Onto.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.Onto.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolutionFourthStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_twisted_resolution_fourth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ i, HoloMap RW.A FA.S.A (q i)) → (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → (Function.Injective fun w => (q 0 w, q 1 w)) → ∀ (l : Fin BM.q) (x : RW.X), FA.pr (q 0 x) ∈ BM.O l → (∀ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x))) (fstPt k₀ (RW.lift x x)) p ≠ 0) → (∀ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x))) (sndPt k₀ (RW.lift x x)) p ≠ 0) → ∃ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a₀ a₁ : ℂ), SameOrbit (RW.lift x x) (FC.wVec M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x))) (FC.Lca τ ca cb c a₀) τ a k₀ ca cb (a₁ - a₀)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.Cell.vector_of_chart | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.Cell.vector_of_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.Cell.vector_of_chart <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolutionSixthStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_twisted_resolution_sixth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ i, HoloMap RW.A FA.S.A (q i)) → (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → (Function.Injective fun w => (q 0 w, q 1 w)) → ∀ (l : Fin BM.q) (x : RW.X), FA.pr (q 0 x) ∈ BM.O l → ∀ V, IsOpen V → x ∈ V → ∃ x' ∈ V, FA.pr (q 0 x') ∈ BM.O l \ bdry BM.s ∧ ∀ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x'))) (fstPt k₀ (RW.lift x' x')) p ≠ 0 ∧ FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x'))) (sndPt k₀ (RW.lift x' x')) p ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.dens_w | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.dens_w | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.dens_w <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolutionThirdStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_twisted_resolution_third : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)), Nonempty RW.X := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FibNonempty.anLogRes_W_nonempty | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FibNonempty.anLogRes_W_nonempty | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FibNonempty.anLogRes_W_nonempty <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticDenseGoodPointsStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_analytic_dense_good_points : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (l : Fin BM.q) (x : FA.Re.R.X), FA.pr (FA.Re.π x) ∈ BM.O l → ∀ V, IsOpen V → x ∈ V → ∃ x' ∈ V, FA.pr (FA.Re.π x') ∈ BM.O l \ bdry BM.s ∧ ∀ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (FA.Re.π x'))) (FA.Re.R.lift x' x') p ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.dens_r | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.dens_r | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.dens_r <;> assumption)
end

