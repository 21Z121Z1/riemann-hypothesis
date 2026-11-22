import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XSqR
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0039
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0049
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0105
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0114
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0096
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComponentResFibreSum
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0096
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0075
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0098
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0099
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0083
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0079
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0081
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0041
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0090
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0033
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0008
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsCuspDataForTorusInvariant
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0097
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AlgebraicSquareXiIntersection
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.algebraic_square_xi_intersection : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (k₀ : K) (xi2 : K → ℤ) (Q : AlgSq P d k₀ xi2) (Xi : HermLine ι) (X₀ X₁ : HermLine Q.ιW), Xi.a = xi2 → IsSmoothHerm Xi → IsPullHerm (Q.κ 0) (Q.v 0) Xi X₀ → IsPullHerm (Q.κ 1) (Q.v 1) Xi X₁ → ∀ T : Fin (d + 1) → HermLine Q.ιW, (∀ j, IsSmoothHerm (T j)) → II Q.KW Q.ιW Q.PW (d + 3) (Fin.cons X₀ (Fin.cons X₀ T)) - II Q.KW Q.ιW Q.PW (d + 3) (Fin.cons X₁ (Fin.cons X₁ T)) = 2 * (ptsIntegral Q.PW (pot (Fin.cons X₀ T : Fin (d + 2) → HermLine Q.ιW)) (Q.logNormT Xi) - ptsIntegral Q.PW (pot (Fin.cons X₁ T : Fin (d + 2) → HermLine Q.ιW)) (Q.logNormT Xi)) := by
  first | exact @PositivityTheory.Xgp.t_sq_R | exact PositivityTheory.Xgp.t_sq_R
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ConePtsSubsetMcPtsOfMinimal
section
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxComp

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}

theorem conePts_subset_mcPts_of_minimal {P : Ideal (MRing ι)} {Q : Ideal (MRingOver ℂ ι)}
    (hQ : Q ∈ (cxIdeal P).minimalPrimes) : conePts Q ⊆ mcPts P := fun _ hz =>
  ⟨hz.1, fun f hf => hz.2 _ (hQ.1.2 (Ideal.mem_map_of_mem _ hf))⟩

theorem exists_minimal_of_mem_mcPts {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) :
    ∃ Q ∈ (cxIdeal P).minimalPrimes, z ∈ conePts Q := by
  have hz' : z ∈ conePts (cxIdeal P) := by rw [← mcPts_eq_conePts]; exact hz
  have hle : cxIdeal P ≤ RingHom.ker (eval z : MRingOver ℂ ι →+* ℂ) :=
    fun f hf => RingHom.mem_ker.2 (hz'.2 f hf)
  have : (RingHom.ker (eval z : MRingOver ℂ ι →+* ℂ)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨Q, hQ, hQle⟩ := Ideal.exists_minimalPrimes_le hle
  exact ⟨Q, hQ, hz'.1, fun f hf => RingHom.mem_ker.1 (hQle hf)⟩

theorem mem_conePts_of_segre_eq {P : Ideal (MRing ι)} {Q : Ideal (MRingOver ℂ ι)} (hP : IsArithVar P (e + 1))
    (hQ : Q ∈ (cxIdeal P).minimalPrimes) {z z' : (Σ k, ι k) → ℂ} (hz : z ∈ conePts Q)
    (hz' : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) (hs : segre z = segre z') : z' ∈ conePts Q := by
  classical
  choose i0 hi0 using hz.1
  obtain ⟨-, h4⟩ := eq_bsmul_of_segre_eq i0 hi0 hs
  have hJ := GroundTheory.Heights₂.Heights.HilbertSamuel.ComponentResBridge.isMultiHomogIdeal_of_mem_minimalPrimes hP hQ
  have h5 := ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul hJ (fun k => z' ⟨k, i0 k⟩ / z ⟨k, i0 k⟩) z hz.2
  refine ⟨hz', fun f hf => ?_⟩
  rw [h4]
  exact h5 f hf

theorem isSheet_of_isSetSheet {P : Ideal (MRing ι)} {Q : Ideal (MRingOver ℂ ι)}
    (hQ : Q ∈ (cxIdeal P).minimalPrimes) {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    (h : IsSetSheet (conePts Q) Ψ y w γ) : IsSheet P Ψ y w γ :=
  ⟨h.1, h.2.mono fun _ h' => ⟨h'.1, conePts_subset_mcPts_of_minimal hQ h'.2.1, h'.2.2⟩⟩

theorem isSetSheet_of_isSheet {P : Ideal (MRing ι)} {Q : Ideal (MRingOver ℂ ι)} (hP : IsArithVar P (e + 1))
    (hQ : Q ∈ (cxIdeal P).minimalPrimes) {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    (hone : ∀ Q' ∈ (cxIdeal P).minimalPrimes, ∀ z, z ∈ conePts Q → z ∈ conePts Q' →
      Ψ (segre z) = Fin.cons 1 y → Q' = Q)
    (hw : w ∈ setFibre (conePts Q) Ψ y) (h : IsSheet P Ψ y w γ) :
    IsSetSheet (conePts Q) Ψ y w γ := by
  obtain ⟨z, hz, hzw, -⟩ := hw
  obtain ⟨hd, hm, hΨγ⟩ := h.2.self_of_nhds
  have hγQ : γ y ∈ conePts Q := mem_conePts_of_segre_eq hP hQ hz hm.1 (hzw.trans h.1.symm)
  have hfin : (cxIdeal P).minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
  have hev : ∀ᶠ y' in 𝓝 y, ∀ Q' ∈ (cxIdeal P).minimalPrimes, Q' ≠ Q → γ y' ∉ conePts Q' := by
    refine (Filter.eventually_all_finite hfin).2 fun Q' hQ' => ?_
    by_cases hne : Q' = Q
    · exact Eventually.of_forall fun _ h' => absurd hne h'
    have hnot : γ y ∉ conePts Q' := fun hc => hne (hone Q' hQ' _ hγQ hc hΨγ)
    obtain ⟨f, hf, hf0⟩ : ∃ f ∈ Q', eval (γ y) f ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hnot ⟨hm.1, hcon⟩
    have hc : ContinuousAt (fun y' => eval (γ y') f) y :=
      (MvPolynomial.continuous_eval f).continuousAt.comp hd.continuousAt
    filter_upwards [hc.eventually_ne hf0] with y' hy' _ hmem
    exact hy' (hmem.2 f hf)
  refine ⟨h.1, ?_⟩
  filter_upwards [h.2, hev] with y' h1 h2
  obtain ⟨Q', hQ', hz'⟩ := exists_minimal_of_mem_mcPts h1.2.1
  by_cases hne : Q' = Q
  · subst hne
    exact ⟨h1.1, hz', h1.2.2⟩
  · exact absurd hz' (h2 Q' hQ' hne)

end GlobalTheory.CompanionTheory.Ar.Pub.CxComp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvergenceRateStatementHoldsStatement
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convergence_rate_statement_holds : ConvergenceRateStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.convergenceRate_holds | exact GlobalTheory.CompanionTheory.Ar.Giv.convergenceRate_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.convergenceRate_holds <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.DetFacChange
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Scal

section Values

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}

theorem reg_prod_zpow (hz : z ∈ mcPts (mCoordIdeal x)) {κ : Type} [Fintype κ] (t : κ → Ω) (e : κ → ℤ)
    (h0 : ∀ k, t k ≠ 0) (ht : ∀ k, RegAt x (mCoordIdeal z) (t k)) (ht' : ∀ k, RegAt x (mCoordIdeal z) (t k)⁻¹) :
    RegAt x (mCoordIdeal z) (∏ k, t k ^ e k) ∧
      valAt x (∏ k, t k ^ e k) z = ∏ k, valAt x (t k) z ^ e k := by
  let u : κ → (regRing x z)ˣ := fun k =>
    ⟨⟨t k, ht k⟩, ⟨(t k)⁻¹, ht' k⟩, Subtype.ext (mul_inv_cancel₀ (h0 k)), Subtype.ext (inv_mul_cancel₀ (h0 k))⟩
  let f : (regRing x z)ˣ →* Ωˣ := Units.map (regRing x z).subtype.toMonoidHom
  let g : (regRing x z)ˣ →* ℂˣ := Units.map (regVal x hz).toMonoidHom
  let U : (regRing x z)ˣ := ∏ k, u k ^ e k
  have h1 : ((U : regRing x z) : Ω) = ∏ k, t k ^ e k := by
    have e1 : ((U : regRing x z) : Ω) = ((f U : Ωˣ) : Ω) := rfl
    rw [e1, map_prod, Units.coe_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_zpow, Units.val_zpow_eq_zpow_val]
    rfl
  have h2 : valAt x ((U : regRing x z) : Ω) z = ∏ k, valAt x (t k) z ^ e k := by
    have e1 : valAt x ((U : regRing x z) : Ω) z = ((g U : ℂˣ) : ℂ) := rfl
    rw [e1, map_prod, Units.coe_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_zpow, Units.val_zpow_eq_zpow_val]
    rfl
  rw [← h1]
  exact ⟨(U : regRing x z).2, h2⟩

theorem reg_detFac (hz : z ∈ mcPts (mCoordIdeal x)) {N : ℕ} (j : ℕ) (i : Fin N) {A : Matrix (Fin N) (Fin N) Ω}
    (hA : ∀ a b, RegAt x (mCoordIdeal z) (A a b)) :
    RegAt x (mCoordIdeal z) (detFac j i A) ∧ valAt x (detFac j i A) z = detFac j i (valMat x z A) := by
  have h₁ := reg_minor hz hA (wIdx N j) (wIdx N j)
  have h₂ := reg_minor hz hA (omIdx N j) (omIdx N j)
  unfold detFac
  split_ifs
  · exact ⟨ValRing.regAt_mul h₁.1 h₂.1, (reg_mul hz h₁.1 h₂.1).2.trans (by rw [h₁.2, h₂.2])⟩
  · rw [mul_one, mul_one]; exact h₁
  · rw [one_mul, one_mul]; exact h₂
  · rw [mul_one, mul_one]; exact ⟨ValRing.regAt_one x z, CovMap.LocImg.FV.valAt_one' hz⟩

theorem ratio_reg (hz : z ∈ mcPts (mCoordIdeal x)) {k : K} {c₁ c₂ : ι k}
    (h₁ : (X ⟨k, c₁⟩ : MRing ι) ∉ mCoordIdeal z) (h₂ : (X ⟨k, c₂⟩ : MRing ι) ∉ mCoordIdeal z) :
    x ⟨k, c₂⟩ / x ⟨k, c₁⟩ ≠ 0 ∧ RegAt x (mCoordIdeal z) (x ⟨k, c₂⟩ / x ⟨k, c₁⟩) ∧
      valAt x (x ⟨k, c₂⟩ / x ⟨k, c₁⟩) z = z ⟨k, c₂⟩ / z ⟨k, c₁⟩ := by
  have hne : ∀ {c : ι k}, (X ⟨k, c⟩ : MRing ι) ∉ mCoordIdeal z → z ⟨k, c⟩ ≠ 0 := fun {c} hc h0 => hc (by
    show mConeMap z (X ⟨k, c⟩) = 0
    rw [mConeMap, aeval_X, h0, map_zero, zero_mul])
  obtain ⟨hx₁, hv⟩ := CovGraph.isValueAt_coord_ratio K ι Ω x z k c₁ hz (hne h₁)
  obtain ⟨hx₂, -⟩ := CovGraph.isValueAt_coord_ratio K ι Ω x z k c₂ hz (hne h₂)
  refine ⟨div_ne_zero hx₂ hx₁, ⟨fun l => if l = k then 1 else 0, X ⟨k, c₂⟩, X ⟨k, c₁⟩,
    isMultiHomog_X_single ⟨k, c₂⟩, isMultiHomog_X_single ⟨k, c₁⟩, h₁, ?_⟩, ?_⟩
  · simp only [aeval_X]
    field_simp
  · rw [valAt_eq hz (hv c₂), inv_mul_eq_div]

end Values

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ} (M : FlagModel y Ψ N j) {F₁ F₂ : FrameData ι Ψ N M.Ω M.blk}

include M in

theorem detFac_change (h₁ : M.IsFrame F₁) (h₂ : M.IsFrame F₂) (p : Ψ × Fin N) :
    detFac j p.2 (F₂.T p.1) = detFac j p.2 (F₁.T p.1) * detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1) := by
  have hT₁ := h₁.1 p.1
  have hu₁ : IsUnit (F₁.T p.1).det := hT₁.2.isUnit
  have h := ((GlobalTheory.T.block_diagonal_minor_vanishing M.Ω N j p.2 M.j_le).2.2.2 _ _ hT₁.1 ((hT₁.1.inv hu₁).mul (h₂.1 p.1).1)).2
  rwa [Matrix.mul_nonsing_inv_cancel_left _ _ hu₁] at h

theorem prod_ratio (c₁ : ∀ k, M.x ⟨k, F₁.c k⟩ ≠ 0) (p : Ψ × Fin N) :
    (∏ k', (M.x ⟨k', F₂.c k'⟩ / M.x ⟨k', F₁.c k'⟩) ^ M.b p k') * ∏ k', M.x ⟨k', F₁.c k'⟩ ^ M.b p k' =
      ∏ k', M.x ⟨k', F₂.c k'⟩ ^ M.b p k' := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k' _ => ?_
  rw [← mul_zpow, div_mul_cancel₀ _ (c₁ k')]

open CovMap.LocImg.FrameChange in

theorem frame_rel (h₁ : M.IsFrame F₁) (h₂ : M.IsFrame F₂) (c₁ : ∀ k, M.x ⟨k, F₁.c k⟩ ≠ 0) (p : Ψ × Fin N) (k : K)
    (hp : M.blk p = some k) (m : ι k) (I' : Finset (Fin N)) (hI' : IsStepRows N j p.2 I') :
    detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1) * ∑ I, F₁.u ⟨k, m⟩ I * minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I I' =
      (∏ k', (M.x ⟨k', F₂.c k'⟩ / M.x ⟨k', F₁.c k'⟩) ^ M.b p k') * F₂.u ⟨k, m⟩ I' := by
  have hj := M.j_le
  have hT₁ := h₁.1 p.1
  have hT₂ := h₂.1 p.1
  have hu₁ : IsUnit (F₁.T p.1).det := hT₁.2.isUnit
  have hA₁ : (∏ k', M.x ⟨k', F₁.c k'⟩ ^ M.b p k') ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ (c₁ k')
  have hS : IsBlockDiag j ((F₁.T p.1)⁻¹ * F₂.T p.1) := (hT₁.1.inv hu₁).mul hT₂.1
  have hE : IsBlockDiag j (unitCols I' (stepCols N j p.2) hI'.1 : Matrix (Fin N) (Fin N) M.Ω) :=
    unitCols_blockDiag _ _ _ (stepRows_same_side hI')
  have e1 := h₁.2.1 p k hp m _ (hS.mul hE)
  have e2 := h₂.2.1 p k hp m _ hE
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu₁] at e1
  have hm : ∀ I, minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1 * unitCols I' (stepCols N j p.2) hI'.1) I (stepCols N j p.2) =
      minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I I' := fun I => by
    rw [(GlobalTheory.T.block_diagonal_minor_vanishing M.Ω N j p.2 hj).1]
    simp only [minor_unitCols, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hr : ∑ I, F₂.u ⟨k, m⟩ I * minorIJ (unitCols I' (stepCols N j p.2) hI'.1) I (stepCols N j p.2) =
      F₂.u ⟨k, m⟩ I' := by
    simp only [minor_unitCols, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [hm] at e1
  rw [hr] at e2
  have hd := detFac_change M h₁ h₂ p
  have hA := prod_ratio M (F₂ := F₂) c₁ p
  apply mul_left_cancel₀ hA₁
  linear_combination (-detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1)) * e1 + e2 -
    (∑ I, M.coef ⟨k, m⟩ I * minorIJ (F₂.T p.1 * unitCols I' (stepCols N j p.2) hI'.1) I (stepCols N j p.2)) * hd -
    F₂.u ⟨k, m⟩ I' * hA

theorem frame_none (h₁ : M.IsFrame F₁) (h₂ : M.IsFrame F₂) (c₁ : ∀ k, M.x ⟨k, F₁.c k⟩ ≠ 0) (p : Ψ × Fin N)
    (hp : M.blk p = none) :
    F₂.υ p * ∏ k', (M.x ⟨k', F₂.c k'⟩ / M.x ⟨k', F₁.c k'⟩) ^ M.b p k' =
      detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1) * F₁.υ p := by
  have hA₁ : (∏ k', M.x ⟨k', F₁.c k'⟩ ^ M.b p k') ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ (c₁ k')
  have e1 := h₁.2.2.2 p hp
  have e2 := h₂.2.2.2 p hp
  have hd := detFac_change M h₁ h₂ p
  have hA := prod_ratio M (F₂ := F₂) c₁ p
  apply mul_left_cancel₀ hA₁
  linear_combination (detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1)) * e1 - e2 + M.lam p * hd + F₂.υ p * hA

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (F₁ F₂ : FrameData ι Ψ N M.Ω M.blk), zb ∈ mcPts (mCoordIdeal M.x) → M.IsFrame F₁ → M.IsFrame F₂ → M.GoodAt F₁ (mCoordIdeal zb) → M.GoodAt F₂ (mCoordIdeal zb) → (∀ τ, IsBlockDiag j (valMat M.x zb ((F₁.T τ)⁻¹ * F₂.T τ)) ∧ (valMat M.x zb ((F₁.T τ)⁻¹ * F₂.T τ)).det ≠ 0) ∧ ∀ p : Ψ × Fin N, (∀ k, M.blk p = some k → ∀ h : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j h → ∀ m : ι k, detFac j p.2 (valMat M.x zb ((F₁.T p.1)⁻¹ * F₂.T p.1)) * plk M F₁ zb p.2 ⟨k, m⟩ (valMat M.x zb ((F₁.T p.1)⁻¹ * F₂.T p.1) * h) = (∏ k', (zb ⟨k', F₂.c k'⟩ / zb ⟨k', F₁.c k'⟩) ^ M.b p k') * plk M F₂ zb p.2 ⟨k, m⟩ h) ∧ (M.blk p = none → valAt M.x (F₂.υ p) zb * (∏ k', (zb ⟨k', F₂.c k'⟩ / zb ⟨k', F₁.c k'⟩) ^ M.b p k') = detFac j p.2 (valMat M.x zb ((F₁.T p.1)⁻¹ * F₂.T p.1)) * valAt M.x (F₁.υ p) zb) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M zb F₁ F₂ hz hF₁ hF₂ hG₁ hG₂
  have hj := M.j_le
  have r₁₂ := GlobalTheory.T.frame_change_regular_entries K ι Φ y Ψ N j M zb F₁ F₂ hz hF₁ hF₂ hG₁ hG₂
  have r₂₁ := GlobalTheory.T.frame_change_regular_entries K ι Φ y Ψ N j M zb F₂ F₁ hz hF₂ hF₁ hG₂ hG₁
  have hprod : ∀ τ, ((F₁.T τ)⁻¹ * F₂.T τ) * ((F₂.T τ)⁻¹ * F₁.T τ) = 1 := fun τ => by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (hF₂.1 τ).2.isUnit,
      Matrix.nonsing_inv_mul _ (hF₁.1 τ).2.isUnit]
  have hSS : ∀ τ, valMat M.x zb ((F₁.T τ)⁻¹ * F₂.T τ) * valMat M.x zb ((F₂.T τ)⁻¹ * F₁.T τ) = 1 := fun τ => by
    rw [← (regMat_mul hz (r₁₂ τ) (r₂₁ τ)).2, hprod]
    exact CovMap.LocImg.FV.valMat_one hz
  have hbd : ∀ τ, IsBlockDiag j ((F₁.T τ)⁻¹ * F₂.T τ) := fun τ =>
    ((hF₁.1 τ).1.inv (hF₁.1 τ).2.isUnit).mul (hF₂.1 τ).1
  have hbd' : ∀ τ, IsBlockDiag j ((F₂.T τ)⁻¹ * F₁.T τ) := fun τ =>
    ((hF₂.1 τ).1.inv (hF₂.1 τ).2.isUnit).mul (hF₁.1 τ).1
  refine ⟨fun τ => ⟨CovMap.LocImg.FV.valMat_blockDiag hz (hbd τ), fun h0 => ?_⟩, fun p => ?_⟩
  · have h := congrArg Matrix.det (hSS τ)
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h
    exact zero_ne_one h
  have ht := fun k : NonPluckerBlocks M.blk => ratio_reg hz (hG₁.1 k) (hG₂.1 k)
  have ht' := fun k : NonPluckerBlocks M.blk => ratio_reg hz (hG₂.1 k) (hG₁.1 k)
  have c₁ : ∀ k, M.x ⟨k, F₁.c k⟩ ≠ 0 := fun k h => (ht' k).1 (by rw [h, zero_div])
  obtain ⟨hrR, hrV⟩ := reg_prod_zpow hz (fun k : NonPluckerBlocks M.blk => M.x ⟨k, F₂.c k⟩ / M.x ⟨k, F₁.c k⟩) (M.b p)
    (fun k => (ht k).1) (fun k => (ht k).2.1) (fun k => by rw [inv_div]; exact (ht' k).2.1)
  simp only [fun k : NonPluckerBlocks M.blk => (ht k).2.2] at hrV
  obtain ⟨hdR, hdV⟩ := reg_detFac hz j p.2 (r₁₂ p.1)
  refine ⟨fun k hk h hh m => ?_, fun hp => ?_⟩
  · have hdet : ((F₁.T p.1)⁻¹ * F₂.T p.1).det ≠ 0 := fun h0 => by
      have h := congrArg Matrix.det (hprod p.1)
      rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h
      exact zero_ne_one h
    have hdne := CovMap.LocImg.FrameChange.detFac_ne_zero hj p.2 (hbd p.1) hdet
    obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = (∏ k', (M.x ⟨k', F₂.c k'⟩ / M.x ⟨k', F₁.c k'⟩) ^ M.b p k') /
        detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1) := ⟨_, rfl⟩
    have hρ' : detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1) * ρ =
        ∏ k', (M.x ⟨k', F₂.c k'⟩ / M.x ⟨k', F₁.c k'⟩) ^ M.b p k' := by
      rw [hρ, mul_comm]; exact div_mul_cancel₀ _ hdne
    have hrel : ∀ (m : ι k) (I' : Finset (Fin N)), IsStepRows N j p.2 I' →
        ∑ I, F₁.u ⟨k, m⟩ I * minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I I' = ρ * F₂.u ⟨k, m⟩ I' := fun m I' hI' => by
      apply mul_left_cancel₀ hdne
      rw [← mul_assoc, hρ']
      exact frame_rel M hF₁ hF₂ c₁ p k hk m I' hI'
    have hstep : IsStepRows N j p.2 (stepCols N j p.2) := CovMap.LocImg.FV.isStepRows_stepCols p.2
    have hinv : ∑ m : ι k, F₂.u' (stepCols N j p.2) ⟨k, m⟩ * F₂.u ⟨k, m⟩ (stepCols N j p.2) = 1 := by
      rw [hF₂.2.2.1 p k hk _ _ hstep hstep, if_pos rfl]
    obtain ⟨hρR, hval⟩ := CovMap.LocImg.FV.reg_values hz p.2 (fun (m : ι k) I => F₁.u ⟨k, m⟩ I)
      (fun (m : ι k) I => F₂.u ⟨k, m⟩ I) (fun m : ι k => F₂.u' (stepCols N j p.2) ⟨k, m⟩) _ ρ _ hstep
      (fun m I => (hG₁.2.1 _ _).1) (fun m I => (hG₂.2.1 _ _).1) (fun m => (hG₂.2.1 _ _).2) (r₁₂ p.1) hrel hinv
    have hmove : ∑ I, valAt M.x (F₁.u ⟨k, m⟩ I) zb *
          minorIJ (valMat M.x zb ((F₁.T p.1)⁻¹ * F₂.T p.1) * h) I (stepCols N j p.2) =
        valAt M.x ρ zb * ∑ I, valAt M.x (F₂.u ⟨k, m⟩ I) zb * minorIJ h I (stepCols N j p.2) :=
      CovMap.LocImg.FV.sum_minor_mul hj p.2 (fun (m : ι k) I => valAt M.x (F₁.u ⟨k, m⟩ I) zb)
        (fun (m : ι k) I => valAt M.x (F₂.u ⟨k, m⟩ I) zb) _ _ hval h hh m
    have hv : detFac j p.2 (valMat M.x zb ((F₁.T p.1)⁻¹ * F₂.T p.1)) * valAt M.x ρ zb =
        ∏ k', (zb ⟨k', F₂.c k'⟩ / zb ⟨k', F₁.c k'⟩) ^ M.b p k' := by
      rw [← hdV, ← (reg_mul hz hdR hρR).2, hρ', hrV]
    rw [plk, plk, hmove, ← mul_assoc, hv]
  · have e := congrArg (fun s => valAt M.x s zb) (frame_none M hF₁ hF₂ c₁ p hp)
    rw [(reg_mul hz (hG₂.2.2 p hp).2.1 hrR).2, (reg_mul hz hdR (hG₁.2.2 p hp).2.1).2, hrV, hdV] at e
    exact e

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Scal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.EigenComponentAppendIndependentSpanStatement
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenComponent_append_independent_span : ∀ (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : 𝓞 E →+* Module.End ℂ V) (s₀ : 𝓞 E →+* ℂ) (I₀ : AddSubgroup V) (r k : ℕ) (v : Fin r → V) (q : Fin k → V), IsOFamily ρ I₀ v → (∀ (c : 𝓞 E), ∀ x ∈ I₀, ρ c x ∈ I₀) → (∀ c, q c ∈ eigSp ρ s₀) → LinearIndependent ℂ (Fin.append (fun a => eigComp ρ s₀ (v a)) q) → ∀ l : Fin k → ℂ, ∑ c, l c • q c ∈ Submodule.span ℂ (I₀ : Set V) → l = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.EigIndep.eq_zero_of_sum_mem_span | exact GlobalTheory.CompanionTheory.Ar.Cusp.EigIndep.eq_zero_of_sum_mem_span | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.EigIndep.eq_zero_of_sum_mem_span <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsAlgHomAdjoinInv
section
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

namespace GlobalTheory.CompanionTheory.Ar.Cmp.Kext

theorem exists_algHom_adjoin_inv :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (σ : Type) (τ : σ → Ω) (F : MvPolynomial σ ℚ)
      (S : Subalgebra ℚ Ω) (E : Type) [CommRing E] [Algebra ℚ E] (u : σ → E),
      aeval τ F ≠ 0 → S = Algebra.adjoin ℚ (insert (aeval τ F)⁻¹ (Set.range τ)) →
      (∀ G : MvPolynomial σ ℚ, aeval τ G = 0 → aeval u G = 0) → IsUnit (aeval u F) →
      ∃ φ : S →ₐ[ℚ] E, ∀ (G : MvPolynomial σ ℚ) (s : S), (s : Ω) = aeval τ G →
        φ s = aeval u G :=
  _root_.UpperTheory.Reformulated.B.Yde9.main

end GlobalTheory.CompanionTheory.Ar.Cmp.Kext
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsBasicOpenOfIsSncModel
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

theorem exists_basicOpen_of_isSncModel : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)), IsSncModel y e J → ∀ p : (k : K) → ι k, (∀ k, y ⟨k, p k⟩ ≠ 0) → ∀ t : (Σ k, ι k) → ℂ, (∀ G : MvPolynomial (Σ k, ι k) ℚ, aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) G = 0 → eval t (map (algebraMap ℚ ℂ) G) = 0) → ∃ (F : MvPolynomial (Σ k, ι k) ℚ) (S : Subalgebra ℚ Ω) (z : Fin e → S) (n : ℕ), aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) F ≠ 0 ∧ eval t (map (algebraMap ℚ ℂ) F) ≠ 0 ∧ S = Algebra.adjoin ℚ (insert (aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) F)⁻¹ (Set.range (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩))) ∧ Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ ∧ ∀ q : Ideal S, q.IsPrime → ((∀ g ∈ J, ∀ s : S, (s : Ω) = aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) g → s ∈ q) ↔ ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q) := by
  intro K _ ι _ Ω _ _ y e J h p hp t ht
  obtain ⟨m, f, a, hf, ha, hsum, hcl⟩ := h p hp
  rw [Algebra.adjoin_range_eq_range_aeval] at hf ha
  choose F hF using fun l => AlgHom.mem_range _ |>.1 (hf l)
  choose A hA using fun l => AlgHom.mem_range _ |>.1 (ha l)
  obtain rfl : f = fun l => aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) (F l) :=
    funext fun l => (hF l).symm
  have hker : aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) (∑ l, A l * F l - 1) = 0 := by
    simp only [map_sub, map_sum, map_mul, map_one, hA]
    exact sub_eq_zero.2 hsum
  have h1 := ht _ hker
  simp only [map_sub, map_sum, map_mul, map_one] at h1
  obtain ⟨l, hl⟩ : ∃ l, eval t (map (algebraMap ℚ ℂ) (F l)) ≠ 0 := by
    by_contra hc
    push_neg at hc
    simp [hc] at h1
  have hfl : aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) (F l) ≠ 0 := fun h0 => hl (ht _ h0)
  obtain ⟨-, z, n, -, -, hspan, hq⟩ := hcl l hfl _ rfl
  exact ⟨F l, _, z, n, hfl, hl, rfl, hspan, hq⟩

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsConjInvariantMollifier
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_conj_invariant_mollifier : ∀ n : ℕ, ∃ ρ : ReciprocityTheory.AnForm.A.Mollifier n, ∀ v, ρ.toFun (star v) = ρ.toFun v := by
  intro n
  obtain ⟨ρ⟩ := ReciprocityTheory.AnForm.A.mollifierInhabit_thm n
  have hmp : MeasureTheory.MeasurePreserving (fun v : Fin n → ℂ => star v) :=
    MeasureTheory.volume_preserving_pi (fun _ => Complex.conjLIE.measurePreserving)
  have hme : MeasurableEmbedding (fun v : Fin n → ℂ => star v) :=
    (starLinearEquiv ℝ (A := Fin n → ℂ)).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  have hsm : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun v : Fin n → ℂ => star v) :=
    contDiff_pi.2 fun i => Complex.conjCLE.contDiff.comp (contDiff_apply ℝ ℂ i)
  have hI : MeasureTheory.Integrable ρ.toFun :=
    MeasureTheory.Integrable.of_integral_ne_zero (by rw [ρ.integral_eq_one]; norm_num)
  have hcomp : ∫ w : Fin n → ℂ, ρ.toFun (star w) = 1 := by
    rw [hmp.integral_comp hme ρ.toFun, ρ.integral_eq_one]
  have hI2 : MeasureTheory.Integrable (fun w : Fin n → ℂ => ρ.toFun (star w)) :=
    MeasureTheory.Integrable.of_integral_ne_zero (by rw [hcomp]; norm_num)
  refine ⟨⟨fun v => (ρ.toFun v + ρ.toFun (star v)) / 2, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (ρ.contDiff.add (ρ.contDiff.comp hsm)).div_const 2
  · intro w
    exact div_nonneg (add_nonneg (ρ.nonneg _) (ρ.nonneg _)) two_pos.le
  · intro w hw
    by_contra h
    have h1 : ρ.toFun w = 0 := by
      by_contra h'
      exact h (ρ.support_subset h')
    have h2 : ρ.toFun (star w) = 0 := by
      by_contra h'
      have hb := ρ.support_subset h'
      rw [Metric.mem_ball, dist_zero_right, norm_star] at hb
      exact h (by rw [Metric.mem_ball, dist_zero_right]; exact hb)
    exact hw (by simp [h1, h2])
  · show ∫ w : Fin n → ℂ, (ρ.toFun w + ρ.toFun (star w)) / 2 = 1
    rw [MeasureTheory.integral_div, MeasureTheory.integral_add hI hI2, ρ.integral_eq_one, hcomp]
    norm_num
  · intro c w hc
    show (ρ.toFun (c • w) + ρ.toFun (star (c • w))) / 2 = (ρ.toFun w + ρ.toFun (star w)) / 2
    rw [star_smul, ρ.circle_inv c w hc, ρ.circle_inv (star c) (star w) (by rw [norm_star]; exact hc)]
  · intro v
    show (ρ.toFun (star v) + ρ.toFun (star (star v))) / 2 = (ρ.toFun v + ρ.toFun (star v)) / 2
    rw [star_star, add_comm]
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsCuspDataForTorusInvariantStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cusp_data_for_torus_invariant : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) [Nonempty Ψ] (U : ((Σ k, J k) → ℂ) → ℝ), (∀ z, 0 ≤ U z) → (∀ z ∈ D.Xo, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → U (torusSmul c z) = U z) → ∃ Cd : CuspData D ℤ (Fin 2 → ℤ), Cd.cuspWeight = U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Fake.every_weight_is_cusp_weight | exact GlobalTheory.CompanionTheory.Ar.Cusp.Fake.every_weight_is_cusp_weight | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Fake.every_weight_is_cusp_weight <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsMeasurableDominatingFunctionStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspWeight_factors_through_measurable_log_bounded : ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting D O Lt), ∃ (G : X.M.Xc → ℝ) (C : ℝ), @Measurable X.M.Xc ℝ (borel X.M.Xc) _ (X.S.R.Yo.indicator G) ∧ (∀ x ∈ X.S.R.Yo, |G x| ≤ C + C * Real.log (X.S.R.r x)) ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), X.M.proj z ∈ X.S.R.Yo → X.Cd.cuspWeight z = G (X.M.proj z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.cuspWeight_descends | exact GlobalTheory.CompanionTheory.Ar.Giv.cuspWeight_descends | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.cuspWeight_descends <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsMulPowEqAevalOfMemAdjoinInv
section
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem exists_mul_pow_eq_aeval_of_mem_adjoin_inv :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (σ : Type) (τ : σ → Ω) (F : MvPolynomial σ ℚ)
      (S : Subalgebra ℚ Ω), aeval τ F ≠ 0 →
      S = Algebra.adjoin ℚ (insert (aeval τ F)⁻¹ (Set.range τ)) →
      ∀ s : S, ∃ (N : ℕ) (G : MvPolynomial σ ℚ), (s : Ω) * aeval τ F ^ N = aeval τ G := by
  intro Ω _ _ σ τ F S hf hS s
  obtain ⟨x, hx⟩ := s
  subst hS
  change ∃ (N : ℕ) (G : MvPolynomial σ ℚ), x * aeval τ F ^ N = aeval τ G
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rcases hy with rfl | ⟨q, rfl⟩
    · exact ⟨1, 1, by simp [hf]⟩
    · exact ⟨0, X q, by simp⟩
  | algebraMap r =>
    exact ⟨0, C r, by simp [MvPolynomial.algebraMap_eq]⟩
  | add a b _ _ iha ihb =>
    obtain ⟨N, G, h⟩ := iha
    obtain ⟨M, H, h'⟩ := ihb
    refine ⟨N + M, G * F ^ M + H * F ^ N, ?_⟩
    simp only [map_add, map_mul, map_pow, ← h, ← h']
    ring
  | mul a b _ _ iha ihb =>
    obtain ⟨N, G, h⟩ := iha
    obtain ⟨M, H, h'⟩ := ihb
    refine ⟨N + M, G * H, ?_⟩
    simp only [map_mul, ← h, ← h']
    ring

end GlobalTheory.CompanionTheory.Ar.Cmp
end

