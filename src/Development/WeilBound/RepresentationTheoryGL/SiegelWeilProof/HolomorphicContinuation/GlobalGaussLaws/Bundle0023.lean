import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0022
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0018
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerivStep
section
noncomputable section

open Topology Metric

namespace PositivityTheory.Rg.Sw.Glob

namespace DilDH

variable {E : Type} [MetricSpace E] [ProperSpace E]

theorem deriv_step {U : Set ℂ} (hU : IsOpen U) {g : ℂ → E → ℂ}
    (hc : ContinuousOn (fun p : ℂ × E => g p.1 p.2) (U ×ˢ Set.univ))
    (hd : ∀ u, DifferentiableOn ℂ (fun z => g z u) U) :
    ContinuousOn (fun p : ℂ × E => deriv (fun z => g z p.2) p.1) (U ×ˢ Set.univ) := by
  intro p hp
  obtain ⟨z0, u0⟩ := p
  have hz0 : z0 ∈ U := hp.1
  have hopen : IsOpen (U ×ˢ (Set.univ : Set E)) := hU.prod isOpen_univ
  apply ContinuousAt.continuousWithinAt
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.1 hU z0 hz0
  set r := R / 4 with hr
  have hr0 : 0 < r := by positivity
  have hK : closedBall z0 (2 * r) ⊆ U := (closedBall_subset_ball (by linarith)).trans hRU
  rw [Metric.continuousAt_iff']
  intro ε hε
  have hunif : ∀ᶠ u in 𝓝 u0, ∀ w ∈ closedBall z0 (2 * r), dist (g w u) (g w u0) < ε * r / 2 := by
    apply (isCompact_closedBall z0 (2 * r)).eventually_forall_of_forall_eventually
    intro w hw
    have hwU : w ∈ U := hK hw
    have hcont : ContinuousAt (fun p : ℂ × E => g p.1 p.2) (w, u0) :=
      hc.continuousAt (hopen.mem_nhds ⟨hwU, trivial⟩)
    have h1 : Filter.Tendsto (fun q : E × ℂ => g q.2 q.1) (𝓝 (u0, w)) (𝓝 (g w u0)) :=
      hcont.tendsto.comp (continuous_swap.tendsto (u0, w))
    have h2 : Filter.Tendsto (fun q : E × ℂ => g q.2 u0) (𝓝 (u0, w)) (𝓝 (g w u0)) :=
      hcont.tendsto.comp ((continuous_snd.prodMk continuous_const).tendsto (u0, w))
    have hε' : 0 < ε * r / 4 := by positivity
    filter_upwards [Metric.tendsto_nhds.1 h1 _ hε', Metric.tendsto_nhds.1 h2 _ hε'] with q hq1 hq2
    calc dist (g q.2 q.1) (g q.2 u0)
        ≤ dist (g q.2 q.1) (g w u0) + dist (g q.2 u0) (g w u0) := dist_triangle_right _ _ _
      _ < ε * r / 4 + ε * r / 4 := add_lt_add hq1 hq2
      _ = ε * r / 2 := by ring
  have hd0 : ContinuousAt (deriv fun z => g z u0) z0 :=
    ((hd u0).deriv hU).continuousOn.continuousAt (hU.mem_nhds hz0)
  have e1 := (continuous_fst.tendsto (z0, u0)).eventually
    (Metric.tendsto_nhds.1 hd0 (ε / 2) (by positivity))
  have e2 := (continuous_fst.tendsto (z0, u0)).eventually (Metric.ball_mem_nhds z0 hr0)
  have e3 := (continuous_snd.tendsto (z0, u0)).eventually hunif
  filter_upwards [e1, e2, e3] with q hq1 hq2 hq3
  obtain ⟨z, u⟩ := q
  simp only at hq1 hq2 hq3 ⊢
  have hzU : closedBall z r ⊆ closedBall z0 (2 * r) := by
    intro w hw
    rw [mem_closedBall] at hw ⊢
    calc dist w z0 ≤ dist w z + dist z z0 := dist_triangle _ _ _
      _ ≤ r + r := add_le_add hw hq2.le
      _ = 2 * r := by ring
  have hcu : deriv (fun z => g z u) z = Complex.cderiv r (fun z => g z u) z :=
    (Complex.cderiv_eq_deriv hU (hd u) hr0 (hzU.trans hK)).symm
  have hcu0 : deriv (fun z => g z u0) z = Complex.cderiv r (fun z => g z u0) z :=
    (Complex.cderiv_eq_deriv hU (hd u0) hr0 (hzU.trans hK)).symm
  have hsph : sphere z r ⊆ U := sphere_subset_closedBall.trans (hzU.trans hK)
  have hdiff : dist (Complex.cderiv r (fun z => g z u) z) (Complex.cderiv r (fun z => g z u0) z)
      < ε * r / 2 / r := by
    rw [dist_eq_norm]
    apply Complex.norm_cderiv_sub_lt hr0
    · intro w hw
      rw [← dist_eq_norm]
      exact hq3 w (hzU (sphere_subset_closedBall hw))
    · exact (hd u).continuousOn.mono hsph
    · exact (hd u0).continuousOn.mono hsph
  have hhalf : ε * r / 2 / r = ε / 2 := by field_simp
  rw [hhalf] at hdiff
  have hfirst : dist (deriv (fun z => g z u) z) (deriv (fun z => g z u0) z) < ε / 2 := by
    rw [hcu, hcu0]
    exact hdiff
  calc dist (deriv (fun z => g z u) z) (deriv (fun z => g z u0) z0)
      ≤ dist (deriv (fun z => g z u) z) (deriv (fun z => g z u0) z)
        + dist (deriv (fun z => g z u0) z) (deriv (fun z => g z u0) z0) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hfirst hq1
    _ = ε := by ring

def scaleL (m n : ℕ) (s : ℝ) (X : Fin n → ℝ) : (Fin m → Fin n → ℂ) ≃ₗ[ℝ] (Fin m → Fin n → ℂ) where
  toFun u := fun i j => u i j * (Real.exp (s * X j) : ℂ)
  invFun u := fun i j => u i j * (Real.exp (-(s * X j)) : ℂ)
  map_add' u v := by funext i j; simp [add_mul]
  map_smul' r u := by funext i j; simp [Complex.real_smul, mul_assoc]
  left_inv u := by
    funext i j
    simp only [mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one,
      mul_one]
  right_inv u := by
    funext i j
    simp only [mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one,
      mul_one]

end DilDH

theorem schScale : SchScale := by
  intro m n f s X a hf
  obtain ⟨S, hS⟩ := hf
  refine ⟨a • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (DilDH.scaleL m n s X).toContinuousLinearEquiv S, ?_⟩
  funext u
  simp only [SchwartzMap.smul_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, smul_eq_mul, ← hS]
  rfl

theorem contDeriv : ContDeriv := by
  intro m n U hU f hc hd r
  induction r generalizing f with
  | zero => simpa only [iteratedDeriv_zero] using hc
  | succ k ih =>
    have h1 := DilDH.deriv_step hU hc hd
    have h2 : ∀ u, DifferentiableOn ℂ (fun z => deriv (fun z => f z u) z) U :=
      fun u => (hd u).deriv hU
    have h3 := ih (fun z u => deriv (fun z => f z u) z) h1 h2
    simpa only [iteratedDeriv_succ'] using h3

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GIwasawa
section
namespace PositivityTheory.Rg.Sw.Glob

theorem gIwasawa : GIwasawa := GlobalTheory.StdUnn.Iwasawa.exists_mul

end PositivityTheory.Rg.Sw.Glob
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussM
section
noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob

open GaussH

private theorem fromBlocks_unitary_and_conj_JJ_eq {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) (h1 : Xᴴ * X + Yᴴ * Y = 1)
    (h2 : Xᴴ * Y = Yᴴ * X) :
    (fromBlocks X (-Y) Y X)ᴴ * fromBlocks X (-Y) Y X = 1 ∧
      (fromBlocks X (-Y) Y X)ᴴ * JJ n * fromBlocks X (-Y) Y X = JJ n := by
  constructor
  · rw [fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one]
    simp [h2]
    rw [h1, add_comm, h1, fromBlocks_one]
  · rw [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    simp [h2]
    exact ⟨by rw [add_comm, h1], by rw [← neg_add, h1]⟩

private theorem exists_normalizing_factor_of_left_inverse {n : ℕ} (X Y A B : Matrix (Fin n) (Fin n) ℂ) (h : A * X + B * Y = 1) :
    ∃ R : Matrix (Fin n) (Fin n) ℂ, (X * R)ᴴ * (X * R) + (Y * R)ᴴ * (Y * R) = 1 := by
  classical
  set M := Xᴴ * X + Yᴴ * Y with hM
  have hpsd : M.PosSemidef :=
    (posSemidef_conjTranspose_mul_self X).add (posSemidef_conjTranspose_mul_self Y)
  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have hq : star v ⬝ᵥ M *ᵥ v = 0 := by rw [hMv, dotProduct_zero]
    simp_rw [hM, add_mulVec, dotProduct_add, ← mulVec_mulVec, dotProduct_mulVec _ _ (X *ᵥ v),
      dotProduct_mulVec _ _ (Y *ᵥ v), vecMul_conjTranspose, star_star] at hq
    have h2 := (add_eq_zero_iff_of_nonneg (dotProduct_star_self_nonneg _)
      (dotProduct_star_self_nonneg _)).mp hq
    have hx := dotProduct_star_self_eq_zero.mp h2.1
    have hy := dotProduct_star_self_eq_zero.mp h2.2
    apply hv
    rw [← one_mulVec v, ← h, add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hx, hy, mulVec_zero,
      mulVec_zero, add_zero]
  open scoped MatrixOrder in
  obtain ⟨S, hSS, hSa⟩ : ∃ S : Matrix (Fin n) (Fin n) ℂ, S * S = M ∧ Sᴴ = S :=
    ⟨CFC.sqrt M, CFC.sqrt_mul_sqrt_self M hpsd.nonneg, (CFC.sqrt_nonneg M).isSelfAdjoint⟩
  have hS : IsUnit S.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    apply hdet
    rw [← hSS, det_mul, h0, zero_mul]
  refine ⟨S⁻¹, ?_⟩
  simp only [conjTranspose_mul, conjTranspose_nonsing_inv, hSa]
  calc S⁻¹ * Xᴴ * (X * S⁻¹) + S⁻¹ * Yᴴ * (Y * S⁻¹) = S⁻¹ * (S * S) * S⁻¹ := by
        rw [hSS, hM]; noncomm_ring
    _ = 1 := by rw [← mul_assoc, nonsing_inv_mul _ hS, one_mul, mul_nonsing_inv _ hS]

private theorem exists_mul_lower_zero_and_inK_of_normalized (n : ℕ) (y : GR n) (X Y C D R : Matrix (Fin n) (Fin n) ℂ)
    (hb : C * X + D * Y = 0) (hR : (X * R)ᴴ * (X * R) + (Y * R)ᴴ * (Y * R) = 1)
    (hiso' : (X * R)ᴴ * (Y * R) = (Y * R)ᴴ * (X * R)) (hC : toBlocks₂₁ (mR y) = C)
    (hD : toBlocks₂₂ (mR y) = D) :
    ∃ (p : ↥(GR n)) (k : ↥(GR n)), y = p * k ∧ toBlocks₂₁ (mR p) = 0 ∧ InK (mR k) := by
  obtain ⟨hU, hS⟩ := fromBlocks_unitary_and_conj_JJ_eq (X * R) (Y * R) hR hiso'
  generalize hkv : fromBlocks (X * R) (-(Y * R)) (Y * R) (X * R) = kv at hU hS
  have hU' : kv * kvᴴ = 1 := mul_eq_one_comm.mp hU
  have hu : (⟨kv, kvᴴ, hU', hU⟩ : GL (Fin n ⊕ Fin n) ℂ) ∈ GR n := hS
  refine ⟨y * ⟨_, hu⟩, (⟨_, hu⟩ : GR n)⁻¹, (mul_inv_cancel_right y _).symm, ?_, ?_⟩
  · have hm : mR (y * ⟨_, hu⟩) = mR y * kv := rfl
    rw [hm, ← hkv, ← fromBlocks_toBlocks (mR y), fromBlocks_multiply, toBlocks_fromBlocks₂₁, hC, hD,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.add_mul, hb, Matrix.zero_mul]
  · refine ⟨(⟨_, hu⟩ : GR n)⁻¹.2, ?_⟩
    have hm : mR (⟨_, hu⟩ : GR n)⁻¹ = kvᴴ := rfl
    rw [hm, conjTranspose_conjTranspose]
    exact hU'

theorem iwaGR : IwaGR := by
  intro n y
  classical
  have hprod : mR y * mR y⁻¹ = 1 := by simp [mR]
  have hG : InG (mR y⁻¹) := (y⁻¹).2
  have hiso : (toBlocks₁₁ (mR y⁻¹))ᴴ * toBlocks₂₁ (mR y⁻¹) =
      (toBlocks₂₁ (mR y⁻¹))ᴴ * toBlocks₁₁ (mR y⁻¹) := by
    have h := congrArg toBlocks₁₁ hG
    rw [← fromBlocks_toBlocks (mR y⁻¹), JJ, fromBlocks_conjTranspose, fromBlocks_multiply,
      fromBlocks_multiply] at h
    simp at h
    exact (neg_add_eq_zero.mp h).symm
  have hb := hprod
  rw [← fromBlocks_toBlocks (mR y), ← fromBlocks_toBlocks (mR y⁻¹), fromBlocks_multiply,
    ← fromBlocks_one, fromBlocks_inj] at hb
  obtain ⟨R, hR⟩ := exists_normalizing_factor_of_left_inverse _ _ _ _ hb.1
  have hiso' : (toBlocks₁₁ (mR y⁻¹) * R)ᴴ * (toBlocks₂₁ (mR y⁻¹) * R) =
      (toBlocks₂₁ (mR y⁻¹) * R)ᴴ * (toBlocks₁₁ (mR y⁻¹) * R) := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc _ _ R, hiso, Matrix.mul_assoc]
  exact exists_mul_lower_zero_and_inK_of_normalized n y _ _ _ _ R hb.2.2.1 hR hiso' rfl rfl

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.IsSiegelI
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DilEH

attribute [local irreducible] famC

variable {D : D7} {n : ℕ} {θ : InfFam D} {V : HSp D} {τ : D.what₂.Tau} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
  {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {ι : GR n →* G D n}
  {L : GR n → ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ)}

theorem isSiegel_I : IsSiegel (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  unfold IsSiegel
  have e : (-(Complex.I / 2)) • (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ) - (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ) = 1 := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def, Complex.conj_I, ← sub_smul, smul_smul]
    have : -(Complex.I / 2) * (Complex.I - -Complex.I) = 1 := by ring_nf; rw [Complex.I_sq]; ring
    rw [this, one_smul]
  rw [e]; exact Matrix.PosDef.one

set_option maxHeartbeats 800000 in
theorem exch (hDR : DReal) (hDB : DBound) (hDC : DCalc) (hDL : DifferenceQuotientIsometryExchange) (hCD : ContDeriv) (hSS : SchScale) (hSF : SchFP)
    (hL : IsLocFact ω τ fr ι L) (hθ : IsInfFam θ) (hfr : IsUnit fr.det) {Ψ : Mx D V.rank n → ℂ}
    (hΨ : AwayCls θ τ fr Ψ) {x₀ : Mx D V.rank n} (hx₀ : Ψ x₀ ≠ 0) {ε : Fin V.rank → Bool} {t c : ℝ} (hc : 0 < c)
    (htc : |t| = c) {e : ℤ}
    (hG : ∀ (y : GR n) (Z : Matrix (Fin n) (Fin n) ℂ), IsSiegel Z →
      L y (gZf ε t c Z) = fun u => jF e (cnt (epsT t ε) true) (cnt (epsT t ε) false) y Z * gZf ε t c (actZ y Z) u)
    {X : Fin n → ℝ} {a : ℝ → GR n} (ha : ∀ s, IsDil X s (a s)) (y'' : GR n) {κ : ℝ} (hκ : 0 < κ)
    (hL2 : ∀ f, IsSch f → ∫ u, ‖L y'' f u‖ ^ 2 = κ * ∫ u, ‖f u‖ ^ 2) (r : ℕ) :
    L y'' (fP c ((dil c X ^ r) 1)) = fun u => iteratedDeriv r (fun s : ℝ => famC ε t c e y'' X s u) 0 := by
  have hg0 : gZf ε t c (Complex.I • 1) = fP c (1 : PX V.rank n) := (DilAH.fP_one ε t c hc).symm
  have hg0s : IsSch (gZf ε t c (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)) : (Fin V.rank → Fin n → ℂ) → ℂ) := by
    rw [hg0]; exact hSF _ _ c hc 1
  have hbase : ∀ (y : GR n) (s : ℝ), L (y * a s) (gZf ε t c (Complex.I • 1)) = famC ε t c e y X s := by
    intro y s
    rw [hG _ _ isSiegel_I, hDR _ _ ε t c e y X a ha s]
  set Gf : ℕ → ℝ → (Fin V.rank → Fin n → ℂ) → ℂ := fun r s u => iteratedDeriv r (fun s' : ℝ => famC ε t c e 1 X s' u) s
    with hGf
  set Ef : ℕ → ℝ → (Fin V.rank → Fin n → ℂ) → ℂ :=
    fun r s u => iteratedDeriv r (fun s' : ℝ => famC ε t c e y'' X s' u) s with hEf
  obtain ⟨hC1, hC2⟩ := hDC V.rank n ε t c e X hc htc
  obtain ⟨hB1, hB2, -⟩ := hDB V.rank n ε t c e X hc htc
  have hGs : ∀ r s, IsSch (Gf r s) := by
    intro r s
    have : Gf r s = fun u => (Real.exp (s * (V.rank : ℝ) * ∑ j, X j) : ℂ) *
        fP c ((dil c X ^ r) 1) (fun a j => u a j * Real.exp (s * X j)) := by
      funext u; exact hC1 s r u
    rw [this]
    exact hSS _ _ _ s X _ (hSF _ _ c hc _)
  have hstrip : IsOpen (stripS X) := DBoundBH.isOpen_stripS X
  have hR : ∀ s : ℝ, (s : ℂ) ∈ stripS X := fun s j => by simp [div_pos Real.pi_pos]

  set F : ℂ → (Fin V.rank → Fin n → ℂ) → ℂ := fun z u => famC ε t c e y'' X z u with hF
  have hFd : ∀ u, DifferentiableOn ℂ (fun z => F z u) (stripS X) := fun u => hB1 y'' u
  have hFc : ContinuousOn (fun p : ℂ × (Fin V.rank → Fin n → ℂ) => F p.1 p.2) (stripS X ×ˢ Set.univ) := by
    have hcont : Continuous (fun p : ℂ × (Fin V.rank → Fin n → ℂ) => ((y'', p) : GR n × (ℂ × (Fin V.rank → Fin n → ℂ)))) :=
      continuous_const.prodMk continuous_id
    exact hB2.comp hcont.continuousOn fun p hp => ⟨Set.mem_univ _, hp⟩
  have hEr : ∀ r u, (fun s : ℝ => iteratedDeriv r (fun s' : ℝ => F s' u) s) = fun s : ℝ => iteratedDeriv r (fun z => F z u) s :=
    fun r u => DilCH.iteratedDeriv_ofReal hstrip (hFd u) hR r
  have key : ∀ r s, L y'' (Gf r s) = Ef r s := by
    intro r
    induction r with
    | zero =>
      intro s
      have e1 : Gf 0 s = L (a s) (gZf ε t c (Complex.I • 1)) := by
        funext u; rw [← one_mul (a s), hbase]; simp [hGf]
      have e2 : Ef 0 s = famC ε t c e y'' X s := by funext u; simp [hEf]
      rw [e1, e2, ← DilCH.L_mul hL hθ hfr hΨ hx₀ y'' (a s) hg0s, hbase]
    | succ r ih =>
      intro s
      refine hDL V.rank n (L y'') κ hκ (fun f hf => hL.1 y'' f hf)
        (fun f g hf hg => DilCH.L_sub hL hθ hfr hΨ hx₀ y'' hf hg)
        (fun a' f hf => DilCH.L_smul hL hθ hfr hΨ hx₀ y'' a' hf) hL2 (Gf r) (Gf (r + 1) s) (Ef (r + 1) s) s
        (hGs r) (hGs (r + 1) s) ?_ (hC2 r s) ?_
      ·
        have hcd := hCD V.rank n (stripS X) hstrip F hFc hFd (r + 1)
        have : Ef (r + 1) s = fun u => iteratedDeriv (r + 1) (fun z => F z u) (s : ℂ) := by
          funext u; simp only [hEf]; rw [show (fun s' : ℝ => famC ε t c e y'' X s' u) = fun s' : ℝ => F s' u from rfl,
            congrFun (hEr (r + 1) u) s]
        rw [this]
        exact hcd.comp_continuous (f := fun u : Fin V.rank → Fin n → ℂ => ((s : ℂ), u))
          (continuous_const.prodMk continuous_id) fun u => ⟨hR s, Set.mem_univ _⟩
      · intro u
        simp only [ih]
        have hd : HasDerivAt (fun s' : ℝ => Ef r s' u) (Ef (r + 1) s u) s := by
          have e3 : (fun s' : ℝ => Ef r s' u) = fun s' : ℝ => iteratedDeriv r (fun z => F z u) s' := hEr r u
          have e4 : Ef (r + 1) s u = iteratedDeriv (r + 1) (fun z => F z u) s := congrFun (hEr (r + 1) u) s
          rw [e3, e4, iteratedDeriv_succ]
          exact ((DilCH.diffOn_iteratedDeriv hstrip (hFd u) r).differentiableAt
            (hstrip.mem_nhds (hR s))).hasDerivAt.comp_ofReal
        have := hd.tendsto_slope_zero
        refine this.congr fun h => ?_
        simp only [div_eq_inv_mul, Complex.real_smul, Complex.ofReal_inv]
  have e0 : Gf r 0 = fP c ((dil c X ^ r) 1) := by
    funext u; rw [show Gf r 0 u = _ from hC1 0 r u]; simp
  rw [← e0, key r 0]

end PositivityTheory.Rg.Sw.Glob.DilEH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRedField
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def genSet (D : D7) (n : ℕ) : Set (G D n) :=
  {g | (∃ b, mat g = blk4 1 b 0 1) ∨ (∃ a d, mat g = blk4 a 0 0 d) ∨ (∃ c, mat g = blk4 1 0 c 1)}

def blkDm {R : Type} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂

def eI {R : Type} [CommRing R] (I : Finset (Fin n)) : Matrix (Fin n) (Fin n) R :=
  Matrix.diagonal fun i => if i ∈ I then 1 else 0

def wIm {R : Type} [CommRing R] (I : Finset (Fin n)) : Matrix (Fin (n + n)) (Fin (n + n)) R :=
  blk4 (1 - eI I) (eI I) (-eI I) (1 - eI I)

def J2 (R : Type) [CommRing R] (n : ℕ) : Matrix (Fin (n + n)) (Fin (n + n)) R := blk4 0 1 (-1) 0

def UnitD : Prop :=
  ∀ (D : D7) (n : ℕ) (g : G D n), IsUnit (blkDm (mat g)).det → g ∈ Subgroup.closure (genSet D n)

def PIn : Prop := ∀ (D : D7) (n : ℕ), ∀ p ∈ P D n, p ∈ Subgroup.closure (genSet D n)

def KIn : Prop := ∀ (D : D7) (n : ℕ), ∀ k ∈ K D n, k ∈ Subgroup.closure (genSet D n)

def LocRedField : Prop :=
  ∀ (k : Type) [Field k] (σ : k →+* k), (∀ a, σ (σ a) = a) → ∀ (n : ℕ) (g : GL (Fin (n + n)) k),
    g ∈ Formalism.UG.UJ σ (J2 k n) → ∃ I : Finset (Fin n), IsUnit (blkDm ((g : Matrix (Fin (n + n)) (Fin (n + n)) k) * wIm I)).det

def LocRedSplit : Prop :=
  ∀ (k : Type) [Field k] (n : ℕ) (g : GL (Fin (n + n)) k), ∃ (a d : GL (Fin n) k) (I : Finset (Fin n)),
    IsUnit (blkDm ((g : Matrix (Fin (n + n)) (Fin (n + n)) k) * blk4 a.1 0 0 d.1 * wIm I)).det

def KInInf : Prop :=
  ∀ (D : D7) (n : ℕ), ∀ k ∈ K D n, (mat k).map (finPart D) = 1 → k ∈ Subgroup.closure (genSet D n)

def KInFin : Prop :=
  ∀ (D : D7) (n : ℕ), ∀ k ∈ K D n, (∀ τ, (mat k).map (Formalism.IndefR.Eqv.psiT D τ) = 1) → k ∈ Subgroup.closure (genSet D n)

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.VacKOf
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open PositivityTheory.Rg.Sw.Glob.VacS PositivityTheory.Rg.Sw.Glob.VacB PositivityTheory.Rg.Sw.Glob.VacC PositivityTheory.Rg.Sw.Glob.VacE PositivityTheory.Rg.Sw.Glob.VacF
  PositivityTheory.Rg.Sw.Glob.VacG PositivityTheory.Rg.Sw.Glob.VacH PositivityTheory.Rg.Sw.Glob.VacI PositivityTheory.Rg.Sw.Glob.VacJ PositivityTheory.Rg.Sw.Glob.VacK

private theorem cnt_true_add_cnt_false {m : ℕ} (ε : Fin m → Bool) : cnt ε true + cnt ε false = m := by
  unfold cnt
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  have h : ∀ a : Fin m, ((if ε a = true then 1 else 0) + (if ε a = false then 1 else 0) : ℕ) = 1 := by
    intro a
    cases ε a <;> simp
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

theorem vacK_of : GZSch → LawN → LawNbar → LocMul → LNe → VacK := by
  intro hGZ hN hNb hLM hLNe
  unfold PositivityTheory.Rg.Sw.Glob.VacK
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL e hlev k hk
  have hl0 : l τ ≠ 0 := hLNe D ψ θ l hC.hψ hC.hθ hC.hl τ
  have hc0 : 0 < cLoc l τ := VacF.cpos hl0
  have hSch : ∀ K : ℂ, IsSch (DG (m := V.rank) (n := n) K (fun _ _ => ((cLoc l τ : ℝ) : ℂ))) :=
    fun K => VacE.isSch_DG hGZ ε (tLoc l τ) (cLoc l τ) hc0 VacF.tabs K
  obtain ⟨u, u', φ, hu, hu', hφ, hkm⟩ := VacG.kak (mR k) hk
  have hdu : IsUnit u.det := Matrix.isUnit_det_of_left_inverse hu
  have hdu' : IsUnit u'.det := Matrix.isUnit_det_of_left_inverse hu'
  have hk_eq : k = VacB.mkG (mM u) (VacB.inG_mM u hdu) * VacB.mkG (VacB.kth φ) (VacB.inK_kth φ).1 *
      VacB.mkG (mM u') (VacB.inG_mM u' hdu') := by
    apply Subtype.ext
    apply Units.ext
    change mR k = mR (VacB.mkG (mM u) (VacB.inG_mM u hdu)) * mR (VacB.mkG (VacB.kth φ) (VacB.inK_kth φ).1) *
      mR (VacB.mkG (mM u') (VacB.inG_mM u' hdu'))
    rw [VacB.mR_mkG, VacB.mR_mkG, VacB.mR_mkG]
    exact hkm
  have hLM' := hLM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hC L hL
  have h1 : L (VacB.mkG (mM u') (VacB.inG_mM u' hdu')) (DG 1 (fun _ _ => ((cLoc l τ : ℝ) : ℂ))) =
      DG (1 * (u'.det ^ e * (star u'.det) ^ ((V.rank : ℤ) - e))) (fun _ _ => ((cLoc l τ : ℝ) : ℂ)) := by
    rw [hlev _ u' hdu' (VacB.mR_mkG _ _) _ (hSch 1)]
    exact VacH.levF_unitary e u' hu' 1 _
  have h2 := VacJ.rot_gen hC hl0 hN hNb hLM hGZ L hL e hlev φ hφ
    (1 * (u'.det ^ e * (star u'.det) ^ ((V.rank : ℤ) - e)))
  have h3 : ∀ K : ℂ, L (VacB.mkG (mM u) (VacB.inG_mM u hdu)) (DG K (fun _ _ => ((cLoc l τ : ℝ) : ℂ))) =
      DG (K * (u.det ^ e * (star u.det) ^ ((V.rank : ℤ) - e))) (fun _ _ => ((cLoc l τ : ℝ) : ℂ)) := by
    intro K
    rw [hlev _ u hdu (VacB.mR_mkG _ _) _ (hSch K)]
    exact VacH.levF_unitary e u hu K _
  have hLk : L k (DG 1 (fun _ _ => ((cLoc l τ : ℝ) : ℂ))) =
      DG (1 * (u'.det ^ e * (star u'.det) ^ ((V.rank : ℤ) - e)) *
        (∏ a, ∏ j, ((Real.cos (φ j) : ℂ) + Complex.I * (VacE.rhoT (tLoc l τ) ε a : ℂ) * (Real.sin (φ j) : ℂ))) *
        (u.det ^ e * (star u.det) ^ ((V.rank : ℤ) - e))) (fun _ _ => ((cLoc l τ : ℝ) : ℂ)) := by
    rw [hk_eq, hLM' (VacB.mkG (mM u) (VacB.inG_mM u hdu) * VacB.mkG (VacB.kth φ) (VacB.inK_kth φ).1)
      (VacB.mkG (mM u') (VacB.inG_mM u' hdu')) _ (hSch 1), h1,
      hLM' (VacB.mkG (mM u) (VacB.inG_mM u hdu)) (VacB.mkG (VacB.kth φ) (VacB.inK_kth φ).1) _ (hSch _), h2, h3]
  have hsu : star u.det = u.det⁻¹ := by
    have h := congrArg Matrix.det hu
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
    exact eq_inv_of_mul_eq_one_left h
  have hsu' : star u'.det = u'.det⁻¹ := by
    have h := congrArg Matrix.det hu'
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
    exact eq_inv_of_mul_eq_one_left h
  have hm : (V.rank : ℤ) = ((cnt (epsT (tLoc l τ) ε) true + cnt (epsT (tLoc l τ) ε) false : ℕ) : ℤ) := by
    rw [cnt_true_add_cnt_false]
  have hX : (∏ j, Complex.exp (Complex.I * (φ j : ℂ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => Complex.exp_ne_zero _
  have hXinv : ∏ j, Complex.exp (-(Complex.I * (φ j : ℂ))) = (∏ j, Complex.exp (Complex.I * (φ j : ℂ)))⁻¹ := by
    simp only [Complex.exp_neg, Finset.prod_inv_distrib]
  have hK : 1 * (u'.det ^ e * (star u'.det) ^ ((V.rank : ℤ) - e)) *
      (∏ a, ∏ j, ((Real.cos (φ j) : ℂ) + Complex.I * (VacE.rhoT (tLoc l τ) ε a : ℂ) * (Real.sin (φ j) : ℂ))) *
      (u.det ^ e * (star u.det) ^ ((V.rank : ℤ) - e)) =
      jF e (cnt (epsT (tLoc l τ) ε) true) (cnt (epsT (tLoc l τ) ε) false) k (Complex.I • 1) := by
    rw [VacI.jF_kak e _ _ k u u' φ hu hu' hφ hkm, VacK.prodF, hsu, hsu', hm, hXinv]
    exact VacK.alg _ _ _ hdu.ne_zero hdu'.ne_zero hX e _ _
  rw [VacC.vac_eq, hLk]
  funext v
  rw [VacC.dg_const, VacC.dg_const, hK]
  ring

end PositivityTheory.Rg.Sw.Glob
end
end

