import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1563
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1570
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinResidueHolomorphicRegionTwo
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1564
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivHeisenbergCMRealLineFiniteInvariant
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

noncomputable section

namespace GlobalTheory.HeisDerivCM

open Formalism.IndefR.DatumF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem symplOHF_add_left (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (x x' y : WOF F E nS nT) :
    symplOHF σ JS JT ξ₀ (x + x') y = symplOHF σ JS JT ξ₀ x y + symplOHF σ JS JT ξ₀ x' y := by
  unfold symplOHF symplOF hOF
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add]

theorem symplOHF_add_right (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (x y y' : WOF F E nS nT) :
    symplOHF σ JS JT ξ₀ x (y + y') = symplOHF σ JS JT ξ₀ x y + symplOHF σ JS JT ξ₀ x y' := by
  unfold symplOHF symplOF hOF
  simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add]

theorem map_symplOHF_eq_zero {B : Type} [CommRing B] [Algebra F B] (p : AF F →ₐ[F] B)
    (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (x y : WOF F E nS nT)
    (h : x.map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom = 0 ∨
      y.map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom = 0) :
    p (symplOHF σ JS JT ξ₀ x y) = 0 := by
  have h1 : p (symplOF σ JS JT ξ₀ x y) = 0 := by
    unfold symplOF hOF
    rw [GlobalTheory.WeilVacMove.sum_reorder (cAF σ) (fun k i => incAF F E (JS⁻¹ k i)) (fun j l => incAF F E (JT j l)) x y]
    refine GlobalTheory.FockCompare.map_trace_sesq_eq_zero p σ _ (fun k i => incAF F E (JS⁻¹ k i))
      (fun j l => incAF F E (JT j l)) xᵀ yᵀ (h.imp (fun h => ?_) fun h => ?_) <;>
    · ext i j
      exact congrFun (congrFun h j) i
  unfold symplOHF
  rw [map_mul, h1, mul_zero]

theorem symplOHF_fin_real (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (u v : WOF F E nS nT)
    (hu : u.map (infPartF F E) = 0) (hv : v.map (finPartF F E) = 0) :
    symplOHF σ JS JT ξ₀ u v = 0 ∧ symplOHF σ JS JT ξ₀ v u = 0 :=
  ⟨Prod.ext (map_symplOHF_eq_zero (fstA F) σ JS JT ξ₀ u v (Or.inl hu))
      (map_symplOHF_eq_zero (sndA F) σ JS JT ξ₀ u v (Or.inr hv)),
    Prod.ext (map_symplOHF_eq_zero (fstA F) σ JS JT ξ₀ v u (Or.inr hu))
      (map_symplOHF_eq_zero (sndA F) σ JS JT ξ₀ v u (Or.inl hv))⟩

theorem heisOF_deriv_fix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ u : Formalism.IndefR.DatumF.WOF F E nS nT, u.map (Formalism.IndefR.DatumF.infPartF F E) = 0 → Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (u) f = f →
      Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (u) (fun w => deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w)) 0) = fun w => deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w)) 0 := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ _ f L _ hL u hu hf
  funext w
  have key : ∀ t : ℝ, B.ψ (symplOHF σ JS JT ξ₀ w u) * heisOF σ JS JT ξ₀ B.ψ (L t) f (w + u) =
      heisOF σ JS JT ξ₀ B.ψ (L t) f w := by
    intro t
    obtain ⟨h1, h2⟩ := symplOHF_fin_real σ JS JT ξ₀ u (L t) hu (hL t)
    have hfx := congrFun hf (w + L t)
    simp only [heisOF] at hfx ⊢
    conv_rhs => rw [← hfx]
    rw [symplOHF_add_left, symplOHF_add_left, h1, h2, add_zero, add_zero,
      show w + u + L t = w + L t + u by abel]
    ring
  show B.ψ (symplOHF σ JS JT ξ₀ w u) * deriv (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) f (w + u)) 0 = _
  rw [← deriv_const_mul_field]
  exact congrArg (fun g : ℝ → ℂ => deriv g 0) (funext key)

end GlobalTheory.HeisDerivCM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationsCommuteDistinctPlacesStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivations_commute_distinct_places : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (w : InfinitePlace F) (τ : EmbOver E w) (D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (SmG σ J)), IsDer σ J τ D →
    ∀ (w' : InfinitePlace F) (τ' : EmbOver E w') (D' : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (SmG σ J)),
    IsDer σ J τ' D' → w ≠ w' → ∀ X X', D X * D' X' = D' X' * D X := by
  first | exact @GlobalTheory.LeviHC.der_comm_of_ne | exact GlobalTheory.LeviHC.der_comm_of_ne | (intros; apply GlobalTheory.LeviHC.der_comm_of_ne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivedActionIntertwinesOfGroup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open Complex SchwartzMap
open scoped Real RealInnerProductSpace Topology

namespace GlobalTheory.RealWeil.DRhoTransfer

variable {l : Type} [Fintype l]

theorem exists_decay (h : Sch l) (N : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ y, (1 + ‖y‖) ^ N * ‖h y‖ ≤ M := by
  refine ⟨2 ^ N * (Finset.Iic (N, 0)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) h, by positivity, fun y => ?_⟩
  have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N, 0)) (le_refl N) (le_refl 0) h y
  simpa [norm_iteratedFDeriv_zero] using this

theorem translate_bound (h : Sch l) (N : ℕ) (p : EuclideanSpace ℝ l) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℝ, |s| ≤ 1 → ∀ x, ‖h (x + s • p)‖ ≤ M * ((1 + ‖x‖) ^ N)⁻¹ := by
  obtain ⟨M, hM, hb⟩ := exists_decay h N
  refine ⟨M * (1 + ‖p‖) ^ N, by positivity, fun s hs x => ?_⟩
  have h1 : 1 + ‖x‖ ≤ (1 + ‖x + s • p‖) * (1 + ‖p‖) := by
    have h0 : ‖x‖ ≤ ‖x + s • p‖ + ‖s • p‖ := by
      have := norm_sub_le (x + s • p) (s • p)
      simpa using this
    have h2 : ‖s • p‖ ≤ ‖p‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) hs
    nlinarith [norm_nonneg (x + s • p), norm_nonneg p]
  have h3 : (1 + ‖x‖) ^ N ≤ (1 + ‖x + s • p‖) ^ N * (1 + ‖p‖) ^ N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h1 N
  have hpos : 0 < (1 + ‖x‖) ^ N := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  calc ‖h (x + s • p)‖ * (1 + ‖x‖) ^ N ≤ ‖h (x + s • p)‖ * ((1 + ‖x + s • p‖) ^ N * (1 + ‖p‖) ^ N) := by
        gcongr
    _ = ((1 + ‖x + s • p‖) ^ N * ‖h (x + s • p)‖) * (1 + ‖p‖) ^ N := by ring
    _ ≤ M * (1 + ‖p‖) ^ N := by gcongr; exact hb _

theorem lintegral_inv_pow_lt_top (K : ℝ) :
    ∫⁻ x : EuclideanSpace ℝ l, ‖K * ((1 + ‖x‖) ^ (Module.finrank ℝ (EuclideanSpace ℝ l) + 1))⁻¹‖ₑ ^ 2 < ⊤ := by
  set N := Module.finrank ℝ (EuclideanSpace ℝ l) + 1 with hN
  have hi := integrable_one_add_norm (E := EuclideanSpace ℝ l) (μ := volume) (r := 2 * N)
    (by rw [hN]; push_cast; have := Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ (EuclideanSpace ℝ l)); linarith)
  have hi2 := hi.const_mul (K ^ 2)
  have e : ∀ x : EuclideanSpace ℝ l, ‖K * ((1 + ‖x‖) ^ N)⁻¹‖ₑ ^ 2 = ‖K ^ 2 * (1 + ‖x‖) ^ (-(2 * N : ℝ))‖ₑ := by
    intro x
    rw [← enorm_pow, mul_pow, inv_pow, ← pow_mul, Real.rpow_neg (by positivity),
      show (2 * (N : ℝ)) = ((N * 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  simp_rw [e]
  exact hi2.hasFiniteIntegral

theorem taylor_bound (w : l ⊕ l → ℝ) (f : Sch l) :
    ∃ B : EuclideanSpace ℝ l → ℝ, (∀ x, 0 ≤ B x) ∧ (∫⁻ x, ‖B x‖ₑ ^ 2 < ⊤) ∧
      ∀ t : ℝ, |t| ≤ 1 → ∀ x, ‖rhoFun (t • w) f x - f x - t * dRho w f x‖ ≤ t ^ 2 * B x := by
  set N := Module.finrank ℝ (EuclideanSpace ℝ l) + 1
  obtain ⟨M, hM, hb⟩ := translate_bound (dRho w (dRho w f)) N (pPart w)
  refine ⟨fun x => M * ((1 + ‖x‖) ^ N)⁻¹, fun x => by positivity, lintegral_inv_pow_lt_top M, fun t ht x => ?_⟩
  set h := dRho w f with hh
  have hB : ∀ s : ℝ, |s| ≤ 1 → ‖rhoFun (s • w) (dRho w h) x‖ ≤ M * ((1 + ‖x‖) ^ N)⁻¹ := fun s hs => by
    rw [rhoFun, norm_mul, norm_phase, one_mul, pPart_smul]
    exact hb s hs x
  have habs : ∀ s σ : ℝ, σ ∈ Set.uIcc 0 s → |σ| ≤ |s| := fun s σ hσ => by
    simpa using Set.abs_sub_left_of_mem_uIcc hσ
  have step1 : ∀ s : ℝ, |s| ≤ 1 → ‖rhoFun (s • w) h x - h x‖ ≤ M * ((1 + ‖x‖) ^ N)⁻¹ * |s| := by
    intro s hs
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun σ : ℝ => rhoFun (σ • w) h x)
      (f' := fun σ => rhoFun (σ • w) (dRho w h) x) (s := Set.uIcc 0 s) (C := M * ((1 + ‖x‖) ^ N)⁻¹)
      (fun σ _ => (hasDerivAt_rhoFun_at w h x σ).hasDerivWithinAt)
      (fun σ hσ => hB σ ((habs s σ hσ).trans hs)) (convex_uIcc 0 s) Set.left_mem_uIcc Set.right_mem_uIcc
    simpa [rhoFun_zero, Real.norm_eq_abs] using this
  have hd : ∀ σ : ℝ, HasDerivAt (fun σ : ℝ => rhoFun (σ • w) f x - f x - σ * h x)
      (rhoFun (σ • w) h x - h x) σ := fun σ => by
    have e1 : HasDerivAt (fun σ : ℝ => (σ : ℂ) * h x) (h x) σ := by
      simpa using (hasDerivAt_id σ).ofReal_comp.mul_const (h x)
    exact ((hasDerivAt_rhoFun_at w f x σ).sub_const (f x)).sub e1
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun σ : ℝ => rhoFun (σ • w) f x - f x - σ * h x)
    (f' := fun σ => rhoFun (σ • w) h x - h x) (s := Set.uIcc 0 t) (C := M * ((1 + ‖x‖) ^ N)⁻¹ * |t|)
    (fun σ _ => (hd σ).hasDerivWithinAt)
    (fun σ hσ => (step1 σ ((habs t σ hσ).trans ht)).trans (mul_le_mul_of_nonneg_left (habs t σ hσ) (by positivity)))
    (convex_uIcc 0 t) Set.left_mem_uIcc Set.right_mem_uIcc
  simp only [zero_smul, rhoFun_zero, sub_self, ofReal_zero, zero_mul, sub_zero, Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  rw [← sq_abs t]
  ring

theorem enorm_sub_sq_le (a b : ℂ) : ‖a - b‖ₑ ^ 2 ≤ 2 * ‖a‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := by
  simp only [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [norm_sub_le a b, norm_nonneg a, norm_nonneg b, norm_nonneg (a - b), sq_nonneg (‖a‖ - ‖b‖)]

theorem lintegral_le_of_bound (φ : EuclideanSpace ℝ l → ℂ) (B : EuclideanSpace ℝ l → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hB : ∀ x, 0 ≤ B x) (h : ∀ x, ‖φ x‖ ≤ c * B x) :
    ∫⁻ x, ‖φ x‖ₑ ^ 2 ≤ ENNReal.ofReal c ^ 2 * ∫⁻ x, ‖B x‖ₑ ^ 2 := by
  rw [← lintegral_const_mul' _ _ (by simp)]
  refine lintegral_mono fun x => ?_
  rw [← mul_pow]
  gcongr
  calc ‖φ x‖ₑ = ENNReal.ofReal ‖φ x‖ := (ofReal_norm_eq_enorm _).symm
    _ ≤ ENNReal.ofReal (c * B x) := ENNReal.ofReal_le_ofReal (h x)
    _ = ENNReal.ofReal c * ‖B x‖ₑ := by rw [ENNReal.ofReal_mul hc, Real.enorm_eq_ofReal (hB x)]

theorem dRho_intertwine : ∀ (l : Type) [Fintype l] (L' : (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ))
    (A' : GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l) (C : ℝ≥0∞), C ≠ ⊤ →
    (∀ f, ∫⁻ x, ‖A' f x‖ₑ ^ 2 ≤ C * ∫⁻ x, ‖f x‖ₑ ^ 2) →
    (∀ w (f f' : GlobalTheory.RealWeil.Sch l), ⇑f' = GlobalTheory.RealWeil.rhoFun w ⇑f →
      ⇑(A' f') = GlobalTheory.RealWeil.rhoFun (L' w) ⇑(A' f)) →
    ∀ w f, A' (GlobalTheory.RealWeil.dRho w f) = GlobalTheory.RealWeil.dRho (L' w) (A' f) := by
  intro l _ L' A' C hC hA hI w f
  obtain ⟨B₁, hB₁0, hB₁i, hB₁⟩ := taylor_bound w f
  obtain ⟨B₂, hB₂0, hB₂i, hB₂⟩ := taylor_bound (L' w) (A' f)
  set u := A' (dRho w f) - dRho (L' w) (A' f) with hu
  have t1 : ∫⁻ x, ‖B₁ x‖ₑ ^ 2 ≠ ⊤ := hB₁i.ne
  have t2 : (2 : ℝ≥0∞) * C ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hC
  have t4 : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  obtain ⟨K, hK⟩ : ∃ K : ℝ≥0∞, K = 2 * C * (∫⁻ x, ‖B₁ x‖ₑ ^ 2) + 2 * ∫⁻ x, ‖B₂ x‖ₑ ^ 2 := ⟨_, rfl⟩
  have hKt : K ≠ ⊤ := by
    rw [hK]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top t2 t1, ENNReal.mul_ne_top t4 hB₂i.ne⟩
  have hmeas : ∀ g : Sch l, AEMeasurable (fun x => ‖g x‖ₑ ^ 2) volume := fun g =>
    ((ENNReal.continuous_pow 2).comp g.continuous.enorm).aemeasurable
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 → ∫⁻ x, ‖u x‖ₑ ^ 2 ≤ ENNReal.ofReal (t ^ 2) * K := by
    intro t ht0 ht1
    have hta : |t| ≤ 1 := by rw [abs_of_pos ht0]; exact ht1
    obtain ⟨g, hg⟩ := exists_schwartz_rhoFun l (t • w) f
    have hAg : ⇑(A' g) = rhoFun (t • L' w) ⇑(A' f) := by rw [hI (t • w) f g hg, map_smul]
    set k := g - f - (t : ℂ) • dRho w f with hk
    set m := A' g - A' f - (t : ℂ) • dRho (L' w) (A' f) with hm
    have hkb : ∀ x, ‖k x‖ ≤ t ^ 2 * B₁ x := fun x => by
      have e : k x = rhoFun (t • w) f x - f x - t * dRho w f x := by
        simp only [hk, SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul, hg]
      rw [e]; exact hB₁ t hta x
    have hmb : ∀ x, ‖m x‖ ≤ t ^ 2 * B₂ x := fun x => by
      have e : m x = rhoFun (t • L' w) (A' f) x - A' f x - t * dRho (L' w) (A' f) x := by
        simp only [hm, SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul, hAg]
      rw [e]; exact hB₂ t hta x
    have hum : (t : ℂ) • u = m - A' k := by
      simp only [hu, hk, hm, map_sub, map_smul, smul_sub]
      abel
    obtain ⟨a, ha⟩ : ∃ a : ℝ≥0∞, a = ENNReal.ofReal (t ^ 2) := ⟨_, rfl⟩
    have ha0 : a ≠ 0 := ha ▸ (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have hat : a ≠ ⊤ := ha ▸ ENNReal.ofReal_ne_top
    have hIk := lintegral_le_of_bound k B₁ (by positivity) hB₁0 hkb
    have hIm := lintegral_le_of_bound m B₂ (by positivity) hB₂0 hmb
    have hsc : ∀ x, ‖((t : ℂ) • u) x‖ₑ ^ 2 = a * ‖u x‖ₑ ^ 2 := fun x => by
      rw [SchwartzMap.smul_apply, enorm_smul, mul_pow, ha, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
        Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have main : a * ∫⁻ x, ‖u x‖ₑ ^ 2 ≤ a * (a * K) := by
      calc a * ∫⁻ x, ‖u x‖ₑ ^ 2 = ∫⁻ x, ‖((t : ℂ) • u) x‖ₑ ^ 2 := by
            rw [← lintegral_const_mul' _ _ hat]; simp only [hsc]
        _ = ∫⁻ x, ‖m x - A' k x‖ₑ ^ 2 := by rw [hum]; simp only [SchwartzMap.sub_apply]
        _ ≤ ∫⁻ x, (2 * ‖m x‖ₑ ^ 2 + 2 * ‖A' k x‖ₑ ^ 2) := lintegral_mono fun x => enorm_sub_sq_le _ _
        _ = 2 * (∫⁻ x, ‖m x‖ₑ ^ 2) + 2 * ∫⁻ x, ‖A' k x‖ₑ ^ 2 := by
            rw [lintegral_add_left' ((hmeas m).const_mul 2), lintegral_const_mul' _ _ t4, lintegral_const_mul' _ _ t4]
        _ ≤ 2 * (ENNReal.ofReal (t ^ 2) ^ 2 * ∫⁻ x, ‖B₂ x‖ₑ ^ 2) +
              2 * (C * (ENNReal.ofReal (t ^ 2) ^ 2 * ∫⁻ x, ‖B₁ x‖ₑ ^ 2)) := by
            have hAk : ∫⁻ x, ‖A' k x‖ₑ ^ 2 ≤ C * (ENNReal.ofReal (t ^ 2) ^ 2 * ∫⁻ x, ‖B₁ x‖ₑ ^ 2) :=
              (hA k).trans (by gcongr)
            gcongr
        _ = a * (a * K) := by rw [hK, ha]; ring
    rw [← ha]
    exact (ENNReal.mul_le_mul_iff_right ha0 hat).mp main
  have hz : ∫⁻ x, ‖u x‖ₑ ^ 2 = 0 := by
    refine le_antisymm ?_ bot_le
    have ht : Filter.Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ 2) * K) (𝓝[>] 0) (𝓝 0) := by
      have := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal ((continuous_pow 2).tendsto (0 : ℝ)))
        (Or.inr hKt)
      simpa using this.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact key t ht.1 ht.2.le
  have hae := (lintegral_eq_zero_iff' (hmeas u)).1 hz
  have hu0 : ⇑u = fun _ => (0 : ℂ) := by
    refine (Continuous.ae_eq_iff_eq volume u.continuous (continuous_const (y := (0 : ℂ)))).1 ?_
    filter_upwards [hae] with x hx
    have hx' : ‖u x‖ₑ ^ 2 = 0 := hx
    simpa using hx'
  have : u = 0 := by ext x; simpa using congrFun hu0 x
  exact sub_eq_zero.1 this

end GlobalTheory.RealWeil.DRhoTransfer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricShortExactIsometric
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VMetric

theorem isometric_det_tens_det (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    (S : ShortComplex X.Modules) (r s : ℕ) (h : VMetric p S.X₂ (r + s)) (H : h.IsCInf)
    (hS : S.ShortExact) (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) (hf : IsSubbundle S.f) :
    ((VMetric.det (H.restrict hf h₁)).tens (VMetric.det (H.quot hS h₁ h₃))).Isometric (VMetric.det H) := by
  refine HermLB.isometric_of_local (J := VBExt.AdaptedChart S r s) (fun a => a.U)
    (fun x => VBExt.exists_adaptedChart hS h₁ h₃ x)
    (fun a => a.mid hS) (fun a => (a.sub, a.quot)) (fun _ => le_rfl) (fun _ => le_inf le_rfl le_rfl)
    (fun _ => 1) (fun x a a' hx hx' => ?_) (fun σ a y hy => ?_)
  · have key : gm (𝟙 X) x _ ((VMetric.det H).B.g (a.mid hS) (a'.mid hS)) =
        gm (𝟙 X) x _ (((VMetric.det (H.restrict hf h₁)).tens (VMetric.det (H.quot hS h₁ h₃))).B.g
          (a.sub, a.quot) (a'.sub, a'.quot)) :=
      ((congrArg (gm (𝟙 X) x _) (VBExt.detUnit_sumElim hS a.he a.ht a'.he a'.ht inf_le_left inf_le_right)).trans
        (map_mul _ _ _)).trans
        (CechPic.gm_tens (VB.det S.X₁ r) (VB.det S.X₃ s) (𝟙 X) x (a.sub, a.quot) (a'.sub, a'.quot)
          ⟨hx, hx⟩ ⟨hx', hx'⟩).symm
    rw [map_one, map_one, mul_one, key, mul_inv_cancel]
  · rw [CxPts.logSq_one hy, add_zero]
    change -Real.log ((h.met σ).G (a.mid hS) y).det.re =
      -Real.log (((h.met σ).restrict hf h₁).G a.sub y).det.re +
        -Real.log (((h.met σ).quot hS h₁ h₃).G a.quot y).det.re
    have hP := (h.met σ).posDef_gram_frame hS a hy
    have e₁ : ((h.met σ).restrict hf h₁).G a.sub y = subGram ((h.met σ).gram a.frame y) := rfl
    have e₂ : ((h.met σ).G (a.mid hS) y).det = ((h.met σ).gram a.frame y).det := by
      rw [(h.met σ).gram_frame hS a hy, Matrix.det_submatrix_equiv_self]
    have e₃ : ((h.met σ).gram a.frame y).det =
        (subGram ((h.met σ).gram a.frame y)).det * (quotGram ((h.met σ).gram a.frame y)).det := by
      have hA := posDef_subGram hP
      letI : Invertible ((h.met σ).gram a.frame y).toBlocks₁₁ := hA.isUnit.invertible
      conv_lhs => rw [← Matrix.fromBlocks_toBlocks ((h.met σ).gram a.frame y)]
      rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
      rfl
    rw [e₁, (h.met σ).quot_G hS h₁ h₃ a hy, e₂, e₃]
    have hA := posDef_subGram hP
    have hQ := posDef_quotGram hP
    have i₁ : (subGram ((h.met σ).gram a.frame y)).det.im = 0 := (Complex.lt_def.1 hA.det_pos).2.symm
    rw [Complex.mul_re, i₁, zero_mul, sub_zero, Real.log_mul (det_re_pos hA).ne' (det_re_pos hQ).ne']
    ring

end GlobalTheory.VMetric
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantMetricIsometric
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory

namespace VMetric

theorem isometric_det_of_isIsometry : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (E E' : X.Modules) (r : ℕ) (h : VMetric p E r) (h' : VMetric p E' r) (φ : E ≅ E') (H : h.IsCInf) (H' : h'.IsCInf), h.IsIsometry h' φ → (VMetric.det H).Isometric (VMetric.det H') := by
  intro k _ X p E E' r h h' φ H H' hφ
  rw [isIsometry_iff] at hφ
  subst hφ
  exact isometric_det_map H φ

end VMetric

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtPullbackForm
section
set_option autoImplicit false

open Set Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.CxForm
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.PullCoefDiff

theorem repr_mul_eq_sum {n : ℕ} (x y : Alt n) (S : Finset (Fin (n + n))) :
    (bas n).repr (x * y) S =
      ∑ A, ∑ B, (bas n).repr x A * (bas n).repr y B * (bas n).repr (bas n A * bas n B) S := by
  conv_lhs => rw [← (bas n).sum_repr x, ← (bas n).sum_repr y]
  rw [Finset.sum_mul_sum]
  simp only [map_sum, Finsupp.finset_sum_apply, smul_mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem ι_eq_sum {m : ℕ} (u : Fin m ⊕ Fin m → ℂ) :
    ExteriorAlgebra.ι ℂ u = ∑ a, u (.inl a) • dz a + ∑ a, u (.inr a) • dzb a := by
  simp only [dz, dzb, ← map_smul, ← map_sum, ← map_add]
  refine congrArg _ (funext ?_)
  rintro (b | b) <;> simp [Pi.single_apply, Finset.sum_apply]

theorem differentiableAt_repr_pull {n m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : E → V n →L[ℂ] V m} {v : E} (hL : ∀ b a, DifferentiableAt ℝ (fun x => L x (coordVec b) a) v)
    (θ : Alt m) (S : Finset (Fin (n + n))) :
    DifferentiableAt ℝ (fun x => (bas n).repr (pull (L x) θ) S) v := by
  induction θ using ExteriorAlgebra.induction generalizing S with
  | algebraMap r => simp only [AlgHom.commutes]; exact differentiableAt_const _
  | ι u =>
    rw [ι_eq_sum]
    simp only [map_add, map_sum, map_smul, (pull_dz _ _).1, (pull_dz _ _).2, Finsupp.add_apply,
      Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]
    refine DifferentiableAt.add ?_ ?_
    · exact DifferentiableAt.fun_sum fun a _ => (DifferentiableAt.fun_sum fun b _ => (hL b a).mul_const _).const_mul _
    · refine DifferentiableAt.fun_sum fun a _ => (DifferentiableAt.fun_sum fun b _ =>
        DifferentiableAt.mul_const ?_ _).const_mul _
      exact Complex.conjCLE.differentiableAt.comp v (hL b a)
  | mul a b ha hb =>
    simp only [map_mul, repr_mul_eq_sum (pull _ a)]
    exact DifferentiableAt.fun_sum fun A _ => DifferentiableAt.fun_sum fun B _ => ((ha A).mul (hb B)).mul_const _
  | add a b ha hb =>
    simp only [map_add, Finsupp.add_apply]
    exact (ha S).add (hb S)

theorem differentiableAt_repr_pull_fderiv : ∀ {n m : ℕ} {φ : V n → V m} {U : Set (V n)}, IsOpen U →
    DifferentiableOn ℂ φ U → ∀ {v : V n}, v ∈ U → ∀ (θ : Alt m) (S : Finset (Fin (n + n))),
    DifferentiableAt ℝ (fun x => (bas n).repr (pull (fderiv ℂ φ x) θ) S) v := by
  intro n m φ U hU hφ v hv θ S
  refine differentiableAt_repr_pull (fun b a => ?_) θ S
  have h₁ : ContDiffAt ℂ 2 φ v := GlobalTheory.SCV.contDiffAt_of_differentiableOn hφ (hU.mem_nhds hv) 2
  have h₂ : DifferentiableAt ℂ (fderiv ℂ φ) v :=
    (h₁.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h₃ : DifferentiableAt ℂ (fun x => fderiv ℂ φ x (coordVec b)) v := h₂.clm_apply (differentiableAt_const _)
  have h₄ : DifferentiableAt ℂ (fun x => fderiv ℂ φ x (coordVec b) a) v :=
    (EuclideanSpace.proj (𝕜 := ℂ) a).differentiableAt.comp v h₃
  exact h₄.restrictScalars ℝ

end GlobalTheory.PullCoefDiff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledDarbouxCoordsRationalOfRational
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.DblSchr.ddr_rat : ∀ (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (κ : Type) [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
    (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
      co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
    ∀ x : Matrix (Fin T.rank) (Fin (GlobalTheory.Doubling.dblSp S).rank) D.host.E, ∃ y z : κ ⊕ κ → D.host.F,
      (GlobalTheory.DblSchr.ddr co).e (incM D.host.F x) =
        (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i)) := by
  intro D S T JA JB ξ κ _ co h x
  obtain ⟨y₁, z₁, h₁⟩ := h (x.submatrix id finSumFinEquiv).toCols₁
  obtain ⟨y₂, z₂, h₂⟩ := h (x.submatrix id finSumFinEquiv).toCols₂
  refine ⟨Sum.elim y₁ y₂, Sum.elim z₁ (-z₂), ?_⟩
  rw [GlobalTheory.DblSchr.ddr, GlobalTheory.DblSchr.reD_e, Equiv.symm_symm]
  have e1 : ((incM D.host.F x).submatrix id finSumFinEquiv).toCols₁ = incM D.host.F (x.submatrix id finSumFinEquiv).toCols₁ := rfl
  have e2 : ((incM D.host.F x).submatrix id finSumFinEquiv).toCols₂ = incM D.host.F (x.submatrix id finSumFinEquiv).toCols₂ := rfl
  simp only [GlobalTheory.DblSchr.dblD, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, e1, e2, h₁, h₂]
  refine Prod.ext ?_ ?_
  · funext i; rcases i with i | i <;> rfl
  · funext i; rcases i with i | i <;> simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinResidueHolomorphicRegionTwoStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nhds_dop_central_eq_holomorphic_smul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) (Eis : ℂ → GAd σ J → ℂ) (c : ℂ → ℂ),
    HidaSetting σ J X Y L a h → EisensteinHyp σ J (col0 X) (col0 Y) h Eis c →
    ∀ (k₀ : ℕ) (U₀ : Set ℂ) (H₀ : ℂ → GAd σ J → ℂ), U₀ ∈ 𝓝 (((n : ℂ) - 1) / 2) →
      (∀ s ∈ U₀, s ≠ (((n : ℂ) - 1) / 2) → ∀ g, H₀ s g = (s - (((n : ℂ) - 1) / 2)) ^ k₀ * Eis s g) →
      (∀ s ∈ U₀, IsSmoothModerate σ J (H₀ s)) →
      (∀ μ, GlobalTheory.EisLine.IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H₀ s)) U₀) →
      ∃ V ∈ 𝓝 (((n : ℂ) - 1) / 2), ∀ z, GlobalTheory.UAut.IsCentral σ J z → ∃ χ : ℂ → ℂ, DifferentiableOn ℂ χ (interior V) ∧
        ∀ s ∈ V, GlobalTheory.UAut.dop z (H₀ s) = χ s • H₀ s := by
  first | exact @GlobalTheory.EisRes.CentralEig.dop_eigen_near_rho | exact GlobalTheory.EisRes.CentralEig.dop_eigen_near_rho | (intros; apply GlobalTheory.EisRes.CentralEig.dop_eigen_near_rho <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqArithmeticGroupMulScalarOfMovedFramesStatement
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_arithmeticGroup_mul_scalar_of_moved_frames : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X₂ X : Data E r) (δ h : GL (Fin r) E), X₂.Ψ = X.Ψ → (∀ x ∈ X₂.dom, ∀ x' : Frame X.Ψ r, GlobalTheory.LevModel.Moved X₂ X δ x x' → ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact h x' = rmul (lact γ x') b) → ∃ γ ∈ X.Γ, ∃ ζ : E, (h : Matrix (Fin r) (Fin r) E) = (γ : Matrix (Fin r) (Fin r) E) * Matrix.scalar (Fin r) ζ := by
  first | exact @GlobalTheory.LevModel.eq_mul_scalar_of_moved | exact GlobalTheory.LevModel.eq_mul_scalar_of_moved | (intros; apply GlobalTheory.LevModel.eq_mul_scalar_of_moved <;> assumption)
end

