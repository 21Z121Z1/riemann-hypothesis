import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1738
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1598
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0195
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1753
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1764
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0492
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1766
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1719
import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0043
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1744
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0227
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1731
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0224
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Formalism.UnipotentAdelicQuotients.ThmBInHecke
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNontrivialHeckeChar
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1711

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFiniteAdelicFactorOffPlace
section
open scoped Matrix GlobalTheory.VacAny ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

namespace GlobalTheory.HaarFactorOffPlace

theorem lintegral_factor {A V : Type} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd₂ A]
    [MeasurableNeg A] [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd₂ V] [MeasurableNeg V]
    (μ : Measure A) (ν : Measure V) [SFinite μ] [SFinite ν] [μ.IsAddRightInvariant]
    [ν.IsAddRightInvariant] (c : A → V) (e : V → A) (hcm : Measurable c)
    (hce : ∀ y t, c (y + e t) = c y + t) (O : Set V) (hOm : MeasurableSet O)
    (hOneg : ∀ x, x ∈ O ↔ -x ∈ O) (hO : ν O = 1) (K : A → ℝ≥0∞) (hK : Measurable K)
    (hKe : ∀ y t, K (y + e t) = K y) (g : V → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y, g (c y) * K y ∂μ = (∫⁻ t, g t ∂ν) * ∫⁻ y, O.indicator 1 (c y) * K y ∂μ := by
  have hχm : Measurable (O.indicator (1 : V → ℝ≥0∞)) := measurable_one.indicator hOm
  have hcs : ∀ y t, c (y - e t) = c y - t := fun y t => by
    have h := hce (y - e t) t
    rw [sub_add_cancel] at h
    rw [h, add_sub_cancel_right]
  have hKs : ∀ y t, K (y - e t) = K y := fun y t => by
    have h := hKe (y - e t) t
    rw [sub_add_cancel] at h
    exact h.symm
  have hχneg : ∀ x, O.indicator (1 : V → ℝ≥0∞) (-x) = O.indicator 1 x := fun x => by
    by_cases hx : x ∈ O
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hOneg x).1 hx)]; rfl
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx ((hOneg x).2 h))]
  have hχint : ∫⁻ t, O.indicator 1 t ∂ν = 1 := by
    rw [lintegral_indicator_one hOm]; exact hO
  have hA : ∀ t, ∫⁻ y, g (c y) * K y ∂μ = ∫⁻ y, g (c y + t) * K y ∂μ := fun t => by
    rw [← lintegral_add_right_eq_self (fun y => g (c y) * K y) (e t)]
    simp only [hce, hKe]
  have hL : ∫⁻ y, g (c y) * K y ∂μ =
      ∫⁻ y, ∫⁻ s, O.indicator 1 (s - c y) * (g s * K y) ∂ν ∂μ := by
    calc ∫⁻ y, g (c y) * K y ∂μ
        = (∫⁻ t, O.indicator 1 t ∂ν) * ∫⁻ y, g (c y) * K y ∂μ := by rw [hχint, one_mul]
      _ = ∫⁻ t, O.indicator 1 t * ∫⁻ y, g (c y) * K y ∂μ ∂ν := (lintegral_mul_const _ hχm).symm
      _ = ∫⁻ t, O.indicator 1 t * ∫⁻ y, g (c y + t) * K y ∂μ ∂ν :=
          lintegral_congr fun t => by rw [← hA t]
      _ = ∫⁻ t, ∫⁻ y, O.indicator 1 t * (g (c y + t) * K y) ∂μ ∂ν :=
          lintegral_congr fun t =>
            (lintegral_const_mul _ ((hg.comp (hcm.add_const t)).mul hK)).symm
      _ = ∫⁻ y, ∫⁻ t, O.indicator 1 t * (g (c y + t) * K y) ∂ν ∂μ := by
          apply lintegral_lintegral_swap
          exact ((hχm.comp measurable_fst).mul
            ((hg.comp ((hcm.comp measurable_snd).add measurable_fst)).mul
              (hK.comp measurable_snd))).aemeasurable
      _ = ∫⁻ y, ∫⁻ s, O.indicator 1 (s - c y) * (g s * K y) ∂ν ∂μ := by
          refine lintegral_congr fun y => ?_
          rw [← lintegral_sub_right_eq_self (fun t => O.indicator 1 t * (g (c y + t) * K y)) (c y)]
          refine lintegral_congr fun s => ?_
          simp only [add_sub_cancel]
  have hM : ∀ s, ∫⁻ y, O.indicator 1 (c y) * K y ∂μ =
      ∫⁻ y, O.indicator 1 (s - c y) * K y ∂μ := fun s => by
    rw [← lintegral_sub_right_eq_self (fun y => O.indicator 1 (c y) * K y) (e s)]
    refine lintegral_congr fun y => ?_
    simp only [hcs, hKs]
    rw [← neg_sub, hχneg]
  rw [hL]
  calc ∫⁻ y, ∫⁻ s, O.indicator 1 (s - c y) * (g s * K y) ∂ν ∂μ
      = ∫⁻ s, ∫⁻ y, O.indicator 1 (s - c y) * (g s * K y) ∂μ ∂ν := by
        apply lintegral_lintegral_swap
        exact ((hχm.comp (measurable_snd.sub (hcm.comp measurable_fst))).mul
          ((hg.comp measurable_snd).mul (hK.comp measurable_fst))).aemeasurable
    _ = ∫⁻ s, g s * ∫⁻ y, O.indicator 1 (s - c y) * K y ∂μ ∂ν := by
        refine lintegral_congr fun s => ?_
        have hm : Measurable fun y => O.indicator (1 : V → ℝ≥0∞) (s - c y) * K y :=
          (hχm.comp (measurable_const.sub hcm)).mul hK
        rw [← lintegral_const_mul _ hm]
        refine lintegral_congr fun y => ?_
        ring
    _ = ∫⁻ s, g s * ∫⁻ y, O.indicator 1 (c y) * K y ∂μ ∂ν :=
        lintegral_congr fun s => by rw [← hM s]
    _ = (∫⁻ t, g t ∂ν) * ∫⁻ y, O.indicator 1 (c y) * K y ∂μ := lintegral_mul_const _ hg

end GlobalTheory.HaarFactorOffPlace

namespace GlobalTheory.HaarFactorOffPlace

theorem lintegral_evalV_mul_shiftInvariant : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [MeasurableSpace (κ → Af F)] [BorelSpace (κ → Af F)]
    (w : HeightOneSpectrum (𝓞 F)) [MeasurableSpace (κ → Fv F w)] [BorelSpace (κ → Fv F w)]
    (μf : Measure (κ → Af F)) [μf.IsAddHaarMeasure] (μw : Measure (κ → Fv F w)) [μw.IsAddHaarMeasure],
    μw {t | ∀ i, t i ∈ w.adicCompletionIntegers F} = 1 →
    ∀ (K : (κ → Af F) → ℝ≥0∞), Measurable K → (∀ (y : κ → Af F) (t : κ → Fv F w), K (fun i => y i + singleFin w (t i)) = K y) →
    ∀ (g : (κ → Fv F w) → ℝ≥0∞), Measurable g →
      ∫⁻ y, g (fun i => evalV F w (y i)) * K y ∂μf =
        (∫⁻ t, g t ∂μw) * ∫⁻ y, {t : κ → Fv F w | ∀ i, t i ∈ w.adicCompletionIntegers F}.indicator 1 (fun i => evalV F w (y i)) * K y ∂μf := by
  intro F _ _ κ _ _ _ w _ _ μf _ μw _ hO K hK hKinv g hg
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F w
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (κ → Af F) := inferInstance
  haveI : SecondCountableTopology (κ → Fv F w) := inferInstance
  haveI : LocallyCompactSpace (κ → Af F) := inferInstance
  haveI : LocallyCompactSpace (κ → Fv F w) := inferInstance
  have hcont : Continuous fun (y : κ → Af F) (i : κ) => evalV F w (y i) :=
    continuous_pi fun i => (GlobalTheory.GaugeGlue.continuous_evalV w).comp (continuous_apply i)
  have hOc : IsClosed {t : κ → Fv F w | ∀ i, t i ∈ w.adicCompletionIntegers F} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i =>
      (Valued.isClosed_integer (Fv F w)).preimage (continuous_apply i)
  refine lintegral_factor μf μw (fun y i => evalV F w (y i)) (fun t i => singleFin w (t i))
    hcont.measurable ?_ _ hOc.measurableSet ?_ hO K hK (fun y t => hKinv y t) g hg
  · intro y t
    funext i
    simp only [Pi.add_apply, map_add, evalV_singleFin_self]
  · intro x
    simp only [Set.mem_setOf_eq, Pi.neg_apply, neg_mem_iff]

end GlobalTheory.HaarFactorOffPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdentityOfTensorHeisenbergEigen
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix

namespace GlobalTheory.DblVacEigen

theorem local_identity_of_tens_eigen : ∀ {F : Type} [Field F] [NumberField F] (v : Pl F) {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : Darboux B κ) (ψ : AddChar (AF F) ℂ) (γ : W) (f : (κ → Fv F v) → ℂ)
    (R : (κ → AF F) → ℂ) (c : ℂ), At (evFin F v) γ → (∀ x z, At (evFin F v) z → R (x + z) = R x) →
    ∀ x₀, R x₀ ≠ 0 → co.rho ψ γ (tens (evFin F v) f R) = c • tens (evFin F v) f R →
    ∀ ξ : κ → Fv F v, GlobalTheory.LatVac.psiAt ψ v (ξ ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2 +
        (2 : Fv F v)⁻¹ * ((GlobalTheory.LatVac.locCo co v γ).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2)) *
      f (ξ + (GlobalTheory.LatVac.locCo co v γ).1) = c * f ξ := by
  intro F _ _ v W _ _ B κ _ co ψ γ f R c hγ hR x₀ hx₀ hA ξ
  have hx1 : ∀ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) ((co.e γ).1 k) := fun k u hu => by
    have h := congrArg (fun w => (co.e w).1 k) (hγ u hu)
    simpa [LinearEquiv.map_smul] using h
  have hy1 : ∀ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) ((co.e γ).2 k) := fun k u hu => by
    have h := congrArg (fun w => (co.e w).2 k) (hγ u hu)
    simpa [LinearEquiv.map_smul] using h
  set z : κ → AF F := fun k => GlobalTheory.LatVac.liftV v (ξ k - evFin F v (x₀ k)) with hz
  have hzat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z :=
    GlobalTheory.VacIndic.at_pi fun k => GlobalTheory.LatVac.at_liftV v _
  set x : κ → AF F := x₀ + z with hx
  have hevx : (fun i => evFin F v (x i)) = ξ := by
    funext i
    simp [hx, hz, GlobalTheory.LatVac.evFin_liftV]
  have hrx : R x = R x₀ := hR x₀ z hzat
  have hrx1 : R (x + (co.e γ).1) = R x := hR x _ (GlobalTheory.VacIndic.at_pi hx1)
  have key := congrFun hA x
  simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, Pi.smul_apply, smul_eq_mul] at key
  have hAt : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v)
      (x ⬝ᵥ (co.e γ).2 + ⅟(2 : AF F) * ((co.e γ).1 ⬝ᵥ (co.e γ).2)) := by
    refine GlobalTheory.VacIndic.at_add ?_ (GlobalTheory.VacIndic.at_mul_left ?_)
    · exact GlobalTheory.VacIndic.at_sum _ _ fun i => GlobalTheory.VacIndic.at_mul_left (hy1 i)
    · exact GlobalTheory.VacIndic.at_sum _ _ fun i => GlobalTheory.VacIndic.at_mul_left (hy1 i)
  rw [GlobalTheory.VacIndic.psi_of_at ψ hAt, hrx1] at key
  have hhalf : evFin F v (⅟(2 : AF F)) = (2 : Fv F v)⁻¹ := by
    rw [GlobalTheory.VacIndic.invOf_two_eq, GlobalTheory.VacIndic.evFin_algebraMap]
    simp [map_ofNat]
  have hdot : ∀ a b : κ → AF F, evFin F v (a ⬝ᵥ b) = (fun i => evFin F v (a i)) ⬝ᵥ (fun i => evFin F v (b i)) := by
    intro a b
    simp [dotProduct, map_sum, map_mul]
  have hsum : (fun i => evFin F v ((x + (co.e γ).1) i)) = ξ + (GlobalTheory.LatVac.locCo co v γ).1 := by
    funext i
    rw [← hevx]
    simp [GlobalTheory.LatVac.locCo]
  rw [map_add, map_mul, hhalf, hdot, hdot, hevx, hsum] at key
  have hr0 : R x ≠ 0 := hrx ▸ hx₀
  rw [GlobalTheory.LatVac.psiAt_apply]
  have := key
  apply mul_right_cancel₀ hr0
  simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this ⊢
  linear_combination this

end GlobalTheory.DblVacEigen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRationalPointsOfUnipotentCoordsRational
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem mem_ratPts_of_crd_rat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (u : GAd σ J) (b₀ : Matrix (Fin j) (Fin m) E) (c₀ : Matrix (Fin j) (Fin j) E), Crd σ J C D Z J₀ u (adMat F b₀) (adMat F c₀) → u ∈ ratPts σ J := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF u b₀ c₀ h
  have hmul : ∀ {a b c : ℕ} (X : Matrix (Fin a) (Fin b) E) (Y : Matrix (Fin b) (Fin c) E),
      adMat F (X * Y) = adMat F X * adMat F Y := fun X Y => by
    unfold adMat
    exact Matrix.map_mul (f := (inclR (F := F) (AF F) : E →+* _))
  have hadd : ∀ {a b : ℕ} (X Y : Matrix (Fin a) (Fin b) E),
      adMat F (X + Y) = adMat F X + adMat F Y := fun X Y => by
    ext i k; simp [adMat]
  have hsub : ∀ {a b : ℕ} (X Y : Matrix (Fin a) (Fin b) E),
      adMat F (X - Y) = adMat F X - adMat F Y := fun X Y => by
    ext i k; simp [adMat]
  refine GlobalTheory.T.mem_unitaryRationalPoints_of_frameImages_rational F E σ n J j m C D Z J₀ hF u C
    (D - Z * (J₀⁻¹ * cT (σ : E →+* E) b₀) + C * c₀) (Z + C * b₀) h.onC ?_ ?_
  · rw [h.onZ, hadd, hmul]
  · rw [h.onD, hadd, hsub, hmul, hmul, hmul]
    rfl

end GlobalTheory.SphEis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCompletedHeckeLCMOneLePhragmenLindelof
section
open NumberField IsDedekindDomain GlobalTheory.CMVal

noncomputable section
namespace GlobalTheory.HeckeLOneBound
open GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds

theorem norm_factor (s c : ℂ) :
    ‖2 * (2 * (Real.pi : ℂ)) ^ (-(s + c)) * Complex.Gamma (s + c)‖ =
      2 * (2 * Real.pi) ^ (-(s.re + c.re)) * ‖Complex.Gamma (s + c)‖ := by
  have h2 : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  rw [norm_mul, norm_mul, h2, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  simp

theorem norm_archFactor_real {I : Type} [Fintype I] (n : I → ℤ) {x : ℝ} (hx : 0 < x) :
    ‖archFactor n (x : ℂ)‖ = ∏ i, (2 * (2 * Real.pi) ^ (-(x + ((|n i| : ℤ) : ℝ) / 2)) *
      Real.Gamma (x + ((|n i| : ℤ) : ℝ) / 2)) := by
  unfold archFactor
  rw [norm_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [norm_factor]
  have hc : ((x : ℂ) + ((|n i| : ℤ) : ℂ) / 2) = ((x + ((|n i| : ℤ) : ℝ) / 2 : ℝ) : ℂ) := by
    simp only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_intCast, Complex.ofReal_ofNat]
  have h0 : (0 : ℝ) ≤ ((|n i| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg (n i)
  rw [hc, Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.Gamma_pos_of_pos (by linarith))]
  congr 3
  simp

theorem norm_archFactor_le {I : Type} [Fintype I] (n : I → ℤ) {s : ℂ} (hs : 0 < s.re) :
    ‖archFactor n s‖ ≤ ‖archFactor n (s.re : ℂ)‖ := by
  rw [norm_archFactor_real n hs]
  unfold archFactor
  rw [norm_prod]
  refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
  rw [norm_factor]
  have h0 : (0 : ℝ) ≤ ((|n i| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg (n i)
  have hre : (s + ((|n i| : ℤ) : ℂ) / 2).re = s.re + ((|n i| : ℤ) : ℝ) / 2 := by simp
  have hre' : (((|n i| : ℤ) : ℂ) / 2).re = ((|n i| : ℤ) : ℝ) / 2 := by simp
  rw [hre']
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have := PI.EF.norm_Gamma_le (w := s + ((|n i| : ℤ) : ℂ) / 2) (by rw [hre]; linarith)
  rwa [hre] at this

theorem pl_strip {f : ℂ → ℂ} (hf : Differentiable ℂ f) {a b C : ℝ} (hab : a < b)
    (hbd : ∃ C' : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖f s‖ ≤ C')
    (ha : ∀ s : ℂ, s.re = a → ‖f s‖ ≤ C) (hb : ∀ s : ℂ, s.re = b → ‖f s‖ ≤ C)
    {z : ℂ} (hza : a ≤ z.re) (hzb : z.re ≤ b) : ‖f z‖ ≤ C := by
  refine PhragmenLindelof.vertical_strip hf.diffContOnCl ?_ ha hb hza hzb
  refine ⟨0, div_pos Real.pi_pos (sub_pos.2 hab), 0, ?_⟩
  obtain ⟨C', hC'⟩ := hbd
  refine Asymptotics.IsBigO.of_bound C' ?_
  refine Filter.eventually_inf_principal.2 (Filter.Eventually.of_forall fun z hz => ?_)
  simp only [zero_mul, Real.exp_zero, norm_one, mul_one]
  exact hC' z hz.1.le hz.2.le

theorem factor_three_halves_le {c : ℝ} (hc : 1 ≤ c) :
    2 * (2 * Real.pi) ^ (-(3 / 2 + c)) * Real.Gamma (3 / 2 + c) ≤
      2 * (2 * Real.pi) ^ (-(1 + c)) * Real.Gamma (1 + c) * (1 + c) := by
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have h1 : (2 * Real.pi) ^ (-(3 / 2 + c)) ≤ (2 * Real.pi) ^ (-(1 + c)) :=
    Real.rpow_le_rpow_of_exponent_le hpi (by linarith)
  have h2 : Real.Gamma (3 / 2 + c) ≤ Real.Gamma (1 + c + 1) :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn (Set.mem_Ici.2 (by linarith)) (Set.mem_Ici.2 (by linarith)) (by linarith)
  rw [Real.Gamma_add_one (by linarith)] at h2
  have hg : 0 ≤ Real.Gamma (3 / 2 + c) := (Real.Gamma_pos_of_pos (by linarith)).le
  have hp : 0 ≤ (2 * Real.pi) ^ (-(1 + c)) := by positivity
  calc 2 * (2 * Real.pi) ^ (-(3 / 2 + c)) * Real.Gamma (3 / 2 + c)
      ≤ 2 * (2 * Real.pi) ^ (-(1 + c)) * Real.Gamma (3 / 2 + c) := by gcongr
    _ ≤ 2 * (2 * Real.pi) ^ (-(1 + c)) * ((1 + c) * Real.Gamma (1 + c)) := by gcongr
    _ = _ := by ring

theorem archFactor_three_halves_le {I : Type} [Fintype I] (m : I → ℤ) (hm : ∀ i, 0 < m i) :
    ‖archFactor (fun i => 2 * m i) (3 / 2)‖ ≤ ‖archFactor (fun i => 2 * m i) 1‖ * ∏ i, (1 + (m i : ℝ)) := by
  have e32 : (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) := by push_cast; ring
  have e1 : (1 : ℂ) = ((1 : ℝ) : ℂ) := by simp
  rw [e32, e1, norm_archFactor_real _ (by norm_num), norm_archFactor_real _ (by norm_num), ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun i _ => ?_) fun i _ => ?_
  · have : 0 < 3 / 2 + ((|2 * m i| : ℤ) : ℝ) / 2 := by
      have : (0 : ℝ) ≤ ((|2 * m i| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg _
      linarith
    have := Real.Gamma_pos_of_pos this
    positivity
  · have hc : ((|2 * m i| : ℤ) : ℝ) / 2 = (m i : ℝ) := by
      rw [abs_of_pos (by have := hm i; omega)]; push_cast; ring
    rw [hc]
    exact factor_three_halves_le (by exact_mod_cast hm i)

end GlobalTheory.HeckeLOneBound

namespace GlobalTheory.HeckeLOneBound
open GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds

theorem norm_heckeL_one_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    GlobalTheory.Published.HeckeFunctionalEquationAbs → GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.CompletedLBoundedInStrips → IsCMType φ →
    ∀ (χ : HChar E) (m : I → ℤ) (a : HeightOneSpectrum (𝓞 E) →₀ ℕ) (Λ : ℂ → ℂ),
    IsUnitary χ → TrivOnF χ → HasInf χ φ m → (∀ i, 0 < m i) → (∀ v, ExpAt χ v (a v)) → IsHeckeL χ Λ →
    ‖Λ 1‖ ≤ ‖riemannZeta (3 / 2)‖ ^ Module.finrank ℚ E *
      ((((discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k : ℕ) : ℝ)) * ∏ i, (1 + (m i : ℝ)) := by
  intro E _ _ _ I _ φ hFE hB hφ χ m a Λ hu htr hinf hpos ha hL
  set n : I → ℤ := fun i => 2 * m i with hn_def
  set A : ℕ := (discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k with hA_def
  set Z : ℝ := ‖riemannZeta (3 / 2)‖ ^ Module.finrank ℚ E with hZ_def
  have hinf' : Formalism.L2.Host.HChar.HasInf χ φ n := hinf
  obtain ⟨i₀⟩ := GlobalTheory.LValNe.nonempty_of_isCMType hφ
  have hn : ∃ i, n i ≠ 0 := ⟨i₀, by have := hpos i₀; simp only [hn_def]; omega⟩
  have hn' : ∃ i, (fun i => -n i) i ≠ 0 := ⟨i₀, by have := hpos i₀; simp only [hn_def]; omega⟩
  have hu' := GlobalTheory.Published.HeckeFEModel.isUnitary_inv hu
  have hinv := GlobalTheory.Published.HeckeFEModel.hasInf_inv hinf'
  obtain ⟨Λc, hΛc, hbc⟩ := hB E I φ hφ χ n hu hinf' hn
  obtain ⟨Λc', hΛc', -⟩ := hB E I φ hφ χ⁻¹ (fun i => -n i) hu' hinv hn'
  obtain ⟨ε, hε, hfe⟩ := hFE E I φ hφ χ n a Λc Λc' hu hinf' hn ha hΛc hΛc'
  have hL' : IsHeckeL χ⁻¹ Λ := GlobalTheory.T.isPrimitiveHeckeLFunction_inv_of_trivialOnMaxReal E χ Λ htr hL
  have harch : archFactor (fun i => -n i) = archFactor n := by
    funext s; unfold archFactor; simp only [abs_neg]
  have hApos : 0 < A := by
    refine Nat.mul_pos (Int.natAbs_pos.2 (discr_ne_zero E)) ?_
    unfold Finsupp.prod
    exact Finset.prod_pos fun v _ => pow_pos (Nat.pos_of_ne_zero fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)) _
  have hA1 : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hApos
  have hZ0 : 0 ≤ Z := by positivity
  set F : ℝ := ‖archFactor n (3 / 2)‖ with hF_def
  have hF0 : 0 ≤ F := norm_nonneg _

  have hline : ∀ s : ℂ, s.re = 3 / 2 → ‖Λc s‖ ≤ F * Z := fun s hs => by
    rw [hΛc.eq_mul hL (by rw [hs]; norm_num), norm_mul]
    have h1 := norm_archFactor_le n (s := s) (by rw [hs]; norm_num)
    rw [hs] at h1
    have h1' : ‖archFactor n s‖ ≤ F := by
      rw [hF_def]; convert h1 using 3; push_cast; ring
    exact mul_le_mul h1' (GlobalTheory.T.norm_heckeLFunction_le_zeta_three_halves_pow E χ Λ s hu hL hs.ge) (norm_nonneg _) hF0
  have hline' : ∀ s : ℂ, s.re = 3 / 2 → ‖Λc' s‖ ≤ F * Z := fun s hs => by
    rw [hΛc'.eq_mul hL' (by rw [hs]; norm_num), norm_mul, harch]
    have h1 := norm_archFactor_le n (s := s) (by rw [hs]; norm_num)
    rw [hs] at h1
    have h1' : ‖archFactor n s‖ ≤ F := by
      rw [hF_def]; convert h1 using 3; push_cast; ring
    exact mul_le_mul h1' (GlobalTheory.T.norm_heckeLFunction_le_zeta_three_halves_pow E χ⁻¹ Λ s hu' hL' hs.ge) (norm_nonneg _) hF0

  have hleft : ∀ s : ℂ, s.re = -1 / 2 → ‖Λc s‖ ≤ A * F * Z := fun s hs => by
    rw [hfe s, norm_mul, norm_mul, hε, one_mul, Complex.norm_natCast_cpow_of_pos hApos]
    have hre : (1 / 2 - s).re = 1 := by
      simp only [Complex.sub_re, hs]; norm_num
    rw [hre, Real.rpow_one, mul_assoc]
    refine mul_le_mul_of_nonneg_left (hline' _ ?_) (by positivity)
    simp only [Complex.sub_re, Complex.one_re, hs]; norm_num
  have hright : ∀ s : ℂ, s.re = 3 / 2 → ‖Λc s‖ ≤ A * F * Z := fun s hs => by
    refine (hline s hs).trans ?_
    rw [mul_assoc]
    exact le_mul_of_one_le_left (by positivity) hA1

  have hbd := hbc (-1 / 2) (3 / 2) (by norm_num)
  have h1 : ‖Λc 1‖ ≤ A * F * Z :=
    pl_strip hΛc.1 (by norm_num) hbd hleft hright (by norm_num) (by norm_num)

  have hg : ∀ i, Complex.Gamma ((1 : ℂ) + ((|n i| : ℤ) : ℂ) / 2) ≠ 0 := fun i => by
    refine Complex.Gamma_ne_zero_of_re_pos ?_
    have : (0 : ℝ) ≤ ((|n i| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg (n i)
    simp only [Complex.add_re, Complex.one_re, Complex.div_re, Complex.intCast_re, Complex.intCast_im]
    norm_num
    positivity
  have e1 := GlobalTheory.LValNe.completed_eq hΛc hL hg
  have hG : 0 < ‖archFactor n 1‖ := norm_pos_iff.2 (GlobalTheory.LValNe.archFactor_ne_zero hg)
  have hrat := archFactor_three_halves_le m hpos
  rw [e1, norm_mul] at h1
  have hP0 : 0 ≤ ∏ i, (1 + (m i : ℝ)) :=
    Finset.prod_nonneg fun i _ => by have : (0 : ℝ) < m i := by exact_mod_cast hpos i
                                     linarith
  have key : ‖archFactor n 1‖ * ‖Λ 1‖ ≤ ‖archFactor n 1‖ * (Z * (A : ℝ) * ∏ i, (1 + (m i : ℝ))) := by
    refine h1.trans ?_
    have : A * F * Z ≤ A * (‖archFactor n 1‖ * ∏ i, (1 + (m i : ℝ))) * Z := by gcongr
    refine this.trans (le_of_eq ?_)
    ring
  exact le_of_mul_le_mul_left key hG

end GlobalTheory.HeckeLOneBound

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDiagonalTorusCharacterFlatLineWeightStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_diagonalTorusCharacter_flatLineWeight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ) (τ : Psi H) (t : Ix Dw → (CAt σ)ˣ), ‖GlobalTheory.CompHS.diagChar (exOf Dw (flatWt Dw τ) 0) t‖ = (∏ j : Fin (Dw.mult (conjEmb τ.1)), ‖toC ((t (some ⟨conjEmb τ.1, j⟩) : CAt σ))‖) / ∏ i : Fin (Dw.mult τ.1), ‖toC ((t (some ⟨τ.1, i⟩) : CAt σ))‖ := by
  first | exact @GlobalTheory.CompHS.FlatDiag.norm_diagChar_flatWt | exact GlobalTheory.CompHS.FlatDiag.norm_diagChar_flatWt | (intros; apply GlobalTheory.CompHS.FlatDiag.norm_diagChar_flatWt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyNormBoundAbsoluteConstantStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedFamily_normBound_absoluteConstant : GlobalTheory.ColNorms.FamilyNorms := by
  first | exact @GlobalTheory.ColNorms.FamilyBound.familyNorms | exact GlobalTheory.ColNorms.FamilyBound.familyNorms | (intros; apply GlobalTheory.ColNorms.FamilyBound.familyNorms <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedAbsDetMulIntegralCompMulVecFinitePlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.InertLagChar

theorem haarChar_det_mul_integral_comp_mulVec_localField (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (m : MeasurableSpace (Fin N → k)) (hm : m = borel _)
    (ν : @Measure (Fin N → k) m) (hν : @Measure.IsAddHaarMeasure _ _ _ m ν)
    (T : GL (Fin N) k) (f : (Fin N → k) → ℂ) :
    ((distribHaarChar k (Matrix.GeneralLinearGroup.det T) : ℝ) : ℂ) * ∫ y, f (T.val *ᵥ y) ∂ν = ∫ y, f y ∂ν := by
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  have h2 : m = MeasurableSpace.pi := hm.trans (@BorelSpace.measurable_eq (Fin N → k) _ MeasurableSpace.pi Pi.borelSpace).symm
  subst h2
  have hc := Measure.isAddLeftInvariant_eq_smul ν (Measure.pi fun _ : Fin N => (Measure.addHaar : Measure k))
  rw [hc, integral_smul_nnreal_measure, integral_smul_nnreal_measure,
    ← GlobalTheory.WeilM.integral_comp_mulVec (Measure.addHaar : Measure k) T f, mul_smul_comm]

theorem nabs_det_mul_integral_comp_mulVec :
    ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)),
    @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∀ (T : GL (Fin N) (Fv F v)) (f : (Fin N → Fv F v) → ℂ),
      ((GlobalTheory.SplitWeil.nabs (Fv F v) (Matrix.GeneralLinearGroup.det T) : ℝ) : ℂ) * ∫ y, f (T.val *ᵥ y) ∂ν = ∫ y, f y ∂ν := by
  intro F _ _ v N ν hν T f
  exact haarChar_det_mul_integral_comp_mulVec_localField (Fv F v) N _ rfl ν hν T f

end GlobalTheory.InertLagChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenSigmaStableUnitNeighborhoodStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_sigma_stable_unit_neighborhood : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (m : ℕ), 0 < m → ∃ U : Subgroup (AdeleRing (𝓞 F) F ⊗[F] E)ˣ, IsOpen (U : Set (AdeleRing (𝓞 F) F ⊗[F] E)ˣ) ∧
      (∀ x ∈ U, Units.map (Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) σ).toRingHom.toMonoidHom x ∈ U) ∧
      ∀ x ∈ U, ∃ s ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E,
        HeckeCharacterZeroLocus.ThmBIn.finPart F E (x : AdeleRing (𝓞 F) F ⊗[F] E) = 1 + (m : FiniteAdeleRing (𝓞 F) F ⊗[F] E) * s := by
  first | exact @GlobalTheory.IdeleCongr.exists_open_congruence_subgroup | exact GlobalTheory.IdeleCongr.exists_open_congruence_subgroup | (intros; apply GlobalTheory.IdeleCongr.exists_open_congruence_subgroup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaValuesAtNegIntUniqueStatement
section
open NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialZeta_values_at_neg_int_unique : ∀ {E : Type} [Field E] [NumberField E] {k : ℕ}, 2 ≤ k → ∀ {z z' : ClassGroup (GlobalTheory.CMVal.OF E) → ℚ}, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsClassZetaVals k z → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsClassZetaVals k z' → z = z' := by
  first | exact @GlobalTheory.ZetaValUnique.classZetaVals_unique | exact GlobalTheory.ZetaValUnique.classZetaVals_unique | (intros; apply GlobalTheory.ZetaValUnique.classZetaVals_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOneFgLatticeEqFractionalIdealSmulVectorStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankOne_fg_lattice_eq_fractionalIdeal_smul_vector : ∀ {K : Type} [Field K] [NumberField K] {m : ℕ} (ell : Submodule (𝓞 K) (Fin m → K)),
    ReciprocityTheory.GeometryOfNumbersTheory.latRank K ell = 1 → ell.FG →
    ∃ v : Fin m → K, v ≠ 0 ∧ ∃ 𝔟 : Submodule (𝓞 K) K, 𝔟.FG ∧ 𝔟 ≠ ⊥ ∧
      ∀ e, e ∈ ell ↔ ∃ β ∈ 𝔟, e = β • v := by
  first | exact @GlobalTheory.latRank_one_eq_ideal_smul | exact GlobalTheory.latRank_one_eq_ideal_smul | (intros; apply GlobalTheory.latRank_one_eq_ideal_smul <;> assumption)
end

