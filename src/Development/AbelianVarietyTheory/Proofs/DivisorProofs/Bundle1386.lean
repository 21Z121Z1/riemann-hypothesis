import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1358
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0564
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1359
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import GroundTheory.LocalFields.LocalFourierHaar
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0327
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenKerOfContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1364
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingProjectionStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_embedding_projection : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (P : Finset (SV (wittIndex V))) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (t : GAd D.sp.cm.sig V.gram), t ∈ Φ.levi D.sp.cm (AF D.host.F) P → embAt D.sp.cm.sig V.gram S (projAt D.sp.cm.sig V.gram S t) ∈ Φ.levi D.sp.cm (AF D.host.F) P := by
  first | exact @GlobalTheory.LeviAt.embAt_projAt_mem_levi | exact GlobalTheory.LeviAt.embAt_projAt_mem_levi | (intros; apply GlobalTheory.LeviAt.embAt_projAt_mem_levi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieFirstOfLieSecond
section
open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

open NumberField MvPolynomial Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.RealLift.LieFirstPf

variable {P Q R S : ℕ}

def swapE (P Q R S : ℕ) : Formalism.BasicNotions.TH.Pol R S P Q ≃ₗ[ℂ] Formalism.BasicNotions.TH.Pol P Q R S :=
  (renameEquiv ℂ (Equiv.prodComm (Ix R S) (Ix P Q))).toLinearEquiv

theorem swapE_apply (f : Formalism.BasicNotions.TH.Pol R S P Q) : swapE P Q R S f = rename Prod.swap f := rfl

theorem lineSign_swap (a : Ix P Q) (b : Ix R S) :
    lineSign (p := R) (q := S) (r := P) (s := Q) b a = lineSign (p := P) (q := Q) (r := R) (s := S) a b := by
  rcases a with a | a <;> rcases b with b | b <;> rfl

theorem swapE_heisOp (c : Matrix (Ix R S) (Ix P Q) ℂ) (f : Formalism.BasicNotions.TH.Pol R S P Q) :
    swapE P Q R S (heisOp c f) = heisOp cᵀ (swapE P Q R S f) := by
  simp only [heisOp, swapE_apply, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.sub_apply,
    map_smul, map_sum, map_sub, GlobalTheory.FockSwap.rename_raiB, GlobalTheory.FockSwap.rename_lowB]
  congr 1
  refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun l => ?_
  simp [lineSign_swap]

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def swapT (ι : Type) (P Q R S : ℕ) :
    (⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol R S P Q) ≃ₗ[ℂ] ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S :=
  PiTensorProduct.congr fun _ => swapE P Q R S

theorem swapT_atPl (w : ι) (L' : Module.End ℂ (Formalism.BasicNotions.TH.Pol R S P Q)) (L : Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S))
    (h : ∀ f, swapE P Q R S (L' f) = L (swapE P Q R S f)) (T : ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol R S P Q) :
    swapT ι P Q R S (atPl w L' T) = atPl w L (swapT ι P Q R S T) := by
  have e : (swapT ι P Q R S).toLinearMap ∘ₗ atPl w L' = atPl w L ∘ₗ (swapT ι P Q R S).toLinearMap := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, atPl, swapT,
      PiTensorProduct.map_tprod, PiTensorProduct.congr_tprod]
    congr 1
    funext i
    by_cases hi : i = w
    · subst hi; simp [h]
    · simp [Function.update_of_ne hi]
  exact LinearMap.congr_fun e T

theorem swapT_sumPl (L' : ι → Module.End ℂ (Formalism.BasicNotions.TH.Pol R S P Q)) (L : ι → Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S))
    (h : ∀ w f, swapE P Q R S (L' w f) = L w (swapE P Q R S f)) (T : ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol R S P Q) :
    swapT ι P Q R S (sumPl L' T) = sumPl L (swapT ι P Q R S T) := by
  simp only [sumPl, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun w _ => swapT_atPl w (L' w) (L w) (h w) T

end Tensor

open scoped Classical in

theorem lieFirst_of_lieSecond : LieSecond → LieFirst := by
  intro h2 F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d d' a b A C Φ om χ m hCM hψ hfr hΦ hdd hW hm
  have hfr' : Framed τ JB JA b a C A := ⟨by rw [mul_comm]; exact hfr.1, hfr.2.2, hfr.2.1⟩
  have hΦ' : IsFockMap ψ τ d' C A (Φ ∘ₗ (swapT (InfinitePlace F) P Q R S).toLinearMap) := by
    refine ⟨hΦ.1.comp (swapT (InfinitePlace F) P Q R S).injective, fun u hu c hc T => ?_⟩
    have hu' : At (evI F) uᵀ := fun x hx => by rw [← Matrix.transpose_smul, hu x hx, Matrix.transpose_zero]
    have hc' : ∀ w, uᵀ.map (piInf (τ w)) = A w * (c w)ᵀ * (C w)ᵀ := fun w => by
      rw [Matrix.transpose_map, hc w]; simp [Matrix.transpose_mul, Matrix.mul_assoc]
    have key := hΦ.2 uᵀ hu' (fun w => (c w)ᵀ) hc' (swapT (InfinitePlace F) P Q R S T)
    have hr : ∀ t : ℝ, d'.rho ψ (realAd F t • u) = d.rho ψ (realAd F t • uᵀ) := fun t => by
      show schr ψ (d'.e _) = schr ψ (d.e _)
      rw [← hdd, Matrix.transpose_smul, Matrix.transpose_transpose]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hr]
    rwa [swapT_sumPl (fun w => heisOp (c w)) (fun w => heisOp (c w)ᵀ) (fun w f => swapE_heisOp (c w) f)]
  have hA := h2 F E σ β α κ R S P Q ψ τ JB JA d' b a C A _ om χ m hCM hψ hfr' hΦ' hW hm
  intro γ hγ Y hY T
  have key := hA γ hγ Y hY ((swapT (InfinitePlace F) P Q R S).symm T)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at key
  rwa [swapT_sumPl (fun w => fockAct2 R S P Q (Y w) + (((m w : ℂ) / 2) * (Y w).trace) • 1)
    (fun w => fockAct1 P Q R S (Y w) + (((m w : ℂ) / 2) * (Y w).trace) • 1) (fun w f => by
      simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add, map_smul, swapE_apply,
        (GlobalTheory.FockSwap.swap_symmetry R S P Q).2.1]), LinearEquiv.apply_symm_apply] at key

end GlobalTheory.RealLift.LieFirstPf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentOfFiltrationSymbolDetNeZeroStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_of_filtration_symbol_det_ne_zero : ∀ (E A' : Type) [Field E] [AddCommGroup A'] [Module E A'] (r d : ℕ) (I : Fin r → Type) [∀ a, Fintype (I a)] [∀ a, DecidableEq (I a)] (U : ℕ → Submodule E A') (sym : ∀ a : Fin r, U a →ₗ[E] (I a → E)), (∀ a < r, U (a + 1) ≤ U a) → (∀ (a : Fin r) (x : U a), sym a x = 0 ↔ x.1 ∈ U (a + 1)) → ∀ (ix : (Σ a, I a) ↪ Fin d) (J : Finset (Fin d)) (v : Fin d → A') (hv : ∀ q, v (ix q) ∈ U q.1), (∀ k ∈ J, k ∉ Set.range ix ∧ v k ∈ U r) → (∀ a, (Matrix.of fun i i' : I a => sym a ⟨v (ix ⟨a, i'⟩), hv ⟨a, i'⟩⟩ i).det ≠ 0) → LinearIndependent E (fun k : J => v k) → LinearIndependent E fun k : {k // k ∈ Set.range ix ∨ k ∈ J} => v k := by
  first | exact @GlobalTheory.HSShort.linearIndependent_of_symbol_det_ne_zero | exact GlobalTheory.HSShort.linearIndependent_of_symbol_det_ne_zero | (intros; apply GlobalTheory.HSShort.linearIndependent_of_symbol_det_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqRightTranslate
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped NNReal ENNReal

namespace GlobalTheory.SplitFlip

theorem lintegral_mul_invT_sq : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a d : ℕ}
    (Φ : Matrix (Fin a) (Fin d) k → ℂ) (h : GL (Fin d) k),
    ∀ ν : @Measure (Matrix (Fin a) (Fin d) k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
      ∫⁻ Y, ‖Φ (Y * (GlobalTheory.SplitFlip.invT h).1)‖ₑ ^ 2 ∂ν =
        ‖GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet h) (a : ℂ)‖ₑ * ∫⁻ Y, ‖Φ Y‖ₑ ^ 2 ∂ν := by
  intro k _ _ _ _ a d Φ h ν hν
  letI mk : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  letI mM : MeasurableSpace (Matrix (Fin a) (Fin d) k) := borel _
  haveI : BorelSpace (Matrix (Fin a) (Fin d) k) := ⟨rfl⟩
  haveI := hν
  set M : Matrix (Fin d) (Fin d) k := (invT h).1 with hM
  set M' : Matrix (Fin d) (Fin d) k := ((invT h)⁻¹).1
  have hMM' : M * M' = 1 := Units.mul_inv _
  have hM'M : M' * M = 1 := Units.inv_mul _
  let L : Matrix (Fin a) (Fin d) k ≃ᵐ Matrix (Fin a) (Fin d) k :=
    { toFun := fun Y => Y * M
      invFun := fun Y => Y * M'
      left_inv := fun Y => by simp [Matrix.mul_assoc, hMM']
      right_inv := fun Y => by simp [Matrix.mul_assoc, hM'M]
      measurable_toFun := (continuous_id.matrix_mul continuous_const).measurable
      measurable_invFun := (continuous_id.matrix_mul continuous_const).measurable }
  let f0 : Matrix (Fin a) (Fin d) k → (Fin a × Fin d → k) := fun Y p => Y p.1 p.2
  have hEc : Continuous f0 := continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1)
  let g0 : (Fin a × Fin d → k) → Matrix (Fin a) (Fin d) k := fun f => Matrix.of fun i j => f (i, j)
  have hEsc : Continuous g0 :=
    continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)
  let E : Matrix (Fin a) (Fin d) k ≃+ (Fin a × Fin d → k) :=
    { toFun := f0, invFun := g0, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
      map_add' := fun _ _ => rfl }
  let EM : Matrix (Fin a) (Fin d) k ≃ᵐ (Fin a × Fin d → k) :=
    { toFun := f0, invFun := g0, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
      measurable_toFun := hEc.measurable, measurable_invFun := hEsc.measurable }
  haveI hμ : (ν.map E).IsAddHaarMeasure := E.isAddHaarMeasure_map ν hEc hEsc
  let K : Matrix (Fin a × Fin d) (Fin a × Fin d) k := Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin a) (Fin a) k) Mᵀ
  have hK : ∀ Y, K *ᵥ f0 Y = f0 (Y * M) := by
    intro Y; funext p
    simp [K, f0, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply, Matrix.mul_apply, mul_comm]
  have hdetK : K.det = (((gdet h)⁻¹ ^ a : kˣ) : k) := by
    rw [Matrix.det_kronecker, Matrix.det_one, one_pow, one_mul, Matrix.det_transpose, Fintype.card_fin, ← gdet_invT]
    simp [M, gdet]
  have hu : K.det ≠ 0 := by rw [hdetK]; exact Units.ne_zero _
  have hlam : (Measure.addHaar : Measure k).map (fun x => algebraMap k k K.det * x) =
      (distribHaarChar k (gdet h) ^ a) • (Measure.addHaar : Measure k) := by
    have h2 := GlobalTheory.CompanionTheory.SW.DetScale.char_smul_map (Measure.addHaar : Measure k) ((gdet h)⁻¹ ^ a)
    rw [Algebra.algebraMap_self, RingHom.id_apply, hdetK]
    have hcd : distribHaarChar k (gdet h) ^ a * distribHaarChar k ((gdet h)⁻¹ ^ a) = 1 := by
      rw [map_pow, map_inv, ← mul_pow, mul_inv_cancel₀ distribHaarChar_pos.ne', one_pow]
    calc (Measure.addHaar : Measure k).map (fun x => (((gdet h)⁻¹ ^ a : kˣ) : k) * x)
        = (distribHaarChar k (gdet h) ^ a * distribHaarChar k ((gdet h)⁻¹ ^ a)) •
            (Measure.addHaar : Measure k).map (fun x => (((gdet h)⁻¹ ^ a : kˣ) : k) * x) := by rw [hcd, one_smul]
      _ = _ := by rw [mul_smul, h2]
  have h1 := GlobalTheory.CompanionTheory.SW.DetScale.map_mulVec_eq_smul k k (Fin a × Fin d) K hu Measure.addHaar inferInstance _ hlam
    (ν.map E) hμ
  simp only [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] at h1
  have key : ν.map L = (distribHaarChar k (gdet h) ^ a) • ν := by
    apply EM.map_measurableEquiv_injective
    rw [Measure.map_map EM.measurable L.measurable, Measure.map_smul]
    have e1 : (EM ∘ L) = (fun x => K *ᵥ x) ∘ EM := by funext Y; exact (hK Y).symm
    rw [e1, ← Measure.map_map (GlobalTheory.CompanionTheory.SW.DetScale.measurable_mulVec K) EM.measurable]
    exact h1
  have hl := lintegral_map_equiv (fun Y => ‖Φ Y‖ₑ ^ 2) L (μ := ν)
  rw [key] at hl
  refine hl.symm.trans ?_
  rw [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  congr 1
  simp only [apow, GlobalTheory.SplitWeil.nabs, Complex.cpow_natCast, enorm_pow]
  rw [ENNReal.coe_pow]; congr 1; rw [← ofReal_norm_eq_enorm]; simp

end GlobalTheory.SplitFlip
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqSchwartzPosFinite
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem schwartzBruhat_matrix_lintegral_sq_ne_zero_ne_top : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a d : ℕ}
    (Φ : Matrix (Fin a) (Fin d) k → ℂ), Φ ∈ SB (Matrix (Fin a) (Fin d) k) → Φ ≠ 0 →
    ∀ ν : @Measure (Matrix (Fin a) (Fin d) k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
      ∫⁻ Y, ‖Φ Y‖ₑ ^ 2 ∂ν ≠ 0 ∧ ∫⁻ Y, ‖Φ Y‖ₑ ^ 2 ∂ν ≠ ⊤ := by
  intro k _ _ _ _ a d Φ hΦ h0 ν hν
  letI : MeasurableSpace (Matrix (Fin a) (Fin d) k) := borel _
  haveI : BorelSpace (Matrix (Fin a) (Fin d) k) := ⟨rfl⟩
  obtain ⟨hlc, hcs⟩ : IsLocallyConstant Φ ∧ HasCompactSupport Φ := hΦ
  have hc : Continuous Φ := hlc.continuous
  have hcont : Continuous fun Y => ‖Φ Y‖ₑ ^ 2 :=
    (ENNReal.continuous_pow 2).comp hc.enorm
  constructor
  · intro h
    rw [lintegral_eq_zero_iff hcont.measurable] at h
    have h' := (Continuous.ae_eq_iff_eq ν hcont continuous_zero).1 h
    apply h0
    funext Y
    have := congrFun h' Y
    simpa using this
  · obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcs
    have hle : ∫⁻ Y, ‖Φ Y‖ₑ ^ 2 ∂ν ≤
        ∫⁻ Y, (tsupport Φ).indicator (fun _ => ENNReal.ofReal C ^ 2) Y ∂ν := by
      refine lintegral_mono fun Y => ?_
      by_cases hY : Y ∈ tsupport Φ
      · rw [Set.indicator_of_mem hY]
        gcongr
        rw [← ofReal_norm_eq_enorm]
        exact ENNReal.ofReal_le_ofReal (hC Y)
      · simp [image_eq_zero_of_notMem_tsupport hY]
    refine ne_top_of_le_ne_top ?_ hle
    rw [lintegral_indicator_const (isClosed_tsupport Φ).measurableSet]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      (IsCompact.measure_lt_top hcs).ne

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterSmoothUnitary
section
noncomputable section

namespace GlobalTheory.ChrWSmooth

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem continuous_chrW {χ : Chr F E} (hχ : Continuous χ) {v : Pl F} (t : E →ₐ[F] Fv F v) :
    Continuous (chrW χ t) := by
  have hm : Continuous (Units.map (complMap (splitPrime_under t)).toMonoidHom) :=
    Units.continuous_map (GlobalTheory.LFun.SplitChart.continuous_complMap (splitPrime_under t))
  have h1 : Continuous fun x : (Fv F v)ˣ => ((chrW χ t x : ℂˣ) : ℂ) :=
    (continuous_locChar hχ (splitPrime t)).comp hm
  have h2 : Continuous fun x : (Fv F v)ˣ => (((chrW χ t x)⁻¹ : ℂˣ) : ℂ) := by
    have : (fun x : (Fv F v)ˣ => (((chrW χ t x)⁻¹ : ℂˣ) : ℂ)) = fun x => ((chrW χ t x⁻¹ : ℂˣ) : ℂ) := by
      funext x; rw [map_inv]
    rw [this]
    exact h1.comp continuous_inv
  exact Units.continuous_iff.2 ⟨h1, h2⟩

theorem isUnitaryChar_chrW (χ : Chr F E) {v : Pl F} (t : E →ₐ[F] Fv F v) :
    GlobalTheory.SmGL.IsUnitaryChar (chrW χ t) := fun g => by
  show ‖((Circle.toUnits _ : ℂˣ) : ℂ)‖ = 1
  exact Circle.norm_coe _

theorem chrW_nu_smooth_unitary : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ t : E →ₐ[F] Fv F v, GlobalTheory.SmGL.IsSmoothChar (chrW X.ν t) ∧ GlobalTheory.SmGL.IsUnitaryChar (chrW X.ν t) := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hT v _ t
  have hν : Continuous X.ν := by
    show Continuous fun x => X.α x / X.β x
    exact hT.chars.heckeα.1.div' hT.chars.heckeβ.1
  exact ⟨GlobalTheory.RootEx.UniformLattices.isOpen_ker_of_continuous _ (continuous_chrW hν t), isUnitaryChar_chrW _ t⟩

end GlobalTheory.ChrWSmooth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLinearOperatorL2Isometry
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.PolarSB

open MeasureTheory ComplexConjugate

variable {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ]

theorem integrable_mul_conj {f h : X → ℂ} (hf : f ∈ SB X) (hh : h ∈ SB X) :
    Integrable (fun x => f x * conj (h x)) μ := by
  have cf : Continuous f := hf.1.continuous
  have ch : Continuous h := hh.1.continuous
  exact (cf.mul (Complex.continuous_conj.comp ch)).integrable_of_hasCompactSupport
    (hf.2.mul_right)

theorem conj_mem {h : X → ℂ} (hh : h ∈ SB X) : (fun y => conj (h y)) ∈ SB X :=
  ⟨hh.1.comp _, hh.2.comp_left (map_zero _)⟩

theorem self_eq {g : X → ℂ} (hg : g ∈ SB X) :
    ENNReal.ofReal (∫ x, ‖g x‖ ^ 2 ∂μ) = ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ ∧
    (∫ x, g x * conj (g x) ∂μ) = ((∫ x, ‖g x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  have hi : Integrable (fun x => g x * conj (g x)) μ := integrable_mul_conj μ hg hg
  have hn : Integrable (fun x => ‖g x‖ ^ 2) μ := by
    have := hi.norm
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  constructor
  · rw [ofReal_integral_eq_lintegral_ofReal hn (Filter.Eventually.of_forall fun x => by positivity)]
    congr 1; funext x
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  · rw [← integral_complex_ofReal]
    congr 1; funext x
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem expand {f h : X → ℂ} (hf : f ∈ SB X) (hh : h ∈ SB X) (c : ℂ) :
    ∫ x, (c • h + f) x * conj ((c • h + f) x) ∂μ =
      c * conj c * ∫ x, h x * conj (h x) ∂μ + c * ∫ x, h x * conj (f x) ∂μ +
      conj c * ∫ x, f x * conj (h x) ∂μ + ∫ x, f x * conj (f x) ∂μ := by
  have e : (fun x => (c • h + f) x * conj ((c • h + f) x)) =
      fun x => (c * conj c) * (h x * conj (h x)) + c * (h x * conj (f x)) +
        conj c * (f x * conj (h x)) + f x * conj (f x) := by
    funext x; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]; ring
  rw [e, integral_add, integral_add, integral_add, integral_const_mul, integral_const_mul,
    integral_const_mul]
  all_goals first
    | exact integrable_mul_conj μ hf hf
    | exact (integrable_mul_conj μ hh hh).const_mul _
    | exact (integrable_mul_conj μ hh hf).const_mul _
    | exact (integrable_mul_conj μ hf hh).const_mul _
    | exact ((integrable_mul_conj μ hh hh).const_mul _).add ((integrable_mul_conj μ hh hf).const_mul _)
    | exact (((integrable_mul_conj μ hh hh).const_mul _).add
        ((integrable_mul_conj μ hh hf).const_mul _)).add ((integrable_mul_conj μ hf hh).const_mul _)

end GlobalTheory.PolarSB

open MeasureTheory ComplexConjugate in

theorem GlobalTheory.PolarSB.pairing_eq : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl F)
    (T : ((κ → Fv F v) → ℂ) → (κ → Fv F v) → ℂ),
    (∀ φ ∈ SB (κ → Fv F v), T φ ∈ SB (κ → Fv F v)) →
    (∀ φ ∈ SB (κ → Fv F v), ∀ φ' ∈ SB (κ → Fv F v), ∀ c : ℂ, T (c • φ + φ') = c • T φ + T φ') →
    ∀ μ : @MeasureTheory.Measure (κ → Fv F v) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    (∀ φ ∈ SB (κ → Fv F v), ∫⁻ y, ‖T φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ → Fv F v),
      ∫ x, T φ₁ x * starRingEnd ℂ (T (fun y => starRingEnd ℂ (φ₂ y)) x) ∂μ = ∫ x, φ₁ x * φ₂ x ∂μ := by
  intro F _ _ κ _ v T hSB hlin μ hμ hnorm φ₁ h₁ φ₂ h₂
  letI : MeasurableSpace (κ → Fv F v) := borel _
  haveI : BorelSpace (κ → Fv F v) := ⟨rfl⟩
  set w : (κ → Fv F v) → ℂ := fun y => starRingEnd ℂ (φ₂ y) with hw
  have hwSB : w ∈ SB (κ → Fv F v) := GlobalTheory.PolarSB.conj_mem h₂
  have hN : ∀ g ∈ SB (κ → Fv F v),
      ∫ x, T g x * conj (T g x) ∂μ = ∫ x, g x * conj (g x) ∂μ := by
    intro g hg
    obtain ⟨a1, a2⟩ := GlobalTheory.PolarSB.self_eq μ hg
    obtain ⟨b1, b2⟩ := GlobalTheory.PolarSB.self_eq μ (hSB g hg)
    rw [a2, b2]
    congr 1
    have := hnorm g hg
    rw [← a1, ← b1] at this
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun _ => by positivity)
      (integral_nonneg fun _ => by positivity)).1 this
  have key : ∀ c : ℂ,
      c * ∫ x, T w x * conj (T φ₁ x) ∂μ + conj c * ∫ x, T φ₁ x * conj (T w x) ∂μ =
      c * ∫ x, w x * conj (φ₁ x) ∂μ + conj c * ∫ x, φ₁ x * conj (w x) ∂μ := by
    intro c
    have hm : c • w + φ₁ ∈ SB (κ → Fv F v) := add_mem (Submodule.smul_mem _ c hwSB) h₁
    have e1 := hN _ hm
    rw [hlin w hwSB φ₁ h₁ c, GlobalTheory.PolarSB.expand μ h₁ hwSB c,
      GlobalTheory.PolarSB.expand μ (hSB _ h₁) (hSB _ hwSB) c, hN _ h₁, hN _ hwSB] at e1
    linear_combination e1
  have k1 := key 1
  have kI := key Complex.I
  simp only [map_one, one_mul, Complex.conj_I] at k1 kI
  have hfin : ∫ x, T φ₁ x * conj (T w x) ∂μ = ∫ x, φ₁ x * conj (w x) ∂μ := by
    linear_combination (k1 + Complex.I * kI) / 2 +
      (-(∫ x, T w x * conj (T φ₁ x) ∂μ) + ∫ x, T φ₁ x * conj (T w x) ∂μ
        + ∫ x, w x * conj (φ₁ x) ∂μ - ∫ x, φ₁ x * conj (w x) ∂μ) / 2 * Complex.I_sq
  rw [hfin]
  simp [hw]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogEvalSubLeBlockSphereMeanMultidegreeStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_eval_sub_le_blockSphereMean_multidegree : ∀ (B N : ℕ) (a : Fin B → ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (h : MvPolynomial (Fin B × Fin N) ℂ), A.det ≠ 0 → IsMultiHomogeneous a h → ∀ p : Fin B × Fin N → ℂ, (∀ i, frameNorm A (fun j => p (i, j)) = 1) → eval p h ≠ 0 → Real.log ‖eval p h‖ - (∑ i, (a i : ℝ)) * (harmonic (N - 1) : ℝ) / 2 ≤ blockSphereMean B N (linSubst A h) := by
  first | exact @GlobalTheory.LelongBlocksMulti.log_eval_sub_le_blockSphereMean | exact GlobalTheory.LelongBlocksMulti.log_eval_sub_le_blockSphereMean | (intros; apply GlobalTheory.LelongBlocksMulti.log_eval_sub_le_blockSphereMean <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LongWConjApply
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix

namespace GlobalTheory.WhitHered

variable {N c : ℕ} (m : Fin c → ℕ) (hN : ∑ a, m a = N)

theorem sum_rev_eq (hN : ∑ a, m a = N) : ∑ b, m (Fin.revPerm b) = N := by
  rw [← hN]
  exact Equiv.sum_comp Fin.revPerm m

def revPlace : Fin N ≃ Fin N :=
  (stdBlocks (fun b => m (Fin.revPerm b)) (sum_rev_eq m hN)).symm.trans
    ((Equiv.sigmaCongrLeft (β := fun a => Fin (m a)) Fin.revPerm).trans (stdBlocks m hN))

theorem revPlace_apply (b : Fin c) (j : Fin (m (Fin.revPerm b))) :
    revPlace m hN (stdBlocks (fun b => m (Fin.revPerm b)) (sum_rev_eq m hN) ⟨b, j⟩) = stdBlocks m hN ⟨Fin.revPerm b, j⟩ := by
  rw [revPlace, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.trans_apply]
  rfl

variable (k : Type) [Field k]

def longW : GL (Fin N) k := (Matrix.permMatrixHom (R := k)).toHomUnits (revPlace m hN)

theorem longW_apply (i j : Fin N) :
    ((longW m hN k : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j = if i = revPlace m hN j then 1 else 0 := by
  simp only [longW, MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Equiv.Perm.inv_def, Option.mem_def, Option.some.injEq]
  by_cases h : i = revPlace m hN j
  · subst h; simp
  · rw [if_neg h, if_neg]; intro h'; exact h (by rw [← h']; simp)

theorem longW_conj_apply (A : GL (Fin N) k) (i j : Fin N) :
    (((longW m hN k)⁻¹ * A * longW m hN k : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j =
      (A : Matrix (Fin N) (Fin N) k) (revPlace m hN i) (revPlace m hN j) := by
  have hinv : ∀ i j, (((longW m hN k)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j =
      if j = revPlace m hN i then 1 else 0 := by
    intro i j
    simp only [longW, ← map_inv, MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply, inv_inv,
      PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, eq_comm]
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (revPlace m hN j)]
  · rw [longW_apply, if_pos rfl, mul_one, Matrix.mul_apply, Finset.sum_eq_single (revPlace m hN i)]
    · rw [hinv, if_pos rfl, one_mul]
    · intro b _ hb
      rw [hinv, if_neg hb, zero_mul]
    · simp
  · intro b _ hb
    rw [longW_apply, if_neg hb, mul_zero]
  · simp

end GlobalTheory.WhitHered

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialCountsDegreeAndWeightedSumStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monomial_counts_degree_and_weighted_sum : ∀ D T : ℕ, 1 ≤ D → D + 1 ≤ T → (∀ a : ℕ, Nat.card (MonoDeg (Fin D) a) = (a + D - 1).choose (D - 1)) ∧ Nat.card (Σ a : Fin (T - D), MonoDeg (Fin D) a) = (T - 1).choose D ∧ (D + 1) * ∑ a ∈ Finset.range (T - D), (a + D - 1).choose (D - 1) * (T - a) = (T - 1).choose D * (T + D * (D + 1)) := by
  first | exact @GlobalTheory.HSShort.monomial_counts | exact GlobalTheory.HSShort.monomial_counts | (intros; apply GlobalTheory.HSShort.monomial_counts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumConsEqMulOfEffectiveDivisorSuppSectionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.num_cons_eq_mul_of_effective_divisor_supp_section : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), W.Small → ∀ Θ : CartierDiv W.Z, Θ.Eff → (Θ.supp : Set W.Z) = Set.range W.δ → ∃ μ : ℤ, μ ≠ 0 ∧ ∀ y : Fin Y.dim → CartierDiv W.Z, letI := algebraΓOfHom (W.p₁ ≫ Y.str); W.num (Fin.cons Θ y : Fin (Y.dim + 1) → CartierDiv W.Z) = μ * interNumRed F (⟨closure {W.δ (genericPoint Y.X)}, isClosed_closure⟩ : Closeds W.Z) fun i => toLB (y i) := by
  first | exact @GlobalTheory.FlagPush.Dbl.num_cons_eq_mul_of_supp_eq_range | exact GlobalTheory.FlagPush.Dbl.num_cons_eq_mul_of_supp_eq_range | (intros; apply GlobalTheory.FlagPush.Dbl.num_cons_eq_mul_of_supp_eq_range <;> assumption)
end

