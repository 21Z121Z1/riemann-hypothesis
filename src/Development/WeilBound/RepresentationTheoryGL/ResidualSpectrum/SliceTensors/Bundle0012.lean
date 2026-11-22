import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.TwistedSlicesSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1435
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0011

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.LintegralMulRight
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL
open scoped ENNReal

namespace PositivityTheory.Rg.Rs.SmoothingSquareIntegrable

theorem sq_lintegral_le {Y : Type*} [MeasurableSpace Y] (ρ : Measure Y) {g : Y → ℝ≥0∞} (hg : AEMeasurable g ρ) :
    (∫⁻ y, g y ∂ρ) ^ 2 ≤ ρ Set.univ * ∫⁻ y, g y ^ 2 ∂ρ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ρ Real.HolderConjugate.two_two (f := fun _ => (1 : ℝ≥0∞))
    aemeasurable_const hg
  simp only [ENNReal.one_rpow, lintegral_const] at h
  calc (∫⁻ y, g y ∂ρ) ^ 2 ≤ (ρ Set.univ ^ (1 / 2 : ℝ) * (∫⁻ y, g y ^ (2 : ℝ) ∂ρ) ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
        simpa [Pi.mul_apply] using h
    _ = ρ Set.univ * ∫⁻ y, g y ^ 2 ∂ρ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (_ ^ (1 / 2 : ℝ)), ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

theorem lintegral_sq_lt_top {μ : Measure (GA E N)} [μ.IsHaarMeasure] {φ : GA E N → ℂ}
    (h : MemL2Quotient (latticeGL E N) μ φ) : ∫⁻ x in stdDom (latticeGL E N), ‖φ x‖ₑ ^ 2 ∂μ < ⊤ := by
  have hm := ((memL2_iff_fundamental_domain (isFundamentalDomain_stdDom (latticeGL E N) μ)).1 h).2
  have := hm.2
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top] at this
  simpa using this

theorem lintegral_mul_right {μ : Measure (GA E N)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {φ : GA E N → ℂ}
    (h : MemL2Quotient (latticeGL E N) μ φ) (g : GA E N) :
    ∫⁻ x in stdDom (latticeGL E N), ‖φ (x * g)‖ₑ ^ 2 ∂μ = ∫⁻ x in stdDom (latticeGL E N), ‖φ x‖ₑ ^ 2 ∂μ := by
  have hd := isFundamentalDomain_stdDom (latticeGL E N) μ
  have hm : AEMeasurable (fun q => ‖descend (latticeGL E N) φ q‖ₑ ^ 2) (quotMeasure (latticeGL E N) μ) :=
    h.2.1.enorm.pow_const 2
  have e1 := lintegral_quotMeasure hd (fun q => ‖descend (latticeGL E N) φ q‖ₑ ^ 2)
  have e2 := lintegral_quotMeasure hd (fun q => ‖descend (latticeGL E N) φ (rmul (latticeGL E N) g q)‖ₑ ^ 2)
  simp only [rmul_mk, h.1.descend_mk] at e1 e2
  rw [← e1, ← e2]
  have hp := measurePreserving_rmul (Γ := latticeGL E N) (μ := μ) g
  conv_rhs => rw [← hp.map_eq]
  rw [lintegral_map' (by rwa [hp.map_eq]) (measurable_rmul g).aemeasurable]

theorem memL2_of_smoothing (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (ν : Measure (Lie E N))
    [ν.IsAddHaarMeasure] {α : Lie E N → ℂ} (hα : GlobalTheory.CuspQuot.IsTest (invSet E N) α) {φ : GA E N → ℂ}
    (hc : Continuous φ) (h : MemL2Quotient (latticeGL E N) μ φ) :
    MemL2Quotient (latticeGL E N) μ (GlobalTheory.CuspQuot.smoothing ν α φ) := by
  have hd := isFundamentalDomain_stdDom (latticeGL E N) μ
  have : ProperSpace (Lie E N) := FiniteDimensional.proper ℝ _
  have : SigmaFinite ν := Measure.IsAddHaarMeasure.sigmaFinite ν
  have hl : LeftInv (latticeGL E N) φ := h.1
  have hlS : LeftInv (latticeGL E N) (GlobalTheory.CuspQuot.smoothing ν α φ) := fun γ hγ g => by
    simp only [GlobalTheory.CuspQuot.smoothing, chart, mul_assoc, hl γ hγ]
  have hH : Continuous fun p : GA E N × Lie E N => α p.2 * chart φ p.1 p.2 :=
    GlobalTheory.CuspQuot.continuous_integrand hα hc
  have hmS : AEStronglyMeasurable (GlobalTheory.CuspQuot.smoothing ν α φ) (μ.restrict (stdDom (latticeGL E N))) :=
    (hH.stronglyMeasurable.integral_prod_right' (ν := ν)).aestronglyMeasurable
  set K := tsupport α with hKdef
  have hKν : ν K < ⊤ := hα.2.1.isCompact.measure_lt_top
  have hpt : ∀ x, ‖GlobalTheory.CuspQuot.smoothing ν α φ x‖ₑ ^ 2 ≤ ν K * ∫⁻ y, ‖α y * chart φ x y‖ₑ ^ 2 ∂ν := by
    intro x
    have h1 : ‖GlobalTheory.CuspQuot.smoothing ν α φ x‖ₑ ≤ ∫⁻ y in K, ‖α y * chart φ x y‖ₑ ∂ν := by
      rw [setLIntegral_eq_of_support_subset]
      · exact enorm_integral_le_lintegral_enorm _
      · intro y hy
        by_contra hyK
        apply hy
        simp [image_eq_zero_of_notMem_tsupport hyK]
    have hx : Continuous fun y => α y * chart φ x y := hH.comp (continuous_const.prodMk continuous_id)
    have h2 := sq_lintegral_le (ν.restrict K) (g := fun y => ‖α y * chart φ x y‖ₑ) hx.enorm.aemeasurable
    rw [Measure.restrict_apply_univ] at h2
    calc _ ≤ (∫⁻ y in K, ‖α y * chart φ x y‖ₑ ∂ν) ^ 2 := by gcongr
      _ ≤ ν K * ∫⁻ y in K, ‖α y * chart φ x y‖ₑ ^ 2 ∂ν := h2
      _ ≤ ν K * ∫⁻ y, ‖α y * chart φ x y‖ₑ ^ 2 ∂ν := by gcongr; exact Measure.restrict_le_self
  set I := ∫⁻ x in stdDom (latticeGL E N), ‖φ x‖ₑ ^ 2 ∂μ with hIdef
  have hI : I < ⊤ := lintegral_sq_lt_top h
  have hin : ∀ y, ∫⁻ x in stdDom (latticeGL E N), ‖α y * chart φ x y‖ₑ ^ 2 ∂μ = ‖α y‖ₑ ^ 2 * I := by
    intro y
    by_cases hy : IsUnit (Matrix.of y)
    · simp_rw [chart, dif_pos hy, enorm_mul, mul_pow]
      rw [lintegral_const_mul' _ _ (by simp), lintegral_mul_right h]
    · have : α y = 0 := image_eq_zero_of_notMem_tsupport fun h' => hy (hα.2.2 h')
      simp [this]
  have hα2 : ∫⁻ y, ‖α y‖ₑ ^ 2 ∂ν < ⊤ := by
    have hmα := hα.1.continuous.memLp_of_hasCompactSupport (p := 2) (μ := ν) hα.2.1
    have := hmα.2
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top] at this
    simpa using this
  have hmeas : AEMeasurable (Function.uncurry fun x y => ‖α y * chart φ x y‖ₑ ^ 2)
      ((μ.restrict (stdDom (latticeGL E N))).prod ν) :=
    ((ENNReal.continuous_pow 2).comp hH.enorm).measurable.aemeasurable
  refine (memL2_iff_fundamental_domain hd).2 ⟨hlS, hmS, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  calc ∫⁻ x in stdDom (latticeGL E N), ‖GlobalTheory.CuspQuot.smoothing ν α φ x‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ x in stdDom (latticeGL E N), ν K * ∫⁻ y, ‖α y * chart φ x y‖ₑ ^ 2 ∂ν ∂μ := lintegral_mono hpt
    _ = ν K * ∫⁻ x in stdDom (latticeGL E N), ∫⁻ y, ‖α y * chart φ x y‖ₑ ^ 2 ∂ν ∂μ :=
        lintegral_const_mul' _ _ hKν.ne
    _ = ν K * ∫⁻ y, ∫⁻ x in stdDom (latticeGL E N), ‖α y * chart φ x y‖ₑ ^ 2 ∂μ ∂ν := by
        rw [lintegral_lintegral_swap hmeas]
    _ = ν K * ((∫⁻ y, ‖α y‖ₑ ^ 2 ∂ν) * I) := by
        simp_rw [hin]
        rw [lintegral_mul_const' _ _ hI.ne]
    _ < ⊤ := ENNReal.mul_lt_top hKν (ENNReal.mul_lt_top hα2 hI)

end PositivityTheory.Rg.Rs.SmoothingSquareIntegrable

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMapF
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin
open scoped ContDiff

namespace PositivityTheory.Rg.Rs.InducedTensorMap

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

omit [IsTotallyComplex E] in

theorem F.hasDerivAt_line {a : ℕ} {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : Lie E a → Y}
    (hf : ContDiffAt ℝ ∞ f (oneL E a)) (X : Lie E a) :
    HasDerivAt (fun t : ℝ => f (oneL E a + t • X)) (fderiv ℝ f (oneL E a) X) 0 := by
  have hl : HasDerivAt (fun t : ℝ => oneL E a + t • X) X 0 :=
    (((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (oneL E a)).congr_deriv (one_smul _ _)
  have hd : HasFDerivAt f (fderiv ℝ f (oneL E a)) (oneL E a + (0 : ℝ) • X) := by
    rw [zero_smul, add_zero]
    exact (hf.differentiableAt (by simp)).hasFDerivAt
  exact hd.comp_hasDerivAt (0 : ℝ) hl

theorem lieD_of_expansion {H : GA E (r + s) → ℂ} (hH : H ∈ Sm E (r + s)) {n : ℕ} (K : Fin n → GA E r × GA E s → ℂ)
    (C : Fin n → Lie E (r + s) → ℂ) (b₁ : Lie E (r + s) → GL (Fin r) (Cinf E))
    (b₂ : Lie E (r + s) → GL (Fin s) (Cinf E)) (hC : ∀ j, ContDiffAt ℝ ∞ (C j) (oneL E (r + s)))
    (h₁ : b₁ (oneL E (r + s)) = 1) (h₂ : b₂ (oneL E (r + s)) = 1) (m : GA E r × GA E s)
    (he : chart H (lev (Ad E) r s m) =ᶠ[nhds (oneL E (r + s))]
      fun y => ∑ j, C j y * K j (m.1 * infGL E r (b₁ y), m.2 * infGL E s (b₂ y)))
    (X : Lie E (r + s)) (D : Fin n → ℂ)
    (hD : ∀ j, HasDerivAt (fun t : ℝ => K j (m.1 * infGL E r (b₁ (oneL E (r + s) + t • X)),
      m.2 * infGL E s (b₂ (oneL E (r + s) + t • X)))) (D j) 0) :
    lieD X H (lev (Ad E) r s m) = ∑ j, (fderiv ℝ (C j) (oneL E (r + s)) X * K j m + C j (oneL E (r + s)) * D j) := by
  have l0 : oneL E (r + s) + (0 : ℝ) • X = oneL E (r + s) := by rw [zero_smul, add_zero]
  have hl : HasDerivAt (fun t : ℝ => oneL E (r + s) + t • X) X 0 :=
    (((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (oneL E (r + s))).congr_deriv (one_smul _ _)
  have a1 := F.hasDerivAt_line (contDiffAt_chart hH (lev (Ad E) r s m) isUnit_one) X
  have a2 := HasDerivAt.fun_sum (u := Finset.univ) fun j _ => (F.hasDerivAt_line (hC j) X).mul (hD j)
  have ht : Filter.Tendsto (fun t : ℝ => oneL E (r + s) + t • X) (nhds 0) (nhds (oneL E (r + s))) := by
    have := hl.continuousAt.tendsto
    rwa [l0] at this
  have a3 := a2.congr_of_eventuallyEq (ht.eventually he)
  refine (a1.unique a3).trans (Finset.sum_congr rfl fun j _ => ?_)
  simp only [l0, h₁, h₂, map_one, mul_one]

theorem res_lie {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (H : Good U₁ U₂ f₁ f₂) {F : Sm E (r + s)} (hF : F ∈ indSub U₁ U₂)
    (hK : F ∈ finVec (cptRep E (r + s))) (X : Lie E (r + s)) :
    res 1 (lieD X (ind f₁ f₂ F.1)) = tensOp f₁ f₂ (res 1 (lie E (r + s) X F).1) := by
  obtain ⟨n, G, C, b₁, b₂, hG, hC, hb₁, hb₂, h₁, h₂, e⟩ := exists_expansion hF hK
  have g₁ : (fun t : ℝ => b₁ (oneL E (r + s) + t • X)) 0 = 1 := by simp only [zero_smul, add_zero, h₁]
  have g₂ : (fun t : ℝ => b₂ (oneL E (r + s) + t • X)) 0 = 1 := by simp only [zero_smul, add_zero, h₂]
  choose G' hd₁ hd₂ using fun j => tensOp_deriv H.hf₁ H.hf₂ (fun t : ℝ => b₁ (oneL E (r + s) + t • X))
    (fun t : ℝ => b₂ (oneL E (r + s) + t • X)) _ _ g₁ g₂ (InducedTensorMap.F.hasDerivAt_line hb₁ X) (InducedTensorMap.F.hasDerivAt_line hb₂ X) (hG j)
  have hid : ∀ j, tensOp LinearMap.id LinearMap.id (G j) = G j := fun j => tensOp_id (hG j)
  have eF : ∀ m : GA E r × GA E s, chart F.1 (lev (Ad E) r s m) =ᶠ[nhds (oneL E (r + s))]
      fun y => ∑ j, C j y * G j (m.1 * infGL E r (b₁ y), m.2 * infGL E s (b₂ y)) := by
    intro m
    have := e (good_id H.hU₁ H.hU₂) m
    rw [ind_id H.hU₁ H.hU₂ hF] at this
    simpa only [hid] using this
  have eq1 : res 1 (lie E (r + s) X F).1 =
      ∑ j, (fderiv ℝ (C j) (oneL E (r + s)) X • G j + C j (oneL E (r + s)) • G' j) := by
    funext m
    rw [res_apply, mul_one, lie_apply,
      lieD_of_expansion F.2 G C b₁ b₂ hC h₁ h₂ m (eF m) X (fun j => G' j m) (fun j => hd₁ j m)]
    simp [Finset.sum_apply]
  funext m
  rw [res_apply, mul_one, eq1, map_sum,
    lieD_of_expansion (ind_mem_Sm H hF hK) (fun j => tensOp f₁ f₂ (G j)) C b₁ b₂ hC h₁ h₂ m (e H m) X
      (fun j => tensOp f₁ f₂ (G' j) m) (fun j => hd₂ j m)]
  simp [Finset.sum_apply]

theorem ind_lie {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (H : Good U₁ U₂ f₁ f₂) {F : Sm E (r + s)} (hF : F ∈ indSub U₁ U₂)
    (hK : F ∈ finVec (cptRep E (r + s))) (X : Lie E (r + s)) (hX : lie E (r + s) X F ∈ indSub U₁ U₂) :
    ind f₁ f₂ (lie E (r + s) X F).1 = lieD X (ind f₁ f₂ F.1) := by
  let Gs : Sm E (r + s) := ⟨ind f₁ f₂ F.1, ind_mem_Sm H hF hK⟩
  have hleft : ∀ (u : BlockIx (r + s) r → Ad E) x,
      lieD X (ind f₁ f₂ F.1) (unip u * x) = lieD X (ind f₁ f₂ F.1) x := by
    intro u x
    have e : chart (ind f₁ f₂ F.1) (unip u * x) = chart (ind f₁ f₂ F.1) x := by
      funext y
      unfold chart
      split_ifs with hy
      · rw [mul_assoc, ind_left H hF]
      · rfl
    simp only [lieD, e]
  refine ext_res (ind_left H hX) hleft fun k g => ?_
  obtain ⟨X', hX'⟩ : ∃ X', rt E (r + s) (cf (r + s) k g) * lie E (r + s) X =
      lie E (r + s) X' * rt E (r + s) (cf (r + s) k g) := by
    refine ⟨toL ((Unitary.toUnits k).val * Matrix.of X * ((Unitary.toUnits k)⁻¹).val), ?_⟩
    rw [cf, map_mul, mul_assoc, ← lie_rt_fin, ← mul_assoc, ← mul_assoc]
    exact congrArg (· * _) (GlobalTheory.CapAdInv.rt_lie (Unitary.toUnits k) (Matrix.of X))
  have ec : ∀ ψ : Sm E (r + s), res (cf (r + s) k g) (lie E (r + s) X ψ).1 =
      res 1 (lie E (r + s) X' (rt E (r + s) (cf (r + s) k g) ψ)).1 := fun ψ => funext fun m => by
    have := congrArg (fun f : Module.End ℂ (Sm E (r + s)) => (f ψ).1 (lev (Ad E) r s m * 1)) hX'
    simp only [Module.End.mul_apply, rt_apply, mul_one] at this
    rw [res_apply, res_apply, mul_one]
    exact this
  have hF' : rt E (r + s) (cf (r + s) k g) F ∈ indSub U₁ U₂ := isInd_rt hF k g
  have hK' := finVec_rt hK k g
  have hr : (rt E (r + s) (cf (r + s) k g) Gs).1 = ind f₁ f₂ (rt E (r + s) (cf (r + s) k g) F).1 :=
    funext fun x => (ind_rt H hF k g x).symm
  have h1 : res (cf (r + s) k g) (lieD X (ind f₁ f₂ F.1)) = res (cf (r + s) k g) (lie E (r + s) X Gs).1 := rfl
  have h2 : (lie E (r + s) X' (rt E (r + s) (cf (r + s) k g) Gs)).1 =
      lieD X' (ind f₁ f₂ (rt E (r + s) (cf (r + s) k g) F).1) := by
    rw [← hr]
    rfl
  rw [ind_levi H hX k g, h1, ec Gs, ec F, h2, res_lie H hF' hK' X']

end PositivityTheory.Rg.Rs.InducedTensorMap

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceE
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace PositivityTheory.Rg.Rs.SliceClasses

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem exp_left (hD : Dict) (hT : FinTr) {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (φ : Sm E (r + s)) (hφ : IsAutForm φ)
    (τs : Finset ℝ) (a : ℝ → ℂ) (F : GA E (r + s) → ℂ)
    (hF : ∀ g, F g = ∑ t ∈ τs, a t * An.ctn r φ.1 (aT E (r + s) r t * g))
    (ψ : Sm E r) (hψ : IsAutForm ψ) (m₂ : GA E s) (h : GA E (r + s))
    (hψF : ∀ m₁, ψ.1 m₁ = F (lev (Ad E) r s (m₁, m₂) * h)) :
    ∀ r₁, 0 < r₁ → r₁ < r → ∀ c₁ ∈ Exp r₁ ψ.1, c₁ ∈ Exp r₁ φ.1 := by
  intro r₁ h0 h1 c₁ hc₁
  obtain ⟨F', hF'span, hF'ne, hF'eig⟩ := (E_exp_iff hD ψ hψ h0 h1 c₁).1 hc₁
  refine (E_exp_iff hD φ hφ h0 (by omega) c₁).2 ?_
  have hφc : Continuous φ.1 := GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E _ φ hφ.level
  have hcr₁ : Continuous (An.ctn r₁ φ.1) := E_cont_ctn r₁ hφc hφ.left
  have hset : (Set.range fun t => E_L E (r + s) r₁ t (An.ctn r₁ φ.1)) =
      Set.range fun t : ℝ => fun g => An.ctn r₁ φ.1 (aT E (r + s) r₁ t * g) := rfl
  have hfd := hT E (r + s) φ hφ r₁ h0 (by omega) _ ((hD E (r + s)).2.2.2 φ hφ r₁ h0 (by omega)).1
  rw [← hset] at hfd
  have := hfd
  have key := E_key_left h1 φ hφ τs a F hF ψ.1 m₂ h hψF
  have hP := E_cont_join (E := E) (n := r + s) (S := {r₁, r}) r₁
  set B := E_B (fun b : {x : PPos (r + s) {r₁, r} // ¬ IsTop r₁ x} → Ad E =>
        (parGL (joinPos (r := r₁) 0 b) : GA E (r + s)))
      (fun t (m : GA E r) => aT E (r + s) r t * (lev (Ad E) r s (m, m₂) * h))
      ((E_vol E r r₁)⁻¹ * ((E_vol E (r + s) r)⁻¹ * E_vol E (r + s) r₁)) τs a with hBdef
  have hcs : ∀ w ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) r₁ t (An.ctn r₁ φ.1)), Continuous w := by
    rw [hset]; exact E_cont_span r₁ hcr₁
  have hadd : ∀ v ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) r₁ t (An.ctn r₁ φ.1)),
      ∀ w ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) r₁ t (An.ctn r₁ φ.1)), B (v + w) = B v + B w :=
    fun v hv w hw => E_B_add hP _ _ _ _ (hcs v hv) (hcs w hw)
  have hsm : ∀ (c : ℂ), ∀ w ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) r₁ t (An.ctn r₁ φ.1)),
      B (c • w) = c • B w := fun c w _ => E_B_smul _ _ _ _ _ c w
  have hBL : ∀ (t : ℝ), ∀ w ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) r₁ t (An.ctn r₁ φ.1)),
      B (E_L E (r + s) r₁ t w) = Complex.exp (0 * t) • E_L E r r₁ t (B w) := fun t w _ => by
    rw [hBdef, E_hB_left h1, zero_mul, Complex.exp_zero, one_smul]
  have hF'2 : F' ∈ Submodule.span ℂ (Set.range fun t => E_L E r r₁ t (B (An.ctn r₁ φ.1))) := by
    rw [← key]; exact hF'span
  have hF'3 : ∀ t : ℝ, E_L E r r₁ t F' = Complex.exp (c₁ * t) • F' := fun t => by
    funext g; rw [E_L_apply, hF'eig t g]; rfl
  obtain ⟨G, hG, hGne, hGeig⟩ := E_lift (fun t => E_L E (r + s) r₁ t) (fun t => E_L E r r₁ t) constant_term_zero_eq E_LL
    (An.ctn r₁ φ.1) B hadd hsm c₁ 0 hBL F' hF'2 hF'ne hF'3
  refine ⟨G, hset ▸ hG, hGne, fun t g => ?_⟩
  have := congrFun (hGeig t) g
  rw [E_L_apply, add_zero] at this
  exact this

variable {r s : ℕ}

theorem E_G_base {r₂ : ℕ} (hr₂ : 0 < r₂) (φ : Sm E (r + s)) (hφ : IsAutForm φ) (τs : Finset ℝ) (a : ℝ → ℂ)
    (F : GA E (r + s) → ℂ) (hF : ∀ g, F g = ∑ t ∈ τs, a t * An.ctn r φ.1 (aT E (r + s) r t * g)) (c : ℂ)
    (hc : ∀ (t : ℝ) g, F (aT E (r + s) r t * g) = Complex.exp (c * t) * F g) (t : ℝ) (z : GA E (r + s)) :
    E_B (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} → Ad E =>
        (parGL (joinPos (r := r + r₂) 0 b) : GA E (r + s)))
      (fun t (z : GA E (r + s)) => aT E (r + s) r t * z) 1 τs a (An.ctn (r + r₂) φ.1) (aT E (r + s) r t * z) =
    Complex.exp (c * t) * E_B (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} → Ad E =>
        (parGL (joinPos (r := r + r₂) 0 b) : GA E (r + s)))
      (fun t (z : GA E (r + s)) => aT E (r + s) r t * z) 1 τs a (An.ctn (r + r₂) φ.1) z := by
  have hpq : r < r + r₂ := by omega
  have hpos : ∀ x : PPos (r + s) {r, r + r₂}, ¬ IsTop r x → ((x.1.1 : ℕ) < r ↔ (x.1.2 : ℕ) < r) := fun x hx => by
    have := E_pos_bot hpq x hx
    omega
  have hv : (E_vol E (r + s) r)⁻¹ * E_vol E (r + s) (r + r₂) ≠ 0 :=
    mul_ne_zero (inv_ne_zero (E_vol_ne _ _)) (E_vol_ne _ _)
  have key : ∀ z, ∫ b, F (parGL (joinPos (r := r) 0 b) * z)
      ∂(Measure.pi fun _ : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop r x} => boxMeasure E) =
      ((E_vol E (r + s) r)⁻¹ * E_vol E (r + s) (r + r₂)) *
        E_B (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} → Ad E =>
          (parGL (joinPos (r := r + r₂) 0 b) : GA E (r + s)))
        (fun t (z : GA E (r + s)) => aT E (r + s) r t * z) 1 τs a (An.ctn (r + r₂) φ.1) z := by
    intro z
    rw [E_int_right hr₂ φ hφ τs a F hF z]
    simp only [E_B]
    rw [one_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    ring
  have eig : ∫ b, F (parGL (joinPos (r := r) 0 b) * (aT E (r + s) r t * z))
      ∂(Measure.pi fun _ : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop r x} => boxMeasure E) =
      Complex.exp (c * t) * ∫ b, F (parGL (joinPos (r := r) 0 b) * z)
        ∂(Measure.pi fun _ : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop r x} => boxMeasure E) := by
    rw [← integral_const_mul]
    congr 1
    funext b
    rw [← mul_assoc, ← aT_comm_parGL _ _ _ _ hpos, mul_assoc, hc]
  apply mul_left_cancel₀ hv
  rw [← key, mul_left_comm, ← key, eig]

theorem eisenstein_constant_term_span {r₂ : ℕ} (hr₂ : 0 < r₂) (φ : Sm E (r + s)) (hφ : IsAutForm φ) (τs : Finset ℝ) (a : ℝ → ℂ)
    (F : GA E (r + s) → ℂ) (hF : ∀ g, F g = ∑ t ∈ τs, a t * An.ctn r φ.1 (aT E (r + s) r t * g)) (c : ℂ)
    (hc : ∀ (t : ℝ) g, F (aT E (r + s) r t * g) = Complex.exp (c * t) * F g) (t : ℝ) :
    ∀ w ∈ Submodule.span ℂ (Set.range fun u => E_L E (r + s) (r + r₂) u (An.ctn (r + r₂) φ.1)), ∀ z,
      E_B (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} → Ad E =>
          (parGL (joinPos (r := r + r₂) 0 b) : GA E (r + s)))
        (fun t (z : GA E (r + s)) => aT E (r + s) r t * z) 1 τs a w (aT E (r + s) r t * z) =
      Complex.exp (c * t) * E_B (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} → Ad E =>
          (parGL (joinPos (r := r + r₂) 0 b) : GA E (r + s)))
        (fun t (z : GA E (r + s)) => aT E (r + s) r t * z) 1 τs a w z := by
  have hφc : Continuous φ.1 := GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E _ φ hφ.level
  have hcr : Continuous (An.ctn (r + r₂) φ.1) := E_cont_ctn (r + r₂) hφc hφ.left
  have hset : (Set.range fun u => E_L E (r + s) (r + r₂) u (An.ctn (r + r₂) φ.1)) =
      Set.range fun u : ℝ => fun g => An.ctn (r + r₂) φ.1 (aT E (r + s) (r + r₂) u * g) := rfl
  have hcs : ∀ w ∈ Submodule.span ℂ (Set.range fun u => E_L E (r + s) (r + r₂) u (An.ctn (r + r₂) φ.1)),
      Continuous w := by
    rw [hset]; exact E_cont_span _ hcr
  have hP := E_cont_join (E := E) (n := r + s) (S := {r, r + r₂}) (r + r₂)
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, rfl⟩ := hx
    intro z
    rw [E_G_shift hr₂, E_G_shift hr₂, ← mul_assoc, aT_comm, mul_assoc, E_G_base hr₂ φ hφ τs a F hF c hc]
  | zero =>
    intro z
    simp [E_B]
  | add x y hx hy ihx ihy =>
    intro z
    rw [E_B_add hP _ _ _ _ (hcs x hx) (hcs y hy)]
    simp only [Pi.add_apply]
    rw [ihx, ihy, mul_add]
  | smul d x _ ih =>
    intro z
    rw [E_B_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [ih]
    ring

theorem E_key_right {r₂ : ℕ} (hr₂ : 0 < r₂) (φ : Sm E (r + s)) (hφ : IsAutForm φ) (τs : Finset ℝ) (a : ℝ → ℂ)
    (F : GA E (r + s) → ℂ) (hF : ∀ g, F g = ∑ t ∈ τs, a t * An.ctn r φ.1 (aT E (r + s) r t * g))
    (ψ : GA E s → ℂ) (m₁ : GA E r) (h : GA E (r + s)) (hψF : ∀ m₂, ψ m₂ = F (lev (Ad E) r s (m₁, m₂) * h)) :
    An.ctn r₂ ψ = E_B (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} → Ad E =>
        (parGL (joinPos (r := r + r₂) 0 b) : GA E (r + s)))
      (fun t (m : GA E s) => aT E (r + s) r t * (lev (Ad E) r s (m₁, m) * h))
      ((E_vol E s r₂)⁻¹ * ((E_vol E (r + s) r)⁻¹ * E_vol E (r + s) (r + r₂))) τs a (An.ctn (r + r₂) φ.1) := by
  funext m₂
  set y := lev (Ad E) r s (m₁, m₂) * h with hy
  have e2 : ∀ A : UPos s r₂ → Ad E, ψ (unipGL A * m₂) =
      F (parGL (joinPos (r := r) 0 fun q => A ((eR r s r₂ hr₂).symm q)) * y) := by
    intro A
    rw [hψF]
    congr 1
    have e : lev (Ad E) r s (m₁, unipGL A * m₂) = lev (Ad E) r s (1, unipGL A) * lev (Ad E) r s (m₁, m₂) := by
      rw [← map_mul, Prod.mk_mul_mk, one_mul]
    rw [e, lev_unipGL_right r s r₂ hr₂, mul_assoc]
  rw [E_ctn_eq, constantTerm_eq_integral]
  simp only [e2]
  rw [← integral_box_reindex (eR r s r₂ hr₂) (fun b => F (parGL (joinPos (r := r) 0 b) * y)),
    E_int_right hr₂ φ hφ τs a F hF y]
  simp only [E_B]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

theorem exp_right (hD : Dict) (hT : FinTr) {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (φ : Sm E (r + s)) (hφ : IsAutForm φ)
    (τs : Finset ℝ) (a : ℝ → ℂ) (F : GA E (r + s) → ℂ)
    (hF : ∀ g, F g = ∑ t ∈ τs, a t * An.ctn r φ.1 (aT E (r + s) r t * g)) (c : ℂ)
    (hc : ∀ (t : ℝ) g, F (aT E (r + s) r t * g) = Complex.exp (c * t) * F g)
    (ψ : Sm E s) (hψ : IsAutForm ψ) (m₁ : GA E r) (h : GA E (r + s))
    (hψF : ∀ m₂, ψ.1 m₂ = F (lev (Ad E) r s (m₁, m₂) * h)) :
    ∀ r₂, 0 < r₂ → r₂ < s → ∀ c₂ ∈ Exp r₂ ψ.1, c + c₂ ∈ Exp (r + r₂) φ.1 := by
  intro r₂ h0 h1 c₂ hc₂
  obtain ⟨F', hF'span, hF'ne, hF'eig⟩ := (E_exp_iff hD ψ hψ h0 h1 c₂).1 hc₂
  refine (E_exp_iff hD φ hφ (by omega) (by omega) (c + c₂)).2 ?_
  have hφc : Continuous φ.1 := GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E _ φ hφ.level
  have hcr : Continuous (An.ctn (r + r₂) φ.1) := E_cont_ctn (r + r₂) hφc hφ.left
  have hset : (Set.range fun t => E_L E (r + s) (r + r₂) t (An.ctn (r + r₂) φ.1)) =
      Set.range fun t : ℝ => fun g => An.ctn (r + r₂) φ.1 (aT E (r + s) (r + r₂) t * g) := rfl
  have hfd := hT E (r + s) φ hφ (r + r₂) (by omega) (by omega) _
    ((hD E (r + s)).2.2.2 φ hφ (r + r₂) (by omega) (by omega)).1
  rw [← hset] at hfd
  have := hfd
  have key := E_key_right h0 φ hφ τs a F hF ψ.1 m₁ h hψF
  have hP := E_cont_join (E := E) (n := r + s) (S := {r, r + r₂}) (r + r₂)
  set B := E_B (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} → Ad E =>
        (parGL (joinPos (r := r + r₂) 0 b) : GA E (r + s)))
      (fun t (m : GA E s) => aT E (r + s) r t * (lev (Ad E) r s (m₁, m) * h))
      ((E_vol E s r₂)⁻¹ * ((E_vol E (r + s) r)⁻¹ * E_vol E (r + s) (r + r₂))) τs a with hBdef
  have hcs : ∀ w ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) (r + r₂) t (An.ctn (r + r₂) φ.1)),
      Continuous w := by
    rw [hset]; exact E_cont_span (r + r₂) hcr
  have hadd : ∀ v ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) (r + r₂) t (An.ctn (r + r₂) φ.1)),
      ∀ w ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) (r + r₂) t (An.ctn (r + r₂) φ.1)),
      B (v + w) = B v + B w :=
    fun v hv w hw => E_B_add hP _ _ _ _ (hcs v hv) (hcs w hw)
  have hsm : ∀ (d : ℂ), ∀ w ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) (r + r₂) t (An.ctn (r + r₂) φ.1)),
      B (d • w) = d • B w := fun d w _ => E_B_smul _ _ _ _ _ d w
  have hBL : ∀ (t : ℝ), ∀ w ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) (r + r₂) t (An.ctn (r + r₂) φ.1)),
      B (E_L E (r + s) (r + r₂) t w) = Complex.exp (c * t) • E_L E s r₂ t (B w) := fun t w hw => by
    funext m₂
    have eB : ∀ (f : GA E (r + s) → ℂ) (m : GA E s), B f m =
        ((E_vol E s r₂)⁻¹ * ((E_vol E (r + s) r)⁻¹ * E_vol E (r + s) (r + r₂))) *
        E_B (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} → Ad E =>
          (parGL (joinPos (r := r + r₂) 0 b) : GA E (r + s)))
          (fun t (z : GA E (r + s)) => aT E (r + s) r t * z) 1 τs a f (lev (Ad E) r s (m₁, m) * h) := by
      intro f m
      simp only [hBdef, E_B, one_mul]
    rw [Pi.smul_apply, E_L_apply, eB, eB, E_G_shift h0, E_aT_right h1.le, eisenstein_constant_term_span h0 φ hφ τs a F hF c hc t w hw,
      smul_eq_mul]
    ring
  have hF'2 : F' ∈ Submodule.span ℂ (Set.range fun t => E_L E s r₂ t (B (An.ctn (r + r₂) φ.1))) := by
    rw [← key]; exact hF'span
  have hF'3 : ∀ t : ℝ, E_L E s r₂ t F' = Complex.exp (c₂ * t) • F' := fun t => by
    funext g; rw [E_L_apply, hF'eig t g]; rfl
  obtain ⟨G, hG, hGne, hGeig⟩ := E_lift (fun t => E_L E (r + s) (r + r₂) t) (fun t => E_L E s r₂ t) constant_term_zero_eq E_LL
    (An.ctn (r + r₂) φ.1) B hadd hsm c₂ c hBL F' hF'2 hF'ne hF'3
  refine ⟨G, hset ▸ hG, hGne, fun t g => ?_⟩
  have := congrFun (hGeig t) g
  rw [E_L_apply, add_comm c₂ c] at this
  exact this

end PositivityTheory.Rg.Rs.SliceClasses

end
end

