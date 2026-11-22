import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1443
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1396
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1451
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1489
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1471
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1445
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1469
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1455
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerLatticeIntegralNonvanishing
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.LagrFormNZ

theorem exists_leftInv {F : Type} [Field F] {κ : Type} [Fintype κ] {r : ℕ} (a : Fin r → κ → F)
    (ha : LinearIndependent F a) : ∃ C : Matrix (Fin r) κ F, ∀ j, C *ᵥ a j = Pi.single j 1 := by
  have hinj : Function.Injective (Fintype.linearCombination F a) :=
    linearIndependent_iff_injective_fintypeLinearCombination.mp ha
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective (Fintype.linearCombination F a)
    (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' L, fun j => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  have := LinearMap.congr_fun hL (Pi.single j 1)
  simpa [Fintype.linearCombination_apply_single] using this

theorem mulVec_sum_eq {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {r : ℕ} (a : Fin r → κ → F)
    (C : Matrix (Fin r) κ F) (hC : ∀ j, C *ᵥ a j = Pi.single j 1) (x : Fin r → AF F) :
    C.map (algebraMap F (AF F)) *ᵥ (∑ j, x j • fun k => algebraMap F (AF F) (a j k)) = x := by
  funext i
  have h1 : ∀ j, (C.map (algebraMap F (AF F)) *ᵥ fun k => algebraMap F (AF F) (a j k)) i =
      algebraMap F (AF F) ((Pi.single j (1 : F) : Fin r → F) i) := fun j => by
    rw [← hC j, RingHom.map_mulVec]; rfl
  rw [Matrix.mulVec_sum, Finset.sum_apply]
  simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, h1]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_apply, Ne.symm hj]
  · simp

end GlobalTheory.LagrFormNZ

namespace GlobalTheory.LagrFormNZ

theorem lagrForm_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (r : ℕ) (u : Fin r → (κ → F) × (κ → F)), LinearIndependent F (fun j => (u j).1) →
    ∀ μ : @Measure (Fin r → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∃ φ ∈ schA F κ, ∫ x, schr ψ (∑ j, x j • ((fun k => algebraMap F (AF F) ((u j).1 k)),
      (fun k => algebraMap F (AF F) ((u j).2 k)))) φ 0 ∂μ ≠ 0 := by
  intro F _ _ ψ hψ κ _ r u hu μ hμ
  letI : MeasurableSpace (Fin r → AF F) := borel _
  haveI : BorelSpace (Fin r → AF F) := ⟨rfl⟩
  haveI := hμ
  obtain ⟨C, hC⟩ := exists_leftInv (fun j => (u j).1) hu
  set U : Fin r → (κ → AF F) × (κ → AF F) := fun j => ((fun k => algebraMap F (AF F) ((u j).1 k)),
    (fun k => algebraMap F (AF F) ((u j).2 k))) with hU
  set Cm : Matrix (Fin r) κ (AF F) := C.map (algebraMap F (AF F)) with hCm
  have hfst : ∀ x : Fin r → AF F, (∑ j, x j • U j).1 = ∑ j, x j • fun k => algebraMap F (AF F) ((u j).1 k) := by
    intro x; simp [U, Prod.fst_sum]
  have hleft : ∀ x : Fin r → AF F, Cm *ᵥ (∑ j, x j • U j).1 = x := fun x => by
    rw [hfst]; exact mulVec_sum_eq (fun j => (u j).1) C hC x
  have hXc : Continuous fun x : Fin r → AF F => ∑ j, x j • U j :=
    continuous_finset_sum _ fun j _ => (continuous_apply j).smul continuous_const
  set H : (Fin r → AF F) → ℂ := fun x => ψ (0 ⬝ᵥ (∑ j, x j • U j).2 +
    ⅟(2 : AF F) * ((∑ j, x j • U j).1 ⬝ᵥ (∑ j, x j • U j).2)) with hH
  have hHc : Continuous H := hψ.1.comp ((continuous_const.dotProduct (continuous_snd.comp hXc)).add
    (continuous_const.mul ((continuous_fst.comp hXc).dotProduct (continuous_snd.comp hXc))))
  set G : (κ → AF F) → ℂ := fun y => H (Cm *ᵥ y) with hGdef
  have hGc : Continuous G := hHc.comp (Continuous.matrix_mulVec continuous_const continuous_id)
  have hG0 : G 0 = 1 := by simp [G, H]
  have hV : {y | 0 < (G y).re} ∈ 𝓝 (0 : κ → AF F) :=
    (isOpen_lt continuous_const (Complex.continuous_re.comp hGc)).mem_nhds (by simp [hG0])
  set e := GlobalTheory.ArchimedeanL2.splitEquiv F κ with he
  have he0 : e.symm (0, 0) = 0 := map_zero e.symm
  have hW : e.symm ⁻¹' {y | 0 < (G y).re} ∈ 𝓝 ((0 : κ → mixedEmbedding.mixedSpace F), (0 : κ → Af F)) := by
    have hV' : {y | 0 < (G y).re} ∈ 𝓝 (e.symm (0, 0)) := by rw [he0]; exact hV
    exact e.symm.continuous.tendsto (0, 0) hV'
  obtain ⟨U1, hU1, U2, hU2, hsub⟩ := mem_nhds_prod_iff.1 hW
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hU1
  obtain ⟨c, hc0, hcs⟩ := GlobalTheory.EvAdm.exists_scaledInt_subset_of_mem_nhds F κ U2 hU2
  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  let f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ :=
    h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hf : ∀ x, f x = ((b x : ℝ) : ℂ) := fun x => rfl
  set S : Set (κ → Af F) := {y | y - 0 ∈ GlobalTheory.EvAdm.scaledInt F κ c} with hS
  set g : (κ → Af F) → ℂ := S.indicator (fun _ => (1 : ℂ)) with hg
  have hgSB : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := GlobalTheory.EvAdm.indicator_coset_scaledInt_mem_SB F κ c hc0 0
  set φ := pureA F f g with hφ
  have hφmem : φ ∈ schA F κ := Submodule.subset_span ⟨f, g, hgSB, rfl⟩
  have hφe : ∀ y, φ y = f (e y).1 * g (e y).2 := fun y => rfl
  refine ⟨φ, hφmem, ?_⟩
  have hφcases : ∀ y, φ y = ((b (e y).1 : ℝ) : ℂ) ∧ (e y).2 ∈ S ∨ φ y = 0 ∧ (e y).2 ∉ S := by
    intro y
    rw [hφe, hf]
    by_cases hq : (e y).2 ∈ S
    · left; simp [g, Set.indicator_of_mem hq, hq]
    · right; simp [g, Set.indicator_of_notMem hq, hq]
  have hφim : ∀ y, (φ y).im = 0 := fun y => by
    rcases hφcases y with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  have hφre : ∀ y, 0 ≤ (φ y).re := fun y => by
    rcases hφcases y with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h, b.nonneg]
  have hφmemK : ∀ y, φ y ≠ 0 → (e y).1 ∈ Metric.ball (0 : κ → mixedEmbedding.mixedSpace F) δ ∧
      (e y).2 ∈ (GlobalTheory.EvAdm.scaledInt F κ c : Set (κ → Af F)) := by
    intro y hy
    rcases hφcases y with ⟨h, hq⟩ | ⟨h, _⟩
    · refine ⟨?_, by simpa [S] using hq⟩
      have : b (e y).1 ≠ 0 := by
        intro h0; apply hy; rw [h, h0]; simp
      have hs : (e y).1 ∈ Function.support b := this
      rw [b.support_eq] at hs
      exact hs
    · exact absurd h hy
  have hφV : ∀ y, φ y ≠ 0 → 0 < (G y).re := by
    intro y hy
    obtain ⟨h1, h2⟩ := hφmemK y hy
    have : e y ∈ U1 ×ˢ U2 := ⟨hball h1, hcs h2⟩
    have := hsub this
    simpa using this
  have hφ0 : φ 0 = 1 := by
    have e0 : e 0 = (0, 0) := map_zero e
    rw [hφe, e0, hf]
    have hb : b 0 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self (half_pos hδ).le)
    have h0S : (0 : κ → Af F) ∈ S := by simp [S]
    simp [g, Set.indicator_of_mem h0S, hb]
  have hφc : Continuous φ := by
    have hg : Continuous g := hgSB.1.continuous
    exact (f.continuous.comp (continuous_fst.comp e.continuous)).mul (hg.comp (continuous_snd.comp e.continuous))
  set I : (Fin r → AF F) → ℂ := fun x => schr ψ (∑ j, x j • U j) φ 0 with hIdef
  have hI : ∀ x, I x = G (∑ j, x j • U j).1 * φ (∑ j, x j • U j).1 := by
    intro x
    show ψ _ * φ (0 + _) = H (Cm *ᵥ _) * _
    rw [hleft, zero_add]
  have hIc : Continuous I := by
    have : I = fun x => G (∑ j, x j • U j).1 * φ (∑ j, x j • U j).1 := funext hI
    rw [this]
    exact (hGc.comp (continuous_fst.comp hXc)).mul (hφc.comp (continuous_fst.comp hXc))

  set K : Set ((κ → mixedEmbedding.mixedSpace F) × (κ → Af F)) :=
    Metric.closedBall 0 δ ×ˢ (GlobalTheory.EvAdm.scaledInt F κ c : Set (κ → Af F)) with hK
  have hKc : IsCompact K := (isCompact_closedBall _ _).prod (GlobalTheory.EvAdm.isCompact_scaledInt_of_ne_zero hc0)
  have hKcl : IsClosed K := Metric.isClosed_closedBall.prod
    ((GlobalTheory.EvAdm.scaledInt F κ c).isClosed_of_isOpen (GlobalTheory.EvAdm.isOpen_scaledInt c))
  set T : Set (Fin r → AF F) := {x | e (∑ j, x j • U j).1 ∈ K} with hT
  have hTcl : IsClosed T := hKcl.preimage (e.continuous.comp (continuous_fst.comp hXc))
  have hTsub : T ⊆ (fun p => Cm *ᵥ e.symm p) '' K := by
    intro x hx
    exact ⟨_, hx, by simp only [e.symm_apply_apply, hleft]⟩
  have hes : Continuous (e.symm : _ → _) := e.symm.continuous
  have hcm : Continuous fun p => Cm *ᵥ e.symm p := Continuous.matrix_mulVec continuous_const hes
  have hTc : IsCompact T := (hKc.image hcm).of_isClosed_subset hTcl hTsub
  have hsupp : Function.support I ⊆ T := by
    intro x hx
    have hne : φ (∑ j, x j • U j).1 ≠ 0 := by
      intro h0; apply hx; rw [hI, h0, mul_zero]
    obtain ⟨h1, h2⟩ := hφmemK _ hne
    exact ⟨Metric.ball_subset_closedBall h1, h2⟩
  have hIcs : HasCompactSupport I := hTc.of_isClosed_subset (isClosed_tsupport I) (closure_minimal hsupp hTcl)
  have hIint : Integrable I μ := hIc.integrable_of_hasCompactSupport hIcs
  have hre : ∀ x, (I x).re = (G (∑ j, x j • U j).1).re * (φ (∑ j, x j • U j).1).re := by
    intro x; rw [hI, Complex.mul_re, hφim, mul_zero, sub_zero]
  have hnn : 0 ≤ fun x => (I x).re := by
    intro x
    show 0 ≤ (I x).re
    rw [hre]
    by_cases h0 : φ (∑ j, x j • U j).1 = 0
    · simp [h0]
    · exact mul_nonneg (hφV _ h0).le (hφre _)
  have hI0 : (I 0).re = 1 := by
    rw [hre]
    have : (∑ j, (0 : Fin r → AF F) j • U j).1 = 0 := by simp
    rw [this, hG0, hφ0]; simp
  have hpos : 0 < ∫ x, (I x).re ∂μ := by
    rw [integral_pos_iff_support_of_nonneg hnn hIint.re]
    exact (Complex.continuous_re.comp hIc).isOpen_support.measure_pos μ ⟨0, by simp [Function.mem_support, hI0]⟩
  intro hzero
  have := integral_re hIint
  change ∫ x, (I x).re ∂μ = (∫ x, I x ∂μ).re at this
  rw [show (∫ x, I x ∂μ) = 0 from hzero, Complex.zero_re] at this
  exact hpos.ne' this

end GlobalTheory.LagrFormNZ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesSchwartzReal
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch

namespace GlobalTheory.SchOp

theorem iteratedDeriv_cexp_real (a : ℂ) (n : ℕ) :
    iteratedDeriv n (fun y : ℝ => Complex.exp (a * y)) = fun y : ℝ => a ^ n * Complex.exp (a * y) := by
  induction n with
  | zero => funext y; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := by
      simpa using (hasDerivAt_id y).ofReal_comp
    have h : HasDerivAt (fun y : ℝ => a ^ n * Complex.exp (a * y)) (a ^ n * (Complex.exp (a * y) * (a * 1))) y :=
      ((h1.const_mul a).cexp).const_mul (a ^ n)
    rw [h.deriv]; ring

theorem hasTemperateGrowth_ech : Function.HasTemperateGrowth ech := by
  set a : ℂ := -(2 * Real.pi * Complex.I) with ha
  have e : ech = fun y : ℝ => Complex.exp (a * y) := rfl
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => Complex.exp (a * y)) :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  refine ⟨by rw [e]; exact hc, fun n => ⟨0, ‖a‖ ^ n, fun x => ?_⟩⟩
  rw [e, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_cexp_real, pow_zero, mul_one, norm_mul, norm_pow]
  have h1 : ‖Complex.exp (a * x)‖ = 1 := by
    have : a * (x : ℂ) = ((-(2 * Real.pi * x) : ℝ) : ℂ) * Complex.I := by rw [ha]; push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  rw [h1, mul_one]

theorem hasTemperateGrowth_ech_affine {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : Y →L[ℝ] ℝ) (c : ℝ) : Function.HasTemperateGrowth (fun x : Y => ech (L x + c)) :=
  hasTemperateGrowth_ech.comp (L.hasTemperateGrowth.add (Function.HasTemperateGrowth.const c))

theorem sch_schwartz {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (β : LinearMap.BilinForm ℝ Y) (a b : Y) (f : SchwartzMap Y ℂ) : ∃ g : SchwartzMap Y ℂ, ⇑g = sch β a b ⇑f := by
  let L : Y →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (β.flip b)
  have hL : ∀ x, L x = β x b := fun x => rfl
  have hm : Function.HasTemperateGrowth (fun x : Y => ech (β x b + β a b / 2)) := by
    simpa only [hL] using hasTemperateGrowth_ech_affine L (β a b / 2)
  have ht : Function.HasTemperateGrowth (fun x : Y => x + a) :=
    Function.HasTemperateGrowth.id'.add (Function.HasTemperateGrowth.const a)
  have hu : ∃ (k : ℕ) (C : ℝ), ∀ x : Y, ‖x‖ ≤ C * (1 + ‖x + a‖) ^ k := by
    refine ⟨1, 1 + ‖a‖, fun x => ?_⟩
    have h1 : ‖x‖ ≤ ‖x + a‖ + ‖a‖ := by
      calc ‖x‖ = ‖(x + a) - a‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖x + a‖ + ‖a‖ := norm_sub_le _ _
    have h2 := norm_nonneg (x + a)
    have h3 := norm_nonneg a
    rw [pow_one]
    nlinarith
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun x : Y => ech (β x b + β a b / 2)) (SchwartzMap.compCLM ℂ ht hu f), ?_⟩
  funext x
  rw [SchwartzMap.smulLeftCLM_apply_apply hm, SchwartzMap.compCLM_apply]
  simp [sch, smul_eq_mul]

end GlobalTheory.SchOp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzAdelicSliceSmooth
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.FinComm GlobalTheory.VacLine

namespace GlobalTheory.VacLine

theorem slice_schA : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (Ψ : (κ → AF F) → ℂ), Ψ ∈ schA F κ →
    (∀ y : κ → Af F, ∃ f : SInf F κ, ∀ x, slice Ψ x y = f x) ∧ ∀ x, slice Ψ x ∈ SB (κ → Af F) := by
  intro F _ _ κ _ Ψ hΨ
  induction hΨ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    have key : ∀ x y, slice (pureA F f g) x y = f x * g y := by
      intro x y
      simp only [slice, pureA, mkPt, RingEquiv.apply_symm_apply]
    refine ⟨fun y => ⟨g y • f, fun x => ?_⟩, fun x => ?_⟩
    · rw [key, SchwartzMap.smul_apply, smul_eq_mul, mul_comm]
    · have : slice (pureA F f g) x = f x • g := by
        funext y; rw [key]; rfl
      rw [this]
      exact Submodule.smul_mem _ _ hg
  | zero =>
    refine ⟨fun y => ⟨0, fun x => rfl⟩, fun x => ?_⟩
    exact Submodule.zero_mem _
  | add Φ Φ' _ _ h h' =>
    refine ⟨fun y => ?_, fun x => ?_⟩
    · obtain ⟨f, hf⟩ := h.1 y
      obtain ⟨f', hf'⟩ := h'.1 y
      exact ⟨f + f', fun x => by
        show slice Φ x y + slice Φ' x y = (f + f') x
        rw [hf, hf', SchwartzMap.add_apply]⟩
    · have : slice (Φ + Φ') x = slice Φ x + slice Φ' x := rfl
      rw [this]
      exact Submodule.add_mem _ (h.2 x) (h'.2 x)
  | smul a Φ _ h =>
    refine ⟨fun y => ?_, fun x => ?_⟩
    · obtain ⟨f, hf⟩ := h.1 y
      exact ⟨a • f, fun x => by
        show a • slice Φ x y = (a • f) x
        rw [hf, SchwartzMap.smul_apply]⟩
    · have : slice (a • Φ) x = a • slice Φ x := rfl
      rw [this]
      exact Submodule.smul_mem _ _ (h.2 x)

end GlobalTheory.VacLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzPolynomialDecayWords
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix
open scoped Classical

noncomputable section
namespace GlobalTheory.SobClass.Weight
open GlobalTheory.SobClass GlobalTheory.ArchUniq.Coord

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem norm_dH_mul {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (i : κ) (e : mixedEmbedding.mixedSpace F)
    (Φ : (κ → AF F) → ℂ) (z : κ → AF F) :
    ‖dH ψ ((0, archInc F (Pi.single i e)) : (κ → AF F) × (κ → AF F)) Φ z‖ =
      2 * Real.pi * |Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (z i) * e)| * ‖Φ z‖ := by
  set T : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (z i) * e) with hT
  set a : κ → AF F := archInc F (Pi.single i e) with ha
  have key : (fun t : ℝ => schr ψ (realAd F t • ((0, a) : (κ → AF F) × (κ → AF F))) Φ z) =
      fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I) * T * t) * Φ z := by
    funext t
    simp only [schr, Prod.smul_fst, Prod.smul_snd, smul_zero, zero_dotProduct, mul_zero, add_zero]
    have hA : At (evI F) (z ⬝ᵥ (realAd F t • a)) := by
      intro u hu
      simp only [dotProduct, smul_eq_mul, Pi.smul_apply, Finset.mul_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      have := at_archInc (Pi.single i e) j u hu
      simp only [smul_eq_mul] at this
      calc _ = z j * realAd F t * (u * archInc F (Pi.single i e) j) := by rw [ha]; ring
        _ = 0 := by rw [this, mul_zero]
    have hE : evI F (z ⬝ᵥ (realAd F t • a)) = t • (evI F (z i) * e) := by
      rw [evI_eq]
      simp only [dotProduct, smul_eq_mul, Pi.smul_apply, map_sum, map_mul, ← evI_eq, evI_realAd, ha, evI_archInc]
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same, Algebra.smul_def]
      ring
    rw [hψ.2.2 _ hA, hE, map_smul, ← hT, smul_eq_mul]
    congr 2
    push_cast
    ring
  have hd : HasDerivAt (fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I) * T * t) * Φ z)
      (Complex.exp (-(2 * Real.pi * Complex.I) * T * ((0 : ℝ) : ℂ)) * (-(2 * Real.pi * Complex.I) * T * 1) * Φ z) 0 :=
    (((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul (-(2 * Real.pi * Complex.I) * T)).cexp).mul_const (Φ z)
  unfold dH
  rw [key, hd.deriv]
  simp [abs_of_pos Real.pi_pos]

variable (F) in
theorem exists_family : ∃ (n : ℕ) (e : Fin n → mixedEmbedding.mixedSpace F) (c : ℝ), 0 ≤ c ∧ (∀ j, ‖e j‖ ≤ 1) ∧
    ∀ x : mixedEmbedding.mixedSpace F, ‖x‖ ≤ c * ∑ j, |Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x * e j)| := by
  let b := Module.finBasis ℝ (mixedEmbedding.mixedSpace F)
  let e : Fin _ → mixedEmbedding.mixedSpace F := fun j => (1 + ‖b j‖)⁻¹ • b j
  have hp : ∀ j, 0 < 1 + ‖b j‖ := fun j => by positivity
  let f : mixedEmbedding.mixedSpace F →ₗ[ℝ] (Fin _ → ℝ) :=
    LinearMap.pi fun j => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) ∘ₗ LinearMap.mulRight ℝ (e j)
  have hf : ∀ x j, f x j = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x * e j) := fun x j => rfl
  have hker : LinearMap.ker f = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun x hx => eq_zero_of_trace x fun y => ?_
    have h1 : ∀ j, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x * b j) = 0 := by
      intro j
      have := hf x j
      rw [hx, Pi.zero_apply, mul_smul_comm, map_smul, smul_eq_mul] at this
      exact (mul_eq_zero.1 this.symm).resolve_left (inv_pos.2 (hp j)).ne'
    rw [← b.sum_repr y, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [mul_smul_comm, map_smul, h1, smul_zero]
  obtain ⟨K, -, hK⟩ := f.exists_antilipschitzWith hker
  refine ⟨_, e, K, K.2, fun j => ?_, fun x => ?_⟩
  · simp only [e]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hp j)), inv_mul_le_iff₀ (hp j)]
    linarith
  · refine (ZeroHomClass.bound_of_antilipschitz f hK x).trans (mul_le_mul_of_nonneg_left ?_ K.2)
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)).2 fun j => ?_
    rw [hf, Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun j => |Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x * e j)|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ j)

theorem weight_le_words : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ N : ℕ, ∃ (L : Finset (List ((κ → AF F) × (κ → AF F)))) (K : ℝ), (∀ l ∈ L, l.length ≤ N ∧ ∀ w ∈ l, IsArchUnit w) ∧ ∀ (Φ : (κ → AF F) → ℂ) (z : κ → AF F), ‖Φ z‖ * (1 + ∑ i, ‖evI F (z i)‖) ^ N ≤ K * ∑ l ∈ L, ‖wordH ψ l Φ z‖ := by
  intro F _ _ κ _ ψ hψ N
  obtain ⟨n, e, c, hc, he, hx⟩ := exists_family F
  let m : κ × Fin n → (κ → AF F) × (κ → AF F) := fun p => (0, archInc F (Pi.single p.1 (e p.2)))
  have hm : ∀ p, IsArchUnit (m p) := fun p => isArchUnit_mul _ fun i => by
    by_cases h : i = p.1
    · subst h; simpa using he p.2
    · simp [h]
  have hw : ∀ (Φ : (κ → AF F) → ℂ) (z : κ → AF F),
      ‖Φ z‖ * ∑ i, ‖evI F (z i)‖ ≤ c * ∑ p, ‖dH ψ (m p) Φ z‖ := by
    intro Φ z
    rw [Fintype.sum_prod_type, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    refine (mul_le_mul_of_nonneg_left (hx _) (norm_nonneg _)).trans ?_
    rw [mul_left_comm, Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) hc
    simp only [m]
    rw [norm_dH_mul hψ]
    have h1 := mul_nonneg (norm_nonneg (Φ z))
      (abs_nonneg (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (z i) * e j)))
    nlinarith [Real.two_le_pi]
  suffices h : ∃ (L : Finset (List ((κ → AF F) × (κ → AF F)))) (K : ℝ), 0 ≤ K ∧
      (∀ l ∈ L, l.length ≤ N ∧ ∀ w ∈ l, IsArchUnit w) ∧ ∀ (Φ : (κ → AF F) → ℂ) (z : κ → AF F),
      ‖Φ z‖ * (1 + ∑ i, ‖evI F (z i)‖) ^ N ≤ K * ∑ l ∈ L, ‖wordH ψ l Φ z‖ by
    obtain ⟨L, K, -, h⟩ := h
    exact ⟨L, K, h⟩
  induction N with
  | zero => exact ⟨{[]}, 1, zero_le_one, by simp, by simp⟩
  | succ N ih =>
    obtain ⟨L, K, hK, hL, h⟩ := ih
    let L' := L ∪ Finset.univ.biUnion fun p => L.image (List.cons (m p))
    refine ⟨L', K * (1 + c * Fintype.card (κ × Fin n)), by positivity, fun l hl => ?_, fun Φ z => ?_⟩
    · rcases Finset.mem_union.1 hl with hl | hl
      · exact ⟨(hL l hl).1.trans (Nat.le_succ _), (hL l hl).2⟩
      · obtain ⟨p, -, hl⟩ := Finset.mem_biUnion.1 hl
        obtain ⟨l, hl', rfl⟩ := Finset.mem_image.1 hl
        refine ⟨by simpa using (hL l hl').1, fun w hw => ?_⟩
        rcases List.mem_cons.1 hw with rfl | hw
        · exact hm p
        · exact (hL l hl').2 w hw
    · set S := ∑ l ∈ L', ‖wordH ψ l Φ z‖ with hS
      have h1 : ∑ l ∈ L, ‖wordH ψ l Φ z‖ ≤ S :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun _ _ _ => norm_nonneg _
      have h2 : ∀ p, ∑ l ∈ L, ‖dH ψ (m p) (wordH ψ l Φ) z‖ ≤ S := by
        intro p
        have := Finset.sum_image (s := L) (g := List.cons (m p)) (f := fun l => ‖wordH ψ l Φ z‖)
          (fun _ _ _ _ h => List.cons_injective h)
        simp only [wordH_cons] at this
        rw [← this]
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun l hl => Finset.mem_union_right _ ?_)
          fun _ _ _ => norm_nonneg _
        exact Finset.mem_biUnion.2 ⟨p, Finset.mem_univ _, hl⟩
      have h3 : (∑ l ∈ L, ‖wordH ψ l Φ z‖) * ∑ i, ‖evI F (z i)‖ ≤ c * (Fintype.card (κ × Fin n) * S) := by
        rw [Finset.sum_mul]
        refine (Finset.sum_le_sum fun l _ => hw (wordH ψ l Φ) z).trans ?_
        rw [← Finset.mul_sum, Finset.sum_comm]
        refine mul_le_mul_of_nonneg_left ((Finset.sum_le_sum fun p _ => h2 p).trans ?_) hc
        simp
      have h0 : 0 ≤ 1 + ∑ i, ‖evI F (z i)‖ := by positivity
      calc _ = (‖Φ z‖ * (1 + ∑ i, ‖evI F (z i)‖) ^ N) * (1 + ∑ i, ‖evI F (z i)‖) := by ring
        _ ≤ (K * ∑ l ∈ L, ‖wordH ψ l Φ z‖) * (1 + ∑ i, ‖evI F (z i)‖) := mul_le_mul_of_nonneg_right (h Φ z) h0
        _ = K * (∑ l ∈ L, ‖wordH ψ l Φ z‖ + (∑ l ∈ L, ‖wordH ψ l Φ z‖) * ∑ i, ‖evI F (z i)‖) := by ring
        _ ≤ K * (S + c * (Fintype.card (κ × Fin n) * S)) := mul_le_mul_of_nonneg_left (add_le_add h1 h3) hK
        _ = _ := by ring

end GlobalTheory.SobClass.Weight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewDeterminantNeZeroFirstSpaceStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skew_determinant_ne_zero_first_space : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), X.IsSkew σ B r s → X.J.det ≠ 0 := by
  first | exact @GlobalTheory.SkewGram.det_ne_zero | exact GlobalTheory.SkewGram.det_ne_zero | (intros; apply GlobalTheory.SkewGram.det_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianNormAdaptedPosStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin GlobalTheory.TorFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skew_hermitian_norm_adapted_pos : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), IsCMExt F E σ → ∀ (d r s : ℕ) (W : Spc F E d), W.IsSkew σ B r s → ∀ (hσ : ∀ x, σ (σ x) = x) (c : E) (hc : c ≠ 0), σ c = -c → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ τ : E →+* ℂ, (star (fun i => τ (H'.x i)) ᵥ* (c • W.J.map σ).map τ) ⬝ᵥ (fun i => τ (H'.x i)) = 0 ∧ (star (fun i => τ (c⁻¹ * H'.y i)) ᵥ* (c • W.J.map σ).map τ) ⬝ᵥ (fun i => τ (c⁻¹ * H'.y i)) = 0 ∧ (star (fun i => τ (H'.x i)) ᵥ* (c • W.J.map σ).map τ) ⬝ᵥ (fun i => τ (c⁻¹ * H'.y i)) = 1 := by
  first | exact @GlobalTheory.TorFinArch.isotropic_dual_plane | exact GlobalTheory.TorFinArch.isotropic_dual_plane | (intros; apply GlobalTheory.TorFinArch.isotropic_dual_plane <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConductStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : Chr F E), IsHecke F E χ →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), IsSmU (chrW χ t) ∧ (∃ e, GlobalTheory.SplitFlip.CondLE (unifAt v) e (chrW χ t)) ∧
      (GlobalTheory.SplitWeil.IsUnram (chrW χ t) ↔ UnrAt χ (splitPrime t)) := by
  first | exact @GlobalTheory.ChrWLocal.chrW_local | exact GlobalTheory.ChrWLocal.chrW_local | (intros; apply GlobalTheory.ChrWLocal.chrW_local <;> assumption)
end

