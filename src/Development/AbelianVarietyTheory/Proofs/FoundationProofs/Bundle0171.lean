import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0089
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0161
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0167
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0157
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0150
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0163
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0131

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeSumPotentialsCocycleEq
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.DictHk

theorem mat_mul {Γ : Subgroup SL(2, ℤ)} (a b : Γ) :
    GlobalTheory.HeckeFamilyMatrices.mat ((a * b : Γ) : SL(2, ℤ)) = GlobalTheory.HeckeFamilyMatrices.mat a * GlobalTheory.HeckeFamilyMatrices.mat b := rfl

theorem mat_mul_inv {Γ : Subgroup SL(2, ℤ)} (a : Γ) :
    GlobalTheory.HeckeFamilyMatrices.mat a * GlobalTheory.HeckeFamilyMatrices.mat ((a⁻¹ : Γ) : SL(2, ℤ)) = 1 := by
  rw [← mat_mul, mul_inv_cancel]; rfl

theorem mat_one {Γ : Subgroup SL(2, ℤ)} : GlobalTheory.HeckeFamilyMatrices.mat ((1 : Γ) : SL(2, ℤ)) = 1 := rfl

theorem cancel_right {Γ : Subgroup SL(2, ℤ)} {A B : Matrix (Fin 2) (Fin 2) ℤ} (a : Γ)
    (h : A * GlobalTheory.HeckeFamilyMatrices.mat a = B * GlobalTheory.HeckeFamilyMatrices.mat a) : A = B := by
  have := congrArg (· * GlobalTheory.HeckeFamilyMatrices.mat ((a⁻¹ : Γ) : SL(2, ℤ))) h
  simpa only [Matrix.mul_assoc, mat_mul_inv, Matrix.mul_one] using this

theorem det_pos {Γ : Subgroup SL(2, ℤ)} {α : Matrix (Fin 2) (Fin 2) ℤ} {ι : Type}
    {δ : ι → Matrix (Fin 2) (Fin 2) ℤ} (hα : 0 < α.det) (hδ : GlobalTheory.HeckeFamilyMatrices.IsDCReps Γ α δ) (i : ι) :
    0 < (δ i).det := by
  obtain ⟨γ₁, γ₂, h⟩ := hδ.1 i
  rw [h, det_mul, det_mul]
  simpa using hα

theorem exists_perm {Γ : Subgroup SL(2, ℤ)} {α : Matrix (Fin 2) (Fin 2) ℤ} {ι : Type} [Fintype ι]
    {δ : ι → Matrix (Fin 2) (Fin 2) ℤ} (hδ : GlobalTheory.HeckeFamilyMatrices.IsDCReps Γ α δ) (γ : Γ) :
    ∃ π : Equiv.Perm ι, ∀ i, ∃ γ' : Γ, δ i * GlobalTheory.HeckeFamilyMatrices.mat γ = GlobalTheory.HeckeFamilyMatrices.mat γ' * δ (π i) := by
  classical
  have hf : ∀ i, ∃ j, ∃ γ' : Γ, δ i * GlobalTheory.HeckeFamilyMatrices.mat γ = GlobalTheory.HeckeFamilyMatrices.mat γ' * δ j := by
    intro i
    obtain ⟨γ₁, γ₂, h⟩ := hδ.1 i
    obtain ⟨j, ⟨γ', h'⟩, -⟩ := hδ.2 γ₁ (γ₂ * γ)
    refine ⟨j, γ', ?_⟩
    rw [h, ← h', mat_mul, Matrix.mul_assoc]
  choose f g hfg using hf
  have hinj : Function.Injective f := by
    intro i i' hii
    obtain ⟨γ₁, γ₂, h⟩ := hδ.1 i
    obtain ⟨k, -, hk⟩ := hδ.2 γ₁ γ₂
    have e1 : i = k := hk i ⟨1, by rw [mat_one, Matrix.one_mul, h]⟩
    have e2 : i' = k := by
      refine hk i' ⟨g i * (g i')⁻¹, ?_⟩
      rw [← h]
      apply cancel_right γ
      rw [hfg i, Matrix.mul_assoc, hfg i', ← hii, ← Matrix.mul_assoc, ← mat_mul, inv_mul_cancel_right]
    rw [e1, e2]
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), fun i => ⟨g i, hfg i⟩⟩

theorem incr {N l w : ℕ} {ι : Type} [Fintype ι] {δ : ι → Matrix (Fin 2) (Fin 2) ℤ}
    (hdet : ∀ i, 0 < (δ i).det) {F : ℂ → MvPolynomial (Fin 2) ℂ} (hF : F ∈ Pot ℂ w (Gam N l))
    (γ : GlobalTheory.HeckeFamilyMatrices.Lev N l) (π : Equiv.Perm ι) (g : ι → GlobalTheory.HeckeFamilyMatrices.Lev N l)
    (hg : ∀ i, δ i * GlobalTheory.HeckeFamilyMatrices.mat γ = GlobalTheory.HeckeFamilyMatrices.mat (g i) * δ (π i)) (z : ℂ) (hz : z ∈ Hs) :
    slP (GlobalTheory.HeckeFamilyMatrices.mat γ) ((∑ i, opP ℂ (δ i) F) (mob (ofSL γ) z)) - (∑ i, opP ℂ (δ i) F) z =
      ∑ i, slP (δ (π i)) (slP (GlobalTheory.HeckeFamilyMatrices.mat (g i)) (F (mob (ofSL (g i)) Complex.I)) - F Complex.I) := by
  obtain ⟨hmem, hmul, -, -, hSL, htoGQ⟩ := GlobalTheory.KZ.mob_laws
  obtain ⟨hslmul, -⟩ := GlobalTheory.KZ.polySlash_laws ℂ
  have hI : Complex.I ∈ Hs := by simp [Hs]
  have h1 : ∀ a : GlobalTheory.HeckeFamilyMatrices.Lev N l, 0 < (GlobalTheory.HeckeFamilyMatrices.mat a).det := fun a => by simp
  simp only [Finset.sum_apply, map_sum]
  rw [← Equiv.sum_comp π (fun i => opP ℂ (δ i) F z), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨p, hp⟩ := hF.2 (g i) (g i).2
  have hz' := hmem (toGQ (δ (π i))) z hz
  rw [hp _ hI, ← hp _ hz']
  simp only [opP, LinearMap.coe_mk, AddHom.coe_mk, map_sub]
  rw [sub_left_inj]
  have hL : mob (toGQ (δ i)) (mob (ofSL γ) z) = mob (toGQ (δ i * GlobalTheory.HeckeFamilyMatrices.mat γ)) z := by
    rw [htoGQ _ _ (hdet i) (h1 γ), hSL, hmul _ _ _ hz]
  have hR : mob (ofSL (g i)) (mob (toGQ (δ (π i))) z) =
      mob (toGQ (GlobalTheory.HeckeFamilyMatrices.mat (g i) * δ (π i))) z := by
    rw [htoGQ _ _ (h1 (g i)) (hdet (π i)), hSL, hmul _ _ _ hz]
  have hs1 := hslmul (δ i) (GlobalTheory.HeckeFamilyMatrices.mat γ) (F (mob (toGQ (δ i * GlobalTheory.HeckeFamilyMatrices.mat γ)) z))
  have hs2 := hslmul (GlobalTheory.HeckeFamilyMatrices.mat (g i)) (δ (π i)) (F (mob (toGQ (GlobalTheory.HeckeFamilyMatrices.mat (g i) * δ (π i))) z))
  rw [hL, hR, ← hs1, ← hs2, hg i]

theorem dict_hk : ∀ (N l w : ℕ) (α : Matrix (Fin 2) (Fin 2) ℤ) (ι : Type) [Fintype ι]
    (δ : ι → Matrix (Fin 2) (Fin 2) ℤ), 0 < N → 0 < l → 0 < α.det →
    GlobalTheory.HeckeFamilyMatrices.IsDCReps (GlobalTheory.HeckeFamilyMatrices.Lev N l) α δ → ∀ F ∈ Pot ℂ w (Gam N l),
    (∑ i, opP ℂ (δ i) F) ∈ Pot ℂ w (Gam N l) ∧
      cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) (∑ i, opP ℂ (δ i) F) =
        GlobalTheory.HeckeFamilyMatrices.hk (GlobalTheory.HeckeFamilyMatrices.Lev N l) w δ (cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F) := by
  intro N l w α ι _ δ _ _ hα hδ F hF
  have hdet := det_pos hα hδ
  obtain ⟨-, -, hslhom, -⟩ := GlobalTheory.KZ.polySlash_laws ℂ
  have hI : Complex.I ∈ Hs := by simp [Hs]
  refine ⟨⟨fun z => ?_, fun γ hγ => ?_⟩, ?_⟩
  · simp only [Finset.sum_apply]
    exact MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => hslhom _ w _ (hF.1 _)
  · obtain ⟨π, hπ⟩ := exists_perm hδ (⟨γ, hγ⟩ : GlobalTheory.HeckeFamilyMatrices.Lev N l)
    choose g hg using hπ
    exact ⟨_, fun z hz => incr hdet hF ⟨γ, hγ⟩ π g hg z hz⟩
  · funext γ
    have hex := exists_perm hδ γ
    simp only [GlobalTheory.HeckeFamilyMatrices.hk, LinearMap.pi_apply, dif_pos hex, LinearMap.sum_apply, Finset.sum_apply,
      LinearMap.comp_apply, LinearMap.proj_apply]
    rw [cocP, incr hdet hF γ hex.choose (fun i => (hex.choose_spec i).choose)
      (fun i => (hex.choose_spec i).choose_spec) _ hI, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(GlobalTheory.T.dehomogeniseBinaryPoly_homogeneous_equiv_slash w).1 _ _ ((hslhom _ w _ (hF.1 _)).sub (hF.1 _))]
    rfl

end GlobalTheory.KZ.DictHk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnImRpowUnitStripBelowOne
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem stripLow_integrableOn_im_rpow : ∀ (s : ℝ), 0 < s →
    IntegrableOn (fun τ : ℍ => τ.im ^ (s + 1)) {τ | τ ∈ strip ∧ τ.im < 1} := by
  intro s hs
  have hmeasIm : Measurable (fun τ : ℍ => τ.im) := UpperHalfPlane.continuous_im.measurable
  have hf : Measurable (fun τ : ℍ => τ.im ^ (s + 1)) := hmeasIm.pow_const _
  have hT : MeasurableSet {τ : ℍ | τ.im < 1} := measurableSet_lt hmeasIm measurable_const
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  set F : ℍ → ENNReal := Set.indicator {τ : ℍ | τ.im < 1} (fun τ => ‖τ.im ^ (s + 1)‖ₑ) with hFdef
  have hFm : Measurable F := hf.enorm.indicator hT
  have h1 : ∫⁻ τ in {τ | τ ∈ strip ∧ τ.im < 1}, ‖τ.im ^ (s + 1)‖ₑ = ∫⁻ τ in strip, F τ := by
    rw [hFdef, lintegral_indicator hT, Measure.restrict_restrict hT]
    congr 2
    ext τ
    simp [and_comm]
  rw [h1, (GlobalTheory.T.unitStrip_integral_eq_iterated).1 F hFm]
  have h2 : ∀ y ∈ Set.Ioi (0:ℝ), (∫⁻ x in Set.Ico (0 : ℝ) 1, F (ofComplex (x + y * Complex.I))) *
      ENNReal.ofReal (1 / y ^ 2) = Set.indicator (Set.Iio 1) (fun y : ℝ => ENNReal.ofReal (y ^ (s - 1))) y := by
    intro y hy
    have hy0 : (0:ℝ) < y := hy
    have him : ∀ x : ℝ, (ofComplex ((x:ℂ) + y * Complex.I)).im = y := by
      intro x
      rw [ofComplex_apply_of_im_pos (by simpa using hy0)]
      simp [UpperHalfPlane.im]
    have hin : ∀ x : ℝ, F (ofComplex ((x:ℂ) + y * Complex.I)) =
        Set.indicator (Set.Iio 1) (fun y : ℝ => ENNReal.ofReal (y ^ (s + 1))) y := by
      intro x
      simp only [hFdef, Set.indicator, Set.mem_setOf_eq, him, Set.mem_Iio]
      split_ifs
      · exact Real.enorm_eq_ofReal (Real.rpow_nonneg hy0.le _)
      · rfl
    simp_rw [hin]
    rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ico]
    simp only [sub_zero, ENNReal.ofReal_one, mul_one]
    by_cases h : y < 1
    · simp only [Set.indicator, Set.mem_Iio, h, if_true]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hy0.le _)]
      congr 1
      have : y ^ (s + 1) = y ^ (s - 1) * y ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hy0]; norm_num; ring_nf
      rw [this]; field_simp
    · simp [Set.indicator, h]
  rw [setLIntegral_congr_fun measurableSet_Ioi h2, lintegral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, Set.Iio_inter_Ioi]
  have hI : IntegrableOn (fun y : ℝ => y ^ (s - 1)) (Set.Ioo 0 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by linarith)
  exact hI.lintegral_lt_top

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralCoprimeSumUnfoldToUnitStrip
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem unfold_strip : ∀ (L : ℕ) (ρ : ℍ → ℝ) (Ψ : ℍ → ℂ) (W : ℤ × ℤ → ℍ → ℂ), Wt L ρ → IntegrableOn Ψ strip → AEStronglyMeasurable Ψ → (∀ γ : SL(2, ℤ), (L : ℤ) ∣ γ 1 0 → ∀ τ, Ψ (γ • τ) = W (γ 1 0, γ 1 1) τ) → ∫ τ : ℍ, (ρ τ : ℂ) * ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, W x.1 τ = ∫ τ in strip, Ψ τ := by
  intro L ρ Ψ W hρ hΨ hΨm hW
  classical
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  haveI : Countable SL(2, ℤ) := inferInstanceAs (Countable {A : Matrix (Fin 2) (Fin 2) ℤ // A.det = 1})
  haveI : Countable (Gamma0 L) := Subtype.countable
  have memΓ : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 L ↔ (L : ℤ) ∣ γ 1 0 := by
    intro γ
    rw [Gamma0_mem]
    exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _
  have hs : MeasurableSet strip := by
    have : strip = (fun τ : ℍ => τ.re) ⁻¹' Set.Ico 0 1 := by
      ext τ; simp [strip]
    rw [this]
    exact UpperHalfPlane.continuous_re.measurable measurableSet_Ico
  set f : ℍ → ℂ := strip.indicator Ψ with hf_def
  have hfi : Integrable f := (integrable_indicator_iff hs).2 hΨ
  have hfm : AEStronglyMeasurable f := hfi.aestronglyMeasurable
  have mp : ∀ γ : SL(2, ℤ), MeasurePreserving (fun τ : ℍ => γ • τ) volume volume := fun γ =>
    measurePreserving_smul ((γ : GL (Fin 2) ℝ)) (volume : Measure ℍ)
  have me : ∀ γ : SL(2, ℤ), MeasurableEmbedding (fun τ : ℍ => γ • τ) := fun γ =>
    (MeasurableEquiv.smul ((γ : GL (Fin 2) ℝ))).measurableEmbedding
  have rowEq : ∀ (γ : SL(2, ℤ)) (a b : ℤ), γ 1 0 = a → γ 1 1 = b → UpperTheory.V.Af.Rs.row γ = ![a, b] := by
    intro γ a b ha hb
    funext i
    fin_cases i
    · simpa [UpperTheory.V.Af.Rs.row] using ha
    · simpa [UpperTheory.V.Af.Rs.row] using hb
  have step1 : ∀ τ : ℍ, ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, W x.1 τ =
      ∑' γ : Gamma0 L, f ((γ : SL(2, ℤ)) • τ) := by
    intro τ
    have key : ∀ x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, ∃ γ : Gamma0 L,
        ((γ : SL(2, ℤ)) 1 0, (γ : SL(2, ℤ)) 1 1) = x.1 ∧ (γ : SL(2, ℤ)) • τ ∈ strip := by
      intro x
      obtain ⟨γ, ⟨hr, hst⟩, -⟩ := UpperTheory.V.Af.Rs.rowBij.2 τ ⟨![x.1.1, x.1.2], by simpa using x.2.1⟩
      have h0 : γ 1 0 = x.1.1 := by simpa [UpperTheory.V.Af.Rs.row] using congrFun hr 0
      have h1 : γ 1 1 = x.1.2 := by simpa [UpperTheory.V.Af.Rs.row] using congrFun hr 1
      refine ⟨⟨γ, (memΓ γ).2 (h0 ▸ x.2.2)⟩, ?_, hst⟩
      simp [h0, h1]
    choose g hg using key
    have ginj : Function.Injective g := by
      intro x y hxy
      apply Subtype.ext
      rw [← (hg x).1, ← (hg y).1, hxy]
    have hsupp : Function.support (fun γ : Gamma0 L => f ((γ : SL(2, ℤ)) • τ)) ⊆ Set.range g := by
      intro γ hγ
      have hin : (γ : SL(2, ℤ)) • τ ∈ strip := by
        by_contra h
        exact hγ (Set.indicator_of_notMem h _)
      have hL : (L : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 := (memΓ γ).1 γ.2
      have hcop : IsCoprime ((γ : SL(2, ℤ)) 1 0) ((γ : SL(2, ℤ)) 1 1) := UpperTheory.V.Af.Rs.rowBij.1 γ
      refine ⟨⟨((γ : SL(2, ℤ)) 1 0, (γ : SL(2, ℤ)) 1 1), hcop, hL⟩, ?_⟩
      set x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1} := ⟨((γ : SL(2, ℤ)) 1 0, (γ : SL(2, ℤ)) 1 1), hcop, hL⟩
      have hx := hg x
      apply Subtype.ext
      exact (UpperTheory.V.Af.Rs.rowBij.2 τ ⟨![x.1.1, x.1.2], by simpa using x.2.1⟩).unique
        ⟨rowEq _ _ _ (congrArg Prod.fst hx.1) (congrArg Prod.snd hx.1), hx.2⟩ ⟨rowEq _ _ _ rfl rfl, hin⟩
    rw [← ginj.tsum_eq hsupp]
    refine tsum_congr fun x => ?_
    have hx := hg x
    have hL : (L : ℤ) ∣ (g x : SL(2, ℤ)) 1 0 := (memΓ _).1 (g x).2
    rw [hf_def, Set.indicator_of_mem hx.2, hW _ hL τ, hx.1]
  have hsum : ∀ τ, HasSum (fun γ : Gamma0 L => ρ ((γ : SL(2, ℤ))⁻¹ • τ)) 1 := fun τ => by
    have := (Equiv.inv (Gamma0 L)).hasSum_iff.mpr (hρ.sum τ)
    simpa [Function.comp_def] using this
  set F : Gamma0 L → ℍ → ℂ := fun γ τ => (ρ τ : ℂ) * f ((γ : SL(2, ℤ)) • τ) with hF
  set G : Gamma0 L → ℍ → ℂ := fun γ τ => (ρ ((γ : SL(2, ℤ))⁻¹ • τ) : ℂ) * f τ with hG
  have hFG : ∀ γ, F γ = fun τ => G γ ((γ : SL(2, ℤ)) • τ) := by
    intro γ; funext τ; simp [hF, hG]
  have Gm : ∀ γ, AEStronglyMeasurable (G γ) := fun γ =>
    ((Complex.measurable_ofReal.comp (hρ.meas.comp (me ((γ : SL(2, ℤ))⁻¹)).measurable)).aestronglyMeasurable).mul hfm
  have Fm : ∀ γ, AEStronglyMeasurable (F γ) := fun γ => by
    rw [hFG γ]
    exact (Gm γ).comp_measurePreserving (mp γ)
  have tot : ∀ τ, ∑' γ : Gamma0 L, ‖G γ τ‖ₑ = ‖f τ‖ₑ := by
    intro τ
    simp only [hG, enorm_mul]
    rw [ENNReal.tsum_mul_right]
    have : ∑' γ : Gamma0 L, ‖((ρ ((γ : SL(2, ℤ))⁻¹ • τ) : ℝ) : ℂ)‖ₑ = 1 := by
      simp_rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg (hρ.nonneg _)]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => hρ.nonneg _) (hsum τ).summable, (hsum τ).tsum_eq,
        ENNReal.ofReal_one]
    rw [this, one_mul]
  have finG : ∑' γ, ∫⁻ τ, ‖G γ τ‖ₑ ≠ ⊤ := by
    rw [← lintegral_tsum (fun γ => (Gm γ).enorm)]
    simp_rw [tot]
    exact hfi.hasFiniteIntegral.ne
  have finF : ∑' γ, ∫⁻ τ, ‖F γ τ‖ₑ ≠ ⊤ := by
    have : ∀ γ, ∫⁻ τ, ‖F γ τ‖ₑ = ∫⁻ τ, ‖G γ τ‖ₑ := fun γ => by
      rw [hFG γ]
      exact (mp γ).lintegral_comp_emb (me γ) (fun τ => ‖G γ τ‖ₑ)
    simp_rw [this]
    exact finG
  calc ∫ τ : ℍ, (ρ τ : ℂ) * ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, W x.1 τ
        = ∫ τ, ∑' γ, F γ τ := by
          congr 1; funext τ; rw [step1 τ, ← tsum_mul_left]
    _ = ∑' γ, ∫ τ, F γ τ := integral_tsum Fm finF
    _ = ∑' γ, ∫ τ, G γ τ := by
          refine tsum_congr fun γ => ?_
          rw [hFG γ]
          exact (mp γ).integral_comp (me γ) (G γ)
    _ = ∫ τ, ∑' γ, G γ τ := (integral_tsum Gm finG).symm
    _ = ∫ τ, f τ := by
          congr 1; funext τ
          simp only [hG]
          rw [tsum_mul_right, ← Complex.ofReal_tsum, (hsum τ).tsum_eq]
          simp
    _ = ∫ τ in strip, Ψ τ := integral_indicator hs

end GlobalTheory.EisM

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeFunctionDivisibleFirstSubstitution
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM Filter Topology
open scoped MatrixGroups Real ComplexConjugate

namespace GlobalTheory

theorem latF_rows_subst : ∀ (N l : ℕ) (ν : DirichletCharacter ℂ N) (φ : ZMod l → ℂ) (a b c d : ℤ),
    (N : ℤ) * a * d - l * b * c = 1 → 0 < N → 0 < l → ∀ y : ℤ × ℤ,
    (if (N : ℤ) ∣ y.1 then latF l (ch ν) φ (y.1 / N * (N * d) - y.2 * (l * c), -(y.1 / N * b) + y.2 * a) else 0) =
      latF (N * l) (fun _ => 1) (fun z => ν (-(c : ZMod N) * ZMod.castHom (Dvd.intro l rfl) (ZMod N) z) *
        φ ((a : ZMod l) * ZMod.castHom (Dvd.intro_left N rfl) (ZMod l) z)) y := by
  intro N l ν φ a b c d hdet hN hl y
  obtain ⟨y1, y2⟩ := y
  have hNz : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hcop : IsCoprime ((N : ℤ) * d) (l : ℤ) := ⟨a, -(b * c), by linear_combination hdet⟩
  simp only [latF]
  by_cases h1 : (N : ℤ) ∣ y1
  · obtain ⟨m, rfl⟩ := h1
    rw [if_pos (dvd_mul_right _ _)]
    have hdiv : (N : ℤ) * m / N = m := Int.mul_ediv_cancel_left m hNz
    simp only [hdiv]
    have key : ((N : ℤ) * l ∣ N * m) ↔ ((l : ℤ) ∣ m) := by
      constructor
      · intro h; exact (mul_dvd_mul_iff_left hNz).mp h
      · intro h; exact mul_dvd_mul_left _ h
    have key2 : ((l : ℤ) ∣ m * (N * d) - y2 * (l * c)) ↔ ((l : ℤ) ∣ m) := by
      constructor
      · intro h
        have h' : (l : ℤ) ∣ m * (N * d) := by
          have := dvd_add h (dvd_mul_of_dvd_right (dvd_mul_right (l:ℤ) c) y2)
          simpa using this
        exact hcop.symm.dvd_of_dvd_mul_right h'
      · intro h
        exact dvd_sub (dvd_mul_of_dvd_left h _) (dvd_mul_of_dvd_right (dvd_mul_right (l:ℤ) c) y2)
    push_cast
    by_cases h2 : (l : ℤ) ∣ m
    · obtain ⟨m2, rfl⟩ := h2
      rw [if_pos ((key2).mpr (dvd_mul_right _ _)), if_pos (key.mpr (dvd_mul_right _ _))]
      have hlz : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne'
      have e1 : (l : ℤ) * m2 * (N * d) - y2 * (l * c) = l * (m2 * N * d - y2 * c) := by ring
      rw [e1, Int.mul_ediv_cancel_left _ hlz]
      simp only [ch, one_mul, map_intCast]
      congr 2
      · push_cast
        simp [mul_comm]
      · push_cast
        simp [mul_comm]
    · rw [if_neg (fun h => h2 (key2.mp h)), if_neg (fun h => h2 (key.mp h))]
  · rw [if_neg h1, if_neg]
    intro h
    push_cast at h
    exact h1 (dvd_trans (dvd_mul_right _ _) h)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalPositivityEulerFactorPrime
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.LocIneq

theorem term_prime_pow (b : ℕ → ℂ) (s : ℝ) (p : ℕ) (hp : p.Prime) (e : ℕ) :
    LSeries.term b ((1 + s : ℝ) : ℂ) (p ^ e) = b (p ^ e) * ((1 / (p : ℝ) ^ (1 + s) : ℝ) : ℂ) ^ e := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hne : p ^ e ≠ 0 := pow_ne_zero _ hp.ne_zero
  rw [LSeries.term_of_ne_zero hne]
  have h1 : ((p ^ e : ℕ) : ℂ) ^ ((1 + s : ℝ) : ℂ) = ((((p : ℝ) ^ (1 + s)) ^ e : ℝ) : ℂ) := by
    rw [show ((p ^ e : ℕ) : ℂ) = (((p ^ e : ℕ) : ℝ) : ℂ) by push_cast; rfl]
    rw [← Complex.ofReal_cpow (Nat.cast_nonneg _)]
    congr 1
    rw [Nat.cast_pow, ← Real.rpow_natCast_mul hp0, mul_comm, Real.rpow_mul_natCast hp0]
  rw [h1, div_eq_mul_inv]
  congr 1
  push_cast
  rw [one_div, inv_pow]

theorem real_term_prime_pow (b : ℕ → ℂ) (s : ℝ) (p : ℕ) (e : ℕ) :
    ‖b (p ^ e)‖ ^ 2 / ((p ^ e : ℕ) : ℝ) ^ (1 + s) = ‖b (p ^ e)‖ ^ 2 * (1 / (p : ℝ) ^ (1 + s)) ^ e := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  rw [Nat.cast_pow, ← Real.rpow_natCast_mul hp0, mul_comm, Real.rpow_mul_natCast hp0, div_eq_mul_inv,
    one_div, inv_pow]

theorem local_positivity_eulerFactor : ∀ (b ω : ℕ → ℂ) (s C : ℝ) (p : ℕ), 0 < s → p.Prime → b 1 = 1 → ‖ω p‖ = 1 → (∀ r : ℕ, b (p ^ (r + 2)) = b p * b (p ^ (r + 1)) - ω p * b (p ^ r)) → (∀ n : ℕ, ‖b n‖ ^ 2 ≤ C * n) → Real.exp (‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s)) ≤ (1 - 1 / (p : ℝ) ^ (1 + s))⁻¹ * ‖∑' e : ℕ, LSeries.term b ((1 + s : ℝ) : ℂ) (p ^ e)‖ ^ 2 * (∑' e : ℕ, ‖b (p ^ e)‖ ^ 2 / ((p ^ e : ℕ) : ℝ) ^ (1 + s)) * (1 - 1 / (p : ℝ) ^ (2 * (1 + s)))⁻¹ := by
  intro b ω s C p hs hp hb1 hω hrec hbd
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hC : 0 ≤ C := by
    have := hbd 1
    rw [hb1] at this
    simp at this
    linarith
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_eq_mul_self (b p ^ 2 - 4 * ω p)
  set x : ℂ := (b p + z) / 2 with hx
  set y : ℂ := (b p - z) / 2 with hy
  have hxy : x + y = b p := by rw [hx, hy]; ring
  have hxy' : x * y = ω p := by rw [hx, hy]; linear_combination (1 / 4 : ℂ) * hz
  have hc0 : b (p ^ 0) = 1 := by simpa using hb1
  have hc1 : b (p ^ 1) = x + y := by rw [pow_one, hxy]
  have hcr : ∀ r, b (p ^ (r + 2)) = (x + y) * b (p ^ (r + 1)) - x * y * b (p ^ r) := by
    intro r; rw [hxy, hxy']; exact hrec r
  have hroots := GlobalTheory.roots_norm_le_of_bounded_two_step_recursion x y (fun r => b (p ^ r))
    (Real.sqrt C) (Real.sqrt p) (Real.sqrt_nonneg _) hc0 hc1 hcr (by
      intro r
      have h := hbd (p ^ r)
      refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
      rw [mul_pow, ← pow_mul, mul_comm r 2, pow_mul, Real.sq_sqrt hC, Real.sq_sqrt hp0.le]
      simpa using h)
  have hP : (p : ℝ) < (p : ℝ) ^ (1 + s) := by
    conv_lhs => rw [← Real.rpow_one (p : ℝ)]
    exact Real.rpow_lt_rpow_of_exponent_lt hp1 (by linarith)
  have hP0 : 0 < (p : ℝ) ^ (1 + s) := by linarith
  have hsq : 1 / (p : ℝ) ^ (2 * (1 + s)) = (1 / (p : ℝ) ^ (1 + s)) ^ 2 := by
    rw [mul_comm, Real.rpow_mul hp0.le, Real.rpow_two, div_pow, one_pow]
  simp only [term_prime_pow b s p hp, real_term_prime_pow b s p, hsq]
  rw [div_eq_mul_one_div (‖1 + b p‖ ^ 2)]
  have hT0 : 0 < 1 / (p : ℝ) ^ (1 + s) := by positivity
  have hpT : p * (1 / (p : ℝ) ^ (1 + s)) < 1 := by
    rw [mul_one_div, div_lt_one hP0]; exact hP
  generalize 1 / (p : ℝ) ^ (1 + s) = T at hT0 hpT ⊢
  have hT1 : T < 1 := by nlinarith
  have hb : ∀ w : ℂ, ‖w‖ ≤ Real.sqrt p → ‖w‖ ^ 2 * T < 1 := by
    intro w hw
    have : ‖w‖ ^ 2 ≤ p := by
      rw [← Real.sq_sqrt hp0.le]
      exact pow_le_pow_left₀ (norm_nonneg _) hw 2
    nlinarith
  have hxT := hb x hroots.1
  have hyT := hb y hroots.2
  obtain ⟨hL, hR⟩ := GlobalTheory.T.twoStepRecursion_localEulerFactors x y (fun r => b (p ^ r)) T hT0.le hT1 hxT hyT hc0 hc1 hcr
  have hI := GlobalTheory.EisM.locineq x y T hT0.le hT1 hxT hyT
  rw [add_assoc, hxy] at hI
  rw [hxy', hω] at hR
  have hR0 : 0 ≤ ∑' r : ℕ, ‖b (p ^ r)‖ ^ 2 * T ^ r := tsum_nonneg fun r => by positivity
  have hLn := congrArg (fun w : ℂ => ‖w‖ ^ 2) hL
  simp only [norm_one, one_pow] at hLn
  rw [norm_mul, mul_pow] at hLn
  have hL0 : 0 ≤ ‖∑' r : ℕ, b (p ^ r) * (T : ℂ) ^ r‖ ^ 2 := by positivity
  generalize (∑' r : ℕ, ‖b (p ^ r)‖ ^ 2 * T ^ r) = R at hR hR0 ⊢
  generalize ‖∑' r : ℕ, b (p ^ r) * (T : ℂ) ^ r‖ ^ 2 = L at hLn hL0 ⊢
  generalize ‖(1 - x * T) * (1 - y * T)‖ ^ 2 = D at hLn hI
  generalize (1 - ‖x‖ ^ 2 * T) * (1 - ‖y‖ ^ 2 * T) * ‖1 - x * conj y * T‖ ^ 2 = E at hR hI
  generalize Real.exp (‖1 + b p‖ ^ 2 * T) = A at hI ⊢
  have h1 : 0 < 1 - T := by linarith
  have h2 : 0 < 1 - T ^ 2 := by nlinarith
  rw [one_pow, one_mul] at hR
  have hK : 0 ≤ (1 - T)⁻¹ * L * R * (1 - T ^ 2)⁻¹ := by positivity
  have hone : ((1 - T) * D * E) * ((1 - T)⁻¹ * L * R * (1 - T ^ 2)⁻¹) = 1 := by
    calc ((1 - T) * D * E) * ((1 - T)⁻¹ * L * R * (1 - T ^ 2)⁻¹)
        = ((1 - T) * (1 - T)⁻¹) * (L * D) * ((R * E) * (1 - T ^ 2)⁻¹) := by ring
      _ = 1 := by rw [hLn, hR, mul_inv_cancel₀ h1.ne', mul_inv_cancel₀ h2.ne']; ring
  have h3 := mul_le_mul_of_nonneg_right hI hK
  rwa [mul_assoc, hone, mul_one, one_mul] at h3

end GlobalTheory.LocIneq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldSlRightAction
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem frac_sl_right_action : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε), (∀ f, T.sl 1 f = f) ∧ ∀ g h f, T.sl (g * h) f = T.sl h (T.sl g f) := by
  intro Ω _ _ _ ε T
  obtain ⟨hext, hcl, -, -⟩ := GlobalTheory.T.fractionField_ext_closure_injective Ω ε T
  obtain ⟨c1, cmul, -, -⟩ := GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob
  refine ⟨fun f => ?_, fun g h f => ?_⟩
  · have e : (T.sl 1 : T.K ≃ₐ[Ω] T.K).toRingEquiv.toRingHom = RingHom.id T.K := by
      apply hext
      intro a
      exact T.sl_io 1 a a (c1 a).symm
    exact congrArg (fun φ : T.K →+* T.K => φ f) e
  · have e : (T.sl (g * h) : T.K ≃ₐ[Ω] T.K).toRingEquiv.toRingHom =
        ((T.sl h : T.K ≃ₐ[Ω] T.K).toRingEquiv.toRingHom).comp ((T.sl g : T.K ≃ₐ[Ω] T.K).toRingEquiv.toRingHom) := by
      apply hext
      intro a
      obtain ⟨a', ha', hga⟩ := hcl g a
      obtain ⟨a'', ha'', hha⟩ := hcl h a'
      have : (a'' : ℍ → ℂ) = cmp (g * h) a := by rw [ha'', ha', cmul]
      simp only [RingHom.comp_apply]
      show T.sl (g * h) (T.io a) = T.sl h (T.sl g (T.io a))
      rw [T.sl_io (g * h) a a'' this, hga, hha]
    exact congrArg (fun φ : T.K →+* T.K => φ f) e

end GlobalTheory.FN
end

