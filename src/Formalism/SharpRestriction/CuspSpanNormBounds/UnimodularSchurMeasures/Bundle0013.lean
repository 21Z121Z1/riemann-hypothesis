import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle0010
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle0011
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle0007
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle0012

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CNDAll
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

theorem cnd_far_deep (C Cq : ℝ) (hC : 1 ≤ C) (hCq : 0 ≤ Cq) (hCC : 16 * Cq ≤ C) :
    ∃ C₁₀ : ℝ, 1 ≤ C₁₀ ∧ ∀ C₁ ≥ C₁₀, ∀ (X : CData) (S : CSize X) (volK : ℝ) (n₀ : ℕ) (A : ℝ), 1 ≤ n₀ → X.HypB n₀ A →
      1 ≤ X.qq → X.FinVol → S.Strata → S.SepStep → S.DeepStepsQ volK C Cq →
      X.FarCount (X.Acnt C₁) (2 * (X.I.n : ℝ) ^ 2) (S.Mod C₁) ∧ ∀ A₁ : ℝ, 1 ≤ A₁ → X.DeepInt A₁ (S.Mod C₁) := by
  obtain ⟨C₁₀, h1, h⟩ := cnd_deepP C Cq hC hCq hCC
  refine ⟨C₁₀, h1, fun C₁ hC₁ X S volK n₀ A hn₀ hX hq hV hst hsep hS => ⟨?_, ?_⟩⟩
  · have hn : 1 ≤ X.I.n := le_trans hn₀ hX.1.1
    exact cnd_far S C₁ hn (cnd_two_le_Y X hn₀ hX) hst (cnd_pack S hn hst hsep)
  · exact h C₁ hC₁ X S volK n₀ A hn₀ hX hq hV hst hS

end Formalism.MainNotions.LeviCoordinates

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CnTwoPowMul
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

theorem cn_two_pow (q : ℕ) : (2 : ℝ≥0∞) ^ q = ENNReal.ofReal ((2 : ℝ) ^ q) := by
  rw [ENNReal.ofReal_pow (by norm_num)]
  simp

theorem cn_two_pow_mul (q : ℕ) {B : ℝ} : (2 : ℝ≥0∞) ^ q * ENNReal.ofReal (B / 2 ^ q) = ENNReal.ofReal B := by
  rw [cn_two_pow, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

theorem cn_two_qq (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) (hn : 5 ≤ X.I.n) : 2 * X.qq + 1 ≤ X.I.n := by
  obtain ⟨-, hq2⟩ := X.qq_spec hX
  by_cases h : X.qq ≤ 2
  · omega
  · nlinarith

theorem cn_prob : ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ Cv Cres : ℝ, 1 ≤ Cv → ∃ n₁ : ℕ, ∀ (X : CData) (S : CSize X) (n₀ : ℕ) (A C₁ : ℝ),
    n₁ ≤ X.I.n → X.HypB n₀ A → cn_tauS X C₁ ≤ 1 / 2 → X.FinVol → S.Strata → S.Density → S.KappaVol Cv →
    cn_ResBound X Cres → X.ProbMod c₂ (S.Mod C₁) := by
  obtain ⟨c₂, hc₂, n₂, hP⟩ := Formalism.HermitianLatticeCounting.Final.S7.probINonzero (1 / 8) (by norm_num)
  refine ⟨c₂, hc₂, fun Cv Cres hCv => ?_⟩
  obtain ⟨n₁, hκ⟩ := cn_kappa_le Cv Cres hCv
  refine ⟨max (max n₁ n₂) 5, fun X S n₀ A C₁ hn hX hts hV hS hD hK hR => ?_⟩
  have hn1 : n₁ ≤ X.I.n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : n₂ ≤ X.I.n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn5 : 5 ≤ X.I.n := le_trans (le_max_right _ _) hn
  obtain ⟨-, hq2⟩ := X.qq_spec hX
  set E : ℝ := Real.exp (-(c₂ * (X.I.n : ℝ) * (X.I.f : ℝ) * Real.log (X.I.n : ℝ))) with hE
  set vol : ℝ := X.I.vol X.μf X.fund with hvol
  have hvol0 : 0 ≤ vol := ENNReal.toReal_nonneg
  have hle : X.μ (S.Mod C₁)ᶜ ≤ ENNReal.ofReal (vol * E) := by
    refine le_trans (S.compl_Mod_le hS hD hts (cn_two_qq X hX hn5)) ?_
    refine le_trans (cn_sum_types_le X.qq _ (ENNReal.ofReal (vol * E / 2 ^ X.qq)) fun J hJ c => ?_) (cn_two_pow_mul _).le
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hJ
    refine ENNReal.ofReal_le_ofReal ?_
    have a1 := hκ X S n₀ A hn1 hX hK hR J c h1 h2
    have a2 := hP X.I.n X.qq J X.I.f hn2 hq2 h1 (one_le_autInst_f X.I)
    have a3 : S.kap J c ≤ E / 2 ^ X.qq := by
      rw [le_div_iff₀ (by positivity)]
      calc S.kap J c * 2 ^ X.qq ≤ Real.exp (-(1 / 8 * (J : ℝ) * (X.I.n : ℝ) * (X.I.f : ℝ) * Real.log (X.I.n : ℝ))) * 2 ^ X.qq := by
            gcongr
        _ = 2 ^ X.qq * Real.exp (-(1 / 8 * (J : ℝ) * (X.I.n : ℝ) * (X.I.f : ℝ) * Real.log (X.I.n : ℝ))) := mul_comm _ _
        _ ≤ E := a2
    calc vol * S.kap J c ≤ vol * (E / 2 ^ X.qq) := mul_le_mul_of_nonneg_left a3 hvol0
      _ = vol * E / 2 ^ X.qq := by ring
  have : IsFiniteMeasure X.μ := ⟨by
    unfold CData.μ
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hV⟩
  have hadd := measureReal_add_measureReal_compl (μ := X.μ) (S.measurableSet_Mod hS C₁)
  have hc : X.μ.real (S.Mod C₁)ᶜ ≤ vol * E :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg hvol0 (Real.exp_pos _).le) hle
  unfold CData.ProbMod
  rw [← hE, ← hvol]
  have hv : vol = X.μ.real Set.univ := X.vol_eq
  nlinarith

theorem cn_near : ∃ cb c₂ : ℝ, 0 < cb ∧ 0 < c₂ ∧ ∀ Cv Cres A C₁ : ℝ, 1 ≤ Cv → 1 ≤ A → 1 ≤ C₁ → ∃ n₁ : ℕ,
    ∀ (X : CData) (S : CSize X) (n₀ : ℕ) (C cε : ℝ), n₁ ≤ X.I.n → 1 ≤ n₀ → X.HypC n₀ A C cb → 1 ≤ X.qq → 0 < cε →
    cε ≤ 1 / 90000 → S.Strata → S.Density → S.KappaVol Cv → cn_ResBound X Cres →
    S.NearCount (Formalism.HermitianLatticeCounting.S7.epsN cε X.I.n X.I.f) (3 * Real.sqrt ((X.I.n : ℝ) * Formalism.HermitianLatticeCounting.S7.epsN cε X.I.n X.I.f)) →
    X.NearStep (Formalism.HermitianLatticeCounting.S7.epsN cε X.I.n X.I.f) c₂ 1 (S.Mod C₁) := by
  obtain ⟨cb, c₂, hcb, hc₂, hT⟩ := Formalism.HermitianLatticeCounting.Final.CuspThresholdCounts.nearTotalAbs (1 / 8) (by norm_num)
  refine ⟨cb, c₂, hcb, hc₂, fun Cv Cres A C₁ hCv hA hC₁ => ?_⟩
  obtain ⟨n₁, hκ⟩ := cn_kappa_le Cv Cres hCv
  obtain ⟨n₂, hT⟩ := hT (2 * C₁) A (by linarith) hA
  refine ⟨max (max n₁ n₂) 5, fun X S n₀ C cε hn hn₀ hXC hq1 hcε hcε2 hS hD hK hR hN => ?_⟩
  have hX := hXC.1
  have hn1 : n₁ ≤ X.I.n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : n₂ ≤ X.I.n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn5 : 5 ≤ X.I.n := le_trans (le_max_right _ _) hn
  obtain ⟨-, hq2⟩ := X.qq_spec hX
  have hY : 2 ≤ cn_Y X := cnd_two_le_Y X hn₀ hX
  have hf := one_le_autInst_f X.I
  obtain ⟨d1, -, -, -⟩ := Formalism.HermitianLatticeCounting.Final.S7.deltaSmall X.I.n X.qq X.I.f cε (by omega) hf hq2 hcε hcε2
  have hp : X.I.IsPosType X.e := hX.1.2.2.2.2.2.2.1.2.2.2.1
  set M : ℝ := fdegAll X.I X.σ X.w * (X.e 1).re with hM
  have hM0 : 0 ≤ M := mul_nonneg X.fdegAll_nonneg (X.e_one_nonneg hp)
  set E : ℝ := Real.exp (-(c₂ * (X.I.n : ℝ) * (X.I.f : ℝ) * Real.log (X.I.n : ℝ))) with hE
  set vol : ℝ := X.I.vol X.μf X.fund with hvol
  have hvol0 : 0 ≤ vol := ENNReal.toReal_nonneg
  have hts0 : 0 < cn_tauS X C₁ := cnd_tauS_pos X C₁ hY
  have hts : cn_tauS X C₁ ≤ 1 / 2 := cnd_tauS_le_half X hC₁ hq1 hY
  have hmain := S.near_le hS hD hN hX hts0 hts (cn_two_qq X hX hn5) (by positivity) d1
  unfold CData.NearStep
  refine le_trans hmain ?_
  have hDs : 1 * E * X.Ds = M * vol * E := by
    unfold CData.Ds AutInst.Dstar
    rw [hM, hvol]
    ring
  rw [← hE, hDs]
  refine le_trans (cn_sum_types_le X.qq _ (ENNReal.ofReal (M * vol * E / 2 ^ X.qq)) fun J hJ c => ?_) (cn_two_pow_mul _).le
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hJ
  have a1 := hκ X S n₀ A hn1 hX hK hR J c h1 h2
  have hjq : ∀ x, c.blocksFun x ≤ X.qq := fun x => by
    have : c.blocksFun x ≤ ∑ y, c.blocksFun y := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
    rw [c.sum_blocksFun] at this
    exact le_trans this h2
  obtain ⟨-, -, a2⟩ := Formalism.HermitianLatticeCounting.Final.NearFarVolumeBounds.logVolumeBound c.length X.qq X.I.f c.blocksFun C₁ (cn_Y X) hC₁ hY hq1 hjq
  have hg1 : (1 : ℝ) ≤ (X.g : ℝ) := by exact_mod_cast hX.1.2.2.2.2.2.2.2.1
  have a3 := hT X.I.n X.qq J c.length X.I.f X.I.rd X.g X.b hn2 hq2 (c.length_pos_of_pos h1) c.length_le h2 hf hXC.2.2.1
    hX.1.2.2.1 hg1 hX.1.2.2.2.2.2.2.2.2.1 (one_le_discriminant_root X.I) hX.1.2.2.2.1 hXC.2.2.2
  set k' : ℝ := Real.exp (-(1 / 8 * (J : ℝ) * (X.I.n : ℝ) * (X.I.f : ℝ) * Real.log (X.I.n : ℝ))) with hk'
  set P : ℝ := ∏ a, (2 * (X.I.f : ℝ) * c.blocksFun a * Real.log (1 / (2 * cn_tauS X C₁))) with hP
  set P' : ℝ := (2 * C₁ * (X.I.f : ℝ) * (X.qq : ℝ) ^ 2 * Real.log (cn_Y X)) ^ c.length with hP'
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun a _ => by
    have : 0 ≤ Real.log (1 / (2 * cn_tauS X C₁)) := Real.log_nonneg (by
      rw [le_div_iff₀ (by positivity)]; linarith)
    positivity
  have hPP : P ≤ P' := a2
  have hk0 : 0 ≤ k' := (Real.exp_pos _).le
  calc ENNReal.ofReal M * (ENNReal.ofReal (vol * S.kap J c) * (2 * ENNReal.ofReal P))
      ≤ ENNReal.ofReal M * (ENNReal.ofReal (vol * k') * (ENNReal.ofReal 2 * ENNReal.ofReal P')) := by
        have e2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
        rw [← e2]
        gcongr
    _ = ENNReal.ofReal (M * (vol * k' * (2 * P'))) := by
        rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hM0]
    _ ≤ ENNReal.ofReal (M * vol * E / 2 ^ X.qq) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have a4 : k' * (2 * P') ≤ E / 2 ^ X.qq := by
          rw [le_div_iff₀ (by positivity)]
          calc k' * (2 * P') * 2 ^ X.qq = 2 ^ X.qq * (2 * k') * P' := by ring
            _ ≤ E := a3
        calc M * (vol * k' * (2 * P')) = M * vol * (k' * (2 * P')) := by ring
          _ ≤ M * vol * (E / 2 ^ X.qq) := mul_le_mul_of_nonneg_left a4 (by positivity)
          _ = _ := by ring

end Formalism.MainNotions.LeviCoordinates

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.FfgZeroOfInt
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexOrder
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def ffg_IsSq {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (σ' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  Nontrivial H ∧ IsURepOn (UJset ε) σ' ∧ IsIrredOn (UJset ε) σ' ∧ IsSqIntOn ε σ'

def ffg_Equiv {n : ℕ} {H' H : Type} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (ε : Fin n → Bool) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H'))
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∃ U : H' ≃ₗᵢ[ℂ] H, ∀ g ∈ UJset ε, ∀ v : H', U (σ' g v) = σ g (U v)

def QOrth : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool),
    (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), ffg_IsSq ε σ' → ∃ d : ℝ, IsFdeg (Formalism.REAL.muG ε) σ' d) ∧
    ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
      (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H'))
      (H'' : Type) [NormedAddCommGroup H''] [InnerProductSpace ℂ H''] [CompleteSpace H'']
      (σ'' : Matrix (Fin n) (Fin n) ℂ → (H'' →L[ℂ] H'')), ffg_IsSq ε σ' → ffg_IsSq ε σ'' → ¬ ffg_Equiv ε σ' σ'' →
      ∀ (a b : H') (a' b' : H''), ∫ g, coefOn σ' a b g * star (coefOn σ'' a' b' g) ∂(Formalism.REAL.muG ε) = 0

def FCharOther (χ : ∀ n : ℕ, (Fin n → ℝ) → ℕ → ℂ) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : H →L[ℂ] H), Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ →
    IsOrthProjOnto E (lowKSub ε lam σ) →
    ∀ Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H), ff_Sph ε σ Ψ → ff_Compr ε E Ψ → ff_Eig ε (χ n lam) Ψ → ff_DSSum ε Ψ →
    ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
      (π' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), ffg_IsSq ε π' → ∀ (x y : H) (a b : H'),
      ∫ g, ⟪x, Ψ (umat g) y⟫_ℂ * star (coefOn π' a b g) ∂(Formalism.REAL.muG ε) ≠ 0 → ff_HasInfChar ε π' (χ n lam)

def FKTypeOther : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : H →L[ℂ] H), Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ →
    IsOrthProjOnto E (lowKSub ε lam σ) →
    ∀ Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H), ff_Sph ε σ Ψ → ff_Compr ε E Ψ → ff_DSSum ε Ψ →
    ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
      (π' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), ffg_IsSq ε π' → ∀ (x y : H) (a b : H'),
      ∫ g, ⟪x, Ψ (umat g) y⟫_ℂ * star (coefOn π' a b g) ∂(Formalism.REAL.muG ε) ≠ 0 →
      ∃ S : Submodule ℂ H', IsKTypeOf ε π' (Formalism.QuantumDeterminants.lowK ε lam) S

section SlopeTestRemainingChoices

variable {n : ℕ} {ε : Fin n → Bool}

theorem ffg_equiv_symm {H' H : Type} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (h : ffg_Equiv ε σ' σ) : ffg_Equiv ε σ σ' := by
  obtain ⟨U, hU⟩ := h
  refine ⟨U.symm, fun g hg v => ?_⟩
  apply U.injective
  rw [U.apply_symm_apply, hU g hg, U.apply_symm_apply]

theorem ffg_coef_cont {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (v w : H) :
    Continuous (coefOn (ε := ε) σ v w) := by
  have hu : Continuous (fun g : Formalism.REAL.UJ ε => umat g) :=
    Units.continuous_val.comp continuous_subtype_val
  have hm : ∀ g : Formalism.REAL.UJ ε, umat g ∈ UJset ε := fun g => g.2
  exact continuous_const.inner ((hσ.2.2 v).comp_continuous hu hm)

theorem ffg_int_mul {u v : Formalism.REAL.UJ ε → ℂ} (hu : MemLp u 2 (Formalism.REAL.muG ε)) (hv : MemLp v 2 (Formalism.REAL.muG ε)) :
    Integrable (fun g => u g * star (v g)) (Formalism.REAL.muG ε) := by
  first
  | exact hu.integrable_mul hv.star
  | exact MemLp.integrable_mul hu hv.star
  | exact hu.integrable_mul hv.star (by norm_num)

def ffg_CoefOf {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (φ : Formalism.REAL.UJ ε → ℂ) : Prop :=
  ∃ v w : H, φ = coefOn σ v w

def ffg_Other {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (φ : Formalism.REAL.UJ ε → ℂ) : Prop :=
  ∃ (H' : Type) (_ : NormedAddCommGroup H') (_ : InnerProductSpace ℂ H') (_ : CompleteSpace H')
    (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (v w : H'),
    ffg_IsSq ε σ' ∧ ¬ ffg_Equiv ε σ' σ ∧ φ = coefOn σ' v w

theorem ffg_split {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) {φ : Formalism.REAL.UJ ε → ℂ} (hφ : IsDSCoef ε φ) :
    ffg_CoefOf ε σ φ ∨ ffg_Other ε σ φ := by
  obtain ⟨H', i1, i2, i3, σ', v, w, hnt, hU, hI, hS, rfl⟩ := hφ
  by_cases he : ffg_Equiv ε σ' σ
  · left
    obtain ⟨U, hU'⟩ := he
    refine ⟨U v, U w, ?_⟩
    funext g
    simp only [coefOn]
    rw [← hU' (umat g) g.2 v, LinearIsometryEquiv.inner_map_map]
  · right
    exact ⟨H', i1, i2, i3, σ', v, w, ⟨hnt, hU, hI, hS⟩, he, rfl⟩

theorem ffg_ds_memLp {φ : Formalism.REAL.UJ ε → ℂ} (hφ : IsDSCoef ε φ) : MemLp φ 2 (Formalism.REAL.muG ε) := by
  obtain ⟨H', i1, i2, i3, σ', v, w, hnt, hU, hI, hS, rfl⟩ := hφ
  exact hS v w

theorem ffg_ds_cont {φ : Formalism.REAL.UJ ε → ℂ} (hφ : IsDSCoef ε φ) : Continuous φ := by
  obtain ⟨H', i1, i2, i3, σ', v, w, hnt, hU, hI, hS, rfl⟩ := hφ
  exact ffg_coef_cont hU v w

theorem ffg_zero_of_int {h : Formalism.REAL.UJ ε → ℂ} (hc : Continuous h) (h2 : MemLp h 2 (Formalism.REAL.muG ε))
    (h0 : ∫ g, h g * star (h g) ∂(Formalism.REAL.muG ε) = 0) : h = 0 := by
  have heq : ∀ g, h g * star (h g) = ((‖h g‖ ^ 2 : ℝ) : ℂ) := fun g => by
    rw [show star (h g) = (starRingEnd ℂ) (h g) from rfl, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hint : Integrable (fun g => h g * star (h g)) (Formalism.REAL.muG ε) := ffg_int_mul h2 h2
  have hint' : Integrable (fun g => ‖h g‖ ^ 2) (Formalism.REAL.muG ε) := by
    refine hint.norm.congr (ae_of_all _ fun g => ?_)
    simp only
    rw [heq g, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hre : ∫ g, ‖h g‖ ^ 2 ∂(Formalism.REAL.muG ε) = 0 := by
    simp_rw [heq] at h0
    rw [integral_complex_ofReal] at h0
    exact_mod_cast h0
  have hnn : 0 ≤ᵐ[Formalism.REAL.muG ε] fun g => ‖h g‖ ^ 2 := ae_of_all _ fun g => by positivity
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hint').1 hre
  haveI : (Formalism.REAL.muG ε).IsOpenPosMeasure := by
    first
    | infer_instance
    | (unfold Formalism.REAL.muG; infer_instance)
  have hz : (fun g => ‖h g‖ ^ 2) = 0 :=
    ((hc.norm.pow 2).ae_eq_iff_eq (Formalism.REAL.muG ε) continuous_zero).1 hae
  funext g
  have := congrFun hz g
  simpa using this

end SlopeTestRemainingChoices

private theorem ffg_Equiv_trans {n : ℕ} {ε : Fin n → Bool} {H₁ H₂ H₃ : Type}
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    [NormedAddCommGroup H₃] [InnerProductSpace ℂ H₃] {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)}
    {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)} {σ₃ : Matrix (Fin n) (Fin n) ℂ → (H₃ →L[ℂ] H₃)}
    (h₁ : ffg_Equiv ε σ₁ σ₂) (h₂ : ffg_Equiv ε σ₂ σ₃) : ffg_Equiv ε σ₁ σ₃ := by
  obtain ⟨U, hU⟩ := h₁
  obtain ⟨V, hV⟩ := h₂
  refine ⟨U.trans V, fun g hg v => ?_⟩
  rw [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.trans_apply, hU g hg, hV g hg]

theorem ff_ident_of (χ : ∀ n : ℕ, (Fin n → ℝ) → ℕ → ℂ) (q1 : QOrth) (q2 : QClass χ) (q3 : FCharOther χ)
    (q4 : FKTypeOther) : FIdent χ := by
  intro n ε lam H _ _ _ σ E hHC hDS hE Ψ hSph hCompr hEig hDSS x y
  classical
  obtain ⟨N, φ, hφ, hψ⟩ := hDSS x y
  have hL2 : ∀ i, MemLp (φ i) 2 (Formalism.REAL.muG ε) := fun i => ffg_ds_memLp (hφ i)
  have hC : ∀ i, Continuous (φ i) := fun i => ffg_ds_cont (hφ i)
  have hψf : (fun g => ⟪x, Ψ (umat g) y⟫_ℂ) = fun g => ∑ i, φ i g := funext hψ
  have hψL2 : MemLp (fun g => ⟪x, Ψ (umat g) y⟫_ℂ) 2 (Formalism.REAL.muG ε) := by
    rw [hψf]; exact memLp_finset_sum _ fun i _ => hL2 i
  have F2 : ∀ j, ffg_Other ε σ (φ j) →
      ∫ g, ⟪x, Ψ (umat g) y⟫_ℂ * star (φ j g) ∂(Formalism.REAL.muG ε) = 0 := by
    intro j hO
    obtain ⟨H', iA, iB, iC, σ', a, b, hsq, hne, hj⟩ := hO
    rw [hj]
    by_contra h0
    apply hne
    have hsq' := hsq
    obtain ⟨hnt, hU, hI, hS⟩ := hsq'
    exact q2 n ε lam hHC H σ hDS H' σ' hnt hU hI hS
      (q3 n ε lam H σ E hHC hDS hE Ψ hSph hCompr hEig hDSS H' σ' hsq x y a b h0)
      (q4 n ε lam H σ E hHC hDS hE Ψ hSph hCompr hDSS H' σ' hsq x y a b h0)
  have F3 : ∀ i, ¬ ffg_Other ε σ (φ i) → ∀ j, ffg_Other ε σ (φ j) →
      ∫ g, φ i g * star (φ j g) ∂(Formalism.REAL.muG ε) = 0 := by
    intro i hA j hO
    obtain ⟨Hj, jA, jB, jC, σj, a, b, hsqj, hnej, hj⟩ := hO
    obtain ⟨Hi, kA, kB, kC, σi, c, d, hnt, hU, hI, hS, hi⟩ := hφ i
    have hEq : ffg_Equiv ε σi σ := by
      by_contra hne
      exact hA ⟨Hi, kA, kB, kC, σi, c, d, ⟨hnt, hU, hI, hS⟩, hne, hi⟩
    have hne' : ¬ ffg_Equiv ε σi σj := fun h' => hnej (ffg_Equiv_trans (ffg_equiv_symm h') hEq)
    rw [hi, hj]
    exact (q1 n ε).2 Hi σi Hj σj ⟨hnt, hU, hI, hS⟩ hsqj hne' c d a b
  obtain ⟨s, hs⟩ : ∃ s : Finset (Fin N), s = Finset.univ.filter (fun j => ffg_Other ε σ (φ j)) := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : Finset (Fin N), t = Finset.univ.filter (fun j => ¬ ffg_Other ε σ (φ j)) := ⟨_, rfl⟩
  have hsplit : ∀ g, ⟪x, Ψ (umat g) y⟫_ℂ = ∑ i ∈ t, φ i g + ∑ j ∈ s, φ j g := fun g => by
    rw [hψ g, hs, ht, add_comm]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  obtain ⟨h, hh⟩ : ∃ h : Formalism.REAL.UJ ε → ℂ, h = fun g => ∑ j ∈ s, φ j g := ⟨_, rfl⟩
  have hh' : ∀ g, h g = ∑ j ∈ s, φ j g := fun g => by simp only [hh]
  have hhL2 : MemLp h 2 (Formalism.REAL.muG ε) := by rw [hh]; exact memLp_finset_sum _ fun j _ => hL2 j
  have hhC : Continuous h := by rw [hh]; exact continuous_finset_sum _ fun j _ => hC j
  have key : ∀ j ∈ s, ∫ g, h g * star (φ j g) ∂(Formalism.REAL.muG ε) = 0 := by
    intro j hj
    have hOj : ffg_Other ε σ (φ j) := by rw [hs] at hj; exact (Finset.mem_filter.1 hj).2
    have e1 : ∀ g, h g * star (φ j g) =
        ⟪x, Ψ (umat g) y⟫_ℂ * star (φ j g) - ∑ i ∈ t, φ i g * star (φ j g) := fun g => by
      rw [hh' g, hsplit g, ← Finset.sum_mul]; ring
    simp_rw [e1]
    have I1 : Integrable (fun g => ⟪x, Ψ (umat g) y⟫_ℂ * star (φ j g)) (Formalism.REAL.muG ε) :=
      ffg_int_mul hψL2 (hL2 j)
    have I2 : ∀ i ∈ t, Integrable (fun g => φ i g * star (φ j g)) (Formalism.REAL.muG ε) :=
      fun i _ => ffg_int_mul (hL2 i) (hL2 j)
    rw [integral_sub I1 (integrable_finset_sum t I2), integral_finset_sum t I2, F2 j hOj,
      Finset.sum_eq_zero fun i hi => F3 i (by rw [ht] at hi; exact (Finset.mem_filter.1 hi).2) j hOj, sub_zero]
  have hzero : ∫ g, h g * star (h g) ∂(Formalism.REAL.muG ε) = 0 := by
    have e2 : ∀ g, h g * star (h g) = ∑ j ∈ s, h g * star (φ j g) := fun g => by
      rw [← Finset.mul_sum, ← star_sum, ← hh' g]
    simp_rw [e2]
    rw [integral_finset_sum _ fun j _ => ffg_int_mul hhL2 (hL2 j)]
    exact Finset.sum_eq_zero key
  have h0 : h = 0 := ffg_zero_of_int hhC hhL2 hzero
  have hpt : ∀ g, ⟪x, Ψ (umat g) y⟫_ℂ = ∑ i ∈ t, φ i g := fun g => by
    have h1 : ∑ j ∈ s, φ j g = 0 := by rw [← hh' g, h0, Pi.zero_apply]
    rw [hsplit g, h1, add_zero]
  have F1 : ∀ i, ¬ ffg_Other ε σ (φ i) → ∃ v w : H, φ i = coefOn σ v w := fun i hA =>
    (ffg_split σ (hφ i)).resolve_right hA
  refine ⟨N, fun i => if hA : ¬ ffg_Other ε σ (φ i) then (F1 i hA).choose else 0,
    fun i => if hA : ¬ ffg_Other ε σ (φ i) then (F1 i hA).choose_spec.choose else 0, fun g => ?_⟩
  rw [hpt g, ht, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hA : ¬ ffg_Other ε σ (φ i)
  · simp only [if_pos hA, dif_pos hA]
    exact congrFun (F1 i hA).choose_spec.choose_spec g
  · simp [if_neg hA, dif_neg hA, coefOn]

end Formalism.MainNotions.LeviCoordinates

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.ProjectionStatementOfFinal
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def cu.LocGrowth (X : CData) : Prop :=
  ∀ (v : InfinitePlace X.I.F) (s : ℝ), 0 ≤ s →
    (1 ≤ q0At X.I v →
      2 * (X.I.n : ℝ) * Real.sqrt (2 * (q0At X.I v : ℝ)) + s < X.h / 8 / Real.sqrt (2 * (q0At X.I v : ℝ))) →
    Integrable (fun g : Formalism.REAL.UJ (X.I.ε v) =>
      ‖coefOn (X.σ v) (X.w v) (X.w v) g‖ * Real.exp (s * cartanDistance (X.I.ε v) g)) (Formalism.REAL.muG (X.I.ε v))

theorem cu_haarGrowth_of (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) (hL : cu.LocGrowth X) : cu.HaarGrowth X := by
  intro s hs hrate
  have he : Integrable X.e X.μf := hX.2.1.2.2.2.2.2.2.1
  have h1 : Integrable (fun g : X.I.Ginf => ∏ v, (‖coefOn (X.σ v) (X.w v) (X.w v) (g v)‖ *
      Real.exp (s * cartanDistance (X.I.ε v) (g v)))) (Measure.pi fun v => Formalism.REAL.muG (X.I.ε v)) :=
    Integrable.fintype_prod_dep (μ := fun v => Formalism.REAL.muG (X.I.ε v))
      (f := fun v g => ‖coefOn (X.σ v) (X.w v) (X.w v) g‖ * Real.exp (s * cartanDistance (X.I.ε v) g))
      (fun v => hL v s hs (hrate v))
  have h2 := (h1.const_mul (fdegAll X.I X.σ X.w)).mul_prod he.norm
  refine h2.congr (Filter.Eventually.of_forall fun g => ?_)
  show fdegAll X.I X.σ X.w * (∏ v, (‖coefOn (X.σ v) (X.w v) (X.w v) (g.1 v)‖ *
      Real.exp (s * cartanDistance (X.I.ε v) (g.1 v)))) * ‖X.e g.2‖ = ‖X.φ g‖ * cu_wt X s g
  unfold CData.φ phe phOf cu_wt
  rw [norm_mul, norm_mul, norm_star, norm_prod, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg X.fdegAll_nonneg,
    Finset.prod_mul_distrib, Finset.mul_sum, Real.exp_sum]
  ring

def cu.Last (X : CData) : Prop :=
  cu.UnipFine X ∧ cu.LocGrowth X ∧ (∃ S : CSize X, S.Strata ∧ S.PackCount ∧ S.Inv ∧ S.Lip ∧ S.LowN) ∧ X.KernelDiag ∧
    UnimodA X

theorem cu_core_of_last (X : CData) {n₀ : ℕ} {A : ℝ} (hn₀ : 1 ≤ n₀) (hX : X.HypB n₀ A) (h : cu.Last X) : cu.Core X := by
  obtain ⟨sU, sL, ⟨S, a1, a2, a3, a4, a5⟩, sK, sA⟩ := h
  exact ⟨sU, cu_haarGrowth_of X hX sL, cu_sizeStep_of X (le_trans hn₀ hX.1.1) S a1 a2 a3 a4 a5, sK, sA⟩

def cu_StepsLast (n₀ : ℕ) (A C : ℝ) : Prop :=
  ∀ X : CData, X.HypB n₀ A → X.GapAboveThreeHalvesPower → X.GapAboveSquareRootThreshold C → cu.Last X

theorem cuspidal_range_of_final_facts (X : CData) (D : Formalism.BasicNotions.D7) (hdec : DiscreteSeriesDecayBound D) {n₀ : ℕ} {A C : ℝ} (hn₀ : 1 ≤ n₀)
    (hC : 46 ≤ C) (hX : X.HypB n₀ A) (h1 : X.GapAboveThreeHalvesPower) (h2 : X.GapAboveSquareRootThreshold C) (hE : X.LowProj) (hF : cu.FinStep X)
    (hS : cu.Last X) : X.CuspStep :=
  cuspidal_range_of_reduced_facts X D hdec hn₀ hC hX h1 h2 hE hF (cu_core_of_last X hn₀ hX hS)

end Formalism.MainNotions.LeviCoordinates
end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RegularRepAlgebraicMeasurableContinuous
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set Topology
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

theorem packet_bound_of_volume_kernel_conditions (cε C₁ c₁ A A₂ : ℝ) (hcε : 0 < cε) (hcε2 : cε ≤ 1 / 2) (hC₁ : 1 ≤ C₁) (hc₁ : 0 < c₁)
    (hA : 1 ≤ A) (hA₂ : 0 ≤ A₂) :
    ∃ c' : ℝ, 0 < c' ∧ ∃ n₁ : ℕ, ∀ Cb : ℝ, ∃ C₂ : ℝ, ∀ (D : Formalism.BasicNotions.D7) (n₀ : ℕ) (C cb : ℝ),
      n₁ ≤ n₀ → C₂ ≤ C → adm2 D → DiscreteSeriesDecayBound D → Conclusion2 D n₀ A Cb → KernelDiagonalVolumeModulusConditions n₀ A C cb c₁ A₂ cε C₁ →
      PointsLemma D n₀ A C c' cb := by
  obtain ⟨c', hc', n₁, h⟩ := third_part_of_final_estimates cε C₁ c₁ A A₂ hcε hcε2 hC₁ hc₁ hA hA₂
  refine ⟨c', hc', n₁, fun Cb => ?_⟩
  obtain ⟨C₂, h2⟩ := h Cb
  exact ⟨C₂, fun D n₀ C cb a b c d e f => h2 D n₀ C cb a b c d e ((kernel_conditions_iff_without_regular_rep n₀ A C cb c₁ A₂ cε C₁).2 f)⟩

theorem regular_rep_algebraic_measurable_continuous (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) (hu : UnimodF X) :
    RepAlg X ∧ (∀ x y : X.L2, StronglyMeasurable fun g => ⟪x, X.R g y⟫_ℂ) ∧ RepInf X :=
  have hd := RegData_of_HypB X hX
  have ha := UnimodA_of_UnimodF X hu
  ⟨rightRegular_isometric_multiplicative X hd ha, regular_rep_coeff_measurable X hd ha, archimedean_restriction_strongly_continuous X hd ha⟩

end Formalism.MainNotions.LeviCoordinates

end
end

