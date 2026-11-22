import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle0009
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle0001
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle0010
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CndTauSLeHalf

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.ArchimedeanRestrictionStronglyContinuous
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set Topology
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def RepInf (X : CData) : Prop := ∀ F : X.L2, Continuous fun g : X.I.Ginf => X.R (g, 1) F

theorem archimedean_restriction_strongly_continuous (X : CData) (hd : RegData X) (hu : UnimodA X) : RepInf X := by
  intro F
  have hH : X.μf.IsHaarMeasure := hd.1
  have : SecondCountableTopology X.I.Gf := rr_secondCountable X.I X.μf
  have : SecondCountableTopology X.L2 := automorphic_L2_secondCountable X
  obtain ⟨h1, h2, h3⟩ := rightRegular_isometric_multiplicative X hd hu
  refine rr_cont_of_meas (G := X.I.Ginf) (μ := Measure.pi fun v => Formalism.REAL.muG (X.I.ε v))
    (π := fun g => X.R (g, 1)) (fun g h => ?_) h2 (fun g x => h3 _ x) (fun x y => ?_) F
  · rw [← h1]
    congr 1
    simp
  · exact ((regular_rep_coeff_measurable X hd hu x y).comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable

end Formalism.MainNotions.LeviCoordinates

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CnOneLtRd
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma
open Formalism.HermitianLatticeCounting.S7 (dimN Vsph)

def cn_kapBd (Cv : ℝ) {a : ℕ} (j : Fin a → ℕ) (p q n0 f : ℕ) (v res : ℝ) : ℝ :=
  ((Cv ^ dimN j n0 * (Vsph p * Vsph q / (Vsph (p - ∑ x, j x) * Vsph (q - ∑ x, j x) * ∏ x, Vsph (j x)))) ^ f *
      (Cv * v) ^ ((f : ℝ) * (dimN j n0 : ℝ) / 2) * ∏ x, ((Cv * v) ^ (j x ^ 2 * f) * res * Cv ^ f)) *
    (v ^ (-(((p + q : ℕ) : ℝ) ^ 2 - (n0 : ℝ) ^ 2) * (f : ℝ) / 2) * Cv ^ ((p + q) * f))

theorem cn_kappa_num (Cv Cres : ℝ) (hCv : 1 ≤ Cv) : ∃ n₁ : ℕ, ∀ (a p q n0 f : ℕ) (j : Fin a → ℕ) (rd res : ℝ),
    n₁ ≤ p + q → q ≤ p → q ^ 2 ≤ p + q → (∀ x, 1 ≤ j x) → 1 ≤ a → ∑ x, j x ≤ q → p + q = n0 + 2 * ∑ x, j x → 1 ≤ f →
    1 < rd → Real.log (Real.log rd) ≤ ((p + q : ℕ) : ℝ) → 0 ≤ res → res ≤ (Cres * Real.log rd) ^ (2 * f) →
    cn_kapBd Cv j p q n0 f (rd / 2) res ≤
      Real.exp (-(1 / 8 * ((∑ x, j x : ℕ) : ℝ) * ((p + q : ℕ) : ℝ) * (f : ℝ) * Real.log ((p + q : ℕ) : ℝ))) := by
  obtain ⟨C', hC', hA⟩ := Formalism.HermitianLatticeCounting.Final.NearFarVolumeBounds.kappaAssembly Cv hCv
  set C : ℝ := max C' (max |Cres| 1) with hC
  have hCC' : C' ≤ C := le_max_left _ _
  have hCres : |Cres| ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC1 : 1 ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  obtain ⟨n₀, hK⟩ := cn_kappaBoundAbs C hC1
  refine ⟨n₀, fun a p q n0 f j rd res hn hqp hq2 hj ha hJq hpq hf hrd hll hres0 hres => ?_⟩
  have hv : (1 : ℝ) / 2 ≤ rd / 2 := by linarith
  have hv0 : 0 < rd / 2 := by linarith
  have hCv0 : 0 < Cv := by linarith
  have hV : ∀ i, 0 < Vsph i := Formalism.HermitianLatticeCounting.P.vsph_pos
  have hℓ : 0 < Real.log rd := Real.log_pos hrd
  have h1 := hA a p q n0 f j (rd / 2) res
    ((Cv ^ dimN j n0 * (Vsph p * Vsph q / (Vsph (p - ∑ x, j x) * Vsph (q - ∑ x, j x) * ∏ x, Vsph (j x)))) ^ f)
    ((Cv * (rd / 2)) ^ ((f : ℝ) * (dimN j n0 : ℝ) / 2))
    ((rd / 2) ^ (-(((p + q : ℕ) : ℝ) ^ 2 - (n0 : ℝ) ^ 2) * (f : ℝ) / 2) * Cv ^ ((p + q) * f))
    (fun x => (Cv * (rd / 2)) ^ (j x ^ 2 * f) * res * Cv ^ f) hj ha hJq hqp hpq hf hv hres0
    (by positivity) le_rfl (fun x => ⟨by positivity, le_rfl⟩) (by positivity) le_rfl
    (by
      have := hV p; have := hV q; have := hV (p - ∑ x, j x); have := hV (q - ∑ x, j x)
      have : 0 < ∏ x, Vsph (j x) := Finset.prod_pos fun x _ => hV _
      positivity) le_rfl
  have haJ : a ≤ ∑ x, j x := by
    calc a = ∑ _x : Fin a, 1 := by simp
      _ ≤ ∑ x, j x := Finset.sum_le_sum fun x _ => hj x
  have hdN : dimN j n0 ≤ 2 * (∑ x, j x) * (p + q) := by
    rw [hpq]
    exact (Formalism.HermitianLatticeCounting.Final.S7.dimIdentity a j n0).2.1
  have hres' : res ≤ (C * Real.log rd) ^ (2 * f) := by
    refine le_trans hres ?_
    rw [← Even.pow_abs ⟨f, two_mul f⟩ (Cres * Real.log rd), abs_mul, abs_of_pos hℓ]
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hCres hℓ.le) _
  have h2 := hK (p + q) p q (∑ x, j x) a f (dimN j n0) (rd / 2) res (Real.log rd) hn rfl hq2 ha haJ hJq hf hdN hv hℓ hll
    hres0 hres'
  refine le_trans ?_ h2
  unfold cn_kapBd
  refine le_trans h1 ?_
  have hC'0 : 0 < C' := by linarith
  gcongr

def cn_res (X : CData) : ℝ := NumberField.dedekindZeta_residue X.I.E

def cn_ResBound (X : CData) (Cres : ℝ) : Prop := cn_res X ≤ (Cres * Real.log X.I.rd) ^ (2 * X.I.f)

def CSize.KappaVol {X : CData} (S : CSize X) (Cv : ℝ) : Prop :=
  ∀ (J : ℕ) (c : Composition J), 1 ≤ J → J ≤ X.qq →
    S.kap J c ≤ cn_kapBd Cv c.blocksFun (X.I.n - X.qq) X.qq (X.I.n - 2 * J) X.I.f (X.I.rd / 2) (cn_res X)

theorem cn_one_lt_rd (I : AutInst) : 1 < I.rd := by
  have hdeg : 1 < Module.finrank ℚ I.E := by
    have h1 : Module.finrank ℚ I.F * Module.finrank I.F I.E = Module.finrank ℚ I.E := Module.finrank_mul_finrank ℚ I.F I.E
    rw [I.cm.deg2] at h1
    have h2 : 1 ≤ Module.finrank ℚ I.F := Module.finrank_pos
    omega
  have h2 := NumberField.abs_discr_gt_two hdeg
  have h3 : (2 : ℝ) < |(discr I.E : ℝ)| := by exact_mod_cast h2
  unfold AutInst.rd
  have hf : (0 : ℝ) < (I.f : ℝ) := by exact_mod_cast one_le_autInst_f I
  exact Real.one_lt_rpow (by linarith) (by positivity)

theorem cn_kappa_le (Cv Cres : ℝ) (hCv : 1 ≤ Cv) : ∃ n₁ : ℕ, ∀ (X : CData) (S : CSize X) (n₀ : ℕ) (A : ℝ), n₁ ≤ X.I.n →
    X.HypB n₀ A → S.KappaVol Cv → cn_ResBound X Cres → ∀ (J : ℕ) (c : Composition J), 1 ≤ J → J ≤ X.qq →
    S.kap J c ≤ Real.exp (-(1 / 8 * (J : ℝ) * (X.I.n : ℝ) * (X.I.f : ℝ) * Real.log (X.I.n : ℝ))) := by
  obtain ⟨n₁, h⟩ := cn_kappa_num Cv Cres hCv
  refine ⟨max n₁ 4, fun X S n₀ A hn hX hK hR J c hJ1 hJq => ?_⟩
  obtain ⟨-, hq2⟩ := X.qq_spec hX
  have hn4 : 4 ≤ X.I.n := le_trans (le_max_right _ _) hn
  have h2q : 2 * X.qq ≤ X.I.n := by
    by_cases h : X.qq ≤ 1
    · omega
    · nlinarith
  have hpq : X.I.n - X.qq + X.qq = X.I.n := by omega
  have := h c.length (X.I.n - X.qq) X.qq (X.I.n - 2 * J) X.I.f c.blocksFun X.I.rd (cn_res X)
    (by rw [hpq]; exact le_trans (le_max_left _ _) hn) (by omega) (by rw [hpq]; exact hq2) c.one_le_blocksFun
    (c.length_pos_of_pos hJ1) (by rw [c.sum_blocksFun]; exact hJq) (by rw [c.sum_blocksFun]; omega) (one_le_autInst_f X.I)
    (cn_one_lt_rd X.I) (by rw [hpq]; exact hX.1.2.2.2.1) (NumberField.dedekindZeta_residue_pos _).le hR
  rw [c.sum_blocksFun, hpq] at this
  exact le_trans (hK J c hJ1 hJq) this

end Formalism.MainNotions.LeviCoordinates

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CndDiamOfProved
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma
open Formalism.HermitianLatticeCounting.S7 (P0 b1 Ydat)

theorem cnd_cov_of_proved (n f : ℕ) (hf : 1 ≤ f) (rd ρ₀ : ℝ) (hrd : 0 < rd) (hρ₀ : 0 < ρ₀)
    (P : ℝ → Prop) (hP : ∀ R R', R ≤ R' → P R → P R')
    (h : cnd_CovLe (2 * n ^ 2 * f) (Real.sqrt (f : ℝ) / (2 * rd * ρ₀)) P) :
    P (8 * (n : ℝ) ^ 6 * (f : ℝ) ^ ((5 : ℝ) / 2) * rd * ρ₀) := by
  obtain ⟨V, i1, i2, i3, M, hd, hsp, hN, hdual, hR⟩ := h
  have hκ : 0 < Real.sqrt (f : ℝ) / (2 * rd * ρ₀) :=
    div_pos (Real.sqrt_pos.2 (by exact_mod_cast hf)) (by positivity)
  have h1 := Formalism.HermitianLatticeCounting.Final.S7.coverRadius V M hd hsp _ hκ hdual
  have h2 := (Formalism.HermitianLatticeCounting.Final.S7.coverArith n f (Module.finrank ℝ V) rd ρ₀ hf hN hrd hρ₀).2.2
  exact hP _ _ h2 (hR _ h1)

theorem cnd_diam_of_proved (X : CData) (Cq ρ ρ₀ : ℝ) (hCq : 0 ≤ Cq) (hρ₀ : 0 < ρ₀) (h : cnd_Diam X Cq ρ ρ₀) :
    ρ ≤ (16 * Cq) * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ) * ((X.g : ℝ) * (X.I.n : ℝ) ^ 4 * (X.I.f : ℝ) ^ 2) * X.I.rd * ρ₀ := by
  have hrd : 0 < X.I.rd := lt_of_lt_of_le zero_lt_one (one_le_discriminant_root X.I)
  have hco : 0 ≤ Cq * Real.sqrt (X.I.f : ℝ) * (X.g : ℝ) := by positivity
  have hmono2 : ∀ R₁ R R' : ℝ, R ≤ R' → ρ ≤ Cq * Real.sqrt (X.I.f : ℝ) * (X.g : ℝ) * (R₁ + R) →
      ρ ≤ Cq * Real.sqrt (X.I.f : ℝ) * (X.g : ℝ) * (R₁ + R') := fun R₁ R R' hRR h =>
    le_trans h (mul_le_mul_of_nonneg_left (by linarith) hco)
  have h1 := cnd_cov_of_proved X.I.n X.I.f (one_le_autInst_f X.I) X.I.rd ρ₀ hrd hρ₀ _ (by
    intro R R' hRR hh
    obtain ⟨V, i1, i2, i3, M, hd, hsp, hN, hdual, hR⟩ := hh
    exact ⟨V, i1, i2, i3, M, hd, hsp, hN, hdual, fun R₂ hc =>
      le_trans (hR R₂ hc) (mul_le_mul_of_nonneg_left (by linarith) hco)⟩) h
  have h2 := cnd_cov_of_proved X.I.n X.I.f (one_le_autInst_f X.I) X.I.rd ρ₀ hrd hρ₀ _ (hmono2 _) h1
  have hf0 : (0 : ℝ) < (X.I.f : ℝ) := by exact_mod_cast one_le_autInst_f X.I
  have hs : Real.sqrt (X.I.f : ℝ) * (X.I.f : ℝ) ^ ((5 : ℝ) / 2) = (X.I.f : ℝ) ^ 3 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hf0, ← Real.rpow_natCast]
    norm_num
  calc ρ ≤ _ := h2
    _ = (16 * Cq) * (X.I.n : ℝ) ^ 6 * (Real.sqrt (X.I.f : ℝ) * (X.I.f : ℝ) ^ ((5 : ℝ) / 2)) * (X.g : ℝ) * X.I.rd * ρ₀ := by ring
    _ = _ := by rw [hs]; ring

theorem cnd_pointG (Cd : ℝ) (hCd : 1 ≤ Cd) : ∃ C₁₀ : ℝ, 1 ≤ C₁₀ ∧ ∀ (n q f : ℕ) (rd g b τ₁ τs ρ Kxx Bs D volG volK : ℝ),
    1 ≤ n → 1 ≤ q → q ^ 2 ≤ n → 1 ≤ f → 1 ≤ rd → 1 ≤ g → 2 ≤ b → 0 < τ₁ → τ₁ < τs →
    τs ≤ Ydat n f rd g b ^ (-(C₁₀ * (q : ℝ))) → 0 ≤ D → 0 < volK → 0 ≤ volG → 0 ≤ ρ →
    ρ ≤ Cd * (n : ℝ) ^ 2 * (f : ℝ) * g * rd * (2 * τ₁) ^ (1 / (q : ℝ)) →
    Kxx ≤ (Cd * ρ * (n : ℝ) ^ 2 * (f : ℝ) * b1 n q f b) ^ (2 * P0 n q f) * Bs →
    Bs ≤ D * volK⁻¹ * (Cd * (n : ℝ) ^ 2 * b1 n q f b) ^ (n ^ 2 * f) * (Cd / τ₁) ^ (4 * n ^ 2 * f) →
    volG / volK ≤ Ydat n f rd g b ^ (Cd * (n : ℝ) ^ 2 * (f : ℝ)) →
    volG * Kxx ≤ D * Real.exp (-((n : ℝ) ^ 2 * (f : ℝ))) := by
  obtain ⟨C', hC', hch⟩ := Formalism.HermitianLatticeCounting.Final.CuspThresholdCounts.deepChainV Cd hCd
  obtain ⟨C₁₀, h1, hB⟩ := Formalism.HermitianLatticeCounting.Final.S7.deepBound C' hC'
  refine ⟨C₁₀, h1, fun n q f rd g b τ₁ τs ρ Kxx Bs D volG volK hn hq hq2 hf hrd hg hb hτ hlt hτs hD hvK hvG a b' c d
    hvol => ?_⟩
  have h2 := hch n q f rd g b τ₁ τs ρ Kxx Bs D volG volK hn hq hq2 hf hrd hg hb hτ hlt hD hvK hvG a b' c d hvol
  have h3 := hB n q f rd g b hn hq hq2 hf hrd hg hb
  have h4 : τs ^ (12 * n ^ 2 * f) ≤ (Ydat n f rd g b ^ (-(C₁₀ * (q : ℝ)))) ^ (12 * n ^ 2 * f) :=
    pow_le_pow_left₀ (le_trans hτ.le hlt.le) hτs _
  have hb1 : 0 ≤ b1 n q f b := by
    unfold Formalism.HermitianLatticeCounting.S7.b1
    positivity
  have hY0 : 0 ≤ Ydat n f rd g b := by
    unfold Formalism.HermitianLatticeCounting.S7.Ydat
    positivity
  have hYp : 0 ≤ Ydat n f rd g b ^ (C' * (n : ℝ) ^ 2 * (f : ℝ)) *
      (C' * (n : ℝ) ^ 4 * (f : ℝ) ^ 2 * g * rd * b1 n q f b) ^ (16 * q * n ^ 2 * f) := by
    have hC0 : 0 ≤ C' := by linarith
    exact mul_nonneg (Real.rpow_nonneg hY0 _) (pow_nonneg (by positivity) _)
  calc _ ≤ _ := h2
    _ = D * (Ydat n f rd g b ^ (C' * (n : ℝ) ^ 2 * (f : ℝ)) *
          (C' * (n : ℝ) ^ 4 * (f : ℝ) ^ 2 * g * rd * b1 n q f b) ^ (16 * q * n ^ 2 * f) * τs ^ (12 * n ^ 2 * f)) := by ring
    _ ≤ D * Real.exp (-((n : ℝ) ^ 2 * (f : ℝ))) :=
        mul_le_mul_of_nonneg_left (le_trans (mul_le_mul_of_nonneg_left h4 hYp) h3) hD

theorem cnd_Y' (n f : ℕ) (rd g b : ℝ) (hn : 1 ≤ n) (hf : 1 ≤ f) (hrd : 1 ≤ rd) (hg : 1 ≤ g) (hb : 2 ≤ b) :
    Ydat n f rd g b ≤ Ydat n f rd (g * (n : ℝ) ^ 4 * (f : ℝ) ^ 2) b ∧
      Ydat n f rd (g * (n : ℝ) ^ 4 * (f : ℝ) ^ 2) b ≤ Ydat n f rd g b ^ 7 := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hfR : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hY0 : 0 ≤ Ydat n f rd g b := by
    unfold Formalism.HermitianLatticeCounting.S7.Ydat
    positivity
  have hnY : (n : ℝ) ≤ Ydat n f rd g b := by
    unfold Formalism.HermitianLatticeCounting.S7.Ydat
    calc (n : ℝ) = (n : ℝ) * 1 * 1 * 1 * 1 := by ring
      _ ≤ (n : ℝ) * f * rd * g * b := by gcongr
  have hfY : (f : ℝ) ≤ Ydat n f rd g b := by
    unfold Formalism.HermitianLatticeCounting.S7.Ydat
    calc (f : ℝ) = 1 * (f : ℝ) * 1 * 1 * 1 := by ring
      _ ≤ (n : ℝ) * f * rd * g * b := by gcongr
  have he : Ydat n f rd (g * (n : ℝ) ^ 4 * (f : ℝ) ^ 2) b = Ydat n f rd g b * ((n : ℝ) ^ 4 * (f : ℝ) ^ 2) := by
    unfold Formalism.HermitianLatticeCounting.S7.Ydat
    ring
  rw [he]
  constructor
  · have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 4 * (f : ℝ) ^ 2 := by
      have a1 : (1 : ℝ) ≤ (n : ℝ) ^ 4 := one_le_pow₀ hnR
      have a2 : (1 : ℝ) ≤ (f : ℝ) ^ 2 := one_le_pow₀ hfR
      nlinarith
    nlinarith
  · calc Ydat n f rd g b * ((n : ℝ) ^ 4 * (f : ℝ) ^ 2)
        ≤ Ydat n f rd g b * (Ydat n f rd g b ^ 4 * Ydat n f rd g b ^ 2) := by gcongr
      _ = Ydat n f rd g b ^ 7 := by ring

theorem cnd_deepP (C Cq : ℝ) (hC : 1 ≤ C) (hCq : 0 ≤ Cq) (hCC : 16 * Cq ≤ C) :
    ∃ C₁₀ : ℝ, 1 ≤ C₁₀ ∧ ∀ C₁ ≥ C₁₀, ∀ (X : CData) (S : CSize X) (volK : ℝ)
    (n₀ : ℕ) (A : ℝ), 1 ≤ n₀ → X.HypB n₀ A → 1 ≤ X.qq → X.FinVol → S.Strata → S.DeepStepsQ volK C Cq →
    ∀ A₁ : ℝ, 1 ≤ A₁ → X.DeepInt A₁ (S.Mod C₁) := by
  obtain ⟨C₀, h1, hpt⟩ := cnd_pointG (4 * C) (by linarith)
  refine ⟨7 * C₀, by linarith, fun C₁ hC₁ X S volK n₀ A hn₀ hX hq hV hst hS A₁ hA₁ => ?_⟩
  obtain ⟨hvK, hvol, hae⟩ := hS
  have hY := cnd_two_le_Y X hn₀ hX
  have hn : 1 ≤ X.I.n := le_trans hn₀ hX.1.1
  have hnR : (1 : ℝ) ≤ (X.I.n : ℝ) := by exact_mod_cast hn
  have hfR : (1 : ℝ) ≤ (X.I.f : ℝ) := by exact_mod_cast one_le_autInst_f X.I
  have hg1 : (1 : ℝ) ≤ (X.g : ℝ) := by exact_mod_cast hX.1.2.2.2.2.2.2.2.1
  have hb : 2 ≤ X.b := hX.1.2.2.1
  have hq2 := (X.qq_spec hX).2
  have hqR : (0 : ℝ) ≤ (X.qq : ℝ) := Nat.cast_nonneg _
  set g' : ℝ := (X.g : ℝ) * (X.I.n : ℝ) ^ 4 * (X.I.f : ℝ) ^ 2 with hg'
  have hg'1 : 1 ≤ g' := by
    have a1 : (1 : ℝ) ≤ (X.I.n : ℝ) ^ 4 := one_le_pow₀ hnR
    have a2 : (1 : ℝ) ≤ (X.I.f : ℝ) ^ 2 := one_le_pow₀ hfR
    have a3 : (1 : ℝ) ≤ (X.g : ℝ) * (X.I.n : ℝ) ^ 4 := by nlinarith
    rw [hg']
    nlinarith
  obtain ⟨hY1, hY7⟩ := cnd_Y' X.I.n X.I.f X.I.rd (X.g : ℝ) X.b hn (one_le_autInst_f X.I) (one_le_discriminant_root X.I) hg1 hb
  have hYY : cn_Y X = Ydat X.I.n X.I.f X.I.rd (X.g : ℝ) X.b := rfl
  rw [← hYY] at hY1 hY7
  have hYpos : 0 < cn_Y X := by linarith
  have hY'pos : 0 < Ydat X.I.n X.I.f X.I.rd g' X.b := lt_of_lt_of_le hYpos hY1
  have hτle : cn_tauS X C₁ ≤ Ydat X.I.n X.I.f X.I.rd g' X.b ^ (-(C₀ * (X.qq : ℝ))) := by
    have hnp : -(C₀ * (X.qq : ℝ)) ≤ 0 := by
      have : 0 ≤ C₀ * (X.qq : ℝ) := mul_nonneg (by linarith) hqR
      linarith
    have e1 : (cn_Y X ^ 7) ^ (-(C₀ * (X.qq : ℝ))) ≤ Ydat X.I.n X.I.f X.I.rd g' X.b ^ (-(C₀ * (X.qq : ℝ))) :=
      Real.rpow_le_rpow_of_nonpos hY'pos hY7 hnp
    have e2 : (cn_Y X ^ 7) ^ (-(C₀ * (X.qq : ℝ))) = cn_Y X ^ (-(7 * C₀ * (X.qq : ℝ))) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hYpos.le]
      congr 1
      push_cast
      ring
    have e3 : cn_tauS X C₁ ≤ cn_Y X ^ (-(7 * C₀ * (X.qq : ℝ))) := cnd_tauS_anti X hC₁ hY
    rw [e2] at e1
    exact le_trans e3 e1
  have hvol4 : X.I.vol X.μf X.fund / volK ≤
      Ydat X.I.n X.I.f X.I.rd g' X.b ^ (4 * C * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ)) := by
    have hex : 0 ≤ C * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ) := by positivity
    refine le_trans hvol (le_trans (Real.rpow_le_rpow hYpos.le hY1 hex) ?_)
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith)
  refine cnd_deep_int X hV (S.measurableSet_Mod hst C₁) ?_ hA₁
  filter_upwards [hae] with x hx hxM
  have hlt : S.tau1 x < cn_tauS X C₁ := not_le.1 hxM
  have hhalf := lt_of_lt_of_le hlt (cnd_tauS_le_half X (by linarith : (1 : ℝ) ≤ C₁) hq hY)
  obtain ⟨a, τ, ha, haq, hpos, htop, hτ1, H⟩ := hx hhalf
  have hrd0 : 0 ≤ X.I.rd := le_trans zero_le_one (one_le_discriminant_root X.I)
  obtain ⟨ρ, Bs, r0, r1, r2, r3⟩ := cnd_refine C hC X.I.n X.qq X.I.f hq (one_le_autInst_f X.I) X.I.rd g' X.b (S.tau1 x)
    X.Dc volK |(X.kerD x).re| (one_le_discriminant_root X.I) hg'1 (hst.2.2.2.2.2.1 x).1 hhalf (Nat.cast_nonneg _) hvK a τ ha haq hpos
    htop hτ1 (fun b' hb1 hb2 => by
      obtain ⟨ρ, s, mult, s0, s1, s2, s3, s4, s5, s6⟩ := H b' hb1 hb2
      refine ⟨ρ, s, mult, s0, ?_, s2, s3, s4, s5, s6⟩
      have hρ₀ : 0 < τ b' / τ (b' + 1) := div_pos (hpos _) (hpos _)
      refine le_trans (cnd_diam_of_proved X Cq ρ _ hCq hρ₀ s1) ?_
      have : 0 ≤ (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ) * g' * X.I.rd * (τ b' / τ (b' + 1)) := by positivity
      nlinarith)
  exact hpt X.I.n X.qq X.I.f X.I.rd g' X.b (S.tau1 x) (cn_tauS X C₁) ρ _ Bs X.Dc _ volK hn hq hq2 (one_le_autInst_f X.I)
    (one_le_discriminant_root X.I) hg'1 hb (hst.2.2.2.2.2.1 x).1 hlt hτle (Nat.cast_nonneg _) hvK ENNReal.toReal_nonneg r0 r1 r2 r3 hvol4

end Formalism.MainNotions.LeviCoordinates

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CuCountOfPack
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def CSize.Inv {X : CData} (S : CSize X) : Prop := ∀ γ ∈ X.I.GFset, ∀ y, S.tau1 (γ * y) = S.tau1 y

def CSize.Lip {X : CData} (S : CSize X) : Prop :=
  ∀ y g, X.φ g ≠ 0 →
    S.tau1 y * Real.exp (-(1 / (X.I.f : ℝ)) * ∑ v, cartanDistance (X.I.ε v) (g.1 v)) ≤ S.tau1 (y * g)

def CSize.LowN {X : CData} (S : CSize X) : Prop :=
  ∀ W : Submodule X.I.E (Fin X.I.n → X.I.E), X.I.IsIsot W → ∀ x, ∃ c : ℝ, 0 < c ∧ ∀ m ∈ X.I.NA W, c ≤ S.tau1 (m * x)

theorem cu_count_of_pack (X : CData) (hn : 1 ≤ X.I.n) (S : CSize X) (hst : S.Strata) (hP : S.PackCount) (y : X.I.GA) :
    X.FarCount (cu.Act X (S.tau1 y)) (2 * (X.I.n : ℝ) ^ 2) {y} := by
  intro x hx r hr T hT
  obtain rfl : x = y := hx
  have hτ := hst.2.2.2.2.2.1 x
  have hs : (1 : ℝ) ≤ Real.sqrt (X.I.n : ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hn
  have h1 := hP x r hr T hT
  have h2 := Formalism.HermitianLatticeCounting.Final.S7.farCount (InfinitePlace X.I.F) X.I.n r (S.tau1 x) (Real.sqrt (X.I.n : ℝ)) hτ.1
    (by linarith [hτ.2]) hs hr
  have hsq1 : S.tau1 x ^ 2 ≤ 1 := pow_le_one₀ hτ.1.le (by linarith [hτ.2])
  have hbase1 : 1 ≤ 3 * Real.sqrt (X.I.n : ℝ) / S.tau1 x ^ 2 := by
    have := hτ.1
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hA : (3 * Real.sqrt (X.I.n : ℝ) / S.tau1 x ^ 2) ^ (2 * X.I.n ^ 2 * Fintype.card (InfinitePlace X.I.F)) ≤
      cu.Act X (S.tau1 x) :=
    pow_le_pow_right₀ hbase1 (Nat.mul_le_mul_left _ (card_infinite_places_le_degree X.I))
  calc (T.card : ℝ) ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ cu.Act X (S.tau1 x) * Real.exp (2 * (X.I.n : ℝ) ^ 2 * ∑ v, r v) :=
        mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le

theorem cu_sizeStep_of (X : CData) (hn : 1 ≤ X.I.n) (S : CSize X) (hst : S.Strata)
    (hP : S.PackCount) (hI : S.Inv) (hL : S.Lip) (hN : S.LowN) : cu.SizeStep X :=
  ⟨S.tau1, fun y => (hst.2.2.2.2.2.1 y).1, hI, cu_count_of_pack X hn S hst hP, hL, hN⟩

end Formalism.MainNotions.LeviCoordinates
end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.FfHasInfChar
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexOrder
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def ff_SigmaSum {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (σ Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ x y : H, ∃ (N : ℕ) (v w : Fin N → H), ∀ g : Formalism.REAL.UJ ε, ⟪x, Ψ (umat g) y⟫_ℂ = ∑ i, coefOn σ (v i) (w i) g

def FIdent (χ : ∀ n : ℕ, (Fin n → ℝ) → ℕ → ℂ) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : H →L[ℂ] H), Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ →
    IsOrthProjOnto E (lowKSub ε lam σ) →
    ∀ Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H), ff_Sph ε σ Ψ → ff_Compr ε E Ψ → ff_Eig ε (χ n lam) Ψ →
      ff_DSSum ε Ψ → ff_SigmaSum ε σ Ψ

def FSphAlg : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : H →L[ℂ] H), Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ →
    IsOrthProjOnto E (lowKSub ε lam σ) →
    ∀ Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H), ff_Sph ε σ Ψ → ff_Compr ε E Ψ → Ψ 1 = E → ff_SigmaSum ε σ Ψ →
      ∀ g ∈ UJset ε, Ψ g = E ∘L σ g ∘L E

def ff_HasInfChar {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (σ' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (c : ℕ → ℂ) : Prop :=
  ∀ v w : H, IsKFin ε σ' v → ∃ F : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F ∧
    (∀ g ∈ UJset ε, F g = ⟪w, σ' g v⟫_ℂ) ∧ ∀ (k : ℕ), ∀ g ∈ UJset ε, gelfandOp ε k F g = c k * F g

def QInfChar : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Nontrivial H → IsURepOn (UJset ε) σ' → IsIrredOn (UJset ε) σ' →
    IsSqIntOn ε σ' → ∃ c : ℕ → ℂ, ff_HasInfChar ε σ' c

def QClass (χ : ∀ n : ℕ, (Fin n → ℝ) → ℕ → ℂ) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
  ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Nontrivial H' → IsURepOn (UJset ε) σ' → IsIrredOn (UJset ε) σ' →
    IsSqIntOn ε σ' → ff_HasInfChar ε σ' (χ n lam) → (∃ S : Submodule ℂ H', IsKTypeOf ε σ' (Formalism.QuantumDeterminants.lowK ε lam) S) →
    ∃ U : H' ≃ₗᵢ[ℂ] H, ∀ g ∈ UJset ε, ∀ v : H', U (σ' g v) = σ g (U v)

def ff_L {n : ℕ} (lam : Fin n → ℝ) (i : ℕ) : ℝ := oneBasedParam lam i + ((n : ℝ) + 1) / 2 - (i : ℝ)

theorem ff_det_exp {n : ℕ} (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : Formalism.REAL.inP ε X) :
    (NormedSpace.exp X).det = 1 := by
  have hJ2 : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := Formalism.REAL.Jm_mul_self ε
  have hJu : IsUnit (Formalism.REAL.Jm ε) := ⟨⟨Formalism.REAL.Jm ε, Formalism.REAL.Jm ε, hJ2, hJ2⟩, rfl⟩
  have hJinv : (Formalism.REAL.Jm ε)⁻¹ = Formalism.REAL.Jm ε := Matrix.inv_eq_left_inv hJ2
  have hc : Formalism.REAL.Jm ε * X * Formalism.REAL.Jm ε = -X := (Formalism.REAL.parabolic_character_holds n ε X).2 hX
  have h1 : NormedSpace.exp (-X) = Formalism.REAL.Jm ε * NormedSpace.exp X * Formalism.REAL.Jm ε := by
    have := Matrix.exp_conj (Formalism.REAL.Jm ε) X hJu
    rw [hJinv, hc] at this
    exact this
  have h2 : (NormedSpace.exp (-X)).det = (NormedSpace.exp X).det := by
    rw [h1, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, hJ2, Matrix.det_one, one_mul]
  have h3 : NormedSpace.exp (-X) * NormedSpace.exp X = 1 := by
    rw [← Matrix.exp_add_of_commute (-X) X ((Commute.refl X).neg_left)]
    simp
  have h4 : (NormedSpace.exp X).det * (NormedSpace.exp X).det = 1 := by
    have := congrArg Matrix.det h3
    rwa [Matrix.det_mul, h2, Matrix.det_one] at this
  have hpos := Formalism.REAL.leading_minors_positive n X (hermitian_of_mem_p ε X hX).1 (Fin.last n)
  have h5 : Formalism.REAL.lminor (NormedSpace.exp X) (Fin.last n) = (NormedSpace.exp X).det := by
    unfold Formalism.REAL.lminor
    congr 1
  rw [h5] at hpos
  obtain ⟨him, hre⟩ := hpos
  set d := (NormedSpace.exp X).det with hd
  have hdr : d = ((d.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  have h6 : d.re * d.re = 1 := by
    have := congrArg Complex.re h4
    simpa [Complex.mul_re, him] using this
  have h7 : d.re = 1 := by nlinarith
  rw [hdr, h7]
  simp

end Formalism.MainNotions.LeviCoordinates

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.LowestProjectionAllOfAdmitted
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature

namespace BData

variable {X : BData}

theorem meas_mul : Measurable fun p : Formalism.QuantumDeterminants.Mt X.k X.r × Formalism.QuantumDeterminants.Mt X.k X.r =>
    Formalism.QuantumDeterminants.lmulM (Matrix.of p.1) p.2 := by
  unfold Formalism.QuantumDeterminants.lmulM
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  refine Finset.measurable_sum _ fun l _ => ?_
  have h1 : Measurable fun p : Formalism.QuantumDeterminants.Mt X.k X.r × Formalism.QuantumDeterminants.Mt X.k X.r => p.1 i l := by fun_prop
  have h2 : Measurable fun p : Formalism.QuantumDeterminants.Mt X.k X.r × Formalism.QuantumDeterminants.Mt X.k X.r => p.2 l j := by fun_prop
  exact h1.mul h2

variable (X) in

def SquareIntegrabilityBound (B : X.H → X.Vp) : Prop := ∀ χ, X.IsCut B χ → l2SG X.ν (X.Wf B χ) < ⊤

end BData

def BesselFinalFacts : Prop :=
  ∀ X : BData, X.Hyp → X.LowSmooth ∧ X.SmoothCyc ∧
    ∀ B : X.H → X.Vp, X.IsFun B → X.CutStep B ∧ X.SquareIntegrabilityBound B ∧ X.Repro B ∧ X.Exchange B

def LowProjAll : Prop := ∀ X : BData, X.Hyp → X.LowProj

end Formalism.MainNotions.LeviCoordinates

end
end

