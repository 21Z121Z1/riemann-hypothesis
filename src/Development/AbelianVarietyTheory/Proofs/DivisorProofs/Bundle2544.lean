import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1447
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1869
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1443
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1872
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2375
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2102
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1892
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2437
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1637
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1554
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1548
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1950
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2140
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2245
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2438
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2445
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetWittFrameSchwartzBound
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.TorusTheta

theorem min_pow_le_of_mem_cone {r : ℕ} {c : ℝ} (hc : 0 < c) {t : Fin r → ℝ}
    (ht : t ∈ GlobalTheory.SiegelSet.cone r c) (i : Fin r) : min 1 c ^ r ≤ t i := by
  obtain ⟨hpos, hstep, hlast⟩ := ht
  have hm0 : 0 < min 1 c := lt_min one_pos hc
  have hm1 : min 1 c ≤ 1 := min_le_left _ _
  have key : ∀ k : ℕ, ∀ i : Fin r, i.val + k + 1 = r → min 1 c ^ (k + 1) ≤ t i := by
    intro k
    induction k with
    | zero =>
      intro i hi
      simp only [zero_add, pow_one]
      exact (min_le_right _ _).trans (hlast i (by omega))
    | succ k ih =>
      intro i hi
      have hj : i.val + 1 < r := by omega
      have h1 := ih ⟨i.val + 1, hj⟩ (by simp; omega)
      have h2 := hstep i ⟨i.val + 1, hj⟩ rfl
      have h3 : 0 < t ⟨i.val + 1, hj⟩ := hpos _
      calc min 1 c ^ (k + 1 + 1) = min 1 c * min 1 c ^ (k + 1) := by ring
        _ ≤ min 1 c * t ⟨i.val + 1, hj⟩ := mul_le_mul_of_nonneg_left h1 hm0.le
        _ ≤ c * t ⟨i.val + 1, hj⟩ := mul_le_mul_of_nonneg_right (min_le_right _ _) h3.le
        _ ≤ t i := h2
  have := key (r - i.val - 1) i (by omega)
  refine le_trans ?_ this
  exact pow_le_pow_of_le_one hm0.le hm1 (by omega)

theorem mul_norm_le_norm_smul {ι V : Type} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V] {c' : ℝ} (hc' : 0 < c')
    (s : ι → ℝ) (hs : ∀ i, c' ≤ s i) (v : ι → V) : c' * ‖v‖ ≤ ‖fun i => s i • v i‖ := by
  rw [← le_div_iff₀' hc']
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [le_div_iff₀' hc']
  have hsi : 0 < s i := hc'.trans_le (hs i)
  calc c' * ‖v i‖ ≤ s i * ‖v i‖ := mul_le_mul_of_nonneg_right (hs i) (norm_nonneg _)
    _ = ‖s i • v i‖ := by rw [norm_smul, Real.norm_of_nonneg hsi.le]
    _ ≤ ‖fun i => s i • v i‖ := norm_le_pi_norm (fun i => s i • v i) i

theorem prod_elim_pow {κ : Type} [Fintype κ] {r : ℕ} (blk : κ → Option (Fin r)) (t : Fin r → ℝ) (f d : ℕ)
    (hcard : ∀ i : Fin r, (Finset.univ.filter (fun j => blk j = some i)).card = 2 * d) :
    ∏ j, (blk j).elim 1 t ^ f = (∏ i, t i ^ (f * d)) ^ 2 := by
  rw [← Finset.prod_fiberwise (Finset.univ : Finset κ) blk (fun j => ((blk j).elim 1 t : ℝ) ^ f)]
  have h1 : ∀ o : Option (Fin r), ∏ j ∈ Finset.univ.filter (fun j => blk j = o), (blk j).elim 1 t ^ f =
      (o.elim 1 t ^ f) ^ (Finset.univ.filter (fun j => blk j = o)).card := by
    intro o
    rw [← Finset.prod_const]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [(Finset.mem_filter.1 hj).2]
  rw [Finset.prod_congr rfl (fun o _ => h1 o), Fintype.prod_option]
  simp only [Option.elim_none, Option.elim_some, one_pow, one_mul, hcard]
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

end GlobalTheory.TorusTheta

namespace GlobalTheory.TorusTheta

theorem theta_torus_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E),
    GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf → ∀ c : ℝ, 0 < c →
    ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a,
      GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a → ∀ a' : UA σ X.J,
      (a' : GL (Fin n) (AE F E)) = HA.mat (AF F) σ ((1 : E) • X.J.map σ) a → ∀ (y : UA σ X.J) (h : UA σ W.J),
      ‖theta om Φ (a' * y) h‖ ≤ C * ((ht y : ℝ) * ht h) ^ k * ∏ i, t i ^ (Module.finrank ℚ F * d) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hWitt c hc Φ hΦ
  obtain ⟨co, blk, hrat, hcard, hact⟩ := GlobalTheory.T.witt_frame_darboux_coordinates F E σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hWitt
  obtain ⟨M₁, om₁, e, c₀, hco, hP₁, hc₀, he⟩ := GlobalTheory.T.darboux_coords_rational_points F E σ B n d X W M χX χW om r s r' s' hP co hrat
  obtain ⟨N₀, k₃, C₃, hlat⟩ := GlobalTheory.LatScaleSum.thetaSum_norm_le_pow F (Fin n × Fin d)
  have heΦ := (he Φ hΦ).1
  obtain ⟨C₁, k₁, hdec⟩ := GlobalTheory.T.weilRepresentation_pointwise_archimedeanDecay_bound F E σ B n d X W M₁ χX χW om₁ r s r' s' hP₁ (e Φ) heΦ N₀
  obtain ⟨C₂, k₂, hden⟩ := GlobalTheory.T.schwartz_theta_polynomial_growth F E σ B n d X W M₁ χX χW om₁ r s r' s' hP₁ (e Φ) heΦ
  set c' : ℝ := min 1 c ^ r₀ with hc'def
  have hc'0 : 0 < c' := pow_pos (lt_min one_pos hc) _
  have hc'1 : c' ≤ 1 := pow_le_one₀ (lt_min one_pos hc).le (min_le_left _ _)
  refine ⟨‖c₀‖⁻¹ * |C₃| * (c'⁻¹) ^ N₀ * |C₁| * |C₂| ^ k₃, k₁ + k₂ * k₃, ?_⟩
  intro t htc a hta a' ha' y h
  have tlow : ∀ i, c' ≤ t i := min_pow_le_of_mem_cone hc htc
  have tpos : ∀ i, 0 < t i := fun i => hc'0.trans_le (tlow i)
  set u : Fin n × Fin d → ℝ := fun j => (blk j).elim 1 t with hudef
  have hulow : ∀ j, c' ≤ u j := by
    intro j
    simp only [hudef]
    cases blk j with
    | none => exact hc'1
    | some i => exact tlow i
  have hupos : ∀ j, 0 < u j := fun j => hc'0.trans_le (hulow j)
  obtain ⟨κ, hκ, hom⟩ := GlobalTheory.T.torus_action_model_coordinates F E σ B n d X W M₁ χX χW om₁ r s r' s' hP₁ a' u hupos
    (by rw [hco]; exact hact t tpos a hta a' ha')

  have hΨ0 : om (y, h) Φ ∈ schA F (Fin n × Fin d) := (IsUWeilPair.isUSplitting hP.weil).pres _ _ hΦ
  have hT : om (a', 1) (om (y, h) Φ) ∈ schA F (Fin n × Fin d) := (IsUWeilPair.isUSplitting hP.weil).pres _ _ hΨ0
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ, Ψ = om₁ (y, h) (e Φ) := ⟨_, rfl⟩
  have hΨ : Ψ ∈ schA F (Fin n × Fin d) := hΨdef ▸ (IsUWeilPair.isUSplitting hP₁.weil).pres _ _ heΦ
  have hmul : ((a' * y, h) : UA σ X.J × UA σ W.J) = (a', 1) * (y, h) := by
    ext <;> simp
  have hsplit : om (a' * y, h) Φ = om (a', 1) (om (y, h) Φ) := by
    rw [hmul, map_mul, Module.End.mul_apply]
  have heT : e (om (a', 1) (om (y, h) Φ)) = om₁ (a', 1) Ψ := by
    rw [(he _ hΨ0).2.2, (he Φ hΦ).2.2, hΨdef]
  have hthT : thetaSum F (om (a', 1) (om (y, h) Φ)) = c₀⁻¹ * thetaSum F (om₁ (a', 1) Ψ) := by
    rw [← heT, (he _ hT).2.1, ← mul_assoc, inv_mul_cancel₀ hc₀, one_mul]
  have hfun : om₁ (a', 1) Ψ = fun x => κ * Ψ (fun j => infScale F (u j) * x j) := funext (hom Ψ hΨ)
  have hkey : theta om Φ (a' * y) h =
      c₀⁻¹ * (κ * thetaSum F (fun x => Ψ (fun j => infScale F (u j) * x j))) := by
    show thetaSum F (om (a' * y, h) Φ) = _
    rw [hsplit, hthT, hfun]
    unfold thetaSum
    rw [tsum_mul_left]

  have hκ' : ‖κ‖ = ∏ i, t i ^ (Module.finrank ℚ F * d) := by
    have h2 : ‖κ‖ ^ 2 = (∏ i, t i ^ (Module.finrank ℚ F * d)) ^ 2 := by
      rw [hκ]
      exact prod_elim_pow blk t _ d hcard
    have hnn : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ F * d) :=
      Finset.prod_nonneg fun i _ => pow_nonneg (tpos i).le _
    exact (pow_left_inj₀ (norm_nonneg _) hnn two_ne_zero).1 h2

  set P : ℝ := (ht y : ℝ) * ht h with hPdef
  have hP0 : 0 ≤ P := mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
  obtain ⟨m, hm1, hmC, hmint⟩ := hden y h
  have hdecay : ∀ ξ : Fin n × Fin d → F,
      ‖Ψ (fun j => infScale F (u j) * (fun i => algebraMap F (AF F) (ξ i)) j)‖ *
        (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀ ≤ (c'⁻¹) ^ N₀ * (C₁ * P ^ k₁) := by
    intro ξ
    beta_reduce
    have h1 := hdec y h (fun j => infScale F (u j) * algebraMap F (AF F) (ξ j))
    rw [← hΨdef] at h1
    have hnorm : c' * ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖ ≤
        ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖ := by
      simp only [evI_infScale_mul]
      exact mul_norm_le_norm_smul hc'0 u hulow _
    have hle : 1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖ ≤
        c'⁻¹ * (1 + ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖) := by
      have hi : 1 ≤ c'⁻¹ := one_le_inv₀ hc'0 |>.2 hc'1
      have h3 : ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖ ≤
          c'⁻¹ * ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖ := by
        rw [le_inv_mul_iff₀ hc'0]; exact hnorm
      nlinarith [norm_nonneg (fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i)))]
    have hpow : (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀ ≤
        (c'⁻¹) ^ N₀ * (1 + ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖) ^ N₀ := by
      have h0 : 0 ≤ 1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖ :=
        add_nonneg zero_le_one (norm_nonneg _)
      have h4 := pow_le_pow_left₀ h0 hle N₀
      rw [mul_pow] at h4
      exact h4
    calc ‖Ψ (fun j => infScale F (u j) * algebraMap F (AF F) (ξ j))‖ *
          (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀
        ≤ ‖Ψ (fun j => infScale F (u j) * algebraMap F (AF F) (ξ j))‖ *
          ((c'⁻¹) ^ N₀ * (1 + ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖) ^ N₀) :=
          mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
      _ = (c'⁻¹) ^ N₀ * (‖Ψ (fun j => infScale F (u j) * algebraMap F (AF F) (ξ j))‖ *
          (1 + ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖) ^ N₀) := by ring
      _ ≤ (c'⁻¹) ^ N₀ * (C₁ * P ^ k₁) := mul_le_mul_of_nonneg_left h1 (by positivity)
  have hint : ∀ ξ : Fin n × Fin d → F,
      Ψ (fun j => infScale F (u j) * (fun i => algebraMap F (AF F) (ξ i)) j) ≠ 0 →
        ∀ i, IsIntegral ℤ ((m : F) * ξ i) := by
    intro ξ hne
    rw [hΨdef] at hne
    exact hmint _ ξ (fun i => infScale_mul_snd F (u i) _) hne
  have hS := hlat ((c'⁻¹) ^ N₀ * (C₁ * P ^ k₁)) m (fun x => Ψ (fun j => infScale F (u j) * x j)) hm1 hdecay hint

  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hmk : (m : ℝ) ^ k₃ ≤ |C₂| ^ k₃ * P ^ (k₂ * k₃) := by
    rw [pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ hm0 (hmC.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hP0 _))) k₃
  have hS' : ‖thetaSum F (fun x => Ψ (fun j => infScale F (u j) * x j))‖ ≤
      |C₃| * (c'⁻¹) ^ N₀ * |C₁| * |C₂| ^ k₃ * P ^ (k₁ + k₂ * k₃) := by
    refine hS.trans ?_
    calc C₃ * ((c'⁻¹) ^ N₀ * (C₁ * P ^ k₁)) * (m : ℝ) ^ k₃
        ≤ |C₃| * ((c'⁻¹) ^ N₀ * (|C₁| * P ^ k₁)) * (m : ℝ) ^ k₃ := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg hm0 _)
          calc C₃ * ((c'⁻¹) ^ N₀ * (C₁ * P ^ k₁)) ≤ |C₃ * ((c'⁻¹) ^ N₀ * (C₁ * P ^ k₁))| := le_abs_self _
            _ = |C₃| * ((c'⁻¹) ^ N₀ * (|C₁| * P ^ k₁)) := by
              rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (c'⁻¹) ^ N₀),
                abs_of_nonneg (pow_nonneg hP0 _)]
      _ ≤ |C₃| * ((c'⁻¹) ^ N₀ * (|C₁| * P ^ k₁)) * (|C₂| ^ k₃ * P ^ (k₂ * k₃)) :=
          mul_le_mul_of_nonneg_left hmk (by positivity)
      _ = |C₃| * (c'⁻¹) ^ N₀ * |C₁| * |C₂| ^ k₃ * P ^ (k₁ + k₂ * k₃) := by ring
  rw [hkey, norm_mul, norm_mul, norm_inv, hκ']
  have hT0 : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ F * d) :=
    Finset.prod_nonneg fun i _ => pow_nonneg (tpos i).le _
  calc ‖c₀‖⁻¹ * ((∏ i, t i ^ (Module.finrank ℚ F * d)) * ‖thetaSum F (fun x => Ψ (fun j => infScale F (u j) * x j))‖)
      ≤ ‖c₀‖⁻¹ * ((∏ i, t i ^ (Module.finrank ℚ F * d)) *
          (|C₃| * (c'⁻¹) ^ N₀ * |C₁| * |C₂| ^ k₃ * P ^ (k₁ + k₂ * k₃))) := by gcongr
    _ = _ := by ring

end GlobalTheory.TorusTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelWeilSectionLawDiagonalLagrangianStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
theorem _root_.GlobalTheory.T.siegelWeil_section_law_diagonalLagrangian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ),
        (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
          co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.ResEtaF χS nS →
      ∀ ωd : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ),
          Formalism.IndefR.DatumF.IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ omp : UG (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) × UG (cA σ) (incM F JB) →*
            Module.End ℂ ((κ → AF F) → ℂ),
          GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ωd omp →
      ∀ (p : UG (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ)) (t : GL (Fin nT) (AF F ⊗[F] E)),
        p.1.1 * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) = ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * t.1 →
      ∀ Φ ∈ schA F κ, omp (p, 1) Φ ∈ schA F κ ∧
        GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (omp (p, 1) Φ)) =
          (χS (Matrix.GeneralLinearGroup.det t) : ℂ) *
            ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
              (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((Fintype.card (Fin nS) : ℝ) / 2) : ℝ) : ℂ) *
            GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) := by
  first | exact @GlobalTheory.SiegelLawDblTargetF.main_law | exact GlobalTheory.SiegelLawDblTargetF.main_law | (intros; apply GlobalTheory.SiegelLawDblTargetF.main_law <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeMaxSquaredBound
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.LamCore

theorem absA_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) {B : ℝ} (hB : 0 ≤ B) (h : ∀ τ k, |(laOf Dw a n τ k : ℝ)| ≤ B) :
    ((GlobalTheory.LevGeo.absA Dw a : ℕ) : ℝ) ≤ (Module.finrank ℚ E : ℝ) * (((Dw.p + Dw.q : ℕ) : ℝ) * B) := by
  have hn : (0 : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have key : ∀ (b : E →+* ℂ) (i : ℕ), i < Dw.mult b → (a (b, i) : ℝ) ≤ B := by
    intro b i hi
    by_cases hb : b (H.rt : E) = H.rt0
    · have hp : i < Dw.p := by simpa [Datum.mult, hb] using hi
      have := h ⟨b, hb⟩ ⟨i, by omega⟩
      simp only [laOf, weightOf, if_pos hp, Int.cast_add, Int.cast_natCast] at this
      linarith [le_abs_self ((a (b, i) : ℝ) + ((n / 2 : ℕ) : ℝ))]
    · have hq : i < Dw.q := by simpa [Datum.mult, hb] using hi
      have := h ⟨conjEmb b, conj_mem hb⟩ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩
      have e1 : ¬ (Dw.p + (Dw.q - 1 - i) < Dw.p) := by omega
      have e2 : Dw.q - 1 - (Dw.p + (Dw.q - 1 - i) - Dw.p) = i := by omega
      simp only [laOf, weightOf, if_neg e1, e2, conjEmb_conjEmb, Int.cast_sub, Int.cast_neg, Int.cast_natCast] at this
      linarith [neg_abs_le (-(a (b, i) : ℝ) - ((n / 2 : ℕ) : ℝ))]
  unfold GlobalTheory.LevGeo.absA
  rw [Nat.cast_sum, ← NumberField.Embeddings.card E ℂ, ← nsmul_eq_mul, ← Finset.card_univ]
  refine Finset.sum_le_card_nsmul _ _ _ fun b _ => ?_
  rw [Nat.cast_sum]
  refine (Finset.sum_le_card_nsmul _ _ B fun (i : Fin (Dw.mult b)) _ => key b (i : Fin (Dw.mult b)) i.2).trans ?_
  rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ hB
  have : Dw.mult b ≤ Dw.p + Dw.q := by unfold Datum.mult; split_ifs <;> omega
  exact_mod_cast this

theorem collect {f r q L b X x Om w lam sc rd : ℝ} (hf : 8 ≤ f) (hr : 1 ≤ r) (hq0 : 0 ≤ q) (hq : q ≤ r) (hL : 10 ≤ L)
    (hLx : L ≤ x) (hb : 1 ≤ b) (hZ : f * r * L ≤ X) (hOm : |Om| ≤ 3 * L) (hw0 : 0 ≤ w) (hw : w ≤ 10 * (f * r) * b)
    (h1 : lam ≤ ((1 + |Om|) / 2 + 2 * L + (2 * q + 1) * (6 * f + 48) * (2 * L)) * w)
    (h2 : sc ≤ 250 * f ^ 2 * r ^ 2 * (2 * L)) (h3 : rd ≤ 217 * (f * r * L) ^ 2) :
    2 * lam + 2 * sc + rd ≤ x ^ 4 * X ^ 2 * b := by
  have hfr : 1 ≤ f * r := by nlinarith
  have hZ0 : L ≤ f * r * L := by nlinarith
  have hfrX : f * r ≤ X := by nlinarith
  have hX : 1 ≤ X := hfr.trans hfrX
  have a1 : (2 * q + 1) * (6 * f + 48) ≤ (3 * r) * (12 * f) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have a2 : (2 * q + 1) * (6 * f + 48) * (2 * L) ≤ 72 * (f * r * L) := by nlinarith
  have a3 : (1 + |Om|) / 2 + 2 * L + (2 * q + 1) * (6 * f + 48) * (2 * L) ≤ 76 * X := by linarith
  have a4 : w ≤ 10 * X * b := hw.trans (by gcongr)
  have a5 : lam ≤ 76 * X * (10 * X * b) := h1.trans (mul_le_mul a3 a4 hw0 (by positivity))
  have a6 : (f * r * L) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (by linarith) hZ 2
  have a7 : (f * r) * (f * r * L) ≤ X * X := mul_le_mul hfrX hZ (by linarith) (by linarith)
  have a8 : X ^ 2 ≤ X ^ 2 * b := le_mul_of_one_le_right (by positivity) hb
  have a9 : (10 : ℝ) ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) (hL.trans hLx) 4
  have a10 : 10 ^ 4 * (X ^ 2 * b) ≤ x ^ 4 * (X ^ 2 * b) := mul_le_mul_of_nonneg_right a9 (by positivity)
  have a11 : 0 ≤ X ^ 2 * b := by positivity
  nlinarith

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem ne_bot_of_form {K K' R W : Type} [Field K] [NumberField K] [Field K'] [AddCommGroup R] [Module K R] [AddCommGroup W]
    [Module K W] [Module K' W] {C C' : Submodule K R} (hC : C' = C) [Module (𝓞 K) C'] {M : Submodule (𝓞 K) C'}
    (hs : Submodule.span K (M : Set C') = ⊤) {WK : Submodule K W} (e : C ≃ₗ[K] WK) {n : ℕ} {b : Fin n → W} (hb : ∀ k, b k ∈ WK)
    (hsp : Submodule.span K' (Set.range b) = ⊤) {y : W} (hy : y ≠ 0) : M ≠ ⊥ := by
  subst hC
  rintro rfl
  rw [Submodule.bot_coe, Submodule.span_zero_singleton] at hs
  have h3 : ∀ k, b k = 0 := fun k => by
    have h1 : e.symm ⟨b k, hb k⟩ ∈ (⊥ : Submodule K C') := by rw [hs]; exact Submodule.mem_top
    rw [Submodule.mem_bot, LinearEquiv.map_eq_zero_iff] at h1
    exact congrArg Subtype.val h1
  have h4 : Submodule.span K' (Set.range b) ≤ ⊥ := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact h3 k)
  exact hy (h4 (by rw [hsp]; exact Submodule.mem_top))

set_option maxHeartbeats 1000000 in

theorem latW_ne_bot (h : GramAt p i) : latW (p.T.U ((i : ℕ) + 1)) (Gk p i) ≠ ⊥ := by
  obtain ⟨-, -, hg, -, -, hs⟩ := h
  obtain ⟨y, -, hy⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hg
  obtain ⟨n, b, hb, -, -, -, hsp⟩ := p.fw.ks i
  exact ne_bot_of_form (cuspW_wtZ _ _) hs (p.fw.e i) hb hsp hy

set_option maxHeartbeats 1000000 in

theorem slopeMax_le (h6 : GlobalTheory.Published.TamagawaSpecialUnitary) {PP A : ℝ} (hR : RecTied D L) (hG : GramAt p i)
    (hN : HostNum D L PP A 1) (hW : WtNum p i PP) :
    slopeMax_sq (nrmK p.fw i) (latW (p.T.U ((i : ℕ) + 1)) (Gk p i)) ≤ L.sc.x ^ (2 * A + 4) * L.sc.b := by
  have hj : Formalism.L2.Pj.InR D ((i : ℕ) + 1) := ⟨by omega, i.2⟩
  obtain ⟨hLaws, hnorm⟩ := GlobalTheory.LevGeo.laws_of_coreJ D p.T _ p.fw.laws hj
  have hn : normW (p.T.U ((i : ℕ) + 1)) (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) (GlobalTheory.LevGeo.coreDict p.T.toCore ((i : ℕ) + 1))
      (Gk p i) = nrmK p.fw i := by
    funext σ f; exact hnorm _ σ f
  obtain ⟨_, χ, hχ, hOm, -, -⟩ := GlobalTheory.T.logPeriod_eq_kroneckerCharacter_logPeriod_of_host D L p.T.Q p.fw.laws.pins.1 p.Del p.h0
  have hgood : GoodW (p.T.U ((i : ℕ) + 1)) (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1))
      (GlobalTheory.LevGeo.coreDict p.T.toCore ((i : ℕ) + 1)) (Gk p i) := ⟨by rw [hn]; exact hG.2.2.2.1, hG.2.2.2.2⟩
  have main := GlobalTheory.T.kronecker_character_frame_third h6 D _ _ _ _ _ _ _ _ hLaws χ hχ (wtA (p.κ i)) (p.κ i).n hW.dom hgood (latW_ne_bot p i hG)
  rw [hn] at main
  refine main.trans ?_
  rw [hOm, p.fw.laws.pins.2.1.1, hW.cols]
  obtain ⟨-, hL, hLx, -⟩ := hN.big
  have hfd : fdeg D.host.E = D.R.f := by unfold fdeg; rw [hN.deg]; omega
  have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hN.f8
  have hr2 : 2 ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : 1 ≤ D.R.r)
  have hnV : (1 : ℝ) ≤ D.R.nV := by exact_mod_cast (by unfold Ranks.nV; omega : 1 ≤ D.R.nV)
  have hbL : L.sc.b = Real.exp L.sc.L := rfl
  have hb : 1 ≤ L.sc.b := by rw [hbL]; exact Real.one_le_exp (by linarith)
  have hx0 : 0 < L.sc.x := by linarith
  have hXb : L.sc.x ^ A ≤ L.sc.b := by simpa using hN.room
  have hP := hN.poly.2.2
  have hfr : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by nlinarith
  have hZ : (D.R.f : ℝ) * D.R.r * L.sc.L ≤ L.sc.x ^ A :=
    le_trans (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) hnV) (by linarith)) hP
  have ht : ((fdeg D.host.E * D.R.r * D.R.nV : ℕ) : ℝ) ≤ L.sc.b := by
    rw [hfd]; push_cast
    exact (le_mul_of_one_le_right (by positivity) (by linarith)).trans (hP.trans hXb)
  have hs : ((GlobalTheory.LevGeo.absA (dat p i) (wtA (p.κ i)) : ℕ) : ℝ) ≤ 8 * ((D.R.f : ℝ) * D.R.r) * L.sc.b := by
    have := absA_le (dat p i) (wtA (p.κ i)) (p.κ i).n (by positivity) hW.up
    rw [hW.sig.2.2, hN.deg] at this
    push_cast at this
    linarith
  have hs0 : (0 : ℝ) ≤ ((GlobalTheory.LevGeo.absA (dat p i) (wtA (p.κ i)) : ℕ) : ℝ) := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ ((fdeg D.host.E * D.R.r * D.R.nV : ℕ) : ℝ) := Nat.cast_nonneg _
  generalize ((GlobalTheory.LevGeo.absA (dat p i) (wtA (p.κ i)) : ℕ) : ℝ) = s at *
  generalize ((fdeg D.host.E * D.R.r * D.R.nV : ℕ) : ℝ) = t at *
  have hbb : L.sc.b ≤ (D.R.f : ℝ) * D.R.r * L.sc.b := le_mul_of_one_le_left (by linarith) hfr
  have hw : s + t + 1 ≤ 10 * ((D.R.f : ℝ) * D.R.r) * L.sc.b := by linarith
  have hlw : Real.log (s + t + 1) ≤ 2 * (2 * L.sc.L) := by
    refine (Real.log_le_log (by linarith) hw).trans ?_
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity), hbL, Real.log_exp]
    linarith [hN.logfr.1, Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)]
  have hg : ∀ k, 0 < D.host.g k := fun k => (D.host.g_prime k).pos
  have hM : 1 ≤ D.host.g 0 * D.host.g 1 := Nat.mul_pos (hg 0) (hg 1)
  have hlM : Real.log ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) ≤ 30 * (2 * L.sc.L) := by
    push_cast
    rw [Real.log_mul (by exact_mod_cast (hg 0).ne') (by exact_mod_cast (hg 1).ne')]
    linarith [hN.logg 0, hN.logg 1]
  have hd : 1 ≤ D.host.d := by rw [← p.fw.laws.pins.1.1]; exact p.T.Q.H.d_prime.pos
  have hl1 : Real.log ((fdeg D.host.E : ℝ) * D.R.r) ≤ 2 * L.sc.L := by rw [hfd]; linarith [hN.logfr.1]
  have hl2 : Real.log (dE D.host.E) ≤ 4 * (fdeg D.host.E : ℝ) * (2 * L.sc.L) := by
    rw [hfd]; unfold dE
    have : 0 ≤ (D.R.f : ℝ) * L.sc.L := by positivity
    linarith [hN.disc]
  have hl3 : Real.log (D.host.d : ℝ) ≤ 4 * (2 * L.sc.L) := by linarith [hN.logd]
  have n1 := (GlobalTheory.T.supremum_constant_log_bound D.host.E D.R.r D.host.d _ (s + t + 1) (2 * L.sc.L) hr2 hd hM (by linarith) (by linarith)
    hl1 hlM hl2 hl3 hlw).2
  have n2 := GlobalTheory.T.meanLogSupNormLoss_le_linear_in_weight D.host.E D.R.r (dat p i).q D.host.d _ (ofRecord D L p.Del p.h0).logOm s t (2 * L.sc.L) (by omega) hd hM
    (by linarith) hs0 ht0 hl1 hlM hl2 hl3 hlw
  have n3 := (log_rd_le_fieldSz _).trans (hR.core_size_le p (by linarith))
  rw [hfd] at n1 n2
  have hq : ((dat p i).q : ℝ) ≤ D.R.r := by exact_mod_cast (by have := hW.sig.2.2; omega : (dat p i).q ≤ D.R.r)
  have e : L.sc.x ^ (2 * A + 4) = L.sc.x ^ 4 * (L.sc.x ^ A) ^ 2 := by
    rw [Real.rpow_add hx0, mul_comm 2 A, Real.rpow_mul hx0.le, mul_comm]
    norm_cast
  rw [e]
  exact collect hf hr (Nat.cast_nonneg _) hq hL hLx hb hZ hW.om (add_nonneg hs0 ht0) (by linarith) n2 n1 n3

theorem lamCore : Hypotheses2 → Gram → Lifts fun Fm x _ ι p i _ A =>
    slopeMax_sq (nrmK p.fw i) (latW (p.T.U ((i : ℕ) + 1)) (Gk p i)) ≤ (Fm.L x ι).sc.x ^ A * (Fm.L x ι).sc.b := by
  intro hP hG
  refine Closed.imp (Closed.and hG (Closed.and (GlobalTheory.CovTop.Sizes.hostN 1) GlobalTheory.T.weight_bound_holds)) ?_
  rintro eps Fm CH - ⟨⟨_, -, h1⟩, ⟨A, hA, h2⟩, ⟨_, -, h3⟩⟩
  obtain ⟨x0, h⟩ := h1.and (h2.and h3)
  refine ⟨2 * A + 4, by linarith, x0, fun x hx hle ι p hp i => ?_⟩
  obtain ⟨a, b, c⟩ := h x hx hle ι p hp
  exact slopeMax_le p i hP.p6 hp.2 (a i) (b i) (c i)

end GlobalTheory.CovTop.LamCore

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionsPairSumRatFnFamilyTensor
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem smallFam_pair_tens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (J : Type) (f : J → X.functionField) (w : J → ℝ), (∀ j, f j ∈ P.Bl 1 1 (Real.exp (-w j))) → SmallFam (P.L.tens P.A) f w := by
  intro k _ X _ p P J f w hf
  have e (c : (P.L.tens P.A).B.ι) (j : J) :
      f j * (((P.r c.1 * P.r' c.2 : X.functionFieldˣ)) : X.functionField) = P.loc 1 1 (f j) c.1 c.2 := by
    simp only [Pair.loc, Units.val_mul, zpow_one]; ring
  refine ⟨fun c => P.r c.1 * P.r' c.2, GlobalTheory.PtHtComb.isRatSec_tens P.hr P.hr', ?_, ?_⟩
  · intro x c hc j
    rw [e]
    exact (hf j).1 x c.1 c.2 hc.1 hc.2
  · intro σ y c hc j
    obtain ⟨hc₁, hc₂⟩ := mem_ptsIn_inf.1 hc
    have h := nu_eq k X p P 1 1 (f j) (hf j).1 σ y c.1 c.2 hc₁ hc₂
    have hb := (hf j).2 σ y
    rw [h] at hb
    rw [e]
    change _ * Real.exp (-((P.L.φ σ).φ c.1 y + (P.A.φ σ).φ c.2 y) / 2) ≤ _
    simpa using hb

end GlobalTheory.HSNef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionDescendsFiniteFlatSurjeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_descends_finite_flat_surjective : ∀ (S : Scheme.{0}) (A B : Over S) (g : ℕ) (q : A ⟶ B), SmoothOfRelativeDimension g A.hom → Smooth B.hom → IsFinite q.left → Flat q.left → Surjective q.left → SmoothOfRelativeDimension g B.hom := by
  first | exact @GlobalTheory.FiniteSurjRelDim.smoothOfRelativeDimension_of_finite_surjective | exact GlobalTheory.FiniteSurjRelDim.smoothOfRelativeDimension_of_finite_surjective | (intros; apply GlobalTheory.FiniteSurjRelDim.smoothOfRelativeDimension_of_finite_surjective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionFiniteSurjectiveAbelianStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_finite_surjective_abelianVariety : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' : Over (Sp K)) [GrpObj A] [GrpObj A'] (g : ℕ) (q : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' → IsFinite q.left → Surjective q.left → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g A'.hom := by
  first | exact @GlobalTheory.FiniteSurjDimField.smoothOfRelativeDimension_of_finite_surjective | exact GlobalTheory.FiniteSurjDimField.smoothOfRelativeDimension_of_finite_surjective | (intros; apply GlobalTheory.FiniteSurjDimField.smoothOfRelativeDimension_of_finite_surjective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalGenericFibreAffineFrameCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toroidalGenericFibre_affineFrameCover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (V : (gen Y).Opens) (τ : E →+* ℂ), τ (H.rt : E) = H.rt0 → FrameCover Y.t (genι Y) (genStr Y) V (HermitianCompactForm.chi c τ) D.p D.q := by
  first | exact @GlobalTheory.DetLine.frameCover_gen | exact GlobalTheory.DetLine.frameCover_gen | (intros; apply GlobalTheory.DetLine.frameCover_gen <;> assumption)
end

