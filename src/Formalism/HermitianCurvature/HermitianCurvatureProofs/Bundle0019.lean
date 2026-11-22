import Formalism.HermitianCurvature.LatticeHerglotzBound
import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PointwiseStabiliserParametrisationBijective
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ReductionSurjective
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MemIntegralGlOfMiddleBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LduDecompositionExists
import Formalism.HermitianCurvature.StatementTA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTopBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OffDiagonalSchurComplement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0014
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0017
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BudgetLiftSquareRoot
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0008
import Formalism.HermitianCurvature.StatementTB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0018
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockStartPoints
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0013
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OneLevelCoefficients

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockEstimatesSumForm
section
open Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.BaseGramNonnegativity

open Formalism.FourierDecayAlt.crystallineComparison Formalism.FourierDecayAlt.TB

theorem sum_re_nonneg {α : Type} (Y : Finset α) (κ G : α → α → ℂ) (hκ : PSDOn Y κ) (hG : PSDOn Y G) :
    0 ≤ (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * G h h').re := by
  have H := (Matrix.PosSemidef.hadamard hκ hG).re_dotProduct_nonneg (fun _ => (1 : ℂ))
  simp only [dotProduct, Matrix.mulVec, Matrix.hadamard_apply, Matrix.of_apply, Pi.star_apply,
    star_one, one_mul, mul_one, RCLike.re_to_complex] at H
  convert H using 2
  rw [← Finset.sum_coe_sort Y]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [← Finset.sum_coe_sort Y]

variable {E W : Type} [Field E] (D : Data E W)

theorem baseGram_sub (ε : ℝ) (k : ℕ) (w : W) (Y : Finset (Pt E)) (κ κ' : Pt E → Pt E → ℂ) :
    D.N0 ε k w Y (fun h h' => κ' h h' - κ h h') = D.N0 ε k w Y κ' - D.N0 ε k w Y κ := by
  simp only [Data.N0, sub_mul, Finset.sum_sub_distrib, Complex.sub_re, sub_div]

theorem baseGram_smul (ε : ℝ) (k : ℕ) (w : W) (Y : Finset (Pt E)) (r : ℝ) (κ : Pt E → Pt E → ℂ) :
    D.N0 ε k w Y (fun h h' => (r : ℂ) * κ h h') = r * D.N0 ε k w Y κ := by
  simp only [Data.N0, mul_assoc, ← Finset.mul_sum, Complex.re_ofReal_mul, mul_div_assoc]

theorem baseGram_sum (ε : ℝ) (k : ℕ) (w : W) (Y : Finset (Pt E)) {ι : Type} (T : Finset ι)
    (κ : ι → Pt E → Pt E → ℂ) :
    D.N0 ε k w Y (fun h h' => ∑ t ∈ T, κ t h h') = ∑ t ∈ T, D.N0 ε k w Y (κ t) := by
  simp only [Data.N0, Finset.sum_mul, ← Finset.sum_div, ← Complex.re_sum]
  congr 2
  calc _ = ∑ h ∈ Y, ∑ t ∈ T, ∑ h' ∈ Y, κ t h h' * D.gram ε k w h h' :=
        Finset.sum_congr rfl (fun h _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

theorem baseGram_nonneg (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ} (hε : 0 < ε) (k : ℕ) (w : W)
    (Y : Finset (Pt E)) (κ : Pt E → Pt E → ℂ) (hκ : PSDOn Y κ) : 0 ≤ D.N0 ε k w Y κ :=
  div_nonneg (sum_re_nonneg Y κ _ hκ (hG ε hε k w Y)) (hW w).le

theorem baseGramMonotone' : BaseGramMonotone := by
  intro E W _ D hG hW ε hε k w Y κ κ' hκ hκκ'
  refine ⟨baseGram_nonneg D hG hW hε k w Y κ hκ, ?_⟩
  have := baseGram_nonneg D hG hW hε k w Y _ hκκ'
  rw [baseGram_sub] at this
  linarith

theorem corT_ok : CorT := by
  intro E W _ D hG hW ε hε k Y T0 Th KK e Ws θ Mv Bmax Lhs he hMv hθ hTh hsum hL hB
  have key : ∀ w', ∑ t₀ ∈ T0, D.N0 ε k w' Y (Th t₀) ≤ (1 + e) * D.N0 ε k w' Y KK := by
    intro w'
    have h := baseGram_nonneg D hG hW hε k w' Y _ hsum
    have h2 := baseGram_sub D ε k w' Y (fun h h' => ∑ t₀ ∈ T0, Th t₀ h h')
      (fun h h' => ((1 + e : ℝ) : ℂ) * KK h h')
    have h3 : (fun h h' => (1 + (e : ℂ)) * KK h h' - ∑ t₀ ∈ T0, Th t₀ h h') =
        (fun h h' => ((1 + e : ℝ) : ℂ) * KK h h' - ∑ t₀ ∈ T0, Th t₀ h h') := by
      push_cast; rfl
    rw [h3, h2, baseGram_smul, baseGram_sum] at h
    linarith
  have hθ0 := hθ.1
  constructor
  · calc ∑ t₀ ∈ T0, Lhs t₀ ≤ ∑ t₀ ∈ T0, Mv * ∑ w' ∈ Ws, θ w' * D.N0 ε k w' Y (Th t₀) :=
          Finset.sum_le_sum hL
      _ = Mv * ∑ w' ∈ Ws, θ w' * ∑ t₀ ∈ T0, D.N0 ε k w' Y (Th t₀) := by
          rw [← Finset.mul_sum]; congr 1
          rw [Finset.sum_comm]; simp only [Finset.mul_sum]
      _ ≤ Mv * ∑ w' ∈ Ws, θ w' * ((1 + e) * D.N0 ε k w' Y KK) := by
          apply mul_le_mul_of_nonneg_left _ hMv
          exact Finset.sum_le_sum (fun w' _ => mul_le_mul_of_nonneg_left (key w') (hθ0 w'))
      _ = (1 + e) * Mv * ∑ w' ∈ Ws, θ w' * D.N0 ε k w' Y KK := by
          simp only [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun _ _ => by ring)
  · apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by linarith) hMv)
    calc ∑ w' ∈ Ws, θ w' * D.N0 ε k w' Y KK ≤ ∑ w' ∈ Ws, θ w' * Bmax :=
          Finset.sum_le_sum (fun w' hw' => mul_le_mul_of_nonneg_left (hB w' hw') (hθ0 w'))
      _ = Bmax := by rw [← Finset.sum_mul, hθ.2.2, one_mul]

theorem Wb_mono {n m : ℕ} (h : n ≤ m) : D.Wb n ⊆ D.Wb m := by
  intro x hx
  simp only [Data.Wb, Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hx.2.trans h⟩

theorem estBlockOfSumForm_ok : EstBlockOfSumForm := by
  intro E W _ D C₄ hG hW hSF ε hε i s hs hsi hir w hw hcnt hvol
  obtain ⟨Mv, hMv, θ, hθ, hb⟩ := hSF ε hε i s hs hsi hir w hw hcnt hvol
  have hsub : D.Wb (D.cnt w + s * D.K) ⊆ D.Wb (D.cnt w + (s + 1) * D.K) :=
    Wb_mono D (by nlinarith)
  have hext : ∀ g : W → ℝ, ∑ w' ∈ D.Wb (D.cnt w + (s + 1) * D.K), θ w' * g w' =
      ∑ w' ∈ D.Wb (D.cnt w + s * D.K), θ w' * g w' := by
    intro g
    symm
    refine Finset.sum_subset hsub (fun x _ hx => ?_)
    rw [hθ.2.1 x hx, zero_mul]
  refine ⟨θ, ⟨hθ.1, fun a ha => hθ.2.1 a (fun h => ha (hsub h)), ?_⟩, ?_⟩
  · have := hext (fun _ => 1)
    simp only [mul_one] at this
    rw [this, hθ.2.2]
  · intro Y hY κ hκ t₀ S hS
    have h := hb Y hY κ hκ t₀ S hS
    rw [hext]
    have hX : 0 ≤ ∑ w' ∈ D.Wb (D.cnt w + s * D.K), θ w' * D.N0 ε (i - s) w' Y κ :=
      Finset.sum_nonneg (fun w' _ => mul_nonneg (hθ.1 w') (baseGram_nonneg D hG hW hε _ _ Y κ hκ))
    exact h.trans (mul_le_mul_of_nonneg_right hMv hX)

end Formalism.FourierDecayAlt.P.BaseGramNonnegativity

theorem Formalism.FourierDecayAlt.P.baseGramMonotone : Formalism.FourierDecayAlt.crystallineComparison.BaseGramMonotone := Formalism.FourierDecayAlt.P.BaseGramNonnegativity.baseGramMonotone'
theorem Formalism.FourierDecayAlt.P.cosetSumBound : Formalism.FourierDecayAlt.crystallineComparison.CorT := Formalism.FourierDecayAlt.P.BaseGramNonnegativity.corT_ok
theorem Formalism.FourierDecayAlt.P.blockEstimateOfCosetSum : Formalism.FourierDecayAlt.crystallineComparison.EstBlockOfSumForm :=
  Formalism.FourierDecayAlt.P.BaseGramNonnegativity.estBlockOfSumForm_ok
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainAndRowSums
section
open Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.ChainAndRowSums

open Formalism.FourierDecayAlt.crystallineComparison

theorem cm_two {W : Type} (Wd : Finset W) (c : ℕ → W → W → ℝ) (k : ℕ) (w w'' : W) :
    chainMat Wd c (k + 2) w w'' = ∑ w' ∈ Wd, c (k + 2) w w' * chainMat Wd c (k + 1) w' w'' := by
  simp [chainMat]

theorem cm_one {W : Type} (Wd : Finset W) (c : ℕ → W → W → ℝ) : chainMat Wd c 1 = c 1 := by
  simp [chainMat]

theorem chainSum_ok : ChainSum := by
  intro W X Wd s c caa Nd N0 T hs h1 htr hfin
  have key : ∀ n, 1 ≤ n → n ≤ s - 1 → ∀ w ∈ Wd, ∀ t,
      Nd n w t ≤ ∑ w'' ∈ Wd, chainMat Wd c n w w'' * N0 w'' := by
    intro n
    induction n with
    | zero => intro h; omega
    | succ m ih =>
      intro _ hns w hw t
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simpa [cm_one] using h1 w hw t
      · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        have ih' := ih (by omega) (by omega)
        have h := htr (k + 1 + 1) (by omega) hns
          (fun w' => ∑ w'' ∈ Wd, chainMat Wd c (k + 1) w' w'' * N0 w'')
          (by intro w' hw' t'; simpa using ih' w' hw' t') w hw t
        calc Nd (k + 1 + 1) w t
            ≤ ∑ w' ∈ Wd, c (k + 1 + 1) w w' *
                ∑ w'' ∈ Wd, chainMat Wd c (k + 1) w' w'' * N0 w'' := h
          _ = ∑ w'' ∈ Wd, chainMat Wd c (k + 1 + 1) w w'' * N0 w'' := by
            rw [show k + 1 + 1 = k + 2 from rfl]
            simp only [cm_two, Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  intro w hw
  have h := hfin (fun w' => ∑ w'' ∈ Wd, chainMat Wd c (s - 1) w' w'' * N0 w'')
    (fun w' hw' t => key (s - 1) (by omega) le_rfl w' hw' t) w hw
  calc T w ≤ ∑ w' ∈ Wd, caa w w' * ∑ w'' ∈ Wd, chainMat Wd c (s - 1) w' w'' * N0 w'' := h
    _ = ∑ w'' ∈ Wd, coMat Wd c caa s w w'' * N0 w'' := by
      simp only [coMat, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

theorem cm_nonneg {W : Type} (Wd : Finset W) (c : ℕ → W → W → ℝ) (hc : ∀ n w w', 0 ≤ c n w w') :
    ∀ n w w', 0 ≤ chainMat Wd c n w w' := by
  have : ∀ n, (∀ w w', 0 ≤ chainMat Wd c n w w') ∧ (∀ w w', 0 ≤ chainMat Wd c (n + 1) w w') := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun w w' => ?_, fun w w' => ?_⟩
      · simp only [chainMat]; split_ifs <;> norm_num
      · rw [cm_one]; exact hc 1 w w'
    | succ m ih =>
      refine ⟨ih.2, fun w w' => ?_⟩
      rw [cm_two]
      exact Finset.sum_nonneg (fun x _ => mul_nonneg (hc _ _ _) (ih.2 _ _))
  exact fun n => (this n).1

theorem rowSums_ok : RowSums := by
  intro W Wd s c caa M Maa hs hc hcaa hM hMaa
  have row : ∀ n, 1 ≤ n → n < s → ∀ w ∈ Wd,
      ∑ w'' ∈ Wd, chainMat Wd c n w w'' = ∏ k ∈ Ico 1 (n + 1), M k := by
    intro n
    induction n with
    | zero => intro h; omega
    | succ m ih =>
      intro _ hns w hw
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [cm_one, hM 1 le_rfl hns w hw]
      · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        rw [show k + 1 + 1 = k + 2 from rfl]
        simp only [cm_two]
        rw [Finset.sum_comm]
        simp only [← Finset.mul_sum]
        rw [Finset.sum_congr rfl (fun w' hw' => by rw [ih (by omega) (by omega) w' hw'])]
        rw [← Finset.sum_mul, hM (k + 2) (by omega) hns w hw,
          Finset.prod_Ico_succ_top (a := 1) (b := k + 2) (by omega), mul_comm]
  have P := fun w hw => row (s - 1) (by omega) (by omega) w hw
  have hs1 : s - 1 + 1 = s := by omega
  rw [hs1] at P
  have rsum : ∀ w ∈ Wd, ∑ w'' ∈ Wd, coMat Wd c caa s w w'' = Maa * ∏ n ∈ Ico 1 s, M n := by
    intro w hw
    simp only [coMat]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun w' hw' => by rw [P w' hw']), ← Finset.sum_mul, hMaa w hw]
  intro w hw
  refine ⟨rsum w hw, fun hpos => ⟨fun a => ?_, fun a ha => by simp [ha], ?_⟩⟩
  · dsimp only
    split_ifs
    · exact div_nonneg (Finset.sum_nonneg (fun x _ => mul_nonneg (hcaa _ _)
        (cm_nonneg Wd c hc _ _ _))) hpos.le
    · exact le_rfl
  · rw [Finset.sum_congr rfl (fun a ha => if_pos ha), ← Finset.sum_div, rsum w hw]
    exact div_self hpos.ne'

theorem sizesProduct_ok : SizesProduct := by
  intro f s Maa C₄ A B M vol hs hC hA0 hAC hB0 hBC hvol hMaa0 hMaaA hM
  have hC0 : 0 ≤ C₄ := by linarith
  have hprodv : 0 ≤ ∏ n ∈ Ico 1 s, vol n := Finset.prod_nonneg (fun n _ => hvol n)
  have h1 : ∏ n ∈ Ico 1 s, M n ≤ ∏ n ∈ Ico 1 s, (B ^ f * vol n) :=
    Finset.prod_le_prod (fun n hn => (hM n hn).1) (fun n hn => (hM n hn).2)
  have h2 : ∏ n ∈ Ico 1 s, (B ^ f * vol n) ≤ ∏ n ∈ Ico 1 s, (C₄ ^ f * vol n) :=
    Finset.prod_le_prod (fun n _ => mul_nonneg (pow_nonneg hB0 _) (hvol n))
      (fun n _ => mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hB0 hBC f) (hvol n))
  have h3 : A ^ f ≤ C₄ ^ f := pow_le_pow_left₀ hA0 hAC f
  have hMp : 0 ≤ ∏ n ∈ Ico 1 s, M n := Finset.prod_nonneg (fun n hn => (hM n hn).1)
  calc Maa * ∏ n ∈ Ico 1 s, M n ≤ C₄ ^ f * ∏ n ∈ Ico 1 s, (C₄ ^ f * vol n) := by
        apply mul_le_mul (hMaaA.trans h3) (h1.trans h2) hMp (pow_nonneg hC0 _)
    _ = C₄ ^ (f * s) * ∏ n ∈ Ico 1 s, vol n := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico, ← mul_assoc, ← pow_mul,
          ← pow_add]
        congr 2
        rcases s with _ | s
        · omega
        · simp [Nat.mul_succ]; ring

end Formalism.FourierDecayAlt.P.ChainAndRowSums

theorem Formalism.FourierDecayAlt.P.chain_sum_identity : Formalism.FourierDecayAlt.crystallineComparison.ChainSum := Formalism.FourierDecayAlt.P.ChainAndRowSums.chainSum_ok
theorem Formalism.FourierDecayAlt.P.row_sums_identity : Formalism.FourierDecayAlt.crystallineComparison.RowSums := Formalism.FourierDecayAlt.P.ChainAndRowSums.rowSums_ok
theorem Formalism.FourierDecayAlt.P.sizes_product_identity : Formalism.FourierDecayAlt.crystallineComparison.SizesProduct :=
  Formalism.FourierDecayAlt.P.ChainAndRowSums.sizesProduct_ok
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameLevelIndices
section
namespace Formalism.FourierDecayAlt.P.FrameLevelIndices

open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_one)
open Formalism.FourierDecayAlt.S3

section Index

variable {A : Type} [CommRing A] {r k : ℕ}

theorem pointwise_subgroup_le_parabolic : (S3x1.s0G : Subgroup (GL (Idx r k) A)) ≤ S3x1.parG (r := r) (S3x1.gpUnit (A := A) (k := k)) := by
  intro g hg
  exact ((S3x1.mem_pointwise_stabiliser_iff _).1 hg).1

theorem card_s0G : Nat.card {x : Matrix (Idx r k) (Idx r k) A // IsInertiaInfiniteCyclotomic x} =
    Nat.card (S3x1.s0G : Subgroup (GL (Idx r k) A)) := by
  refine S3x2.card_of_subgroupSet _ _ fun x => ⟨fun hx => ?_, ?_⟩
  · exact ⟨Matrix.GeneralLinearGroup.mk'' x (S3x1.par_det S3x1.gpUnit ((S3x1.mem_pointwise_stabiliser_iff x).1 hx).1), hx, rfl⟩
  · rintro ⟨g, hg, rfl⟩; exact hg

theorem card_sG : Nat.card {x : Matrix (Idx r k) (Idx r k) A // IsS x} =
    Nat.card (S3x1.parG (r := r) (S3x1.gpUnit (A := A) (k := k))) := by
  refine S3x2.card_of_subgroupSet _ _ fun x => ⟨fun hx => ?_, ?_⟩
  · exact ⟨Matrix.GeneralLinearGroup.mk'' x (S3x1.par_det S3x1.gpUnit ((S3x1.isS_iff x).1 hx)),
      (S3x1.isS_iff x).1 hx, rfl⟩
  · rintro ⟨g, hg, rfl⟩; exact (S3x1.isS_iff _).2 hg

end Index

section Local

variable {o : Type} [CommRing o] [IsLocalRing o] {r k : ℕ}

theorem first_congruence_eq_reduction_comap (M : FrameLevel o r k) :
    M.K1 = (S3x1.s0G : Subgroup (GL (Idx r k) (IsLocalRing.ResidueField o))).comap (red o (Idx r k)) := by
  ext x
  rw [M.mem_parahoricTimesPrincipalCongruence_iff, Subgroup.mem_comap]
  rfl

theorem Knat_eq (L : Levels o r k) :
    L.Knat = (S3x1.parG (r := r) (S3x1.gpUnit (A := IsLocalRing.ResidueField o) (k := k))).comap
      (red o (Idx r k)) := by
  ext x
  rw [L.mem_Knat, Subgroup.mem_comap, S3x1.isS_iff]
  rfl

end Local

noncomputable def fac (q x : ℕ) : ℝ := 1 - ((q : ℝ) ^ (x + 1))⁻¹

theorem densityProduct_eq_prod_range (q a m : ℕ) :
    densP 1 q ((a : ℤ) + 1) ((a + m : ℕ) : ℤ) = ∏ x ∈ range m, fac q (a + x) := by
  unfold densP
  refine Finset.prod_nbij' (fun i => (i - a - 1).toNat) (fun x => (a : ℤ) + 1 + x) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_Icc, Finset.mem_range] at *
    omega
  · intro x hx
    simp only [Finset.mem_Icc, Finset.mem_range] at *
    omega
  · intro i hi
    simp only [Finset.mem_Icc] at hi
    omega
  · intro x hx
    show ((a : ℤ) + 1 + x - a - 1).toNat = x
    omega
  · intro i hi
    simp only [Finset.mem_Icc] at hi
    obtain ⟨x, rfl⟩ : ∃ x : ℕ, i = (a : ℤ) + 1 + x := ⟨(i - a - 1).toNat, by omega⟩
    have e1 : ((a : ℤ) + 1 + x - a - 1).toNat = x := by omega
    have e2 : (a : ℤ) + 1 + x = ((a + x + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e1, e2, fac]
    simp only [Int.cast_one, one_pow, one_mul, _root_.zpow_neg, zpow_natCast]

theorem gl_real (q n : ℕ) (hq : 1 ≤ q) :
    ((∏ i : Fin n, (q ^ n - q ^ (i : ℕ)) : ℕ) : ℝ) = (q : ℝ) ^ (n * n) * ∏ x ∈ range n, fac q x := by
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have hpow : (q : ℝ) ^ (n * n) = ∏ _x ∈ range n, (q : ℝ) ^ n := by
    rw [Finset.prod_const, Finset.card_range, pow_mul]
  rw [Fin.prod_univ_eq_prod_range (fun i => q ^ n - q ^ i) n, ← Finset.prod_range_reflect, Nat.cast_prod,
    hpow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [Nat.cast_sub (Nat.pow_le_pow_right hq (by omega)), fac]
  have e : n = (n - 1 - j) + (j + 1) := by omega
  push_cast
  conv_lhs => rw [e]
  conv_rhs => rw [e]
  have e' : n - 1 - j + (j + 1) - 1 - j = n - 1 - j := by omega
  rw [e', pow_add]
  field_simp

theorem card_GL_idx (K : Type) [Field K] [Fintype K] (r k : ℕ) :
    Nat.card (GL (Idx r k) K) = Nat.card (GL (Fin (k + 2 * r + 1)) K) := by
  have e : Idx r k ≃ Fin (k + 2 * r + 1) := Fintype.equivFinOfCardEq (by simp; ring)
  exact Nat.card_congr (Units.mapEquiv (Matrix.reindexAlgEquiv K K e).toMulEquiv).toEquiv

section Om

variable {o : Type} [CommRing o] [IsLocalRing o] {r k : ℕ}

theorem kppO_mul {j j' : Matrix (Idx r k) (Idx r k) o} (h : KppO j) (h' : KppO j') : KppO (j * j') := by
  refine ⟨by rw [Matrix.det_mul]; exact h.1.mul h'.1, ?_⟩
  rw [Matrix.map_mul, S3x1.isNU_iff]
  exact S3x1.par_mul S3x1.gpUni ((S3x1.isNU_iff _).1 h.2) ((S3x1.isNU_iff _).1 h'.2)

theorem kppO_inv {j : Matrix (Idx r k) (Idx r k) o} (h : KppO j) : KppO j⁻¹ := by
  refine ⟨Matrix.isUnit_nonsing_inv_det j h.1, ?_⟩
  rw [S3x1.isNU_iff]
  refine S3x1.par_rinv S3x1.gpUni ((S3x1.isNU_iff _).1 h.2) ?_
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ h.1, Matrix.map_one _ (map_zero _) (map_one _)]

theorem kppO_of_isN {n : Matrix (Idx r k) (Idx r k) o} (hn : IsN n) : KppO n := by
  refine ⟨by rw [S3x3.det_of_isN hn]; exact isUnit_one, ?_⟩
  exact ⟨_, 1, S3x3.isN_map _ hn, ⟨1, isUpUni_one _, S3x1.hEmb_one.symm⟩, (Matrix.mul_one _).symm⟩

theorem kppO_hEmb {h : Matrix (Fin k) (Fin k) o} (hd : IsUnit h.det)
    (hu : IsUpUni (h.map (IsLocalRing.residue o))) : KppO (hEmb r h) := by
  refine ⟨by rw [S3x3.det_hEmb]; exact hd, ?_⟩
  exact ⟨1, _, (S3x1.isN_iff _).2 (S3x1.par_one S3x1.gpOne), ⟨_, hu, rfl⟩, by
    rw [S3x3.hEmb_map, Matrix.one_mul]⟩

end Om

end Formalism.FourierDecayAlt.P.FrameLevelIndices

namespace Formalism.FourierDecayAlt.P

open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG)
open Formalism.FourierDecayAlt.S3 Formalism.FourierDecayAlt.P.FrameLevelIndices

theorem first_congruence_index : Formalism.FourierDecayAlt.S3.CongruenceLevelIndex := by
  intro o _ _ _ r k L M
  refine ⟨?_, ?_⟩
  · rw [first_congruence_eq_reduction_comap M, Knat_eq L]
    exact Subgroup.comap_mono pointwise_subgroup_le_parabolic
  · rw [first_congruence_eq_reduction_comap M, Knat_eq L, Subgroup.relIndex_comap,
      Subgroup.map_comap_eq_self_of_surjective (S3x2.red_surjective o _)]
    have : Fintype (IsLocalRing.ResidueField o) := Fintype.ofFinite _
    have h1 := Subgroup.relIndex_mul_relIndex ⊥
      (S3x1.s0G : Subgroup (GL (Idx r k) (IsLocalRing.ResidueField o)))
      (S3x1.parG (r := r) (S3x1.gpUnit (A := IsLocalRing.ResidueField o) (k := k))) bot_le pointwise_subgroup_le_parabolic
    rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, ← card_s0G, ← card_sG,
      card_pointwise_stabiliser (IsLocalRing.ResidueField o) r k, ← Nat.card_eq_fintype_card] at h1
    have hpos : 0 < Nat.card {x : Matrix (Idx r k) (Idx r k) (IsLocalRing.ResidueField o) // IsInertiaInfiniteCyclotomic x} := by
      rw [card_s0G]; exact Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos h1

theorem frameIndex_statement : Formalism.FourierDecayAlt.S3.FrameIndex := by
  intro K _ _ r k
  have hq : 1 ≤ Fintype.card K := Fintype.card_pos
  rw [card_GL_idx, Matrix.card_GL_field, card_frame_stabiliser K r k, card_unipotent_radical K r k, Matrix.card_GL_field,
    gl_real _ _ hq, Nat.cast_mul, gl_real _ _ hq,
    show k + 2 * r + 1 = k + (2 * r + 1) from rfl, densityProduct_eq_prod_range, Finset.prod_range_add,
    show ((r : ℤ) + 1) * (2 * k + 2 * r + 1) = (((r + 1) * (2 * k + 2 * r + 1) : ℕ) : ℤ) by push_cast; ring,
    zpow_natCast, Nat.cast_pow]
  have e : (k + (2 * r + 1)) * (k + (2 * r + 1)) =
      k * k + (r * (r - 1) + 2 * r * (k + 1) + r ^ 2) + (r + 1) * (2 * k + 2 * r + 1) := by
    rcases r with _ | r
    · simp; ring
    · simp only [Nat.add_sub_cancel]; ring
  rw [e, pow_add, pow_add]
  ring

theorem omStable_statement : Formalism.FourierDecayAlt.S3.OmStable := by
  intro o _ _ _ ϖ hϖ r k j n n' h hj hn hn' hd hu
  obtain ⟨hK, X, hX, hcm⟩ := hj
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨kppO_mul (kppO_mul (kppO_of_isN hn) hK) (kppO_of_isN hn'), b33 n * X * b11 n', ?_, ?_⟩
    · obtain ⟨-, -, -, -, n31, n32⟩ := hn
      obtain ⟨-, -, -, n21', n31', -⟩ := hn'
      rw [S3x1.block31_mul, S3x1.block31_mul, n31, n32, n21', n31', hX]
      simp
    · intro l hl
      rw [S3x7.corner_invariant hn.2.1 hn'.1]
      exact hcm l hl
  · refine ⟨kppO_mul (kppO_hEmb hd hu) hK, X, ?_, hcm⟩
    rw [S3x1.block31_mul, S3x1.levi_embedding_block31, S3x1.levi_embedding_block32, S3x1.levi_embedding_block33, hX]
    simp
  · refine ⟨kppO_mul hK (kppO_hEmb hd hu), X, ?_, hcm⟩
    rw [S3x1.block31_mul, S3x1.levi_embedding_block11, S3x1.levi_embedding_block21, S3x1.levi_embedding_block31, hX]
    simp
  · obtain ⟨Y, hY, -, hYc⟩ := S3x7.inverse_corner hϖ j X hK hX
    refine ⟨kppO_inv hK, Y, hY, fun l hl => ?_⟩
    have h1 : IsLocalRing.residue o (cm X l hl) ≠ 0 := by
      rw [Ne, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
      exact hcm l hl
    have h2 : IsLocalRing.residue o (cm Y l hl) ≠ 0 := by
      rw [hYc l hl]
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) h1
    rw [Ne, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at h2
    exact h2

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.OneLevelInequality
section
namespace Formalism.FourierDecayAlt.P

theorem one_level_inequality : Formalism.FourierDecayAlt.TA.OneLevel :=
  one_level_inequality_of_parts split_last_block off_diagonal_schur_complement diagonal_top_block
    diagonal_cosets cosets_last_block_size_one cosets_last_block_size_ge_two

theorem theorem_a_reduction : Formalism.FourierDecayAlt.TA.TheoremAReduction :=
  reduction_bound_of_one_level one_level_inequality epsilon_limit domination_limit
    joint_theorem_A'

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.OneLevelInequalitySplitBySize
section
namespace Formalism.FourierDecayAlt.P

theorem one_level_inequality_split_by_size : Formalism.FourierDecayAlt.TB.OneLevel :=
  levelInequalityOfSteps splitByLastSize schurRecursion_true diagStep
    singleBlockStep longBlockStep

theorem sharp_recursion_theorem_a : Formalism.FourierDecayAlt.TB.TheoremA :=
  towerBoundOfSteps one_level_inequality_split_by_size limitStep joint_theorem_A'

end Formalism.FourierDecayAlt.P
end

