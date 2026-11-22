import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2919
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0740
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2899
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0520
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0539
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0770
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0526
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0564
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0499
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0506
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0554
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0508
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0511
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0741
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2926
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtMapDualBCLeft
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2941
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2917
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2929
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFrameFormNormSqEq
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
open scoped ComplexOrder

open GlobalTheory.HermFrame Filter Topology ComplexConjugate

namespace GlobalTheory.HermFrame

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem ddbar_mul_conj_mul_of_zero {s U : E → ℂ} {z : E} (hs : ContDiffAt ℂ 2 s z) (h0 : s z = 0)
    (hU : ContDiffAt ℝ 2 U z) (ξ η : E) :
    ddbar (fun x => s x * (conj (s x) * U x)) z ξ η = del s z ξ * (conj (del s z η) * U z) := by
  have hR : ContDiffAt ℝ 2 s z := hs.restrict_scalars ℝ
  have hc : ContDiffAt ℝ 2 (fun x => conj (s x)) z := Complex.conjCLE.contDiff.contDiffAt.comp z hR
  have hW : ContDiffAt ℝ 2 (fun x => conj (s x) * U x) z := hc.mul hU
  have he : (fun x => dbar (fun y => s y * (conj (s y) * U y)) x η) =ᶠ[𝓝 z]
      fun x => s x * dbar (fun y => conj (s y) * U y) x η := by
    filter_upwards [eventually_differentiableAt_of_contDiffAt_two hs,
      eventually_differentiableAt_of_contDiffAt_two hW] with x h1 h2
    rw [dbar_mul (h1.restrictScalars ℝ) h2, dbar_eq_zero h1]
    simp
  rw [ddbar_eq_del_dbar (hR.mul hW), del_congr he,
    del_mul (hR.differentiableAt two_ne_zero) (differentiableAt_dbar_apply hW η),
    dbar_mul (hc.differentiableAt two_ne_zero) (hU.differentiableAt two_ne_zero), dbar_conj, h0]
  simp

open Matrix in

theorem extTrace_chg_of_block_eq_zero {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
    {K A : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E} (h : MContDiffAt 1 K z)
    (hp : ∀ᶠ x in 𝓝 z, (K x).PosDef) (hA : MContDiffAt 1 A z) (hu : IsUnit (A z).det)
    (hA0 : ∀ η, mdbar A z η = 0) (ht : (A z).toBlocks₂₁ = 0) (ξ η : E) :
    extTrace (fun x => chg (A x) (K x)) z ξ η = kappa *
      ((secondForm K z ξ + (mdel A z ξ).toBlocks₂₁ * (A z).toBlocks₁₁⁻¹) *
        adj (subGram (K z)) (quotGram (K z))
          (secondForm K z η + (mdel A z η).toBlocks₂₁ * (A z).toBlocks₁₁⁻¹)).trace := by
  have eA : A z = fromBlocks (A z).toBlocks₁₁ (A z).toBlocks₁₂ 0 (A z).toBlocks₂₂ := by
    rw [← ht, fromBlocks_toBlocks]
  have hd := hu
  rw [eA, det_fromBlocks_zero₂₁, IsUnit.mul_iff] at hd
  have hK := hp.self_of_nhds
  have hb (ξ : E) : secondForm (fun x => chg (A x) (K x)) z ξ =
      (A z).toBlocks₂₂⁻¹ * (secondForm K z ξ + (mdel A z ξ).toBlocks₂₁ * (A z).toBlocks₁₁⁻¹) *
        (A z).toBlocks₁₁ := by
    have e := congrArg (A z * ·) (conn_changeFrame h hK.det_pos.ne'.isUnit hA hu hA0 ξ)
    simp only [mul_nonsing_inv_cancel_left _ _ hu] at e
    have e₁ := congrArg toBlocks₂₁ e
    rw [← fromBlocks_toBlocks (conn _ z ξ), ← fromBlocks_toBlocks (conn K z ξ),
      ← fromBlocks_toBlocks (mdel A z ξ), eA] at e₁
    simp only [fromBlocks_multiply, fromBlocks_add, toBlocks_fromBlocks₂₁, Matrix.zero_mul,
      Matrix.mul_zero, zero_add, add_zero] at e₁
    rw [secondForm_eq, secondForm_eq, Matrix.mul_assoc, Matrix.add_mul, Matrix.mul_assoc,
      nonsing_inv_mul _ hd.1, Matrix.mul_one]
    first
      | (rw [← e₁, nonsing_inv_mul_cancel_left _ _ hd.2]; rfl)
      | (rw [add_comm, ← e₁, nonsing_inv_mul_cancel_left _ _ hd.2]; rfl)
  have hp' : ∀ᶠ x in 𝓝 z, (chg (A x) (K x)).PosDef := by
    filter_upwards [hp, hA.eventually_isUnit hu] with x h₁ h₂
    exact posDef_chg ((isUnit_iff_isUnit_det _).2 h₂) h₁
  rw [extTrace_eq (K := fun x => chg (A x) (K x))
    ((hA.transpose.mul h).mul hA.conjTranspose.transpose) hp',
    secondFormAdj, hb, hb, ← trace_mul_adj_chg hd.1 hd.2 (subGram (K z)),
    ← subGram_chg _ (A z).toBlocks₁₂ (A z).toBlocks₂₂,
    ← quotGram_chg (A z).toBlocks₁₂ _ hd.1 (posDef_subGram hK).det_pos.ne'.isUnit, ← eA]

end

theorem chg_mul_sub_form {K A : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ} (hK : K.IsHermitian) :
    chg A K (.inl 0) (.inl 0) * K (.inl 0) (.inl 0) -
      ((‖form K (Pi.single (Sum.inl 0) 1) (fun i => A i (Sum.inl 0))‖ ^ 2 : ℝ) : ℂ) =
    A (.inr 0) (.inl 0) * (conj (A (.inr 0) (.inl 0)) *
      (K (.inl 0) (.inl 0) * K (.inr 0) (.inr 0) - K (.inl 0) (.inr 0) * K (.inr 0) (.inl 0))) := by
  have h1 : conj (K (.inl 0) (.inl 0)) = K (.inl 0) (.inl 0) := hK.apply _ _
  have h2 : conj (K (.inl 0) (.inr 0)) = K (.inr 0) (.inl 0) := hK.apply _ _
  rw [Complex.ofReal_pow, ← Complex.mul_conj', chg_apply, form_eq_sum, form_eq_sum]
  simp [Fintype.sum_sum_type, h1, h2]
  ring

end GlobalTheory.HermFrame

namespace GlobalTheory.LineForm

theorem ofValues_mul_ofValues_eq_zero {n : ℕ} (u u' w w' : ReciprocityTheory.L2DbarEstimates.V n → ℂ) (c : ℂ) :
    ((ofValues (fun ξ η => c * (u ξ * u' η)) : Ev n) : Alt n) *
      (((ofValues (fun ξ η => u ξ * w' η) : Ev n) : Alt n) +
        ((ofValues (fun ξ η => w ξ * u' η) : Ev n) : Alt n)) = 0 := by
  have e : ((ofValues (fun ξ η => c * (u ξ * u' η)) : Ev n) : Alt n) =
      c • ((ofValues (fun ξ η => u ξ * u' η) : Ev n) : Alt n) := by
    simp only [ofValues, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul, Finset.smul_sum, smul_smul]
  rw [e, coe_ofValues_mul, coe_ofValues_mul, coe_ofValues_mul]
  generalize (∑ a, u (GlobalTheory.GoodMetric.coordVec a) • Pi.single (Sum.inl a) (1 : ℂ) : Fin n ⊕ Fin n → ℂ) = x
  generalize (∑ a, w (GlobalTheory.GoodMetric.coordVec a) • Pi.single (Sum.inl a) (1 : ℂ) : Fin n ⊕ Fin n → ℂ) = x'
  generalize (∑ b, u' (GlobalTheory.GoodMetric.coordVec b) • Pi.single (Sum.inr b) (1 : ℂ) : Fin n ⊕ Fin n → ℂ) = y
  generalize (∑ b, w' (GlobalTheory.GoodMetric.coordVec b) • Pi.single (Sum.inr b) (1 : ℂ) : Fin n ⊕ Fin n → ℂ) = y'
  have h := Subalgebra.mem_center_iff.1 (ι_mul_ι_mem_center x y) (ExteriorAlgebra.ι ℂ x)
  have h' := Subalgebra.mem_center_iff.1 (ι_mul_ι_mem_center x' y) (ExteriorAlgebra.ι ℂ y)
  rw [smul_mul_assoc, mul_add, ← mul_assoc _ (ExteriorAlgebra.ι ℂ x), ← h, ← mul_assoc (ExteriorAlgebra.ι ℂ x),
    ExteriorAlgebra.ι_sq_zero, mul_assoc (ExteriorAlgebra.ι ℂ x), h', mul_assoc (ExteriorAlgebra.ι ℂ x'),
    ExteriorAlgebra.ι_sq_zero]
  simp

theorem coe_ofValues_sub_eq {n : ℕ} {α β γ δ : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.L2DbarEstimates.V n → ℂ}
    (h : ∀ ξ η, α ξ η = β ξ η + (γ ξ η + δ ξ η)) :
    ((ofValues α : Ev n) : Alt n) - ((ofValues β : Ev n) : Alt n) =
      ((ofValues γ : Ev n) : Alt n) + ((ofValues δ : Ev n) : Alt n) := by
  simp only [ofValues, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul, Subalgebra.coe_add, h, add_smul,
    Finset.sum_add_distrib, add_sub_cancel_left]

theorem ddc_sinSq_mul_extTrace_sub : ∀ (n : ℕ) (K A : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n → ℝ) (z : ReciprocityTheory.L2DbarEstimates.V n),
    GlobalTheory.HermFrame.MContDiffAt 2 K z → (∀ᶠ x in nhds z, (K x).PosDef) → (∀ a b, AnalyticAt ℂ (fun x => A x a b) z) → IsUnit (A z).det → v z = 1 →
    (∀ᶠ x in nhds z, ‖GlobalTheory.HermFrame.form (K x) (Pi.single (Sum.inl 0) 1) (fun i => A x i (Sum.inl 0))‖ ^ 2 =
      v x * (GlobalTheory.HermFrame.chg (A x) (K x) (Sum.inl 0) (Sum.inl 0)).re * (K x (Sum.inl 0) (Sum.inl 0)).re) →
    ((ofValues (GlobalTheory.HermFrame.ddc (fun x => 1 - v x) z) : Ev n) : Alt n) *
      (((ofValues (GlobalTheory.HermFrame.extTrace (fun x => GlobalTheory.HermFrame.chg (A x) (K x)) z) : Ev n) : Alt n) -
        ((ofValues (GlobalTheory.HermFrame.extTrace K z) : Ev n) : Alt n)) = 0 := by
  intro n K A v z hK hp hA hu hv he
  have hA2 : MContDiffAt 2 A z := fun a b => ((hA a b).contDiffAt (n := 2)).restrict_scalars ℝ
  have hA1 : MContDiffAt 1 A z := fun a b => (hA2 a b).of_le (by norm_num)
  have hK1 : MContDiffAt 1 K z := fun a b => (hK a b).of_le (by norm_num)
  have hC : MContDiffAt 2 (fun x => chg (A x) (K x)) z :=
    (hA2.transpose.mul hK).mul hA2.conjTranspose.transpose
  have hp' : ∀ᶠ x in 𝓝 z, (chg (A x) (K x)).PosDef := by
    filter_upwards [hp, hA1.eventually_isUnit hu] with x h₁ h₂
    exact posDef_chg ((Matrix.isUnit_iff_isUnit_det _).2 h₂) h₁
  set s : ReciprocityTheory.L2DbarEstimates.V n → ℂ := fun x => A x (.inr 0) (.inl 0) with hs
  set U : ReciprocityTheory.L2DbarEstimates.V n → ℂ := fun x =>
    (K x (.inl 0) (.inl 0) * K x (.inr 0) (.inr 0) - K x (.inl 0) (.inr 0) * K x (.inr 0) (.inl 0)) *
      (chg (A x) (K x) (.inl 0) (.inl 0) * K x (.inl 0) (.inl 0))⁻¹ with hU
  have hne : chg (A z) (K z) (.inl 0) (.inl 0) * K z (.inl 0) (.inl 0) ≠ 0 :=
    mul_ne_zero (hp'.self_of_nhds.diag_pos).ne' (hp.self_of_nhds.diag_pos).ne'
  have hU2 : ContDiffAt ℝ 2 U z :=
    (((hK _ _).mul (hK _ _)).sub ((hK _ _).mul (hK _ _))).mul (((hC _ _).mul (hK _ _)).inv hne)
  have hev : (fun x => ((1 - v x : ℝ) : ℂ)) =ᶠ[𝓝 z] fun x => s x * (conj (s x) * U x) := by
    filter_upwards [hp, hp', he] with x h₁ h₂ h₃
    have e := chg_mul_sub_form (A := A x) h₁.isHermitian
    have n₁ := (h₁.diag_pos (i := .inl 0))
    have n₂ := (h₂.diag_pos (i := .inl 0))
    have r₁ : ((K x (.inl 0) (.inl 0)).re : ℂ) = K x (.inl 0) (.inl 0) :=
      Complex.ext rfl (by simpa using (Complex.lt_def.1 n₁).2)
    have r₂ : ((chg (A x) (K x) (.inl 0) (.inl 0)).re : ℂ) = chg (A x) (K x) (.inl 0) (.inl 0) :=
      Complex.ext rfl (by simpa using (Complex.lt_def.1 n₂).2)
    rw [h₃, Complex.ofReal_mul, Complex.ofReal_mul, r₁, r₂] at e
    have n₁' := n₁.ne'
    have n₂' := n₂.ne'
    simp only [hs, hU]
    rw [← mul_assoc (conj _), ← mul_assoc, ← e]
    push_cast
    field_simp
  have hUz : U z ≠ 0 := by
    refine mul_ne_zero ?_ (inv_ne_zero hne)
    have := hp.self_of_nhds.det_pos.ne'
    rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv.symm, Matrix.det_fin_two] at this
    exact this
  have hs0 : s z = 0 := by
    have := hev.self_of_nhds
    simp only [hv, sub_self, Complex.ofReal_zero] at this
    simpa [hUz] using this.symm
  have e1 : ddc (fun x => 1 - v x) z = fun ξ η => (kappa * U z) * (del s z ξ * conj (del s z η)) := by
    funext ξ η
    rw [ddc, leviForm, ddbar_congr hev, ddbar_mul_conj_mul_of_zero (hA _ _).contDiffAt hs0 hU2]
    ring
  have hA0 : ∀ η, mdbar A z η = 0 := fun η => Matrix.ext fun i j =>
    congr($(dbar_eq_zero (hA i j).differentiableAt) η)
  have ht : (A z).toBlocks₂₁ = 0 := by
    ext i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    exact hs0
  set c : ℂ := kappa * ((subGram (K z)).transpose⁻¹ 0 0 * quotGram (K z) 0 0) with hc
  set d : ℂ := (A z).toBlocks₁₁⁻¹ 0 0 with hd
  rw [e1, coe_ofValues_sub_eq (γ := fun ξ η => del s z ξ *
      (c * d * conj (secondForm K z η 0 0 + del s z η * d)))
    (δ := fun ξ η => (c * conj d * secondForm K z ξ 0 0) * conj (del s z η)) fun ξ η => ?_]
  · exact ofValues_mul_ofValues_eq_zero _ (fun η => conj (del s z η)) _ _ _
  · have m (ξ) : (mdel A z ξ).toBlocks₂₁ 0 0 = del s z ξ := rfl
    rw [extTrace_chg_of_block_eq_zero hK1 hp hA1 hu hA0 ht, extTrace_eq hK1 hp, secondFormAdj]
    simp only [adj, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_one, Matrix.add_apply,
      Matrix.conjTranspose_apply, Matrix.transpose_apply, m, ← hd, hc, Complex.star_def, map_add, map_mul]
    ring

end GlobalTheory.LineForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetAddDirection
section
set_option autoImplicit false

noncomputable section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

namespace GlobalTheory.HilbFam

theorem jet_add_dir_of_hasLevel : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F →
    ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (τ c t v : ℂ) (κ : Emb F → ℕ), 0 < τ.im →
    jet (2 * s) L κ τ (c + v) t = ∑ μ ∈ Finset.Iic κ, ((∏ i, rco (2 * s) (κ i) (μ i) : ℤ) : ℂ) * v ^ (∑ i, (κ i - μ i)) * jet (2 * s) L μ τ c t := by
  intro hE F _ _ _ hf s N L hs hN hL τ c t v κ hτ
  obtain ⟨𝔞, 𝔟, x, rfl⟩ := GlobalTheory.T.exists_split_of_hilbertLatticeHasLevel F N L hN hL
  obtain ⟨Z, a, -, ha⟩ := GlobalTheory.T.exists_hilbertEisenstein_fourierCoeffFamily hE F hf 𝔞 𝔟 s hs
  exact GlobalTheory.T.hilbertEisensteinLatticeJet_split_direction_add F (2 * s) 𝔞 𝔟 _ a x τ c t v κ (even_two_mul s) ha hτ

end GlobalTheory.HilbFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetAlgebraicQCoefficients
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

namespace GlobalTheory.HilbFam

theorem qAll_isAlgebraic_hfun : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F],
    2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L →
    ∀ (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (κ : Emb F → ℕ) (Ch : ℍ → ℂ),
    QAll (IsAlgebraic ℚ) N Ch → QAll (IsAlgebraic ℚ) N (hfun (2 * s) L κ Ch) := by
  intro hE F _ _ _ hf s N L hs hN hL z hz κ Ch hCh
  obtain ⟨c, hc, halg⟩ := hCh
  obtain ⟨𝔞, 𝔟, x, rfl⟩ := GlobalTheory.T.exists_split_of_hilbertLatticeHasLevel F N L hN hL
  obtain ⟨Z, a, hZ, ha⟩ := GlobalTheory.T.exists_hilbertEisenstein_fourierCoeffFamily hE F hf 𝔞 𝔟 s hs
  have hconst := GlobalTheory.T.partialZeta_constTerm_eq_rational_value F (2 * s) z _ Z (by omega) hz hZ
  have ha₀ : IsAlgebraic ℚ ((2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - ((2 * s : ℕ) : ℂ))) := by
    rw [hconst]
    exact isAlgebraic_algebraMap (R := ℚ) (A := ℂ) _
  exact ⟨_, GlobalTheory.T.hasQExpansionOfLevel_hilbertEisensteinQuasiPeriodJet F (2 * s) 𝔞 𝔟 _ a x N κ Ch c hN (even_two_mul s) ha hL hc,
    fun n ↦ GlobalTheory.T.hilbertDiagonalRestriction_coeff_isAlgebraic F (2 * s) 𝔞 𝔟 _ a x s N κ c n rfl ha ha₀ halg⟩

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetGaloisConjCoefficients
section
set_option autoImplicit false

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

namespace GlobalTheory.HilbFam

theorem qConj_hfun_twist : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (g : ℂ ≃+* ℂ) (m : ℤ) (κ κ' : Emb F → ℕ) (Ch Ch' : ℍ → ℂ), IsCoprime m (N : ℤ) → g (Complex.exp ((2 * Real.pi * Complex.I) / N)) = Complex.exp ((2 * Real.pi * Complex.I) * m / N) → (∀ i j : Emb F, (∀ y : F, g ((i y : ℝ) : ℂ) = ((j y : ℝ) : ℂ)) → κ' j = κ i) → QConj g N Ch Ch' → QConj g N (hfun (2 * s) L κ Ch) (hfun (2 * s) (twist N L (Matrix.diagonal ![1, (m : ZMod N)])) κ' Ch') := by
  intro hE F _ _ _ hf s N L hs hN hL z hz g m κ κ' Ch Ch' hm hg hκ hC
  obtain ⟨𝔞, 𝔟, x, rfl⟩ := exists_eq_split_of_hasLevel F N L hN hL
  have htw := GlobalTheory.T.hilbertSplitLattice_twist_diagonal_coprime F N 𝔞 𝔟 x m hm hL
  have hL' := hasLevel_twist_of_hasLevel F N _ (Matrix.diagonal ![1, (m : ZMod N)]) hL
  rw [htw] at hL' ⊢
  obtain ⟨Z, a, hZ, ha⟩ := GlobalTheory.T.exists_hilbertEisenstein_fourierCoeffFamily hE F hf 𝔞 𝔟 s hs
  have h0 := constTerm_eq_zetaVal F (2 * s) z _ Z (by omega) hz hZ
  obtain ⟨π, hπ⟩ := aut_perm_emb F g
  have hκ' : κ' = fun j ↦ κ (π.symm j) := by
    funext j
    refine hκ (π.symm j) j fun y ↦ ?_
    rw [hπ, Equiv.apply_symm_apply]
  obtain ⟨c, hc, hc'⟩ := hC
  have hev : Even (2 * s) := even_two_mul s
  refine ⟨_, GlobalTheory.T.hasQExpansionOfLevel_hilbertEisensteinQuasiPeriodJet F (2 * s) 𝔞 𝔟 _ a x N κ Ch c hN hev ha hL hc, ?_⟩
  have h2 := GlobalTheory.T.hasQExpansionOfLevel_hilbertEisensteinQuasiPeriodJet F (2 * s) 𝔞 𝔟 _ a (m * x) N κ' Ch' _ hN hev ha hL' hc'
  have h3 := fun n ↦ GlobalTheory.T.hilbertEisensteinSeries_ringEquiv_conj F (2 * s) 𝔞 𝔟 _ a x s N g m π κ c n rfl hN ha
    (by rw [h0, map_ratCast]) hL hg hπ
  simp only [h3]
  rw [hκ'] at h2 ⊢
  exact h2

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetSmulDirection
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

set_option autoImplicit false

namespace GlobalTheory.HilbFam

theorem jet_smul_dir_of_hasLevel : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (τ c t v : ℂ) (κ : Emb F → ℕ), 0 < τ.im → jet (2 * s) L κ τ (v * c) (v * t) = v ^ (∑ i, κ i) * jet (2 * s) L κ τ c t := by
  intro hE F _ _ _ hf s N L hs hN hL τ c t v κ hτ
  obtain ⟨𝔞, 𝔟, x, rfl⟩ := GlobalTheory.T.exists_split_of_hilbertLatticeHasLevel F N L hN hL
  obtain ⟨Z, a, -, hc⟩ := GlobalTheory.T.exists_hilbertEisenstein_fourierCoeffFamily hE F hf 𝔞 𝔟 s hs
  exact GlobalTheory.T.hilbertEisensteinLatticeJet_split_smul_direction F (2 * s) 𝔞 𝔟 _ a x τ c t v κ (even_two_mul s) hc hτ

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeBundlePowerIsoMinimalSiegelCompactificationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeBundle_power_iso_minimalSiegelCompactification : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left), MinAt5 F z i OZ → IsNormalScheme S → IsProjOver (π ≫ z) → Dense (Set.range j) → j ≫ π = i → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → IsGrpPullback F.univ.A G j e → ∃ a N : ℕ, 1 ≤ a ∧ 1 ≤ N ∧ LBIso (lbPow (hodge G g) N) (lbPow (OZ.pull π) a) := by
  first | exact @GlobalTheory.HodgeMin.hodge_pow_iso_pull_pow_of_minimal_compactification | exact GlobalTheory.HodgeMin.hodge_pow_iso_pull_pow_of_minimal_compactification | (intros; apply GlobalTheory.HodgeMin.hodge_pow_iso_pull_pow_of_minimal_compactification <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateMapOpenImmersion
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartOpen

theorem isOpenImmersion_of_stalk {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f]
    [LocallyOfFinitePresentation f]
    (h : ∀ x : X, ∃ s : Spec (Y.presheaf.stalk (f x)) ⟶ X, s ≫ f = Y.fromSpecStalk (f x)) :
    IsOpenImmersion f := by
  have hbij : ∀ x : X, Function.Bijective (f.stalkMap x).hom := by
    intro x
    refine ⟨?_, f.stalkMap_surjective x⟩
    obtain ⟨s, hs⟩ := h x
    obtain ⟨⟨x', φ, hφ⟩, rfl⟩ := (SpecToEquivOfLocalRing X (Y.presheaf.stalk (f x))).symm.surjective s
    rw [SpecToEquivOfLocalRing_symm_apply] at hs
    dsimp only at hs
    have h1 : f x' = f x := by
      have := Scheme.Hom.comp_apply (Spec.map φ ≫ X.fromSpecStalk x') f (IsLocalRing.closedPoint _)
      rw [hs, Scheme.fromSpecStalk_closedPoint, GlobalTheory.TangentCrit.SpecMap_fromSpecStalk_closedPoint] at this
      exact this.symm
    have hx : x' = x := f.isClosedEmbedding.injective h1
    subst hx
    rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc] at hs
    have key : f.stalkMap x' ≫ φ = 𝟙 _ := by
      have e := (SpecToEquivOfLocalRing Y (Y.presheaf.stalk (f x'))).symm.injective
        (a₁ := ⟨f x', f.stalkMap x' ≫ φ, inferInstance⟩) (a₂ := ⟨f x', 𝟙 _, inferInstance⟩)
        (by rw [SpecToEquivOfLocalRing_symm_apply, SpecToEquivOfLocalRing_symm_apply]
            dsimp only
            rw [hs, Spec.map_id, Category.id_comp])
      rw [SpecToEquivOfLocalRing_eq_iff] at e
      obtain ⟨_, e⟩ := e
      simpa using e
    intro a b hab
    have := congrArg φ.hom hab
    rwa [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, key] at this
  have : Flat f := (Flat.iff_flat_stalkMap f).2 fun x => RingHom.Flat.of_bijective (hbij x)
  exact IsOpenImmersion.of_flat_of_mono f

theorem residue_lift {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f] (x : X) :
    ∃ s : Spec (Y.residueField (f x)) ⟶ X, s ≫ f = Y.fromSpecResidueField (f x) := by
  have hs : Function.Surjective (f.residueFieldMap x).hom := by
    intro a
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective a
    obtain ⟨c, rfl⟩ := f.stalkMap_surjective x b
    exact ⟨IsLocalRing.residue _ c, rfl⟩
  have : IsIso (f.residueFieldMap x) :=
    (ConcreteCategory.isIso_iff_bijective _).2 ⟨(f.residueFieldMap x).hom.injective, hs⟩
  refine ⟨Spec.map (inv (f.residueFieldMap x)) ≫ X.fromSpecResidueField x, ?_⟩
  rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc,
    ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id, Category.id_comp]

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q)
  {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f))

theorem finite_Bt : Module.Finite O (Bt P' x0 hu) := by
  haveI := P'.fin.finite
  exact inferInstanceAs (Module.Finite (OL P' x0 hu) (OL P' x0 hu ⊗[Localization.Away P'.f] P'.B))

theorem free_Bt : Module.Free O (Bt P' x0 hu) := by
  haveI := P'.fin.free
  exact inferInstanceAs (Module.Free (OL P' x0 hu) (OL P' x0 hu ⊗[Localization.Away P'.f] P'.B))

end

theorem isOpenImmersion_jH : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (p : ℕ) [Fact p.Prime] (n : ℕ) [StarRing (𝓞 E)] (P' : GlobalTheory.HTMap.FP t ξ (p ^ n)) (x0 : R →+* 𝓞_ℂ_[p]) (hu : IsUnit (x0 P'.f)) (P : PtP E p) (π : P.G.left ⟶ t.G.left) (hg : IsGrpPullback P.G t.G (spMap x0 ≫ ξ) π) (h : aH P' x0 hu hg.1 ^ (p ^ n) = 1), IsOpenImmersion (jH P' x0 hu hg.1 h).left := by
  intro E _ _ _ H X t R _ ξ p _ n _ P' x0 hu P π hg h
  set j := jH P' x0 hu hg.1 h
  haveI := P.semi.separated
  haveI := P.semi.smooth
  have hm : Mono j.left := by
    haveI := GlobalTheory.T.mono_finite_part_pullback P' x0 hu hg.1
    have e : j.left ≫ (torsion.ι P.G (p ^ n)).left = (aH P' x0 hu hg.1).left := by
      rw [← Over.comp_left, jH_ι]
    exact mono_of_mono_fac e
  have H0 : IsPullback (torsion.ι P.G (p ^ n)).left (torsion P.G (p ^ n)).hom (mulN P.G (p ^ n)).left η[P.G].left := by
    have h := (IsPullback.of_hasPullback (mulN P.G (p ^ n)) (η : 𝟙_ _ ⟶ P.G)).map (Over.forget _)
    have h' : (pullback.snd (mulN P.G (p ^ n)) (η : 𝟙_ _ ⟶ P.G)).left = (torsion P.G (p ^ n)).hom :=
      (Category.comp_id _).symm.trans (Over.w (pullback.snd (mulN P.G (p ^ n)) (η : 𝟙_ _ ⟶ P.G)))
    exact h' ▸ h
  have : LocallyOfFinitePresentation ((mulN P.G (p ^ n)).left ≫ P.G.hom) := by rw [Over.w]; infer_instance
  have h3 := GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp (mulN P.G (p ^ n)).left P.G.hom
  have : IsSeparated ((mulN P.G (p ^ n)).left ≫ P.G.hom) := by rw [Over.w]; infer_instance
  have h4 := IsSeparated.of_comp (mulN P.G (p ^ n)).left P.G.hom
  have hZlfp : LocallyOfFinitePresentation (torsion P.G (p ^ n)).hom :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) H0 h3
  have hZsep : IsSeparated (torsion P.G (p ^ n)).hom :=
    MorphismProperty.of_isPullback (P := @IsSeparated) H0 h4
  haveI := finite_Bt P' x0 hu
  haveI := free_Bt P' x0 hu
  have hHfin : IsFinite (Hs P' x0 hu).hom := by
    change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] (Bt P' x0 hu))))
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 inferInstance
  have hHlfp : LocallyOfFinitePresentation (Hs P' x0 hu).hom := by
    change LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] (Bt P' x0 hu))))
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    haveI : Module.FinitePresentation 𝓞_ℂ_[p] (Bt P' x0 hu) := Module.finitePresentation_of_projective _ _
    exact RingHom.finitePresentation_algebraMap.2 (Algebra.FinitePresentation.of_finitePresentation _ _)
  have hc : j.left ≫ (torsion P.G (p ^ n)).hom = (Hs P' x0 hu).hom := Over.w j
  have : IsFinite (j.left ≫ (torsion P.G (p ^ n)).hom) := by rw [hc]; exact hHfin
  have : LocallyOfFinitePresentation (j.left ≫ (torsion P.G (p ^ n)).hom) := by rw [hc]; exact hHlfp
  have : IsFinite j.left := IsFinite.of_comp j.left (torsion P.G (p ^ n)).hom
  have : IsClosedImmersion j.left := (IsClosedImmersion.iff_isFinite_and_mono _).2 ⟨inferInstance, hm⟩
  have : LocallyOfFinitePresentation j.left :=
    GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp j.left (torsion P.G (p ^ n)).hom
  refine isOpenImmersion_of_stalk j.left fun x => ?_
  obtain ⟨s, hs⟩ := residue_lift j.left x
  haveI : IsLocalRing ((torsion P.G (p ^ n)).left.presheaf.stalk (j.left x)) :=
    LocallyRingedSpace.isLocalRing _ _
  exact GlobalTheory.T.finite_part_pow_eq_one_local P' x0 hu hg h ((torsion P.G (p ^ n)).left.presheaf.stalk (j.left x)) (hS := this)
    ((torsion P.G (p ^ n)).left.fromSpecStalk (j.left x)) ⟨s, hs⟩

end GlobalTheory.FinPartOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasTopFormIntegralFiniteAdditiveHomogeneousStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n),
    (∀ α : A.Fld, A.IsForm α → ∀ ε : ℤˣ, IsFiniteMeasure (A.part α ε)) ∧
    (∀ (g : M → ℝ) (α β : A.Fld), A.IsForm α → A.IsForm β → (∀ ε : ℤˣ, Integrable g (A.part α ε)) → (∀ ε : ℤˣ, Integrable g (A.part β ε)) →
      (∀ ε : ℤˣ, Integrable g (A.part (α + β) ε)) ∧ wInt A g (α + β) = wInt A g α + wInt A g β) ∧
    (∀ (g : M → ℝ) (t : ℝ) (α : A.Fld), A.IsForm α → wInt A g ((t : ℂ) • α) = t * wInt A g α) ∧
    (∀ (g : M → ℝ) (α β : A.Fld), (∀ x, dens (α x) = dens (β x)) → wInt A g α = wInt A g β) := by
  first | exact @GlobalTheory.LineForm.wInt_props | exact GlobalTheory.LineForm.wInt_props | (intros; apply GlobalTheory.LineForm.wInt_props <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClassSumOfAdicSumUnitSmulTermsStatement
section
open IsLocalRing GlobalTheory.Poinc GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClassSum_of_adicSum_unit_smul_terms : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (A : Type) [CommRing A] [IsLocalRing A] (Φ : VPre bar q W A) (y : Φ.Y) (N : ℕ), 1 ≤ N → ∀ (κ : Fin s → Φ.X y) (c : Φ.Q) (V' : Type) [CommRing V'] [IsLocalRing V'] (io : Φ.V y →+* V') (e : V'ˣ) (x : V'), SumI (maximalIdeal V') (fun nu : Fin s → Φ.X y => (e : V') * io (Φ.term y (κ + N • nu) c)) x → Φ.IsClassSum y N κ c io (((e⁻¹ : V'ˣ) : V') * x) := by
  first | exact @GlobalTheory.Poinc.isClassSum_of_sumI | exact GlobalTheory.Poinc.isClassSum_of_sumI | (intros; apply GlobalTheory.Poinc.isClassSum_of_sumI <;> assumption)
end

