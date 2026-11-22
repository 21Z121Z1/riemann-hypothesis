import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ThirdPointDerivativeAtZeroSeriesMemIntegral
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0010
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0013
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0006
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import ReciprocityTheory.DualLattices.Bundle0016
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0007
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NotIsUnitNatCastOfIsLocalHom
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0027
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0009
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlModuleLevelOffDiagNormSqLe

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompactCasimirBoundEmbeddedComponentStatement
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactCasimirBound_embedded_component : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (c : ℝ) (s : Fin n) (y : N s), IsUnitary ε E → (∀ s, IsUnitary ε (F s)) → AlgTens ε E N F io pr → 0 ≤ c → CasKLe ε (F s) c y → ∀ d, CasKLe ε E (c + Real.sqrt n) (io s y d) := by
  first | exact @GlobalTheory.casKLe_io_component | exact GlobalTheory.casKLe_io_component | (intros; apply GlobalTheory.casKLe_io_component <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompactCasimirBoundProjectionDualTensorStatement
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactCasimirBound_projection_dualTensor : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (c : ℝ) (w : M), IsUnitary ε E → (∀ s, IsUnitary ε (F s)) → AlgTens ε E N F io pr → 0 ≤ c → CasKLe ε E c w → ∀ s d, CasKLe ε (F s) (c + Real.sqrt n) (pr s (Pi.single d w)) := by
  first | exact @GlobalTheory.casKLe_proj_single | exact GlobalTheory.casKLe_proj_single | (intros; apply GlobalTheory.casKLe_proj_single <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CovariantDerivativeValueCharacterGerms
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem nabVal_character_columns_of_canonGauge : (∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → Function.Injective (algebraMap R k) → ∀ (w0 : O) (N m n : ℕ) (I : Ideal R), (N : R) ∈ I → ∀ (a c : Fin n → O), (∀ b, star (a b) * a b = (N : O) * c b) →
    ∀ (ι : Type) [Fintype ι] (u : ι → Fin d → R) (S : Fin n → Set ι) (α : Fin n → ι → R), (∀ b, ∀ l ∈ S b, α b l - 1 ∈ I ∧ IsUnit (α b l) ∧
      (dAct k B (a b)).mulVec (fun i => algebraMap R k (u l i)) = algebraMap R k (α b l) • (fun i => algebraMap R k (u l i))) →
    (∀ b, ∀ l ∈ S b, ∀ l' ∈ S b, dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec ((dAct k B (c b * w0)).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) →
    ∀ (χ : Fin n → PS R 1 d) (y : ι × Fin n → R), (∀ b, constantCoeff (χ b) = 1) → (∀ b, ∀ l ∈ S b, Dof B.G.F (u l) (χ b) = C (y (l, b)) * χ b) →
    ∀ P : MvPolynomial (ι × Fin n) R, (∀ mo ∈ P.support, ∀ l b, mo (l, b) ≠ 0 → l ∈ S b) →
    ∃ g : Fin n → PS R 1 d, ∃ r ∈ I, ∑ mo ∈ P.support, algebraMap R k (P.coeff mo) *
      ∏ b, B.nabVal k h w0 m (FB.toK k (g b)) (fun l i => algebraMap R k (u l i)) (MvPolynomial.monomial (colM mo b) 1) =
        algebraMap R k (MvPolynomial.eval y P + r)) :=
  GlobalTheory.nabVal_character_columns (GlobalTheory.exists_integral_germ_nabVal_congr
    GlobalTheory.canonGauge_dmonOf_hL_natCast_mul GlobalTheory.dmonOf_mul_congr_of_congr)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGoodReductionAlgebraicWeierstrassModel
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology UpperHalfPlane

namespace GlobalTheory.MomOne

theorem model_norm_le_one_of_isIntegral {q : ℕ} [Fact q.Prime] {x : ℂ_[q]} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  let S : Subring ℂ_[q] := (NormedField.valuation (K := ℂ_[q])).integer
  have hS := Valuation.integer.integers (NormedField.valuation (K := ℂ_[q]))
  have h1 : IsIntegral S x := hx.tower_top
  have h2 := hS.mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem model_isIntegral_j {d : ℕ} (hd : d ≠ 0) {L : PeriodPair} (hL : IsOK d L) :
    IsIntegral ℤ (GlobalTheory.latticeCurve L).j := by
  have hw : ((GlobalTheory.halfOneAddSqrtNeg d hd : ℍ) : ℂ) = wK d := by
    change (1 + √d * Complex.I) / 2 = _
    rw [wK]; ring
  rw [GlobalTheory.latticeCurve_j (a := 1) (τ := GlobalTheory.halfOneAddSqrtNeg d hd) one_ne_zero]
  · exact GlobalTheory.isIntegral_modularJ_halfOneAddSqrtNeg d hd
  · intro x
    rw [hL x, hw]
    constructor
    · rintro ⟨u, v, rfl⟩
      exact ⟨v, u, by ring⟩
    · rintro ⟨m, n, rfl⟩
      exact ⟨n, m, by ring⟩

theorem exists_model : ∀ (d q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (L : PeriodPair), d.Prime → d % 16 = 7 → IsOK d L → ∃ M : Mdl q, M.ι = ι ∧ M.L = L ∧ M.Ok ∧ IsAlgebraic ℚ M.W.a₁ ∧ IsAlgebraic ℚ M.W.a₂ ∧ IsAlgebraic ℚ M.W.a₃ ∧ IsAlgebraic ℚ M.W.a₄ ∧ IsAlgebraic ℚ M.W.a₆ := by
  intro d q _ ι L hd _ hL
  obtain ⟨E, h₁, h₂, h₃, h₄, h₆, hΔ, hc⟩ :=
    GlobalTheory.CMCurves.exists_integral_curve (model_isIntegral_j hd.ne_zero hL)
  have hE : E.IsElliptic := ⟨hΔ ▸ isUnit_one⟩
  have hj : (GlobalTheory.latticeCurve L).j = E.j := by
    rw [← hc, WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ', hΔ]
    simp
  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq _ _ hj
  have hu : (C.u : ℂ) ≠ 0 := C.u.ne_zero
  have e4 : E.c₄ / 12 = L.g₂ / (C.u : ℂ) ^ 4 := by
    rw [← hC, WeierstrassCurve.variableChange_c₄, GlobalTheory.latticeCurve_c₄, Units.val_inv_eq_inv_val]
    field_simp
  have e6 : E.c₆ / 216 = L.g₃ / (C.u : ℂ) ^ 6 := by
    have : (GlobalTheory.latticeCurve L).c₆ = 216 * L.g₃ := by
      simp only [GlobalTheory.latticeCurve, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆]
      ring
    rw [← hC, WeierstrassCurve.variableChange_c₆, this, Units.val_inv_eq_inv_val]
    field_simp
  have hi : ∀ {x : ℂ}, IsIntegral ℤ x → IsIntegral ℤ ((ι : ℂ →+* ℂ_[q]) x) := fun hx ↦
    hx.map_of_comp_eq (RingHom.id ℤ) (ι : ℂ →+* ℂ_[q]) (RingHom.ext_int _ _)
  have ha : ∀ {x : ℂ}, IsIntegral ℤ x → IsAlgebraic ℚ ((ι : ℂ →+* ℂ_[q]) x) := fun hx ↦
    (IsIntegral.tower_top (A := ℚ) (hi hx)).isAlgebraic
  refine ⟨⟨ι, L, C.u, E.map (ι : ℂ →+* ℂ_[q])⟩, rfl, rfl,
    ⟨hu, model_norm_le_one_of_isIntegral (hi h₁), model_norm_le_one_of_isIntegral (hi h₂),
      model_norm_le_one_of_isIntegral (hi h₃), model_norm_le_one_of_isIntegral (hi h₄),
      model_norm_le_one_of_isIntegral (hi h₆), ?_, ?_, ?_⟩, ha h₁, ha h₂, ha h₃, ha h₄, ha h₆⟩
  · simp [WeierstrassCurve.map_Δ, hΔ]
  · change (E.map (ι : ℂ →+* ℂ_[q])).c₄ / 12 = ι (L.g₂ / (C.u : ℂ) ^ 4)
    rw [← e4, WeierstrassCurve.map_c₄, map_div₀, map_ofNat]
    rfl
  · change (E.map (ι : ℂ →+* ℂ_[q])).c₆ / 216 = ι (L.g₃ / (C.u : ℂ) ^ 6)
    rw [← e6, WeierstrassCurve.map_c₆, map_div₀, map_ofNat]
    rfl

end GlobalTheory.MomOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevEAddTwo
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

open Finset in
open scoped InnerProductSpace in
private lemma adMat_conjTranspose_eq_adMat_swap {n : ℕ} (a b : Fin n) :
    (_root_.GlobalTheory.CasKAdjoint.adMat a b).conjTranspose = _root_.GlobalTheory.CasKAdjoint.adMat b a := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [Matrix.conjTranspose_apply, _root_.GlobalTheory.CasKAdjoint.adMat, Prod.mk.injEq, star_sub, apply_ite star,
    star_one, star_zero]
  congr 1
  · exact if_congr ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₂, h₁, h₃.symm⟩, fun ⟨h₁, h₂, h₃⟩ => ⟨h₂, h₁, h₃.symm⟩⟩ rfl rfl
  · exact if_congr ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₃, h₂.symm, h₁⟩, fun ⟨h₁, h₂, h₃⟩ => ⟨h₃, h₂.symm, h₁⟩⟩ rfl rfl

open Finset in
open scoped InnerProductSpace in
private lemma sum_adMat_apply_first_index_smul {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (a b : Fin n) (x : Fin n × Fin n → M) (i : Fin n × Fin n) :
    ∑ j, _root_.GlobalTheory.CasKAdjoint.adMat a b i j • x j =
      (if i.1 = a then x (b, i.2) else 0) - (if i.2 = b then x (i.1, a) else 0) := by
  obtain ⟨i₁, i₂⟩ := i
  simp only [_root_.GlobalTheory.CasKAdjoint.adMat, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
    Fintype.sum_prod_type, Prod.mk.injEq]
  simp [ite_and]

open Finset in
open scoped InnerProductSpace in
private lemma norm_ite_zero_sq {M : Type} [NormedAddCommGroup M] (p : Prop) [Decidable p] (y : M) :
    ‖if p then y else 0‖ ^ 2 = if p then ‖y‖ ^ 2 else 0 := by
  split_ifs <;> simp

open Finset in
open scoped InnerProductSpace in
private lemma sum_norm_sq_adMat_mulVec_le {M : Type} [NormedAddCommGroup M]
    [InnerProductSpace ℂ M] {n : ℕ} (a b : Fin n) (x : Fin n × Fin n → M) :
    ∑ i, ‖∑ j, _root_.GlobalTheory.CasKAdjoint.adMat a b i j • x j‖ ^ 2 ≤
      2 * ∑ k, ‖x (b, k)‖ ^ 2 + 2 * ∑ k, ‖x (k, a)‖ ^ 2 := by
  simp_rw [sum_adMat_apply_first_index_smul]
  calc ∑ i : Fin n × Fin n, ‖(if i.1 = a then x (b, i.2) else 0) - (if i.2 = b then x (i.1, a) else 0)‖ ^ 2
      ≤ ∑ i : Fin n × Fin n, (2 * ‖if i.1 = a then x (b, i.2) else 0‖ ^ 2
          + 2 * ‖if i.2 = b then x (i.1, a) else 0‖ ^ 2) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h := norm_sub_le (if i.1 = a then x (b, i.2) else 0) (if i.2 = b then x (i.1, a) else 0)
        nlinarith [norm_nonneg ((if i.1 = a then x (b, i.2) else 0) - (if i.2 = b then x (i.1, a) else 0)),
          sq_nonneg (‖if i.1 = a then x (b, i.2) else 0‖ - ‖if i.2 = b then x (i.1, a) else 0‖)]
    _ = 2 * ∑ k, ‖x (b, k)‖ ^ 2 + 2 * ∑ k, ‖x (k, a)‖ ^ 2 := by
        simp only [norm_ite_zero_sq, Finset.sum_add_distrib, ← Finset.mul_sum, Fintype.sum_prod_type]
        rw [Finset.sum_comm (f := fun x_1 y => if y = b then ‖x (x_1, a)‖ ^ 2 else 0)]
        simp

open Finset in
open scoped InnerProductSpace in
private lemma sum_eq_sign_norm_sq_adMat_mulVec_le {M : Type} [NormedAddCommGroup M]
    [InnerProductSpace ℂ M] {n : ℕ} (ε : Fin n → Bool) (x : Fin n × Fin n → M) :
    (∑ a, ∑ b, if ε a = ε b then ∑ i, ‖∑ j, _root_.GlobalTheory.CasKAdjoint.adMat a b i j • x j‖ ^ 2 else 0) ≤
      (8 * (n : ℝ)) ^ 2 * ∑ j, ‖x j‖ ^ 2 := by
  have hS : ∑ j, ‖x j‖ ^ 2 = ∑ b, ∑ k, ‖x (b, k)‖ ^ 2 := Fintype.sum_prod_type _
  have hS' : ∑ j, ‖x j‖ ^ 2 = ∑ a, ∑ k, ‖x (k, a)‖ ^ 2 := by
    rw [hS, Finset.sum_comm]
  have h0 : 0 ≤ ∑ j, ‖x j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc (∑ a, ∑ b, if ε a = ε b then ∑ i, ‖∑ j, _root_.GlobalTheory.CasKAdjoint.adMat a b i j • x j‖ ^ 2 else 0)
      ≤ ∑ a : Fin n, ∑ b : Fin n, (2 * ∑ k, ‖x (b, k)‖ ^ 2 + 2 * ∑ k, ‖x (k, a)‖ ^ 2) := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        split_ifs
        · exact sum_norm_sq_adMat_mulVec_le a b x
        · positivity
    _ = 4 * n * ∑ j, ‖x j‖ ^ 2 := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        rw [← hS, ← hS']
        ring
    _ ≤ (8 * (n : ℝ)) ^ 2 * ∑ j, ‖x j‖ ^ 2 := by
        rcases Nat.eq_zero_or_pos n with hn | hn
        · simp [hn]
        · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
          nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 4 * n) h0)
            (by linarith : (0:ℝ) ≤ 16 * n - 1)]

open Finset in
open scoped InnerProductSpace in
private lemma sum_adMat_apply_second_index_smul {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (a b : Fin n) (y : Fin n × Fin n → M) (j : Fin n × Fin n) :
    ∑ i, _root_.GlobalTheory.CasKAdjoint.adMat a b i j • y i =
      (if j.1 = b then y (a, j.2) else 0) - (if j.2 = a then y (j.1, b) else 0) := by
  obtain ⟨j₁, j₂⟩ := j
  simp only [_root_.GlobalTheory.CasKAdjoint.adMat, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
    Fintype.sum_prod_type, Prod.mk.injEq]
  simp [ite_and, eq_comm]

open Finset in
open scoped InnerProductSpace in
private lemma sum_abs_shifted_weight_sub_le_add_two {n : ℕ} (ω μ : Fin n → ℝ) (a b : Fin n) :
    ∑ c, |ω c + (if c = a then 1 else 0) - (if c = b then 1 else 0) - μ c| ≤ ∑ c, |ω c - μ c| + 2 := by
  calc ∑ c, |ω c + (if c = a then 1 else 0) - (if c = b then 1 else 0) - μ c|
      ≤ ∑ c, (|ω c - μ c| + ((if c = a then 1 else 0) + (if c = b then 1 else 0))) := by
        refine Finset.sum_le_sum fun c _ => ?_
        have h1 : (0:ℝ) ≤ if c = a then 1 else 0 := by split_ifs <;> norm_num
        have h2 : (0:ℝ) ≤ if c = b then 1 else 0 := by split_ifs <;> norm_num
        rw [show ω c + (if c = a then 1 else 0) - (if c = b then 1 else 0) - μ c
          = (ω c - μ c) + ((if c = a then 1 else 0) - (if c = b then 1 else 0)) by ring]
        refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [abs_le]; constructor <;> linarith
    _ = ∑ c, |ω c - μ c| + 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        simp; norm_num

open Finset in
open scoped InnerProductSpace in
private lemma isWeight_shift_of_glRel {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    {E : Fin n → Fin n → Module.End ℂ M} (hG : _root_.Formalism.REAL.GlRel E) {ω : Fin n → ℝ} {x : M} (hx : _root_.Formalism.REAL.IsWeight E ω x)
    (a b : Fin n) :
    _root_.Formalism.REAL.IsWeight E (fun c => ω c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) (E a b x) := by
  intro c
  have h := LinearMap.congr_fun (hG c c a b) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hx c, map_smul, ite_apply, LinearMap.zero_apply,
    @eq_comm _ b c] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  by_cases ha : c = a <;> by_cases hb : c = b
  · subst ha; subst hb; simp
  · subst ha; simp [hb, add_smul]; abel
  · subst hb; simp [ha, sub_smul]; abel
  · simp [ha, hb]

open Finset in
open scoped InnerProductSpace in

theorem _root_.GlobalTheory.lev_E_add_two : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (j : ℕ) (w : M), _root_.Formalism.REAL.GlRel E → _root_.Formalism.REAL.IsUnitary ε E → _root_.BranchingSupport.Lev ε E μ j w → ∀ a b, _root_.BranchingSupport.Lev ε E μ (j + 2) (E a b w) := by
  intro M _ _ n ε E μ j w hG hU hw a b
  unfold _root_.BranchingSupport.Lev _root_.BranchingSupport.WtNear at hw ⊢
  obtain ⟨hC, hS⟩ := hw
  refine ⟨?_, ?_⟩
  · have hK := _root_.Formalism.REAL.isUnitary_kUnit ε E hU
    have h := _root_.GlobalTheory.TensOp.casKLe_tensor_operator M n ε E M (Fin n × Fin n) E (fun i => E i.1 i.2)
      _root_.GlobalTheory.CasKAdjoint.adMat _ (8 * n) hK hK (by positivity) (by positivity)
      (fun a b _ => adMat_conjTranspose_eq_adMat_swap a b)
      (sum_eq_sign_norm_sq_adMat_mulVec_le ε)
      (fun a b _ k v => by
        have hs := sum_adMat_apply_second_index_smul a b (fun i => E i.1 i.2 v) k
        simp only at hs ⊢
        rw [hs]
        have h := LinearMap.congr_fun (hG a b k.1 k.2) v
        simp only [LinearMap.sub_apply, Module.End.mul_apply, ite_apply, LinearMap.zero_apply,
          @eq_comm _ b k.1] at h
        rw [sub_eq_iff_eq_add'] at h
        rw [h]
        split_ifs <;> simp)
      w hC (a, b)
    convert h using 1
    push_cast
    ring
  · rw [← Submodule.mem_comap]
    refine Submodule.span_le.2 ?_ hS
    rintro x ⟨ω, hd, hx⟩
    exact Submodule.subset_span ⟨_, (sum_abs_shifted_weight_sub_le_add_two ω _ a b).trans (by push_cast; linarith),
      isWeight_shift_of_glRel hG hx a b⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.OpExistsEqAdd
section
set_option autoImplicit false

noncomputable section

open scoped TensorProduct
open NumberField

namespace GlobalTheory.AvChartCompare

open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R]

def IsPrimeUnder (w : Place p R) (P : Ideal R) : Prop :=
  P.IsMaximal ∧ (p : R) ∈ P ∧ (P.map w.toOw).IsMaximal ∧
    ∀ Q : Ideal R, Q.IsMaximal → Q ≠ P → Q.map w.toOw = ⊤

def liftOw (w : Place p R) {S : Type} [CommRing S] (ψ : Op p R →+* S) (h : ψ w.e = 1) :
    w.Ow →+* S :=
  Ideal.Quotient.lift _ ψ (by
    intro z hz
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    simp [h])

namespace IsPrimeUnder

variable {w : Place p R} {P : Ideal R}

theorem p_mem (h : IsPrimeUnder w P) : (p : w.Ow) ∈ P.map w.toOw := by
  rw [← map_natCast w.toOw]; exact Ideal.mem_map_of_mem _ h.2.1

theorem map_eq_pow [IsDedekindDomain R] (h : IsPrimeUnder w P) {J : Ideal R} (hJ : J ≠ ⊥) :
    J.map w.toOw =
      P.map w.toOw ^ (UniqueFactorizationMonoid.normalizedFactors J).count P := by
  have := h.1
  obtain ⟨Q, hPQ, hQe⟩ := Ideal.eq_prime_pow_mul_coprime hJ P
  generalize Multiset.count P _ = e at hQe
  have hQ0 : Q ≠ ⊥ := by rintro rfl; exact hJ (by simpa using hQe)
  rw [hQe, Ideal.map_mul, Ideal.map_pow,
    GlobalTheory.Proof.different_power_unramified_iff.map_eq_top_of_coprime _ P h.1 h.2.2.2 Q hQ0 hPQ, Ideal.mul_top]

variable [IsDedekindDomain R] [CharZero R]

theorem span_p_eq (h : IsPrimeUnder w P) :
    Ideal.span {(p : w.Ow)} = P.map w.toOw ^
      (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(p : R)})).count P := by
  rw [← h.map_eq_pow (by simpa using (Fact.out : p.Prime).ne_zero), Ideal.map_span,
    Set.image_singleton, map_natCast]

theorem count_ne_zero (h : IsPrimeUnder w P) :
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(p : R)})).count P ≠ 0 := by
  intro h0
  have h1 := h.span_p_eq
  rw [h0, pow_zero, Ideal.one_eq_top] at h1
  exact h.2.2.1.ne_top (eq_top_iff.2 (h1 ▸ (Ideal.span_singleton_le_iff_mem _).2 h.p_mem))

variable [Module.Finite ℤ R]

theorem pow_inj (h : IsPrimeUnder w P) {i j : ℕ}
    (hij : P.map w.toOw ^ i = P.map w.toOw ^ j) : i = j := by
  have key : ∀ i j : ℕ, P.map w.toOw ^ i = P.map w.toOw ^ j → ¬ i < j := by
    intro i j hij hlt
    have h1 : Ideal.span {(p : w.Ow) ^ i} = Ideal.span {(p : w.Ow) ^ j} := by
      rw [← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow, h.span_p_eq, ← pow_mul,
        ← pow_mul, mul_comm _ i, mul_comm _ j, pow_mul, pow_mul, hij]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (h1 ▸ Ideal.mem_span_singleton_self _)
    have h2 : ∀ (n : ℕ) (x : w.Ow), (p : w.Ow) ^ n * x = 0 → x = 0 := by
      intro n
      induction n with
      | zero => intro x hx; simpa using hx
      | succ n ih =>
        intro x hx
        exact GlobalTheory.Proof.different_power_unramified_iff.ow_p_torsionFree p R w x (ih _ (by linear_combination hx))
    have h3 := h2 i (1 - c * p ^ k * p) (by linear_combination -hc)
    apply h.2.2.1.ne_top
    rw [Ideal.eq_top_iff_one, sub_eq_zero.1 h3]
    exact Ideal.mul_mem_left _ _ h.p_mem
  exact le_antisymm (not_lt.1 (key j i hij.symm)) (not_lt.1 (key i j hij))

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra in

theorem isDiffVal_iff (h : IsPrimeUnder w P) (vd : ℝ) :
    w.IsDiffVal_vp vd ↔ vd =
      ((UniqueFactorizationMonoid.normalizedFactors (differentIdeal ℤ R)).count P : ℝ) /
        ((UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(p : R)})).count P : ℝ) := by
  have : CharZero (FractionRing R) := inferInstance
  have : IsLocalization (Algebra.algebraMapSubmonoid R (nonZeroDivisors ℤ)) (FractionRing R) :=
    IsIntegralClosure.isLocalization _ (FractionRing ℤ) _ _
  have : FiniteDimensional (FractionRing ℤ) (FractionRing R) :=
    .of_isLocalization ℤ R (nonZeroDivisors ℤ)
  have hsep : Algebra.IsSeparable (FractionRing ℤ) (FractionRing R) := inferInstance
  have hD : differentIdeal ℤ R ≠ ⊥ := differentIdeal_ne_bot
  have h1 := h.span_p_eq
  have h2 := h.map_eq_pow hD
  have he := h.count_ne_zero
  generalize Multiset.count P (UniqueFactorizationMonoid.normalizedFactors
    (Ideal.span {(p : R)})) = e at h1 he ⊢
  generalize Multiset.count P (UniqueFactorizationMonoid.normalizedFactors
    (differentIdeal ℤ R)) = k at h2 ⊢
  have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he
  constructor
  · rintro ⟨a, b, hb, hvd, hab⟩
    rw [← Ideal.span_singleton_pow, h1, h2, ← pow_mul, ← pow_mul] at hab
    have h3 : (k : ℝ) * b = e * a := by exact_mod_cast h.pow_inj hab
    have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
    rw [eq_div_iff he']
    apply mul_right_cancel₀ hb'
    rw [h3, ← hvd]; ring
  · rintro rfl
    refine ⟨k, e, Nat.pos_of_ne_zero he, div_mul_cancel₀ _ he', ?_⟩
    rw [← Ideal.span_singleton_pow, h1, h2, ← pow_mul, ← pow_mul, mul_comm]

end IsPrimeUnder

end GlobalTheory.AvChartCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowerSeriesEvalTsumUnitDiscPropertiesStatement
section
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeriesEvalTsum_unitDisc_properties_alt : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (x : K), ‖x‖ < 1 → (∀ f : PowerSeries K, Bdd f → PowerSeriesHasSumAt f x (ev1 f x)) ∧ (∀ f g : PowerSeries K, Bdd f → Bdd g → ev1 (f + g) x = ev1 f x + ev1 g x ∧ ev1 (f - g) x = ev1 f x - ev1 g x ∧ ev1 (f * g) x = ev1 f x * ev1 g x) ∧ (∀ a : K, ev1 (PowerSeries.C a) x = a) ∧ ev1 PowerSeries.X x = x ∧ (∀ P : Polynomial K, Bdd (P : PowerSeries K) ∧ ev1 (P : PowerSeries K) x = P.eval x) ∧ (∀ (ι : Type) (t : Finset ι) (f : ι → PowerSeries K), (∀ i ∈ t, Bdd (f i)) → ev1 (∏ i ∈ t, f i) x = ∏ i ∈ t, ev1 (f i) x) ∧ (∀ f : PowerSeries K, Intg f → ‖ev1 f x‖ ≤ 1 ∧ ‖ev1 f x - PowerSeries.coeff 0 f‖ ≤ ‖x‖ ∧ ‖ev1 f x - PowerSeries.coeff 0 f - PowerSeries.coeff 1 f * x‖ ≤ ‖x‖ ^ 2) ∧ (∀ (f g : PowerSeries K), Intg g → PowerSeries.constantCoeff g = 0 → Bdd f → ev1 (f.subst g) x = ev1 f (ev1 g x)) ∧ (∀ (F : MvPowerSeries (Fin 2) K) (g h : PowerSeries K), Bdd F → Intg g → Intg h → PowerSeries.constantCoeff g = 0 → PowerSeries.constantCoeff h = 0 → ev1 (MvPowerSeries.subst (![g, h] : Fin 2 → MvPowerSeries Unit K) F) x = ev F ![ev1 g x, ev1 h x]) ∧ (∀ (F : MvPowerSeries (Fin 2) K) (y : K), ‖y‖ < 1 → Intg F → Intg (shift1 F y) ∧ ev1 (shift1 F y) x = ev F ![x, y]) ∧ (∀ f : PowerSeries K, ev1 f 0 = PowerSeries.coeff 0 f) := by
  first | exact @GlobalTheory.ConvSer.powerSeriesEvalTsum_unitDisc_properties | exact GlobalTheory.ConvSer.powerSeriesEvalTsum_unitDisc_properties | (intros; apply GlobalTheory.ConvSer.powerSeriesEvalTsum_unitDisc_properties <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirOffDiagonalNormSqLeOfLevel
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem norm_sum_sq_le_fin_mul {M : Type} [NormedAddCommGroup M] {n : ℕ} (s : Finset (Fin n)) (v : Fin n → M) :
    ‖∑ c ∈ s, v c‖ ^ 2 ≤ (n : ℝ) * ∑ c ∈ s, ‖v c‖ ^ 2 := by
  have h1 : ‖∑ c ∈ s, v c‖ ≤ ∑ c ∈ s, ‖v c‖ := norm_sum_le _ _
  have h2 : (∑ c ∈ s, ‖v c‖) ^ 2 ≤ (s.card : ℝ) * ∑ c ∈ s, ‖v c‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h3 : (s.card : ℝ) ≤ n := by
    have := card_le_univ s
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  have h4 : 0 ≤ ∑ c ∈ s, ‖v c‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  calc ‖∑ c ∈ s, v c‖ ^ 2 ≤ (∑ c ∈ s, ‖v c‖) ^ 2 := by gcongr
    _ ≤ (s.card : ℝ) * ∑ c ∈ s, ‖v c‖ ^ 2 := h2
    _ ≤ (n : ℝ) * ∑ c ∈ s, ‖v c‖ ^ 2 := mul_le_mul_of_nonneg_right h3 h4

theorem offDiagPart_sq_le_of_lev : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ)
    (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (x : Fin n → M),
    IsMod ε E μ → Shape ε kk μ bv → j ≤ 4 * n ^ 2 + 2 → (∀ c, Lev ε E μ j (x c)) →
      ∑ b, ‖∑ c ∈ univ.erase b, E b c (x c)‖ ^ 2 ≤ (bv / 16) ^ 2 * ∑ c, ‖x c‖ ^ 2 := by
  intro M _ _ n ε E μ kk j bv x hmod hsh hj hlev

  have step1 : ∀ b, ‖∑ c ∈ univ.erase b, E b c (x c)‖ ^ 2 ≤
      (n : ℝ) * ∑ c ∈ univ.erase b, ‖E b c (x c)‖ ^ 2 :=
    fun b => norm_sum_sq_le_fin_mul _ _
  have swap : ∑ b, ∑ c ∈ univ.erase b, ‖E b c (x c)‖ ^ 2 =
      ∑ c, ∑ b ∈ univ.erase c, ‖E b c (x c)‖ ^ 2 :=
    Finset.sum_comm' (fun b c => by
      simp only [mem_univ, mem_erase, true_and, and_true]
      exact ne_comm)
  have step2 : ∀ c, (n : ℝ) * ∑ b ∈ univ.erase c, ‖E b c (x c)‖ ^ 2 ≤
      (bv / 16) ^ 2 * ‖x c‖ ^ 2 := by
    intro c
    refine le_trans ?_ (lev_offDiag_normSq_le M n ε E μ kk j bv (x c) hmod hsh hj (hlev c))
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)
    calc ∑ b ∈ univ.erase c, ‖E b c (x c)‖ ^ 2
        ≤ ∑ b ∈ univ.erase c, ∑ b' ∈ univ.erase b, ‖E b b' (x c)‖ ^ 2 := by
          refine sum_le_sum fun b hb => ?_
          have hcb : c ∈ univ.erase b :=
            mem_erase.2 ⟨fun h => (mem_erase.1 hb).1 h.symm, mem_univ _⟩
          exact single_le_sum (f := fun b' => ‖E b b' (x c)‖ ^ 2) (fun _ _ => sq_nonneg _) hcb
      _ ≤ ∑ b, ∑ b' ∈ univ.erase b, ‖E b b' (x c)‖ ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
            fun _ _ _ => sum_nonneg fun _ _ => sq_nonneg _
  calc ∑ b, ‖∑ c ∈ univ.erase b, E b c (x c)‖ ^ 2
      ≤ ∑ b, (n : ℝ) * ∑ c ∈ univ.erase b, ‖E b c (x c)‖ ^ 2 := sum_le_sum fun b _ => step1 b
    _ = ∑ c, (n : ℝ) * ∑ b ∈ univ.erase c, ‖E b c (x c)‖ ^ 2 := by
      rw [← mul_sum, swap, mul_sum]
    _ ≤ ∑ c, (bv / 16) ^ 2 * ‖x c‖ ^ 2 := sum_le_sum fun c _ => step2 c
    _ = (bv / 16) ^ 2 * ∑ c, ‖x c‖ ^ 2 := by rw [mul_sum]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlModuleLevelOffDiagNormSqLeStatement
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryGlModule_level_offDiag_normSq_le : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (w : M), IsMod ε E μ → Shape ε kk μ bv → j ≤ 4 * n ^ 2 + 2 → Lev ε E μ j w → (n : ℝ) * ∑ a, ∑ b ∈ univ.erase a, ‖E a b w‖ ^ 2 ≤ (bv / 16) ^ 2 * ‖w‖ ^ 2 := by
  first | exact @GlobalTheory.lev_offDiag_normSq_le | exact GlobalTheory.lev_offDiag_normSq_le | (intros; apply GlobalTheory.lev_offDiag_normSq_le <;> assumption)
end

