import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1359
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1091
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1085
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0351
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0344
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0352
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0434
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0431
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1364
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightDerivativeNilRadicalInvariant
section
open Matrix GlobalTheory.TorFin
open scoped ContDiff

noncomputable section

namespace GlobalTheory.TorFinKill

variable {n : ℕ} {G : Type} [Group G]

theorem isUni_exp {J X : Matrix (Fin n) (Fin n) ℂ} (hJ : IsUnit J.det) (hX : IsSkew J X) :
    IsUni J (NormedSpace.exp X) := by
  have h1 : Xᴴ = J * (-X) * J⁻¹ := by
    rw [mul_neg, ← eq_neg_of_add_eq_zero_left hX, mul_nonsing_inv_cancel_right _ _ hJ]
  unfold IsUni
  rw [← Matrix.exp_conjTranspose, h1, Matrix.exp_conj _ _ ((isUnit_iff_isUnit_det J).2 hJ),
    nonsing_inv_mul_cancel_right _ _ hJ, mul_assoc, ← Matrix.exp_add_of_commute _ _ (Commute.refl X).neg_left,
    neg_add_cancel, NormedSpace.exp_zero, mul_one]

theorem isSkew_real_smul {J Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSkew J Z) (t : ℝ) : IsSkew J (t • Z) := by
  unfold IsSkew at *
  rw [conjTranspose_smul, star_trivial, smul_mul_assoc, mul_smul_comm, ← smul_add, hZ, smul_zero]

theorem map_one_of_isMulOn {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G} (hs : IsMulOn J s) :
    s 1 = 1 := by
  have h1 : IsUni J 1 := by simp [IsUni]
  have := hs 1 1 h1 h1
  rw [one_mul] at this
  exact mul_eq_left.mp this.symm

theorem lineOf_zero {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G} (hs : IsMulOn J s)
    (Z : Matrix (Fin n) (Fin n) ℂ) : lineOf s Z 0 = 1 := by
  simp [lineOf, map_one_of_isMulOn hs]

theorem rho_apply_eq_deriv {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G} (hs : IsMulOn J s)
    {ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s)} (hρ : IsRightDer J s ρ)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSkew J Z) (f : smLoc J s) (g : G) :
    (ρ Z f).1 g = deriv (fun τ : ℝ => f.1 (g * lineOf s Z τ)) 0 := by
  have h := hρ Z hZ f g 0
  rw [lineOf_zero hs, mul_one] at h
  exact h.deriv.symm

theorem decomp {J : Matrix (Fin n) (Fin n) ℂ} (hJh : Jᴴ = J) (hJ : IsUnit J.det) (Y : Matrix (Fin n) (Fin n) ℂ) :
    IsSkew J ((1/2 : ℂ) • (Y - J⁻¹ * Yᴴ * J)) ∧ IsSkew J ((-Complex.I/2) • (Y + J⁻¹ * Yᴴ * J)) ∧
      Y = (1/2 : ℂ) • (Y - J⁻¹ * Yᴴ * J) + Complex.I • ((-Complex.I/2) • (Y + J⁻¹ * Yᴴ * J)) := by
  have hA : (J⁻¹ * Yᴴ * J)ᴴ * J = J * Y := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_nonsing_inv, conjTranspose_conjTranspose, hJh,
      mul_assoc, mul_assoc, nonsing_inv_mul _ hJ, mul_one]
  have hB : J * (J⁻¹ * Yᴴ * J) = Yᴴ * J := by
    rw [← mul_assoc, ← mul_assoc, mul_nonsing_inv _ hJ, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · unfold IsSkew
    rw [conjTranspose_smul, smul_mul_assoc, mul_smul_comm, conjTranspose_sub, sub_mul, mul_sub, hA, hB]
    have : star (1/2 : ℂ) = 1/2 := by simp
    rw [this]
    module
  · unfold IsSkew
    rw [conjTranspose_smul, smul_mul_assoc, mul_smul_comm, conjTranspose_add, add_mul, mul_add, hA, hB]
    have : star (-Complex.I/2 : ℂ) = Complex.I/2 := by simp
    rw [this]
    module
  · rw [smul_smul, show Complex.I * (-Complex.I/2) = 1/2 by linear_combination (-1/2 : ℂ) * Complex.I_sq]
    module

end GlobalTheory.TorFinKill

namespace GlobalTheory.TorFinKill

variable {n : ℕ} {G : Type} [Group G]

def IsLeftInv {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G} (N : Subgroup G) (f : smLoc J s) : Prop :=
  ∀ ν ∈ N, ∀ g, f.1 (ν * g) = f.1 g

theorem isLeftInv_rho_skew {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G} (hs : IsMulOn J s)
    {ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s)} (hρ : IsRightDer J s ρ) {N : Subgroup G}
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSkew J Z) {f : smLoc J s} (hf : IsLeftInv N f) : IsLeftInv N (ρ Z f) := by
  intro ν hν g
  rw [rho_apply_eq_deriv hs hρ hZ, rho_apply_eq_deriv hs hρ hZ]
  congr 1
  funext τ
  rw [mul_assoc, hf ν hν]

theorem rho_apply_add_I {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G}
    (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s)) {Y : Matrix (Fin n) (Fin n) ℂ}
    (Z₁ Z₂ : Matrix (Fin n) (Fin n) ℂ) (hY : Y = Z₁ + Complex.I • Z₂) (f : smLoc J s) (g : G) :
    (ρ Y f).1 g = (ρ Z₁ f).1 g + Complex.I * (ρ Z₂ f).1 g := by
  subst hY
  rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem isLeftInv_rho {J : Matrix (Fin n) (Fin n) ℂ} (hJh : Jᴴ = J) (hJ : IsUnit J.det)
    {s : Matrix (Fin n) (Fin n) ℂ → G} (hs : IsMulOn J s)
    {ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s)} (hρ : IsRightDer J s ρ) {N : Subgroup G}
    (Y : Matrix (Fin n) (Fin n) ℂ) {f : smLoc J s} (hf : IsLeftInv N f) : IsLeftInv N (ρ Y f) := by
  obtain ⟨h1, h2, hY⟩ := decomp hJh hJ Y
  have e1 := isLeftInv_rho_skew hs hρ h1 hf
  have e2 := isLeftInv_rho_skew hs hρ h2 hf
  intro ν hν g
  rw [rho_apply_add_I ρ _ _ hY, rho_apply_add_I ρ _ _ hY, e1 ν hν, e2 ν hν]

theorem isLeftInv_adjoin {J : Matrix (Fin n) (Fin n) ℂ} (hJh : Jᴴ = J) (hJ : IsUnit J.det)
    {s : Matrix (Fin n) (Fin n) ℂ → G} (hs : IsMulOn J s)
    {ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s)} (hρ : IsRightDer J s ρ) {N : Subgroup G}
    {w : Module.End ℂ (smLoc J s)} (hw : w ∈ Algebra.adjoin ℂ (Set.range ρ)) :
    ∀ f : smLoc J s, IsLeftInv N f → IsLeftInv N (w f) := by
  induction hw using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨Y, rfl⟩ := hx
    exact fun f hf => isLeftInv_rho hJh hJ hs hρ Y hf
  | algebraMap r =>
    intro f hf ν hν g
    simp only [Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply]
    rw [hf ν hν]
  | add a b _ _ ha hb =>
    intro f hf ν hν g
    simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
    rw [ha f hf ν hν, hb f hf ν hν]
  | mul a b _ _ ha hb =>
    intro f hf
    exact ha _ (hb f hf)

theorem rho_kill_skew {J : Matrix (Fin n) (Fin n) ℂ} (hJh : Jᴴ = J) (hJ : IsUnit J.det)
    {s : Matrix (Fin n) (Fin n) ℂ → G} (hs : IsMulOn J s)
    {ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s)} (hρ : IsRightDer J s ρ) {x : Fin n → ℂ}
    {N : Subgroup G} (hN : ∀ u, IsUni J u → u - 1 ∈ nilRad J x → s u ∈ N)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSkew J Z) (hZn : Z ∈ nilRad J x) {f : smLoc J s} (hf : IsLeftInv N f) :
    (ρ Z f).1 1 = 0 := by
  rw [rho_apply_eq_deriv hs hρ hZ]
  have hc : (fun τ : ℝ => f.1 (1 * lineOf s Z τ)) = fun _ => f.1 1 := by
    funext τ
    have hmem : lineOf s Z τ ∈ N := by
      refine hN _ (isUni_exp hJ (isSkew_real_smul hZ τ)) ?_
      exact (GlobalTheory.T.nilradical_adjoint_exp_stable n J hJh hJ x _ (Submodule.smul_of_tower_mem _ τ hZn)).2
    rw [one_mul, ← mul_one (lineOf s Z τ), hf _ hmem]
  rw [hc, deriv_const]

end GlobalTheory.TorFinKill

namespace GlobalTheory.TorFin

theorem leftIdl_apply_one_eq_zero : ∀ (n : ℕ) (G : Type) [Group G] (J : Matrix (Fin n) (Fin n) ℂ) (s : Matrix (Fin n) (Fin n) ℂ → G), Jᴴ = J → IsUnit J.det → IsMulOn J s → ∀ ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s), IsRightDer J s ρ → ∀ (x : Fin n → ℂ) (N : Subgroup G), (∀ u, IsUni J u → u - 1 ∈ nilRad J x → s u ∈ N) → ∀ f : smLoc J s, (∀ ν ∈ N, ∀ g, f.1 (ν * g) = f.1 g) → ∀ T ∈ leftIdl ρ (nilRad J x : Set (Matrix (Fin n) (Fin n) ℂ)), (T f).1 1 = 0 := by
  intro n G _ J s hJh hJ hs ρ hρ x N hN f hf T hT
  induction hT using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨Y, hY, w, hw, rfl⟩ := ha
    have hwf : GlobalTheory.TorFinKill.IsLeftInv N (w f) := GlobalTheory.TorFinKill.isLeftInv_adjoin hJh hJ hs hρ hw f hf
    obtain ⟨h1, h2, hYe⟩ := GlobalTheory.TorFinKill.decomp hJh hJ Y
    have hs' := (GlobalTheory.T.nilradical_adjoint_exp_stable n J hJh hJ x Y hY).1
    have m1 : (1/2 : ℂ) • (Y - J⁻¹ * Yᴴ * J) ∈ nilRad J x := Submodule.smul_mem _ _ (Submodule.sub_mem _ hY hs')
    have m2 : (-Complex.I/2) • (Y + J⁻¹ * Yᴴ * J) ∈ nilRad J x := Submodule.smul_mem _ _ (Submodule.add_mem _ hY hs')
    rw [Module.End.mul_apply, GlobalTheory.TorFinKill.rho_apply_add_I ρ _ _ hYe,
      GlobalTheory.TorFinKill.rho_kill_skew hJh hJ hs hρ hN h1 m1 hwf,
      GlobalTheory.TorFinKill.rho_kill_skew hJh hJ hs hρ hN h2 m2 hwf, mul_zero, add_zero]
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb]
  | smul c a _ ha => simp [ha]

end GlobalTheory.TorFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianDetEqUnitMulNormAtInert
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SkewDetParity

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem val_sigma (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (h : Formalism.UG.IsInertAt F E v w) (x : E) : w.valuation E (σ x) = w.valuation E x :=
  GlobalTheory.T.valuation_algHom_eq_of_inertPrime F E σ v w h x

theorem val_algebraMap (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (h : Formalism.UG.IsInertAt F E v w) (x : F) : w.valuation E (algebraMap F E x) = v.valuation F x :=
  GlobalTheory.T.valuation_algebraMap_eq_of_inertPlace F E v w h x

theorem exists_max_dual (w : HeightOneSpectrum (𝓞 E)) : ∃ e : E, e ≠ 0 ∧
    (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) ∧
    ∀ f : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * f))) → w.valuation E f ≤ w.valuation E e :=
  GlobalTheory.T.exists_inverseDifferent_max_valuation E w

theorem exists_local_basis (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E))
    (hL : L.IsLattice E) : ∃ X : Matrix (Fin n) (Fin n) E, IsUnit X.det ∧ (∀ j, (fun i => X i j) ∈ L) ∧
    ∀ x ∈ L, ∀ i, w.valuation E ((X⁻¹ *ᵥ x) i) ≤ 1 :=
  GlobalTheory.T.exists_localBasis_at_prime_of_isLattice E w n L hL

theorem exists_den (w : HeightOneSpectrum (𝓞 E)) (a : E) (ha : w.valuation E a ≤ 1) :
    ∃ s : 𝓞 E, s ∉ w.asIdeal ∧ ∃ r : 𝓞 E, (s : E) * a = r :=
  GlobalTheory.T.exists_integer_denominator_not_mem_of_valuation_le_one E w a ha

theorem exists_common_den (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 E))
    (hσ : ∀ x, w.valuation E (σ x) = w.valuation E x)
    (hden : ∀ a : E, w.valuation E a ≤ 1 → ∃ s : 𝓞 E, s ∉ w.asIdeal ∧ ∃ r : 𝓞 E, (s : E) * a = r)
    (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) (X : Matrix (Fin n) (Fin n) E)
    (hX : ∀ x ∈ L, ∀ i, w.valuation E ((X⁻¹ *ᵥ x) i) ≤ 1) :
    ∃ s : 𝓞 E, s ∉ w.asIdeal ∧ ∀ x ∈ L, ∀ i, ∃ r : 𝓞 E, (s : E) * σ ((X⁻¹ *ᵥ x) i) = r :=
  GlobalTheory.T.exists_common_denominator_conj_localCoords_lattice F E σ w hσ hden n L hL X hX

theorem dual_bound (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (w : HeightOneSpectrum (𝓞 E))
    (hdual : ∀ y, y ∈ L ↔ ∀ x ∈ L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * form σ J y x)))
    (X : Matrix (Fin n) (Fin n) E) (hX : IsUnit X.det) (hG : IsUnit (Xᵀ * J * X.map σ).det)
    (hXc : ∀ x ∈ L, ∀ i, w.valuation E ((X⁻¹ *ᵥ x) i) ≤ 1)
    (s : 𝓞 E) (hs : s ∉ w.asIdeal) (hsr : ∀ x ∈ L, ∀ i, ∃ r : 𝓞 E, (s : E) * σ ((X⁻¹ *ᵥ x) i) = r)
    (e : E) (he : ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) :
    ∀ i k, w.valuation E (e * (Xᵀ * J * X.map σ)⁻¹ i k) ≤ 1 :=
  GlobalTheory.T.selfDualLattice_inverseGram_localBasis_integral F E σ n J L w hdual X hX hG hXc s hs hsr e he

theorem val_det_le (w : HeightOneSpectrum (𝓞 E)) {n : ℕ} (M : Matrix (Fin n) (Fin n) E)
    (c : WithZero (Multiplicative ℤ)) (h : ∀ i j, w.valuation E (M i j) ≤ c) :
    w.valuation E M.det ≤ c ^ n := by
  rw [Matrix.det_apply]
  refine Valuation.map_sum_le _ fun p _ => ?_
  have hp : w.valuation E (∏ i, M (p i) i) ≤ c ^ n := by
    rw [map_prod]
    calc ∏ i, w.valuation E (M (p i) i) ≤ ∏ _i : Fin n, c := Finset.prod_le_prod' fun i _ => h _ _
      _ = c ^ n := by simp
  rcases Int.units_eq_one_or (Equiv.Perm.sign p) with h1 | h1 <;> rw [h1]
  · rwa [one_smul]
  · rwa [Units.neg_smul, one_smul, Valuation.map_neg]

end GlobalTheory.SkewDetParity

namespace GlobalTheory.SkewDetParity

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem form_cols (σ : E →ₐ[F] E) {n : ℕ} (J X : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    (Xᵀ * J * X.map σ) i j = form σ J (fun k => X k i) (fun k => X k j) := by
  simp only [form, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, dotProduct, Matrix.mulVec,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem parity_at (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (hin : Formalism.UG.IsInertAt F E v w) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (hL : L.IsLattice E)
    (hdual : ∀ y, y ∈ L ↔ ∀ x ∈ L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * form σ J y x)))
    (hn : Even n) (hJ : J.det ≠ 0) : ∃ a : E, a ≠ 0 ∧ w.valuation E J.det = w.valuation E a ^ 2 := by
  obtain ⟨e, he0, heD, hemax⟩ := exists_max_dual w
  obtain ⟨X, hXu, hXL, hXc⟩ := exists_local_basis w n L hL
  obtain ⟨s, hs, hsr⟩ := exists_common_den σ w (val_sigma σ v w hin) (exists_den w) n L hL.fg X hXc
  have hσdet : σ X.det = (X.map σ).det := by
    rw [AlgHom.map_det]; rfl
  have hdetG : (Xᵀ * J * X.map σ).det = X.det * J.det * σ X.det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hσdet]
  have hX0 : X.det ≠ 0 := hXu.ne_zero
  have hσX0 : σ X.det ≠ 0 := by
    intro h0; apply hX0; exact (map_eq_zero_iff σ σ.toRingHom.injective).1 h0
  have hG0 : (Xᵀ * J * X.map σ).det ≠ 0 := by
    rw [hdetG]; exact mul_ne_zero (mul_ne_zero hX0 hJ) hσX0
  have hGu : IsUnit (Xᵀ * J * X.map σ).det := isUnit_iff_ne_zero.2 hG0
  have hGij : ∀ i j, w.valuation E ((Xᵀ * J * X.map σ) i j) ≤ w.valuation E e := fun i j => by
    rw [form_cols]
    exact hemax _ fun o => (hdual _).1 (hXL i) _ (hXL j) o
  have hup := val_det_le w _ _ hGij
  have hinv := dual_bound σ n J L w hdual X hXu hGu hXc s hs hsr e heD
  have hlow := val_det_le w (e • (Xᵀ * J * X.map σ)⁻¹) 1 (fun i k => by
    simpa [Matrix.smul_apply] using hinv i k)
  rw [one_pow, Matrix.det_smul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', Fintype.card_fin, map_mul,
    map_pow, map_inv₀] at hlow
  have hvG0 : w.valuation E (Xᵀ * J * X.map σ).det ≠ 0 := (Valuation.ne_zero_iff _).2 hG0
  have hlow' : w.valuation E e ^ n ≤ w.valuation E (Xᵀ * J * X.map σ).det := by
    first
      | rwa [mul_inv_le_iff₀ hvG0, one_mul] at hlow
      | rwa [mul_inv_le_iff₀ (zero_lt_iff.2 hvG0), one_mul] at hlow
  have hEq : w.valuation E (Xᵀ * J * X.map σ).det = w.valuation E e ^ n := le_antisymm hup hlow'
  rw [hdetG, map_mul, map_mul, val_sigma σ v w hin] at hEq
  obtain ⟨m, rfl⟩ := hn
  refine ⟨e ^ m / X.det, div_ne_zero (pow_ne_zero _ he0) hX0, ?_⟩
  have hvX0 : w.valuation E X.det ≠ 0 := (Valuation.ne_zero_iff _).2 hX0
  rw [map_div₀, map_pow, div_pow, ← pow_mul, mul_two, ← hEq]
  field_simp

theorem sigma_sigma (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

theorem det_eq_unit_mul_norm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n r s : ℕ) (W : Spc F E n), W.IsSkew σ B r s → Even n →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → IsField (Fv F v ⊗[F] E) →
    ∃ (y : Fv F v ⊗[F] E) (u : Fv F v), Valued.v u = 1 ∧
      (1 : Fv F v) ⊗ₜ[F] W.J.det = algebraMap (Fv F v) (Fv F v ⊗[F] E) u *
        (y * Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ y) := by
  intro F E _ _ _ _ _ σ B hB n r s W hW hn v w hin _
  by_cases hJ : W.J.det = 0
  · exact ⟨0, 1, map_one _, by simp [hJ]⟩
  obtain ⟨a, ha0, hva⟩ := parity_at σ v w hin n W.J W.L hW.lat hW.dual hn hJ
  have hmap : W.J.map σ = -W.Jᵀ := by
    ext i j
    simp only [Matrix.map_apply, Matrix.neg_apply, Matrix.transpose_apply]
    rw [← hW.skew j i]
  have hfix : σ W.J.det = W.J.det := by
    rw [AlgHom.map_det]
    change (W.J.map σ).det = _
    rw [hmap, Matrix.det_neg, Matrix.det_transpose, Fintype.card_fin, hn.neg_one_pow, one_mul]
  obtain ⟨c, hc⟩ := GlobalTheory.HermLineZeros.exists_of_fixed hB.cm _ hfix
  have hfixN : σ (a * σ a) = a * σ a := by
    rw [map_mul, sigma_sigma σ hB.cm, mul_comm]
  obtain ⟨β, hβ⟩ := GlobalTheory.HermLineZeros.exists_of_fixed hB.cm _ hfixN
  have hσa0 : σ a ≠ 0 := by
    intro h0; apply ha0; exact (map_eq_zero_iff σ σ.toRingHom.injective).1 h0
  have hβ0 : β ≠ 0 := by
    intro h0; rw [h0, map_zero] at hβ; exact mul_ne_zero ha0 hσa0 hβ.symm
  refine ⟨(1 : Fv F v) ⊗ₜ[F] a, algebraMap F (Fv F v) (c / β), ?_, ?_⟩
  · rw [show Valued.v (algebraMap F (Fv F v) (c / β)) = v.valuation F (c / β) from
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (c / β), ← val_algebraMap v w hin, map_div₀, map_div₀, hc, hβ,
      map_mul, val_sigma σ v w hin, hva, sq]
    have : w.valuation E a ≠ 0 := (Valuation.ne_zero_iff _).2 ha0
    exact div_self (mul_ne_zero this this)
  · have key : (algebraMap F (Fv F v) (c / β)) ⊗ₜ[F] (algebraMap F E β) = (1 : Fv F v) ⊗ₜ[F] W.J.det := by
      rw [Algebra.algebraMap_eq_smul_one (c / β), TensorProduct.smul_tmul, Algebra.smul_def, ← map_mul,
        div_mul_cancel₀ _ hβ0, hc]
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hβ,
      Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← key]
    simp

end GlobalTheory.SkewDetParity
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanCharacterTranslatesCoinvariant
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.PRep

namespace GlobalTheory.RankFibre

def stabSub {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (v : V) :
    Subgroup G where
  carrier := {g | ρ g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
    rw [hh, hg]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← hg]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem of_parts (Lirr : (GlobalTheory.Published.BernsteinUnitaryProductIrreducible → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → GlobalTheory.SmGL.IsSmoothChar β → GlobalTheory.SmGL.IsUnitaryChar β → ∀ M : Submodule ℂ (GL (Fin (a + b)) k → ℂ), M ≤ GlobalTheory.RankFibre.indScal ν β a b → (∀ f ∈ M, ∀ h : GL (Fin (a + b)) k, (fun x => f (x * h)) ∈ M) → M = ⊥ ∨ GlobalTheory.RankFibre.indScal ν β a b ≤ M)) (Llaw : (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν β : kˣ →* ℂˣ) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ), GlobalTheory.RankFibre.fibre ν β a b Φ ∈ GlobalTheory.PRep.indSpace (GlobalTheory.SmGL.parab k (GlobalTheory.RankFibre.blocks a b)) (GlobalTheory.SmGL.ofChar (GlobalTheory.RankFibre.parChar ν β a b)))) (Lsmooth : (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar β → ∀ Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k), IsOpen {h : GL (Fin d) k | GlobalTheory.SplitFlip.omA ν β 1 h Φ = Φ})) (Linteg : (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → ∀ Φ ∈ GlobalTheory.RankFibre.fullRankSB k a (a + b), MeasureTheory.Integrable (fun g : GL (Fin a) k => Φ (g.val * GlobalTheory.SplitFlip.X0 k finSumFinEquiv) * (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (((a + b : ℕ) : ℂ) / 2)) (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))))) (Lker : (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsSmoothChar β → ∀ Φ ∈ GlobalTheory.RankFibre.fullRankSB k a (a + b), GlobalTheory.RankFibre.fibre ν β a b Φ = 0 → Φ ∈ GlobalTheory.RankFibre.coinv ν β a (a + b))) : GlobalTheory.Published.BernsteinUnitaryProductIrreducible →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ), a ≤ d →
    ∀ (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → GlobalTheory.SmGL.IsSmoothChar β → GlobalTheory.SmGL.IsUnitaryChar β →
    ∀ N : Submodule ℂ (Matrix (Fin a) (Fin d) k → ℂ),
      Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
        Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) ∧ z = GlobalTheory.SplitFlip.omA ν β g 1 Ψ - Ψ} ≤ N →
      N ≤ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) →
      (∀ (h : GL (Fin d) k), ∀ Ψ ∈ N, GlobalTheory.SplitFlip.omA ν β 1 h Ψ ∈ N) →
      (∀ Ψ ∈ N, (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Ψ Y = 0) →
          Ψ ∈ Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
            Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) ∧ z = GlobalTheory.SplitFlip.omA ν β g 1 Ψ - Ψ}) ∨
      (∀ Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k), (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Ψ Y = 0) → Ψ ∈ N) := by
  intro HB k _ _ _ _ a d had ν β hνs hνu hβs hβu N hCN hNSB hNst
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le had
  borelize k

  have hS0 : ∀ (h : GL (Fin (a + b)) k) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ),
      Φ ∈ fullRankSB k a (a + b) → omA ν β 1 h Φ ∈ fullRankSB k a (a + b) := by
    intro h Φ hΦ
    refine ⟨omA_mem_SB ν β 1 h hΦ.1, fun Y hY => ?_⟩
    have hr : (((1 : GL (Fin a) k)⁻¹).val * Y * (invT h).val).rank ≠ a := by
      rwa [inv_one, Units.val_one, Matrix.one_mul,
        Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units (invT h))]
    simp only [omA, hΦ.2 _ hr, mul_zero]

  have hint : ∀ Φ ∈ fullRankSB k a (a + b), ∀ x : GL (Fin (a + b)) k,
      Integrable (fun g : GL (Fin a) k => omA ν β 1 x Φ (g.val * X0 k finSumFinEquiv) * (ν (gdet g) : ℂ) *
        apow (gdet g) (((a + b : ℕ) : ℂ) / 2)) (haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) :=
    fun Φ hΦ x => Linteg k a b ν hνs _ (hS0 x Φ hΦ)
  have hadd : ∀ Φ ∈ fullRankSB k a (a + b), ∀ Ψ ∈ fullRankSB k a (a + b),
      fibre ν β a b (Φ + Ψ) = fibre ν β a b Φ + fibre ν β a b Ψ := by
    intro Φ hΦ Ψ hΨ
    funext x
    rw [Pi.add_apply]
    unfold fibre
    rw [← integral_add (hint Φ hΦ x) (hint Ψ hΨ x)]
    congr 1
    funext g
    simp only [omA, Pi.add_apply]
    ring
  have hsmul : ∀ (c : ℂ) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ),
      fibre ν β a b (c • Φ) = c • fibre ν β a b Φ := by
    intro c Φ
    funext x
    rw [Pi.smul_apply, smul_eq_mul]
    unfold fibre
    rw [← integral_const_mul]
    congr 1
    funext g
    simp only [omA, Pi.smul_apply, smul_eq_mul]
    ring
  have hzero : fibre ν β a b 0 = 0 := by
    funext x
    simp [fibre, omA]

  let M : Submodule ℂ (GL (Fin (a + b)) k → ℂ) :=
    { carrier := {f | ∃ Ψ ∈ N, Ψ ∈ fullRankSB k a (a + b) ∧ fibre ν β a b Ψ = f}
      zero_mem' := ⟨0, N.zero_mem, (fullRankSB k a (a + b)).zero_mem, hzero⟩
      add_mem' := by
        rintro _ _ ⟨Φ, h1, h2, rfl⟩ ⟨Ψ, h3, h4, rfl⟩
        exact ⟨Φ + Ψ, N.add_mem h1 h3, (fullRankSB k a (a + b)).add_mem h2 h4, hadd Φ h2 Ψ h4⟩
      smul_mem' := by
        rintro c _ ⟨Φ, h1, h2, rfl⟩
        exact ⟨c • Φ, N.smul_mem c h1, (fullRankSB k a (a + b)).smul_mem c h2, hsmul c Φ⟩ }
  have hind : ∀ Ψ ∈ fullRankSB k a (a + b), fibre ν β a b Ψ ∈ indScal ν β a b := by
    intro Ψ hΨ
    refine ⟨?_, Llaw k a b ν β Ψ⟩
    have hle : stabSub ((repA ν β).comp (MonoidHom.inr (GL (Fin a) k) (GL (Fin (a + b)) k))) Ψ ≤
        stabSub (rightReg ℂ (GL (Fin (a + b)) k) ℂ) (fibre ν β a b Ψ) := by
      intro h hh
      have hh' : omA ν β 1 h Ψ = Ψ := hh
      show rightReg ℂ (GL (Fin (a + b)) k) ℂ h (fibre ν β a b Ψ) = fibre ν β a b Ψ
      funext x
      show fibre ν β a b Ψ (x * h) = fibre ν β a b Ψ x
      rw [← fibre_omA, hh']
    exact Subgroup.isOpen_mono hle (Lsmooth k a (a + b) ν β hβs Ψ hΨ.1)
  have hMle : M ≤ indScal ν β a b := by
    rintro _ ⟨Ψ, -, hΨ, rfl⟩
    exact hind Ψ hΨ
  have hMst : ∀ f ∈ M, ∀ h : GL (Fin (a + b)) k, (fun x => f (x * h)) ∈ M := by
    rintro _ ⟨Ψ, h1, h2, rfl⟩ h
    exact ⟨omA ν β 1 h Ψ, hNst h Ψ h1, hS0 h Ψ h2, funext fun x => fibre_omA ν β a b h Ψ x⟩
  rcases Lirr HB k a b ν β hνs hνu hβs hβu M hMle hMst with h0 | hT
  · left
    intro Ψ hΨN hΨr
    have hΨ : Ψ ∈ fullRankSB k a (a + b) := ⟨hNSB hΨN, hΨr⟩
    have hm : fibre ν β a b Ψ ∈ M := ⟨Ψ, hΨN, hΨ, rfl⟩
    rw [h0, Submodule.mem_bot] at hm
    exact Lker k a b ν β hνs hβs Ψ hΨ hm
  · right
    intro Φ hΦ hΦr
    have hΦS : Φ ∈ fullRankSB k a (a + b) := ⟨hΦ, hΦr⟩
    obtain ⟨Ψ, hΨN, hΨS, hZ⟩ := hT (hind Φ hΦS)
    have hd : Φ - Ψ ∈ coinv ν β a (a + b) := by
      refine Lker k a b ν β hνs hβs _ ((fullRankSB k a (a + b)).sub_mem hΦS hΨS) ?_
      rw [sub_eq_add_neg, ← neg_one_smul ℂ Ψ, hadd Φ hΦS _ ((fullRankSB k a (a + b)).smul_mem _ hΨS),
        hsmul, hZ]
      simp
    have := N.add_mem (hCN hd) hΨN
    simpa using this

theorem coinv_or_fullRank_le : GlobalTheory.Published.BernsteinUnitaryProductIrreducible →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ), a ≤ d →
    ∀ (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → GlobalTheory.SmGL.IsSmoothChar β → GlobalTheory.SmGL.IsUnitaryChar β →
    ∀ N : Submodule ℂ (Matrix (Fin a) (Fin d) k → ℂ),
      Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
        Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) ∧ z = GlobalTheory.SplitFlip.omA ν β g 1 Ψ - Ψ} ≤ N →
      N ≤ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) →
      (∀ (h : GL (Fin d) k), ∀ Ψ ∈ N, GlobalTheory.SplitFlip.omA ν β 1 h Ψ ∈ N) →
      (∀ Ψ ∈ N, (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Ψ Y = 0) →
          Ψ ∈ Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
            Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) ∧ z = GlobalTheory.SplitFlip.omA ν β g 1 Ψ - Ψ}) ∨
      (∀ Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k), (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Ψ Y = 0) → Ψ ∈ N) :=
  of_parts GlobalTheory.T.induced_scalar_irreducible GlobalTheory.T.fibre_mem_induced_space GlobalTheory.T.isOpen_stabilizer_schwartzBruhat GlobalTheory.T.integrable_full_rank_fibre GlobalTheory.T.fibre_zero_mem_coinvariants

end GlobalTheory.RankFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTransgressionDensitiesPartitionUnityEqZeroStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_transgression_densities_partition_unity_eq_zero : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), ∀ {ι : Type} [Fintype ι] (ρ : ι → CxPts X.str σ → ℝ), (∀ i y, CInfAt (ρ i) y) → (∀ y, ∑ i, ρ i y = 1) → ∀ (c : AlgChart X.str σ X.dim) (y : CxPts X.str σ), y ∈ c.e.source → ∑ i, corrDens E H₀ H (ρ i) c y = 0 := by
  first | exact @GlobalTheory.GoodTop.sum_corrDens_eq_zero | exact GlobalTheory.GoodTop.sum_corrDens_eq_zero | (intros; apply GlobalTheory.GoodTop.sum_corrDens_eq_zero <;> assumption)
end

