import Mathlib
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0183
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0030
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0011
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralWittTheoremAlmostAllPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0203
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0178
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0204
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0202
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0014

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerGaussianVectorsFockSpace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc Matrix
open scoped ComplexOrder

namespace GlobalTheory.GaussInner

theorem pairing_mul_eq_exp {σ : Type} [Fintype σ] [DecidableEq σ] (S T : Matrix σ σ ℂ) (x y : σ → ℂ)
    (E E' : MvPowerSeries σ ℂ) (hS : Sᵀ = S) (hT : Tᵀ = T)
    (hE : Summable (fun α : σ →₀ ℕ => (GlobalTheory.FockSeq.mfact α : ℝ) * ‖MvPowerSeries.coeff α E‖ ^ 2))
    (hE' : Summable (fun α : σ →₀ ℕ => (GlobalTheory.FockSeq.mfact α : ℝ) * ‖MvPowerSeries.coeff α E'‖ ^ 2))
    (h0 : MvPowerSeries.coeff 0 E = 1) (h0' : MvPowerSeries.coeff 0 E' = 1)
    (hd : ∀ l α, ((α l : ℂ) + 1) * MvPowerSeries.coeff (α + Finsupp.single l 1) E =
      MvPowerSeries.coeff α (x l • E + ∑ k, S l k • (MvPowerSeries.X k * E)))
    (hd' : ∀ l α, ((α l : ℂ) + 1) * MvPowerSeries.coeff (α + Finsupp.single l 1) E' =
      MvPowerSeries.coeff α (y l • E' + ∑ k, T l k • (MvPowerSeries.X k * E')))
    (D : ℝ → ℂ) (hD0 : D 0 = 1)
    (hD : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsUnit (1 - ((t : ℂ) ^ 2) • (T * S)).det ∧
      HasDerivAt D (-((t : ℂ) * (T * S * (1 - ((t : ℂ) ^ 2) • (T * S))⁻¹).trace) * D t) t) :
    (∑' α : σ →₀ ℕ, (GlobalTheory.FockSeq.mfact α : ℂ) * MvPowerSeries.coeff α E * MvPowerSeries.coeff α E') * D 1 =
      Complex.exp (1 / 2 * (x ⬝ᵥ (1 - T * S)⁻¹ *ᵥ (y + T *ᵥ x) +
        y ⬝ᵥ (x + S *ᵥ ((1 - T * S)⁻¹ *ᵥ (y + T *ᵥ x))))) := by
  obtain ⟨hc, hm⟩ := moments σ S T x y E E' hE hE' hd hd'
  set f : ℝ → ℂ := fun s => ∑' α : σ →₀ ℕ, (s : ℂ) ^ α.degree *
    ((GlobalTheory.FockSeq.mfact α : ℂ) * MvPowerSeries.coeff α E * MvPowerSeries.coeff α E') with hf
  set w : ℝ → σ → ℂ := fun s => (1 - ((s : ℂ) ^ 2) • (T * S))⁻¹ *ᵥ (y + (s : ℂ) • T *ᵥ x) with hw
  set u : ℝ → σ → ℂ := fun s => x + (s : ℂ) • S *ᵥ w s with hu
  set Φ : ℝ → ℂ := fun s => (s : ℂ) / 2 * (x ⬝ᵥ w s + y ⬝ᵥ u s) with hΦ
  have hΦ' : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Φ (u t ⬝ᵥ w t) t := fun t ht =>
    GlobalTheory.Mem.GaussPhase.hasDerivAt_phase σ S T x y t hS hT (hD t ht).1
  have hg : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun s => f s * D s * Complex.exp (-Φ s)) 0 t := by
    intro t ht
    have ht' := Set.Ioo_subset_Icc_self ht
    obtain ⟨p, q, m, n, h1, h2, h3, h4, h5⟩ := hm t ht
    have h6 := GlobalTheory.gaussian_pairing_moment_algebra σ S T x y t (f t) p q m n hS hT (hD t ht').1 h1 h2 h3 h4
    change _ = f t * (u t ⬝ᵥ w t + _) at h6
    rw [h6] at h5
    refine ((h5.fun_mul (hD t ht').2).fun_mul (hΦ' t ht').fun_neg.cexp).congr_deriv ?_
    ring
  have hgc : ContinuousOn (fun s => f s * D s * Complex.exp (-Φ s)) (Set.Icc 0 1) :=
    (hc.mul fun t ht => (hD t ht).2.continuousAt.continuousWithinAt).mul
      fun t ht => (hΦ' t ht).fun_neg.cexp.continuousAt.continuousWithinAt
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hgc hg
    intervalIntegrable_const
  have f0 : f 0 = 1 := by
    simp only [hf]
    rw [tsum_eq_single 0]
    · simp [h0, h0', GlobalTheory.FockSeq.mfact]
    · intro α hα
      have : α.degree ≠ 0 := fun h => hα ((Finsupp.degree_eq_zero_iff α).1 h)
      simp [this]
  have Φ0 : Φ 0 = 0 := by simp [hΦ]
  rw [f0, hD0, Φ0, intervalIntegral.integral_zero, Complex.exp_neg] at key
  have e : f 1 * D 1 = Complex.exp (Φ 1) := by
    have := Complex.exp_ne_zero (Φ 1)
    simp only [neg_zero, Complex.exp_zero, mul_one] at key
    field_simp at key
    linear_combination -key
  simpa [hf, hΦ, hu, hw] using e

theorem deriv_gauss {P Q : ℕ} (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) (l : Ix P Q) (α : Ix P Q →₀ ℕ) :
    ((α l : ℂ) + 1) * MvPowerSeries.coeff (α + Finsupp.single l 1) (expPS (gaussPoly A x)) =
      MvPowerSeries.coeff α (x l • expPS (gaussPoly A x) +
        ∑ k, fromBlocks 0 A Aᵀ 0 l k • (MvPowerSeries.X k * expPS (gaussPoly A x))) := by
  rw [GlobalTheory.OscExpDeriv.coeff_deriv_expPS _ _ (coeff_zero_gaussPoly A x)]
  congr 1
  rcases l with i | j
  · rw [GlobalTheory.OscGauss.pderiv_inl_gaussPoly, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_add, map_sum]
    simp [Fintype.sum_sum_type, add_mul, Finset.sum_mul, MvPowerSeries.smul_eq_C_mul, mul_assoc]
  · rw [GlobalTheory.OscGauss.pderiv_inr_gaussPoly, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_add, map_sum]
    simp [Fintype.sum_sum_type, add_mul, Finset.sum_mul, MvPowerSeries.smul_eq_C_mul, mul_assoc]

theorem posDef_smul {P Q : ℕ} {B : Matrix (Fin P) (Fin Q) ℂ} (hB : (1 - Bᴴ * B).PosDef) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : (1 - (((t : ℂ) ^ 2) • B)ᴴ * (((t : ℂ) ^ 2) • B)).PosDef := by
  have h4 : (0 : ℂ) ≤ ((1 - t ^ 4 : ℝ) : ℂ) :=
    Complex.zero_le_real.2 (sub_nonneg.2 (pow_le_one₀ ht.1 ht.2))
  have e : 1 - (((t : ℂ) ^ 2) • B)ᴴ * (((t : ℂ) ^ 2) • B) = (1 - Bᴴ * B) + ((1 - t ^ 4 : ℝ) : ℂ) • (Bᴴ * B) := by
    rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have : star ((t : ℂ) ^ 2) * (t : ℂ) ^ 2 = (t : ℂ) ^ 4 := by simp; ring
    rw [this]; push_cast; module
  rw [e]
  exact hB.add_posSemidef ((posSemidef_conjTranspose_mul_self B).smul h4)

theorem inner_gauss_gauss : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (A B : Matrix (Fin P) (Fin Q) ℂ) (x y : Ix P Q → ℂ), (1 - Aᴴ * A).PosDef → (1 - Bᴴ * B).PosDef → ∀ v w : F.H, HasCoeff F v (expPS (gaussPoly A x)) → HasCoeff F w (expPS (gaussPoly B y)) → let a : Fin P → ℂ := fun i => star (x (Sum.inl i)); let b : Fin Q → ℂ := fun j => star (x (Sum.inr j)); let c : Fin P → ℂ := fun i => y (Sum.inl i); let d : Fin Q → ℂ := fun j => y (Sum.inr j); let M := (1 - B * Aᴴ)⁻¹; let N := (1 - Aᴴ * B)⁻¹; inner ℂ v w = ((1 - Aᴴ * B).det)⁻¹ * Complex.exp (a ⬝ᵥ M *ᵥ c + d ⬝ᵥ N *ᵥ b + a ⬝ᵥ (M * B) *ᵥ b + d ⬝ᵥ (N * Aᴴ) *ᵥ c) := by
  intro P Q F A B x y hA hB v w hv hw a b c d M N
  obtain ⟨s1, hin⟩ := GlobalTheory.FockParseval.parseval _ F v w _ _ hv hw
  obtain ⟨s2, -⟩ := GlobalTheory.FockParseval.parseval _ F w w _ _ hw hw
  have hU : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsUnit (1 - ((t : ℂ) ^ 2) • (Aᴴ * B)).det := fun t ht => by
    simpa only [Matrix.mul_smul] using
      GlobalTheory.isUnit_det_one_sub_conjTranspose_mul_of_contractions P Q A _ hA (posDef_smul hB ht)
  have hU1 : IsUnit (1 - Aᴴ * B).det := by simpa using hU 1 ⟨zero_le_one, le_rfl⟩
  have hy : y = Sum.elim c d := by ext (i | j) <;> rfl
  have key := pairing_mul_eq_exp (fromBlocks 0 Aᴴᵀ Aᴴ 0) (fromBlocks 0 B Bᵀ 0) (Sum.elim a b) y
    (MvPowerSeries.map (starRingEnd ℂ) (expPS (gaussPoly A x))) (expPS (gaussPoly B y))
    (by simp [fromBlocks_transpose]) (by simp [fromBlocks_transpose]) (by simpa using s1) s2
    (by rw [MvPowerSeries.coeff_map]; simp [expPS, MvPowerSeries.coeff_apply]) (by simp [expPS, MvPowerSeries.coeff_apply])
    (fun l α => by
      have := congrArg (starRingEnd ℂ) (deriv_gauss A x l α)
      rw [← MvPowerSeries.coeff_map (f := starRingEnd ℂ) (n := α)] at this
      rcases l with i | j <;>
        simpa [MvPowerSeries.smul_eq_C_mul, Fintype.sum_sum_type, a, b] using this)
    (deriv_gauss B y) (fun s : ℝ => (1 - ((s : ℂ) ^ 2) • (Aᴴ * B)).det) (by simp)
    (fun t ht => GlobalTheory.FockDetDer.hasDerivAt_det_one_sub_sq P Q A B t (hU t ht))
  have hb := GlobalTheory.gaussian_phase_critical_value_blocks P Q A B a c b d hU1
  simp only [← hy] at hb
  rw [hb] at key
  simp only [MvPowerSeries.coeff_map, Complex.ofReal_one, one_pow, one_smul] at key
  rw [hin, ← key, mul_comm, mul_assoc, mul_inv_cancel₀ hU1.ne_zero, mul_one]

end GlobalTheory.GaussInner
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralWittTheoremAlmostAllPlacesStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_witt_theorem_almost_all_places : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (β : F), IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ y ∈ latV (M := M) (n := 1) b v, qR (Fv F v) σ J (y 0) = algebraMap F (Fv F v) β → ∃ g : HA (Fv F v) σ J, g • ratTup (F := F) (Fv F v) x = y ∧ ∀ i j, ((HA.mat (Fv F v) σ J g : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) i j ∈ intV b v ∧ ((HA.mat (Fv F v) σ J g⁻¹ : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) i j ∈ intV b v := by
  first | exact @GlobalTheory.WittIntegral.witt_integral | exact GlobalTheory.WittIntegral.witt_integral | (intros; apply GlobalTheory.WittIntegral.witt_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHCTypeUConj
section
noncomputable section

open Matrix Formalism.MainNotions.S

namespace GlobalTheory.CoefSpace.Conj

variable {k : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)}

theorem ujset_eq (k : ℕ) : UJset (allPos k) = (Matrix.unitaryGroup (Fin k) ℂ : Set _) :=
  GlobalTheory.RealPar.ujset_const true

theorem kset_eq (k : ℕ) : Formalism.REAL.Kset (allPos k) = (Matrix.unitaryGroup (Fin k) ℂ : Set _) :=
  (GlobalTheory.DefiniteCheck.kset_const k true).trans (ujset_eq k)

theorem conj_mem {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ Matrix.unitaryGroup (Fin k) ℂ) :
    g.map star ∈ Matrix.unitaryGroup (Fin k) ℂ :=
  Matrix.transpose_mem_unitaryGroup_iff.2 (Unitary.star_mem hg)

def tor (θ : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℂ := Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)

theorem tor_conj (θ : Fin k → ℝ) : (tor θ).map star = tor (-θ) := by
  rw [tor, Matrix.diagonal_map (star_zero ℂ)]
  congr 1
  funext a
  simp [← Complex.exp_conj]

theorem tor_mem (θ : Fin k → ℝ) : tor θ ∈ Matrix.unitaryGroup (Fin k) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, tor, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  simp [← Complex.exp_conj, ← Complex.exp_add]

theorem wt_iff (μ : Fin k → ℝ) (v : H) : IsWtOn (Formalism.REAL.Kset (allPos k)) π μ v ↔
    ∀ θ, π (tor θ) v = Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • v :=
  ⟨fun h θ => h θ (by rw [kset_eq]; exact tor_mem θ), fun h θ _ => h θ⟩

theorem wt_conj {μ : Fin k → ℝ} {v : H} :
    IsWtOn (Formalism.REAL.Kset (allPos k)) (fun g => π (g.map star)) μ v ↔ IsWtOn (Formalism.REAL.Kset (allPos k)) π (-μ) v := by
  simp only [wt_iff, tor_conj]
  refine ⟨fun h θ => ?_, fun h θ => ?_⟩
  · simpa using h (-θ)
  · simpa using h (-θ)

def revM (k : ℕ) : Matrix (Fin k) (Fin k) ℂ := (1 : Matrix (Fin k) (Fin k) ℂ).submatrix Fin.revPerm id

theorem revM_mem : revM k ∈ Matrix.unitaryGroup (Fin k) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, revM, Matrix.conjTranspose_submatrix,
    Matrix.conjTranspose_one, Matrix.submatrix_mul_equiv, Matrix.mul_one, Matrix.submatrix_id_id]

theorem tor_revM (θ : Fin k → ℝ) : tor θ * revM k = revM k * tor fun a => θ (Fin.rev a) := by
  ext a b
  simp only [tor, revM, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.submatrix_apply, Fin.revPerm_apply, id,
    Matrix.one_apply]
  split_ifs with h
  · subst h
    simp
  · simp

theorem wt_rev (hπ : IsURepOn (UJset (allPos k)) π) {μ : Fin k → ℝ} {v : H} (hv0 : v ≠ 0)
    (hv : IsWtOn (Formalism.REAL.Kset (allPos k)) π μ v) :
    π (revM k) v ≠ 0 ∧ IsWtOn (Formalism.REAL.Kset (allPos k)) π (fun a => μ (Fin.rev a)) (π (revM k) v) := by
  rw [ujset_eq] at hπ
  refine ⟨fun h => hv0 ?_, (wt_iff _ _).2 fun θ => ?_⟩
  · rw [← norm_eq_zero, ← hπ.2.1 _ revM_mem v, h, norm_zero]
  · have e : ∑ a, μ a * θ (Fin.rev a) = ∑ a, μ (Fin.rev a) * θ a := by
      rw [← Equiv.sum_comp Fin.revPerm]
      simp
    rw [← ContinuousLinearMap.comp_apply, ← hπ.1.2 _ (tor_mem θ) _ revM_mem, tor_revM,
      hπ.1.2 _ revM_mem _ (tor_mem _), ContinuousLinearMap.comp_apply, (wt_iff _ _).1 hv, map_smul, e]

theorem cdom_neg_rev {μ Λ : Fin k → ℝ} (h : CDom (allPos k) μ Λ) :
    CDom (allPos k) (fun a => -μ (Fin.rev a)) fun a => -Λ (Fin.rev a) := by
  obtain ⟨c, hc, e⟩ := h
  refine ⟨fun a b => c (Fin.rev b) (Fin.rev a), fun a b h => ⟨Fin.rev_lt_rev.1 (hc _ _ h).1, rfl⟩, ?_⟩
  funext x
  have h1 := congrFun e (Fin.rev x)
  rw [← Equiv.sum_comp Fin.revPerm] at h1
  simp only [← Equiv.sum_comp Fin.revPerm (fun b => (c _ b : ℝ) • Formalism.REAL.root _ b)] at h1
  rw [Finset.sum_comm] at h1
  simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, Formalism.REAL.root, Pi.single_apply, Fin.revPerm_apply,
    Fin.rev_inj, smul_eq_mul] at h1 ⊢
  rw [show -Λ x.rev - -μ x.rev = -(Λ x.rev - μ x.rev) by ring, h1, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun b _ => by ring

theorem isHCTypeU_conj {u : Fin k → ℝ} (h : IsHCTypeU k u π) :
    IsHCTypeU k (fun i => -u (Fin.rev i)) (fun g => π (g.map star)) := by
  obtain ⟨h1, h2, h3, h4, -, h5, ⟨v, -, hv0, hv⟩, h6⟩ := h
  have hl : Formalism.QuantumDeterminants.lowK (allPos k) (fun i => -u (Fin.rev i)) =
      fun a => -Formalism.QuantumDeterminants.lowK (allPos k) u (Fin.rev a) := by
    funext a
    unfold allPos
    rw [GlobalTheory.DefiniteCheck.lowK_const, GlobalTheory.DefiniteCheck.lowK_const, Fin.val_rev, Nat.cast_sub a.2]
    push_cast
    ring
  have h3' := h3
  rw [ujset_eq] at h3'
  refine ⟨h1, h2, ?_, h4, fun _ _ _ _ => trivial, fun S hS hst => h5 S hS fun g hg x hx => ?_,
    ⟨_, trivial, (wt_rev h3 hv0 hv).1, ?_⟩, fun μ x _ hx0 hx => ?_⟩
  · rw [ujset_eq]
    refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun g hg => h3'.2.1 _ (conj_mem hg), fun x => ?_⟩
    · beta_reduce
      rw [Matrix.map_one _ (star_zero ℂ) (star_one ℂ)]
      exact h3'.1.1
    · have : (a * b).map star = a.map star * b.map star := Matrix.map_mul (f := starRingEnd ℂ)
      beta_reduce
      rw [this]
      exact h3'.1.2 _ (conj_mem ha) _ (conj_mem hb)
    · exact (h3'.2.2 x).comp (continuous_id.matrix_map continuous_star).continuousOn fun g hg => conj_mem hg
  · rw [kset_eq] at hg
    have := hst (g.map star) (by rw [kset_eq]; exact conj_mem hg) x hx
    have e : (g.map star).map star = g := by
      ext a b
      simp
    simpa only [e] using this
  · rw [hl, wt_conj]
    convert (wt_rev h3 hv0 hv).2 using 1
    funext a
    simp
  · obtain ⟨a1, a2⟩ := wt_rev h3 hx0 (wt_conj.1 hx)
    rw [hl]
    convert cdom_neg_rev (h6 _ _ trivial a1 a2) using 1
    funext a
    simp

end GlobalTheory.CoefSpace.Conj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralOrthogonalComplementPairIndepGroupElemeStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_orthogonalComplement_pair_indep_groupElement : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R] (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (m' : Measure (Fin 1 → Fin M → R ⊗[F] E)), StepData σ J x a B J' → IsInvTup R σ J' m' → ∀ (y : Fin 1 → Fin (M + 1) → R ⊗[F] E) (g k : HA R σ J), g • ratTup (F := F) R x = k • ratTup (F := F) R x → ∀ f : (Fin 2 → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable f → ∫⁻ y', f (pairOf R σ J B y g y') ∂m' = ∫⁻ y', f (pairOf R σ J B y k y') ∂m' := by
  first | exact @GlobalTheory.TwoStepIndep.lintegral_pairOf_eq | exact GlobalTheory.TwoStepIndep.lintegral_pairOf_eq | (intros; apply GlobalTheory.TwoStepIndep.lintegral_pairOf_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeSmoothVectorsIsKStable
section
noncomputable section

open Matrix
open scoped ContDiff

namespace GlobalTheory.SmoothLowKStable

open Formalism.MainNotions.S GlobalTheory.GardingVec

theorem list_prod_conj {n : ℕ} {g h : Matrix (Fin n) (Fin n) ℂ} (hgh : g * h = 1)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) : l.prod * g = g * (l.map fun x => h * x * g).prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, Matrix.mul_assoc, ih]
    simp only [← Matrix.mul_assoc, hgh, Matrix.one_mul]

theorem smoothVec_apply {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hmul : ∀ g ∈ UJset ε, ∀ h ∈ UJset ε, σ (g * h) = σ g * σ h) {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P)
    (h : Pᴴ * Formalism.REAL.Jm ε * P = G) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ UJset ε) {v : H}
    (hv : Formalism.L2.Theta.SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) v) :
    Formalism.L2.Theta.SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) (σ k v) := by
  have hG : IsUnit G := by
    rw [← h]
    exact (((Matrix.isUnit_conjTranspose _).2 hP).mul
      (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε))).mul hP
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hd
  have hk' : kᴴ * Formalism.REAL.Jm ε * k = Formalism.REAL.Jm ε := hk
  set g := P⁻¹ * k * P with hg
  have hPg : P * g = k * P := by rw [hg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, Matrix.one_mul]
  have hgG : gᴴ * G * g = G := by
    calc gᴴ * G * g = (P * g)ᴴ * Formalism.REAL.Jm ε * (P * g) := by
          rw [← h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Pᴴ * (kᴴ * Formalism.REAL.Jm ε * k) * P := by rw [hPg]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = G := by rw [hk', h]
  have hgu : IsUnit g := by
    have : IsUnit (gᴴ * G * g).det := by rw [hgG]; exact (Matrix.isUnit_iff_isUnit_det G).1 hG
    rw [Matrix.det_mul] at this
    exact (Matrix.isUnit_iff_isUnit_det g).2 (isUnit_of_mul_isUnit_right this)
  have hgd : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hgu
  have hgg : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgd
  have hGg : G * g⁻¹ = gᴴ * G := by
    conv_lhs => rw [← hgG]
    rw [Matrix.mul_assoc, hgg, Matrix.mul_one]
  have hGg' : (g⁻¹)ᴴ * G = G * g := by
    conv_lhs => rw [← hgG]
    rw [Matrix.mul_assoc gᴴ, ← Matrix.mul_assoc, ← conjTranspose_mul, hgg, conjTranspose_one, Matrix.one_mul]
  intro m Xs hX
  have hY : ∀ i, (g⁻¹ * Xs i * g)ᴴ * G + G * (g⁻¹ * Xs i * g) = 0 := fun i => by
    have hXi : (Xs i)ᴴ * G + G * Xs i = 0 := hX i
    calc (g⁻¹ * Xs i * g)ᴴ * G + G * (g⁻¹ * Xs i * g)
        = gᴴ * (Xs i)ᴴ * ((g⁻¹)ᴴ * G) + (G * g⁻¹) * Xs i * g := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = gᴴ * ((Xs i)ᴴ * G + G * Xs i) * g := by
          rw [hGg, hGg']; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hXi]; simp
  have hs := hv m (fun i => g⁻¹ * Xs i * g) hY
  have hmem : ∀ (Ys : Fin m → Matrix (Fin n) (Fin n) ℂ), (∀ i, (Ys i)ᴴ * G + G * Ys i = 0) → ∀ t : Fin m → ℝ,
      P * (List.ofFn fun i => NormedSpace.exp (t i • Ys i)).prod * P⁻¹ ∈ UJset ε := fun Ys hYs t => by
    refine conj_mem hP h (list_prod_mem _ fun g hg => ?_)
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
    exact exp_mem hG (hYs i) _
  have key : ∀ t : Fin m → ℝ,
      σ (P * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * P⁻¹) (σ k v)
        = σ k (σ (P * (List.ofFn fun i => NormedSpace.exp (t i • (g⁻¹ * Xs i * g))).prod * P⁻¹) v) := fun t => by
    have e1 : (List.ofFn fun i => NormedSpace.exp (t i • (g⁻¹ * Xs i * g)))
        = (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).map fun x => g⁻¹ * x * g := by
      rw [List.map_ofFn]
      congr 1
      funext i
      rw [Function.comp_apply, ← Matrix.exp_conj' _ _ hgu, Matrix.mul_smul, Matrix.smul_mul]
    have e2 := list_prod_conj hgg (List.ofFn fun i => NormedSpace.exp (t i • Xs i))
    rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, ← hmul _ (hmem Xs hX t) _ hk,
      ← hmul _ hk _ (hmem _ hY t), e1]
    congr 2
    have e3 : P⁻¹ * k = g * P⁻¹ := by rw [hg, Matrix.mul_assoc _ P, hPP, Matrix.mul_one]
    rw [Matrix.mul_assoc _ P⁻¹, e3, ← Matrix.mul_assoc, Matrix.mul_assoc P, e2]
    simp only [← Matrix.mul_assoc, hPg]
  have := ((σ k).restrictScalars ℝ).contDiff.comp hs
  refine (funext key : _ = _) ▸ this

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.Datum Formalism.IndefR.FWT

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isKStableOn_lowKSub_inf_sm (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (τ : D.what₂.Tau) : IsKStableOn (M.ε τ) (M.σ τ) (lowKSub (M.ε τ) (M.lam τ) (M.σ τ) ⊓ M.sm τ) := by
  intro k hk w hw
  have hkU : k ∈ UJset (M.ε τ) := by
    show kᴴ * Formalism.REAL.Jm _ * k = Formalism.REAL.Jm _
    have h1 : kᴴ * k = 1 := (Matrix.mem_unitaryGroup_iff').1 hk.1
    rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  refine ⟨?_, ?_⟩
  · have : lowKSub (M.ε τ) (M.lam τ) (M.σ τ)
        ≤ (lowKSub (M.ε τ) (M.lam τ) (M.σ τ)).comap (M.σ τ k : _ →ₗ[ℂ] _) :=
      sSup_le fun T hT v hv => (le_sSup hT : T ≤ _) (hT.2.1 k hk v hv)
    exact this hw.1
  · have : M.sm τ ≤ (M.sm τ).comap (M.σ τ k : _ →ₗ[ℂ] _) :=
      Submodule.span_le.2 fun v hv => Submodule.subset_span
        (smoothVec_apply (M.ds τ).2.2.1.1.2 (M.fr_unit τ) (M.fr_gram τ) hkU hv)
    exact this hw.2

end GlobalTheory.SmoothLowKStable

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PostOnSumMemRange
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GoodProjLift

theorem exists_factor {U H X : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup H] [Module ℂ H]
    [AddCommGroup X] [Module ℂ X] (e : H →ₗ[ℂ] X) (he : Function.Injective e) (f : U →ₗ[ℂ] X)
    (hf : ∀ x, f x ∈ LinearMap.range e) : ∃ g : U →ₗ[ℂ] H, ∀ x, e (g x) = f x := by
  refine ⟨(LinearEquiv.ofInjective e he).symm.toLinearMap ∘ₗ f.codRestrict _ hf, fun x => ?_⟩
  have h := (LinearEquiv.ofInjective e he).apply_symm_apply (f.codRestrict _ hf x)
  exact congrArg Subtype.val h

theorem postOn_sum_smul {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {G : Type} [Fintype G]
    (c : G → ℂ) (L : G → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (T : MMap M) :
    postOn M (∑ g, c g • L g) T = ∑ g, c g • postOn M (L g) T := by
  ext v h
  simp [postOn_apply, LinearMap.sum_apply]

theorem postOn_sum_mem_range {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {G : Type} [Fintype G]
    {H : Type} [AddCommGroup H] [Module ℂ H] (e : H →ₗ[ℂ] MMap M)
    (c : G → ℂ) (L : G → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (a : G → H →ₗ[ℂ] H)
    (ha : ∀ g y, e (a g y) = postOn M (L g) (e y)) {T : MMap M} (hT : T ∈ LinearMap.range e) :
    postOn M (∑ g, c g • L g) T ∈ LinearMap.range e := by
  obtain ⟨y, rfl⟩ := hT
  refine ⟨∑ g, c g • a g y, ?_⟩
  rw [postOn_sum_smul, map_sum]
  exact Finset.sum_congr rfl fun g _ => by rw [map_smul, ha]

theorem is_inj {X : Type} [AddCommGroup X] [Module ℂ X] {M : HMod X} {V : Submodule ℂ X} {ip : X → X → ℂ}
    (h : M.Is V ip) : Function.Injective M.e := h.1

theorem is_range {X : Type} [AddCommGroup X] [Module ℂ X] {M : HMod X} {V : Submodule ℂ X} {ip : X → X → ℂ}
    (h : M.Is V ip) : LinearMap.range M.e = V := h.2.1

theorem exists_factor_hmod {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {G : Type} [Fintype G]
    {U : Type} [AddCommGroup U] [Module ℂ U] {H : HMod (MMap M)} {W : Submodule ℂ (MMap M)}
    {ip : MMap M → MMap M → ℂ} (hH : H.Is W ip)
    (c : G → ℂ) {L : G → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)} {a : G → H.H →ₗ[ℂ] H.H}
    (ha : ∀ g y, H.e (a g y) = postOn M (L g) (H.e y)) (f : U →ₗ[ℂ] MMap M) (hf : ∀ x, f x ∈ W) :
    ∃ th : U →ₗ[ℂ] H.H, ∀ x, H.e (th x) = postOn M (∑ g, c g • L g) (f x) :=
  exists_factor _ (is_inj hH) (postOn M (∑ g, c g • L g) ∘ₗ f) fun x =>
    postOn_sum_mem_range M H.e c L a ha (by rw [is_range hH]; exact hf x)

set_option maxHeartbeats 1000000 in

theorem exists_thG : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.thP_thF_mem → ∃ th, ({ R with thG := th } : RealDat D A Ks).thP_thG := by
  intro D G _ _ Pl0 T A Ks _ _ _ R _ _ hM hF
  have key : ∀ i t, ∃ th : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H,
      ∀ x, (R.HW i (sg0 D A)).e (th x) = postOn _ (R.eWf i (sg0 D A)) (R.thF i t x) := fun i t =>
    exists_factor_hmod (hM.HW i (sg0 D A)) (RealDat.eC (A := A) (sg0 D A)) (hM.gW i (sg0 D A)) (R.thF i t) (hF i t)
  choose th hth using key
  exact ⟨th, hth⟩

end GlobalTheory.GoodProjLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProductFormulaChangeSetsOutsideFiniteSetStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_formula_change_sets_outside_finite_set : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (ν : Measure (Fin n → Fin M → AF F ⊗[F] E)) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (S T S' : Finset (HeightOneSpectrum (𝓞 F))) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, v ∈ S' ↔ v ∈ S ∨ v ∈ T) → Disjoint S T → (∀ v, MeasurableSet (A v)) → (∀ v ∉ S', A v = latV b v) → (∀ (fi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (fv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable fi → (∀ v, Measurable (fv v)) → ∫⁻ X in {X | ∀ v ∉ S', projV v (projFin X) ∈ latV b v}, fi (projInf X) * ∏ v ∈ S', fv v (projV v (projFin X)) ∂ν = (∫⁻ Y, fi Y ∂mi) * (∏ v ∈ S', ∫⁻ Y, fv v Y ∂(mv v)) * tailProd b mv S') → ∀ (fi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (fv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable fi → (∀ v, Measurable (fv v)) → ∫⁻ X in {X | ∀ v ∉ S, projV v (projFin X) ∈ A v}, fi (projInf X) * ∏ v ∈ S, fv v (projV v (projFin X)) ∂ν = (∫⁻ Y, fi Y ∂mi) * (∏ v ∈ S, ∫⁻ Y, fv v Y ∂(mv v)) * ((∏ v ∈ T, mv v (A v)) * tailProd b mv S') := by
  first | exact @GlobalTheory.GaugeSetChange.product_formula_change_sets | exact GlobalTheory.GaugeSetChange.product_formula_change_sets | (intros; apply GlobalTheory.GaugeSetChange.product_formula_change_sets <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProductFormulaHaarModulusCmFieldElement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem algebraMap_eq_inclR_mul_sigR {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (R : Type) [CommRing R] [Algebra F R] (u : E) (k : F) (hk : algebraMap F E k = u * σ u) :
    algebraMap R (R ⊗[F] E) (algebraMap F R k) = inclR R u * sigR R σ (inclR R u) := by
  have h1 : sigR R σ (inclR R u) = inclR R (σ u) := by
    simp [sigR, inclR]
  rw [h1, ← map_mul, ← hk, ← IsScalarTower.algebraMap_apply]
  exact ((Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes k).symm

theorem prod_modu_inclR : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ u : E, u ≠ 0 → (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => modu (Fv F v ⊗[F] E) (inclR (Fv F v) u)).Finite ∧ modu (Ainf F ⊗[F] E) (inclR (Ainf F) u) * ∏ᶠ v : HeightOneSpectrum (𝓞 F), modu (Fv F v ⊗[F] E) (inclR (Fv F v) u) = 1 := by
  intro F E _ _ _ _ _ σ h u hu
  haveI := h.1
  obtain ⟨k, hk⟩ := GlobalTheory.HermLineZeros.exists_of_fixed h (u * σ u) (by
    rw [map_mul, GlobalTheory.HermLineZeros.conj_invol h, mul_comm])
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [map_zero] at hk
    exact mul_ne_zero hu ((map_ne_zero σ).2 hu) hk.symm
  have hv : ∀ v : HeightOneSpectrum (𝓞 F), modu (Fv F v ⊗[F] E) (inclR (Fv F v) u) =
      modu (Fv F v) (algebraMap F (Fv F v) k) := fun v =>
    (GlobalTheory.T.haarModulus_tensor_eq_modulus_norm F E σ h (Fv F v) _ _ (hu.isUnit.map _)
      (algebraMap_eq_inclR_mul_sigR σ _ u k hk)).2
  have hi : modu (Ainf F ⊗[F] E) (inclR (Ainf F) u) = modu (Ainf F) (algebraMap F (Ainf F) k) :=
    (GlobalTheory.T.haarModulus_tensor_eq_modulus_norm F E σ h (Ainf F) _ _ (hu.isUnit.map _)
      (algebraMap_eq_inclR_mul_sigR σ _ u k hk)).2
  simp only [hv, hi]
  exact GlobalTheory.T.haarModulus_product_formula_totallyReal F k hk0

end GlobalTheory.GaugeEx
end

