import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0010
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0100
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0101
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.RealPlaceAnalysis.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0103

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsSumEigenvaluesNoncompactPartLe
section
open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory.EigenPartialSum

theorem rank_add_le' {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  refine le_trans (Submodule.finrank_mono ?_)
    (Submodule.finrank_add_le_finrank_add_finrank (LinearMap.range A.mulVecLin)
      (LinearMap.range B.mulVecLin))
  rintro _ ⟨x, rfl⟩
  exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩

theorem rank_le_two_mul {n : ℕ} (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ)
    (h0 : ∀ a b, ε a = ε b → Y a b = 0) (c : Bool) :
    Y.rank ≤ 2 * (univ.filter fun a => ε a = c).card := by
  classical
  set P : Matrix (Fin n) (Fin n) ℂ := diagonal fun a => if ε a = c then 1 else 0 with hP
  have hY : Y = P * Y + Y * P := by
    ext a b
    simp only [hP, Matrix.add_apply, diagonal_mul, mul_diagonal]
    by_cases hab : ε a = ε b
    · simp [h0 a b hab]
    · by_cases ha : ε a = c
      · have hb : ¬ ε b = c := fun hb => hab (ha.trans hb.symm)
        simp [ha, hb]
      · have hb : ε b = c := by
          revert hab ha
          cases ε a <;> cases ε b <;> cases c <;> simp
        simp [ha, hb]
  have hr : P.rank = (univ.filter fun a => ε a = c).card := by
    rw [hP, rank_diagonal, Fintype.card_subtype]
    congr 1
    ext a
    simp
  calc Y.rank = (P * Y + Y * P).rank := by rw [← hY]
    _ ≤ (P * Y).rank + (Y * P).rank := rank_add_le' _ _
    _ ≤ P.rank + P.rank := add_le_add (rank_mul_le_left _ _) (rank_mul_le_right _ _)
    _ = _ := by rw [hr]; ring

theorem apply_eq_zero_of_inP {n : ℕ} {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ}
    (h : inP ε Y) (a b : Fin n) (hab : ε a = ε b) : Y a b = 0 := by
  have h1 := congrFun (congrFun h.2 a) b
  simp only [Jm, mul_diagonal, diagonal_mul, Matrix.neg_apply, hab] at h1
  cases hb : ε b <;> simp [hb] at h1
  · linear_combination (-1 / 2 : ℂ) * h1
  · linear_combination (1 / 2 : ℂ) * h1

theorem sum_sq_eigenvalues {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (hY : Y.IsHermitian) :
    ∑ j, hY.eigenvalues j ^ 2 = hs Y := by
  have h1 : (Y * Y).trace = ((∑ j, hY.eigenvalues j ^ 2 : ℝ) : ℂ) := by
    conv_lhs => rw [hY.spectral_theorem, ← map_mul]
    rw [Unitary.conjStarAlgAut_apply, trace_mul_cycle, Unitary.coe_star_mul_self, one_mul,
      diagonal_mul_diagonal, trace_diagonal]
    simp [sq]
  have h2 : (Y * Y).trace = ((hs Y : ℝ) : ℂ) := by
    simp only [trace, diag_apply, mul_apply, hs]
    push_cast
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [← hY.apply j i, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  exact_mod_cast h1.symm.trans h2

theorem abs_sum_eigenvalues_le : ∀ (n : ℕ) (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ)
    (hY : Y.IsHermitian), inP ε Y → ∀ J : Finset (Fin n), |∑ j ∈ J, hY.eigenvalues j| ≤
      Real.sqrt (2 * ((min (univ.filter fun a => ε a = true).card
        (univ.filter fun a => ε a = false).card : ℕ) : ℝ)) * Real.sqrt (hs Y) := by
  intro n ε Y hY hP J
  classical
  set q : ℕ := min (univ.filter fun a => ε a = true).card
    (univ.filter fun a => ε a = false).card with hq
  have hr : Y.rank ≤ 2 * q := by
    have h1 := rank_le_two_mul ε Y (apply_eq_zero_of_inP hP) true
    have h2 := rank_le_two_mul ε Y (apply_eq_zero_of_inP hP) false
    omega
  set S := J.filter fun j => hY.eigenvalues j ≠ 0 with hS
  have hc : S.card ≤ 2 * q := by
    refine le_trans ?_ hr
    rw [hY.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
    exact card_le_card (filter_subset_filter _ (subset_univ _))
  have hc' : (S.card : ℝ) ≤ 2 * (q : ℝ) := by exact_mod_cast hc
  have hsum : ∑ j ∈ J, hY.eigenvalues j = ∑ j ∈ S, hY.eigenvalues j :=
    (sum_filter_ne_zero J).symm
  have hsq : ∑ j ∈ S, hY.eigenvalues j ^ 2 ≤ hs Y := by
    rw [← sum_sq_eigenvalues Y hY]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => sq_nonneg _
  rw [hsum, ← Real.sqrt_mul (by positivity)]
  refine Real.abs_le_sqrt (le_trans sq_sum_le_card_mul_sum_sq ?_)
  exact mul_le_mul hc' hsq (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)

end GlobalTheory.EigenPartialSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdFormsOfEquivariant
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory

theorem adForms_of_equivariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (Γ Gi Gf : Type) [Group Γ] [Group Gi] [Group Gf] (ιi : Γ →* Gi) (ιf : Γ →* Gf) (K : Subgroup Gf) (ψ : K →* ℂˣ) (Φ : Gf ≃* UPts σ J (FiniteAdeleRing (𝓞 F) F)) (h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (ι : Type) [Fintype ι] (emb : ι → E →+* ℂ) (lam : ι → DomWeight n) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (π : Representation ℂ Gi W) (Jm : W →ₗ⋆[ℂ] (Frames (gramC J emb) → ℂ)), (∀ κ : K, ‖((ψ κ : ℂˣ) : ℂ)‖ = 1) → (∀ h : Gf, h ∈ K ↔ ((h0⁻¹ * Φ h * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ S.U) → (∀ (h : Gf) (hk : h ∈ K) (hy : ((h0⁻¹ * Φ h * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ S.U), ((ψ ⟨h, hk⟩ : ℂˣ) : ℂ) = ((S.chi ⟨_, hy⟩ : ℂˣ) : ℂ)) → (∀ g : GL (Fin n) E, g ∈ UJ (σ : E →+* E) J → ∃ γ : Γ, (Φ (ιf γ)).1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) g) → (∀ (γ : Γ) (g : GL (Fin n) E), (Φ (ιf γ)).1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) g → ∀ (ξ : W) (y y' : Frames (gramC J emb)), IsTr (atInf emb g.1) y' y → Jm (π (ιi γ) ξ) y = Jm ξ y') → (∀ ξ, Jm ξ ∈ ValC (gramC J emb) lam) → ∀ φ : Gf → W, (∀ (γ : Γ) (x : Gf) (κ : K), φ (ιf γ * x * κ) = (((ψ κ)⁻¹ : ℂˣ) : ℂ) • π (ιi γ) (φ x)) → (fun y : UPts σ J (FiniteAdeleRing (𝓞 F) F) => Jm (φ (Φ.symm (y * h0⁻¹)))) ∈ AdForms S emb lam := by
  intro F E _ _ _ _ _ σ n J T f bad S Γ Gi Gf _ _ _ ιi ιf K ψ Φ h0 ι _ emb lam W _ _ π Jm hψ hK hχ hΓ hJ hV φ hφ
  refine Submodule.mem_inf.2 ⟨?_, fun x _ => hV _⟩
  intro g hg x x' κ hx y y' hy
  obtain ⟨γ, hγ⟩ := hΓ g hg
  let κ' : UPts σ J (FiniteAdeleRing (𝓞 F) F) := ⟨κ.1, ((S.U_eq κ.1).1 κ.2).1⟩
  let k : Gf := Φ.symm (h0 * κ' * h0⁻¹)
  have hk1 : h0⁻¹ * Φ k * h0 = κ' := by
    simp only [k, MulEquiv.apply_symm_apply]; group
  have hy1 : ((h0⁻¹ * Φ k * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
      GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ S.U := by
    rw [hk1]; exact κ.2
  have hk : k ∈ K := (hK k).2 hy1
  have hc : ((ψ ⟨k, hk⟩ : ℂˣ) : ℂ) = ((S.chi κ : ℂˣ) : ℂ) := by
    rw [hχ k hk hy1]
    congr 2
    apply Subtype.ext
    show ((h0⁻¹ * Φ k * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
      GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) = κ.1
    rw [hk1]
  have hx' : x' = Φ (ιf γ) * x * κ' := by
    apply Subtype.ext
    rw [hx, ← hγ]; rfl
  have hdec : Φ.symm (x' * h0⁻¹) = ιf γ * Φ.symm (x * h0⁻¹) * ((⟨k, hk⟩ : K) : Gf) := by
    apply Φ.injective
    simp only [k, map_mul Φ, MulEquiv.apply_symm_apply, hx']
    group
  have hconj : (starRingEnd ℂ) (((ψ ⟨k, hk⟩)⁻¹ : ℂˣ) : ℂ) = ((ψ ⟨k, hk⟩ : ℂˣ) : ℂ) := by
    rw [Units.val_inv_eq_inv_val, Complex.inv_eq_conj (hψ _), Complex.conj_conj]
  show Jm (φ (Φ.symm (x' * h0⁻¹))) y = (S.chi κ : ℂ) * Jm (φ (Φ.symm (x * h0⁻¹))) y'
  rw [hdec, hφ, LinearMap.map_smulₛₗ, hconj, hc, Pi.smul_apply, smul_eq_mul, hJ γ g hγ _ y y' hy]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConjCoefficientsWeylModuleRowActNormFock
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

noncomputable section

namespace GlobalTheory.ConjCoeff

theorem conj_mem_delSq {n : ℕ} (lam : DomWeight n) {p : MvPolynomial (Fin n × Fin n) ℂ}
    (hp : p ∈ delSq ℂ n lam) : MvPolynomial.map (starRingEnd ℂ) p ∈ delSq ℂ n lam := by
  induction hp using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    refine Submodule.subset_span ⟨v, ?_⟩
    simp only
    rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul a y _ hy =>
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hy

theorem conj_rowAct {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (p : MvPolynomial (Fin n × Fin n) ℂ) :
    MvPolynomial.map (starRingEnd ℂ) (Formalism.GradedWeylDivisibility.rowAct ℂ g p) =
      Formalism.GradedWeylDivisibility.rowAct ℂ (g.map (starRingEnd ℂ)) (MvPolynomial.map (starRingEnd ℂ) p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h : ∀ (h : Matrix (Fin n) (Fin n) ℂ) (b : ℂ), Formalism.GradedWeylDivisibility.rowAct ℂ h (MvPolynomial.C b :
        MvPolynomial (Fin n × Fin n) ℂ) = MvPolynomial.C b := fun h b =>
      (Formalism.GradedWeylDivisibility.rowAct ℂ h).commutes b
    rw [h, MvPolynomial.map_C, h]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, MvPolynomial.map_X]
    congr 1
    simp [Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_X]

theorem fockF_conj {σ : Type} (p q : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (MvPolynomial.map (starRingEnd ℂ) p) (MvPolynomial.map (starRingEnd ℂ) q) =
      Formalism.REAL.fockF q p := by
  classical
  have hs : (MvPolynomial.map (starRingEnd ℂ) p).support = p.support :=
    MvPolynomial.support_map_of_injective _ (starRingEnd ℂ).injective
  unfold Formalism.REAL.fockF
  rw [hs]
  have h1 : ∑ m ∈ p.support, MvPolynomial.coeff m (MvPolynomial.map (starRingEnd ℂ) p) *
        star (MvPolynomial.coeff m (MvPolynomial.map (starRingEnd ℂ) q)) *
        ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) =
      ∑ m ∈ p.support ∪ q.support, MvPolynomial.coeff m q * star (MvPolynomial.coeff m p) *
        ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
    refine Finset.sum_subset_zero_on_sdiff Finset.subset_union_left ?_ ?_
    · intro m hm
      have : MvPolynomial.coeff m p = 0 := by
        simpa using (Finset.mem_sdiff.1 hm).2
      simp [this]
    · intro m _
      simp only [MvPolynomial.coeff_map]
      simp [mul_comm]
  have h2 : ∑ m ∈ q.support, MvPolynomial.coeff m q * star (MvPolynomial.coeff m p) *
        ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) =
      ∑ m ∈ p.support ∪ q.support, MvPolynomial.coeff m q * star (MvPolynomial.coeff m p) *
        ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
    refine Finset.sum_subset_zero_on_sdiff Finset.subset_union_right ?_ (fun _ _ => rfl)
    intro m hm
    have : MvPolynomial.coeff m q = 0 := by
      simpa using (Finset.mem_sdiff.1 hm).2
    simp [this]
  rw [h1, h2]

theorem conj_coefficients : ∀ (n : ℕ) (lam : DomWeight n), (∀ p ∈ delSq ℂ n lam, MvPolynomial.map (starRingEnd ℂ) p ∈ delSq ℂ n lam) ∧ (∀ (g : Matrix (Fin n) (Fin n) ℂ) (p : MvPolynomial (Fin n × Fin n) ℂ), MvPolynomial.map (starRingEnd ℂ) (Formalism.GradedWeylDivisibility.rowAct ℂ g p) = Formalism.GradedWeylDivisibility.rowAct ℂ (g.map (starRingEnd ℂ)) (MvPolynomial.map (starRingEnd ℂ) p)) ∧ ∀ p q : MvPolynomial (Fin n × Fin n) ℂ, normFock lam (MvPolynomial.map (starRingEnd ℂ) p) (MvPolynomial.map (starRingEnd ℂ) q) = normFock lam q p := by
  intro n lam
  refine ⟨fun p hp => conj_mem_delSq lam hp, conj_rowAct, fun p q => ?_⟩
  rw [normFock, normFock, fockF_conj]

end GlobalTheory.ConjCoeff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConjLinearOntoOfInjectiveOfLeRange
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory

theorem conjLinear_onto_of_injective_of_le_range :
    ∀ (W M : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) (J₀ J₁ : W →ₗ⋆[ℂ] M), (∀ p ∈ S, ∃ ξ, J₀ ξ = p) → Function.Injective J₁ → (∀ ξ, J₁ ξ ∈ S) → ∀ p ∈ S, ∃ ξ, J₁ ξ = p := by
  intro W M _ _ _ _ _ S J₀ J₁ h0 hinj hS
  let f0 : W →ₗ[ℝ] M :=
    { toFun := J₀
      map_add' := J₀.map_add
      map_smul' := fun r x => by
        show J₀ (r • x) = r • J₀ x
        rw [← Complex.coe_smul, J₀.map_smulₛₗ, Complex.conj_ofReal, Complex.coe_smul] }
  let f1 : W →ₗ[ℝ] M :=
    { toFun := J₁
      map_add' := J₁.map_add
      map_smul' := fun r x => by
        show J₁ (r • x) = r • J₁ x
        rw [← Complex.coe_smul, J₁.map_smulₛₗ, Complex.conj_ofReal, Complex.coe_smul] }

  have hle0 : S.restrictScalars ℝ ≤ LinearMap.range f0 := fun p hp => h0 p hp
  have hle1 : LinearMap.range f1 ≤ S.restrictScalars ℝ := by
    rintro _ ⟨ξ, rfl⟩
    exact hS ξ
  have hf1 : Function.Injective f1 := hinj
  have : FiniteDimensional ℝ (S.restrictScalars ℝ) := Submodule.finiteDimensional_of_le hle0
  have hdim : Module.finrank ℝ (S.restrictScalars ℝ) ≤ Module.finrank ℝ (LinearMap.range f1) := by
    rw [LinearMap.finrank_range_of_inj hf1]
    exact (Submodule.finrank_mono hle0).trans (LinearMap.finrank_range_le f0)

  have heq : LinearMap.range f1 = S.restrictScalars ℝ := Submodule.eq_of_le_of_finrank_le hle1 hdim
  intro p hp
  have hp' : p ∈ LinearMap.range f1 := heq ▸ hp
  obtain ⟨ξ, hξ⟩ := hp'
  exact ⟨ξ, hξ⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivLeadMinorExpHermitianZeroDiag
section
open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory.MinorJet

section Linfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem hasDerivAt_exp_entry {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (i j : Fin n) :
    HasDerivAt (fun u : ℝ => NormedSpace.exp ((u : ℂ) • Y) i j)
      ((NormedSpace.exp ((s : ℂ) • Y) * Y) i j) s := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y s
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have h2 := (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt s h
  simp only [Complex.coe_smul]
  exact h2

end Linfty

theorem hasDerivAt_mul_entry {r : ℕ} (G H : ℝ → Matrix (Fin r) (Fin r) ℂ)
    (G' H' : Matrix (Fin r) (Fin r) ℂ) (t : ℝ)
    (hG : ∀ i j, HasDerivAt (fun s => G s i j) (G' i j) t)
    (hH : ∀ i j, HasDerivAt (fun s => H s i j) (H' i j) t) (i j : Fin r) :
    HasDerivAt (fun s => (G s * H s) i j) ((G' * H t + G t * H') i j) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => (hG i k).fun_mul (hH k j))
  simpa [Matrix.mul_apply, Matrix.add_apply, Finset.sum_add_distrib] using h

theorem hasDerivAt_adjugate_entry {r : ℕ} (G : ℝ → Matrix (Fin r) (Fin r) ℂ)
    (A : Matrix (Fin r) (Fin r) ℂ) (t : ℝ) (h0 : G t = 1)
    (hG : ∀ i j, HasDerivAt (fun s => G s i j) (A i j) t) (i j : Fin r) :
    HasDerivAt (fun s => (G s).adjugate i j) ((A.trace • (1 : Matrix (Fin r) (Fin r) ℂ) - A) i j) t := by
  have hP : ∀ a b, HasDerivAt (fun s => (G s).adjugate a b)
      ((((G t).updateRow b (Pi.single a 1)).adjugate * A.updateRow b 0).trace) t := by
    intro a b
    have hrow : ∀ p q, HasDerivAt (fun s => (G s).updateRow b (Pi.single a 1) p q)
        ((A.updateRow b 0) p q) t := by
      intro p q
      by_cases hp : p = b
      · subst hp
        simp only [updateRow_self]
        exact hasDerivAt_const _ _
      · simp only [updateRow_ne hp]
        exact hG p q
    have h := ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det (fun s => (G s).updateRow b (Pi.single a 1)) _ t hrow
    simpa only [adjugate_apply] using h
  let D : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b =>
    (((G t).updateRow b (Pi.single a 1)).adjugate * A.updateRow b 0).trace
  have hD : ∀ a b, HasDerivAt (fun s => (G s).adjugate a b) (D a b) t := fun a b => hP a b
  have h1 := hasDerivAt_mul_entry (fun s => (G s).adjugate) G D A t hD hG i j
  have h2 := (ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det G A t hG).mul_const ((1 : Matrix (Fin r) (Fin r) ℂ) i j)
  have h3 : HasDerivAt (fun s => (G s).det * (1 : Matrix (Fin r) (Fin r) ℂ) i j)
      ((D * G t + (G t).adjugate * A) i j) t := by
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp only [adjugate_mul, Matrix.smul_apply, smul_eq_mul]
  have hu := h3.unique h2
  rw [h0, adjugate_one, Matrix.mul_one, Matrix.one_mul, Matrix.add_apply] at hu
  have hDij : D i j = A.trace * (1 : Matrix (Fin r) (Fin r) ℂ) i j - A i j := by
    linear_combination hu
  convert hD i j using 1
  rw [hDij, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]

private theorem sum_castLE_lemma {n l : ℕ} (hl : l ≤ n) (f : Fin n → ℂ) :
    ∑ x : Fin l, f (Fin.castLE hl x) = ∑ a : Fin n, if a.val < l then f a else 0 := by
  have e : (Finset.univ : Finset (Fin l)).map (Fin.castLEEmb hl) =
      Finset.univ.filter (fun a : Fin n => a.val < l) := by
    ext a
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_filter, Fin.castLEEmb_apply]
    constructor
    · rintro ⟨x, rfl⟩
      simp
    · intro h
      exact ⟨⟨a.val, h⟩, Fin.ext rfl⟩
  rw [← Finset.sum_filter, ← e, Finset.sum_map]
  rfl

theorem trace_block {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (hY : Y.IsHermitian) (l : ℕ) (hl : l ≤ n) :
    ((Y * Y).submatrix (Fin.castLE hl) (Fin.castLE hl)).trace -
      (Y.submatrix (Fin.castLE hl) (Fin.castLE hl) * Y.submatrix (Fin.castLE hl) (Fin.castLE hl)).trace =
    ((∑ a : Fin n, ∑ b : Fin n, if l ≤ a.val ∧ b.val < l then ‖Y a b‖ ^ 2 else 0 : ℝ) : ℂ) := by
  have hH : ∀ a b, Y a b * Y b a = ((‖Y b a‖ ^ 2 : ℝ) : ℂ) := by
    intro a b
    have e : Y a b = star (Y b a) := by
      have := congrFun (congrFun hY a) b
      rw [conjTranspose_apply] at this
      exact this.symm
    rw [e, Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have e1 : ((Y * Y).submatrix (Fin.castLE hl) (Fin.castLE hl)).trace =
      ∑ a : Fin n, if a.val < l then ∑ b : Fin n, Y a b * Y b a else 0 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply, Matrix.mul_apply]
    exact sum_castLE_lemma hl (fun a => ∑ b : Fin n, Y a b * Y b a)
  have e2 : (Y.submatrix (Fin.castLE hl) (Fin.castLE hl) *
      Y.submatrix (Fin.castLE hl) (Fin.castLE hl)).trace =
      ∑ a : Fin n, if a.val < l then ∑ b : Fin n, (if b.val < l then Y a b * Y b a else 0) else 0 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.submatrix_apply]
    rw [← sum_castLE_lemma hl (fun a => ∑ b : Fin n, if b.val < l then Y a b * Y b a else 0)]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    exact sum_castLE_lemma hl (fun b => Y (Fin.castLE hl x) b * Y b (Fin.castLE hl x))
  have key : ∀ a : Fin n, ((if a.val < l then ∑ b : Fin n, Y a b * Y b a else 0) -
      (if a.val < l then ∑ b : Fin n, (if b.val < l then Y a b * Y b a else 0) else 0)) =
      ∑ b : Fin n, ((if l ≤ b.val ∧ a.val < l then ‖Y b a‖ ^ 2 else 0 : ℝ) : ℂ) := by
    intro a
    by_cases ha : a.val < l
    · rw [if_pos ha, if_pos ha, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      by_cases hb : b.val < l
      · rw [if_pos hb, if_neg (fun h => absurd h.1 (Nat.not_le.mpr hb)), sub_self,
          Complex.ofReal_zero]
      · rw [if_neg hb, sub_zero, if_pos ⟨Nat.le_of_not_lt hb, ha⟩, hH]
    · rw [if_neg ha, if_neg ha, sub_self]
      symm
      refine Finset.sum_eq_zero (fun b _ => ?_)
      rw [if_neg (fun h => ha h.2), Complex.ofReal_zero]
  rw [e1, e2, ← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun a _ => key a), Finset.sum_comm,
    Complex.ofReal_sum]
  simp only [Complex.ofReal_sum]

theorem deriv_leadMinor_exp : ∀ (n : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ), Y.IsHermitian → (∀ a, Y a a = 0) → ∀ (l : ℕ) (hl : l ≤ n), deriv (fun t : ℝ => (leadMinor (NormedSpace.exp ((t : ℂ) • Y)) l hl).re) 0 = 0 ∧ deriv (deriv (fun t : ℝ => (leadMinor (NormedSpace.exp ((t : ℂ) • Y)) l hl).re)) 0 = ∑ a : Fin n, ∑ b : Fin n, if l ≤ a.val ∧ b.val < l then ‖Y a b‖ ^ 2 else 0 := by
  intro n Y hY hdiag l hl
  have hE0 : NormedSpace.exp (((0 : ℝ) : ℂ) • Y) = 1 := by simp
  have hM0 : (NormedSpace.exp (((0 : ℝ) : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl) = 1 := by
    rw [hE0]
    exact submatrix_one _ (Fin.castLE_injective hl)
  have hM'0 : (NormedSpace.exp (((0 : ℝ) : ℂ) • Y) * Y).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      Y.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
    rw [hE0, Matrix.one_mul]
  have htr : (Y.submatrix (Fin.castLE hl) (Fin.castLE hl)).trace = 0 := by
    simp [Matrix.trace, hdiag]
  have hM : ∀ (t : ℝ) x y, HasDerivAt
      (fun s : ℝ => (NormedSpace.exp ((s : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl) x y)
      ((NormedSpace.exp ((t : ℂ) • Y) * Y).submatrix (Fin.castLE hl) (Fin.castLE hl) x y) t :=
    fun t x y => hasDerivAt_exp_entry Y t (Fin.castLE hl x) (Fin.castLE hl y)
  have hf : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => (leadMinor (NormedSpace.exp ((s : ℂ) • Y)) l hl).re)
      (((NormedSpace.exp ((t : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl)).adjugate *
        (NormedSpace.exp ((t : ℂ) • Y) * Y).submatrix (Fin.castLE hl) (Fin.castLE hl)).trace.re t := by
    intro t
    have hg := ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det
      (fun s : ℝ => (NormedSpace.exp ((s : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl)) _ t (hM t)
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hg
    simpa [leadMinor, Function.comp_def] using h
  have hderiv : deriv (fun s : ℝ => (leadMinor (NormedSpace.exp ((s : ℂ) • Y)) l hl).re) =
      fun t : ℝ => (((NormedSpace.exp ((t : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl)).adjugate *
        (NormedSpace.exp ((t : ℂ) • Y) * Y).submatrix (Fin.castLE hl) (Fin.castLE hl)).trace.re :=
    funext fun t => (hf t).deriv
  rw [hderiv]
  refine ⟨?_, ?_⟩
  · beta_reduce
    rw [hM0, hM'0, adjugate_one, Matrix.one_mul, htr, Complex.zero_re]
  · have hadj : ∀ x y, HasDerivAt
        (fun s : ℝ => ((NormedSpace.exp ((s : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl)).adjugate x y)
        (((Y.submatrix (Fin.castLE hl) (Fin.castLE hl)).trace • (1 : Matrix (Fin l) (Fin l) ℂ) -
          Y.submatrix (Fin.castLE hl) (Fin.castLE hl)) x y) 0 := by
      intro x y
      have h := hasDerivAt_adjugate_entry
        (fun s : ℝ => (NormedSpace.exp ((s : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl)) _ 0 hM0
        (hM 0) x y
      rwa [hM'0] at h
    have hMd : ∀ x y, HasDerivAt
        (fun s : ℝ => (NormedSpace.exp ((s : ℂ) • Y) * Y).submatrix (Fin.castLE hl) (Fin.castLE hl) x y)
        ((Y * Y).submatrix (Fin.castLE hl) (Fin.castLE hl) x y) 0 := by
      intro x y
      have h := hasDerivAt_mul_entry (fun s : ℝ => NormedSpace.exp ((s : ℂ) • Y)) (fun _ => Y)
        (NormedSpace.exp (((0 : ℝ) : ℂ) • Y) * Y) 0 0 (hasDerivAt_exp_entry Y 0)
        (fun _ _ => hasDerivAt_const _ _) (Fin.castLE hl x) (Fin.castLE hl y)
      rw [hE0, Matrix.one_mul, Matrix.mul_zero, add_zero] at h
      exact h
    have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun x _ =>
      hasDerivAt_mul_entry
        (fun s : ℝ => ((NormedSpace.exp ((s : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl)).adjugate)
        (fun s : ℝ => (NormedSpace.exp ((s : ℂ) • Y) * Y).submatrix (Fin.castLE hl) (Fin.castLE hl))
        _ _ 0 hadj hMd x x)
    have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hsum
    have h3 : HasDerivAt
        (fun t : ℝ => (((NormedSpace.exp ((t : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl)).adjugate *
          (NormedSpace.exp ((t : ℂ) • Y) * Y).submatrix (Fin.castLE hl) (Fin.castLE hl)).trace.re)
        ((((Y.submatrix (Fin.castLE hl) (Fin.castLE hl)).trace • (1 : Matrix (Fin l) (Fin l) ℂ) - Y.submatrix (Fin.castLE hl) (Fin.castLE hl)) *
          (NormedSpace.exp (((0 : ℝ) : ℂ) • Y) * Y).submatrix (Fin.castLE hl) (Fin.castLE hl) +
          ((NormedSpace.exp (((0 : ℝ) : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl)).adjugate *
          (Y * Y).submatrix (Fin.castLE hl) (Fin.castLE hl)).trace).re 0 := h2
    have hv : (((Y.submatrix (Fin.castLE hl) (Fin.castLE hl)).trace • (1 : Matrix (Fin l) (Fin l) ℂ) - Y.submatrix (Fin.castLE hl) (Fin.castLE hl)) *
          (NormedSpace.exp (((0 : ℝ) : ℂ) • Y) * Y).submatrix (Fin.castLE hl) (Fin.castLE hl) +
          ((NormedSpace.exp (((0 : ℝ) : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl)).adjugate *
          (Y * Y).submatrix (Fin.castLE hl) (Fin.castLE hl)).trace =
        ((Y * Y).submatrix (Fin.castLE hl) (Fin.castLE hl)).trace - (Y.submatrix (Fin.castLE hl) (Fin.castLE hl) * Y.submatrix (Fin.castLE hl) (Fin.castLE hl)).trace := by
      rw [hM0, hM'0, adjugate_one, htr, zero_smul, zero_sub, Matrix.neg_mul, Matrix.one_mul,
        Matrix.trace_add, Matrix.trace_neg]
      ring
    rw [h3.deriv, hv, trace_block Y hY l hl, Complex.ofReal_re]

end GlobalTheory.MinorJet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EmbeddedDatumInvariantUnderUnipotentStatement
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embeddedDatum_invariant_under_unipotent : ∀ (K V W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (H : HermSpace K V) (HW : HermSpace K W) (e : W →ₗ[K] V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F G G' : FlagD H r) (𝔡 : Ideal (𝓞 K)) (N : NF H r) (g : ℕ), IsEmb F HW e → Adapt F G 𝔡 N → (∀ (s : V ≃ₗ[K] V) (Λ : Submodule (𝓞 K) V), F.InN (s : V →ₗ[K] V) → (∀ a, s (G.e a) - G'.e a ∈ G'.Xa a.val) → datOf F G' e g (s • Λ) = datOf F G e g Λ ∧ lat0 F e (s • Λ) = lat0 F e Λ ∧ latL F G (s • Λ) = latL F G Λ) ∧ ∀ Λ Λ' : Submodule (𝓞 K) V, datOf F G e g Λ = datOf F G e g Λ' → flagPairDefinitePartLattice G F Λ = flagPairDefinitePartLattice G F Λ' ∧ iotaGraph F G Λ (g : 𝓞 K) = iotaGraph F G Λ' (g : 𝓞 K) := by
  first | exact @GlobalTheory.DegAsm.datOf_move | exact GlobalTheory.DegAsm.datOf_move | (intros; apply GlobalTheory.DegAsm.datOf_move <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDefiniteSpaceIsometryOfAdaptedPairStatement
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_definiteSpace_isometry_of_adapted_pair : ∀ (K V W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (H : HermSpace K V) (HW : HermSpace K W) (e : W →ₗ[K] V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F G : FlagD H r) (𝔡 : Ideal (𝓞 K)) (N : NF H r) (γ : V ≃ₗ[K] V), IsEmb F HW e → Adapt F G 𝔡 N → γ ∈ isomGrp H → (∀ a, G.e a = γ (F.e a)) → ∃ h : W ≃ₗ[K] W, h ∈ isomGrp HW ∧ IsH F G e γ h ∧ (∀ h' : W ≃ₗ[K] W, IsH F G e γ h' → h' = h) ∧ ∀ (g : ℕ) (Λ' : Submodule (𝓞 K) V), (datOf F G e g (γ • Λ')).1 = imLat h (lat0 F e Λ') := by
  first | exact @GlobalTheory.DegAsm.exists_isH | exact GlobalTheory.DegAsm.exists_isH | (intros; apply GlobalTheory.DegAsm.exists_isH <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometricRealisationOfSublatticeStatement
section
open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isometric_realisation_of_sublattice' : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (n : ℕ) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (R : Submodule (𝓞 K) (Fin n → K)), (∀ w, IsUnit (X w).det) → R.FG → ∃ (j : ℕ) (i : Matrix (Fin n) (Fin j) K) (X' : InfinitePlace K → Matrix (Fin j) (Fin j) ℂ) (P : InfinitePlace K → Matrix (Fin n) (Fin j) ℂ) (B : Submodule (𝓞 K) (Fin j → K)), j = rkK R ∧ (∀ w, IsUnit (X' w).det) ∧ (∀ w, (P w)ᴴ * P w = 1) ∧ (∀ w, (X w)⁻¹ * i.map w.embedding = P w * (X' w)⁻¹) ∧ B.FG ∧ Submodule.span K (B : Set (Fin j → K)) = ⊤ ∧ (∀ y ∈ B, i *ᵥ y ∈ R) ∧ (∀ r ∈ R, ∃ y ∈ B, i *ᵥ y = r) ∧ largestSize (Pi.basisFun K (Fin j)) X' B = largestSize (Pi.basisFun K (Fin n)) X R := by
  first | exact @GlobalTheory.exists_isometric_realisation_of_sublattice | exact GlobalTheory.exists_isometric_realisation_of_sublattice | (intros; apply GlobalTheory.exists_isometric_realisation_of_sublattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HilbertSchmidtLowerBoundInverseDifferentStatement
section
open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertSchmidt_lower_bound_inverseDifferent : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (a b : ℕ) (X : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ) (X' : InfinitePlace K → Matrix (Fin b) (Fin b) ℂ) (A : Submodule (𝓞 K) (Fin a → K)) (B : Submodule (𝓞 K) (Fin b → K)) (lo hi : ℝ), (∀ w, IsUnit (X w).det) → (∀ w, IsUnit (X' w).det) → A.FG → B.FG → 0 < lo → (∀ N, N ≤ A → N ≠ ⊥ → lo ≤ size (Pi.basisFun K (Fin a)) X N) → largestSize (Pi.basisFun K (Fin b)) X' B ≤ hi → ∀ ψ : Matrix (Fin a) (Fin b) K, (∃ y ∈ B, ψ *ᵥ y ≠ 0) → (∀ δ ∈ differentIdeal ℤ (𝓞 K), ∀ y ∈ B, δ • (ψ *ᵥ y) ∈ A) → (nPl K : ℝ) * (lo / (|(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (nPl K : ℝ))) * hi)) ^ 2 ≤ ∑ w, ∑ i, ∑ j, ‖((X w)⁻¹ * ψ.map w.embedding * X' w) i j‖ ^ 2 := by
  first | exact @GlobalTheory.DualBound.hs_lower_bound | exact GlobalTheory.DualBound.hs_lower_bound | (intros; apply GlobalTheory.DualBound.hs_lower_bound <;> assumption)
end

