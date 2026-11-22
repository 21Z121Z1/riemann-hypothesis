import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0039
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.NormInfSubmultiplicativeLeAdelicHeight
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.SmoothForms.NormInf

theorem entrySum_mul_le {n : Type} [Fintype n] (A B : Matrix n n ℂ) :
    ∑ i, ∑ j, ‖(A * B) i j‖ ≤ (∑ i, ∑ j, ‖A i j‖) * ∑ i, ∑ j, ‖B i j‖ := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ∑ j, ‖(A * B) i j‖ ≤ ∑ j, ∑ k, ‖A i k‖ * ‖B k j‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [Matrix.mul_apply]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_mul_le _ _)
    _ = ∑ k, ‖A i k‖ * ∑ j, ‖B k j‖ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
    _ ≤ _ := by
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact Finset.single_le_sum (f := fun k => ∑ j, ‖B k j‖)
          (fun k _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ k)

theorem norm_entry_le_opNorm {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (i j : n) :
    ‖A i j‖ ≤ ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A‖ := by
  have h := (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A).le_opNorm (EuclideanSpace.single j (1 : ℂ))
  have h1 : ‖(EuclideanSpace.single j (1 : ℂ) : EuclideanSpace ℂ n)‖ = 1 := by simp
  rw [h1, mul_one] at h
  refine le_trans ?_ h
  refine le_trans (le_of_eq ?_) (PiLp.norm_apply_le _ i)
  congr 1
  change _ = (A *ᵥ Pi.single j 1) i
  simp

theorem sum_mul_add_le {ι : Type} [Fintype ι] (a b c d : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hc : ∀ i, 0 ≤ c i) (hd : ∀ i, 0 ≤ d i) :
    ∑ i, (a i * c i + d i * b i) ≤ (∑ i, (a i + b i)) * ∑ i, (c i + d i) := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h : c i + d i ≤ ∑ i, (c i + d i) :=
    Finset.single_le_sum (f := fun i => c i + d i) (fun i _ => add_nonneg (hc i) (hd i)) (Finset.mem_univ i)
  refine le_trans ?_ (mul_le_mul_of_nonneg_left h (add_nonneg (ha i) (hb i)))
  nlinarith [mul_nonneg (ha i) (hd i), mul_nonneg (hb i) (hc i)]

theorem infMat_mul' {D : D7} (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (V : HSp D) (g h : GA D V) :
    infMat D.sp.cm.sig V.gram θ (g * h) = infMat D.sp.cm.sig V.gram θ g * infMat D.sp.cm.sig V.gram θ h := by
  have : HA.mat (AF D.host.F) D.sp.cm.sig V.gram (g * h) =
    HA.mat (AF D.host.F) D.sp.cm.sig V.gram g * HA.mat (AF D.host.F) D.sp.cm.sig V.gram h := rfl
  simp only [infMat, this, Units.val_mul]
  rw [Matrix.map_mul, Matrix.map_mul]

theorem infHt_le_height {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (τ : D.what₂.Tau) (g : GA D V) : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infHt θ V τ g ≤ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height
  refine le_trans ?_ (le_mul_of_one_le_right' (one_le_finprod' fun _ => le_max_left _ _))
  exact Finset.single_le_prod' (f := fun τ => GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infHt θ V τ g)
    (fun _ _ => le_max_left _ _) (Finset.mem_univ τ)

end GlobalTheory.SmoothForms.NormInf

namespace GlobalTheory.SmoothForms

open NormInf in

theorem normInf_mul_le_and_le_height :
    ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D),
      (∀ g h : GA D V, normInf θ V (g * h) ≤ normInf θ V g * normInf θ V h) ∧
        ∃ C : ℝ, ∀ g : GA D V, normInf θ V g ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g : ℝ) := by
  intro D θ V
  refine ⟨fun g h => ?_, ⟨∑ _τ : D.what₂.Tau, ∑ _i : Fin V.rank, ∑ _j : Fin V.rank, (2 : ℝ), fun g => ?_⟩⟩
  · unfold normInf
    simp only [Finset.sum_add_distrib (s := (Finset.univ : Finset (Fin V.rank)))]
    have hn : ∀ (x : GA D V) τ, 0 ≤ ∑ i, ∑ j, ‖infMat D.sp.cm.sig V.gram (θ τ) x i j‖ := fun x τ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    refine le_trans ?_ (sum_mul_add_le _ _ _ _ (hn g) (hn g⁻¹) (hn h) (hn h⁻¹))
    refine Finset.sum_le_sum fun τ _ => ?_
    rw [_root_.mul_inv_rev, infMat_mul', infMat_mul']
    exact add_le_add (entrySum_mul_le _ _) (entrySum_mul_le _ _)
  · unfold normInf
    simp only [Finset.sum_mul]
    refine Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have h0 := infHt_le_height θ V τ g
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infNorm θ V τ g ≤ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g :=
      ((le_max_left _ _).trans (le_max_right _ _)).trans h0
    have h2 : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infNorm θ V τ g⁻¹ ≤ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans h0
    have h3 := (norm_entry_le_opNorm (infMat D.sp.cm.sig V.gram (θ τ) g) i j).trans (NNReal.coe_le_coe.2 h1)
    have h4 := (norm_entry_le_opNorm (infMat D.sp.cm.sig V.gram (θ τ) g⁻¹) i j).trans (NNReal.coe_le_coe.2 h2)
    linarith

end GlobalTheory.SmoothForms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.NormNatCastAdicCompletionLeOne
section
namespace GlobalTheory.AdicNatCastNorm

theorem norm_natCast_adicCompletion_le_one {F : Type} [inst : Field F] [inst_1 : NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (n : ℕ) :
    ‖(↑n : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v)‖ ≤ (1 : ℝ) :=
  IsUltrametricDist.norm_natCast_le_one _ n

end GlobalTheory.AdicNatCastNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.NormNatCastLe
section
namespace GlobalTheory.AdicNormZpowEstimates

open IsDedekindDomain NumberField

variable {F : Type} [Field F] [NumberField F]

theorem norm_eq_zpow (v : HeightOneSpectrum (RingOfIntegers F)) (y : v.adicCompletion F)
    (hy : y ≠ 0) : ∃ k : ℤ, ‖y‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ k := by
  have h0 : Valued.v y ≠ 0 := by simpa using hy
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ h0]
  exact ⟨_, by push_cast; rfl⟩

theorem one_lt_norm (v : HeightOneSpectrum (RingOfIntegers F)) :
    (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v

theorem norm_le_of_lt (v : HeightOneSpectrum (RingOfIntegers F)) (y : v.adicCompletion F) (m : ℤ)
    (h : ‖y‖ < (Ideal.absNorm v.asIdeal : ℝ) ^ (m + 1)) :
    ‖y‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ m := by
  have h1 := one_lt_norm v
  by_cases hy : y = 0
  · rw [hy, norm_zero]
    positivity
  · obtain ⟨k, hk⟩ := norm_eq_zpow v y hy
    rw [hk] at h ⊢
    rw [zpow_lt_zpow_iff_right₀ h1] at h
    exact zpow_le_zpow_right₀ h1.le (by omega)

theorem natCast_eq (v : HeightOneSpectrum (RingOfIntegers F)) (n : ℕ) :
    (n : v.adicCompletion F)
      = FinitePlace.embedding v (algebraMap (RingOfIntegers F) F (n : RingOfIntegers F)) := by
  rw [map_natCast, map_natCast]

theorem norm_natCast_le (v : HeightOneSpectrum (RingOfIntegers F)) (n : ℕ) :
    ‖(n : v.adicCompletion F)‖ ≤ 1 := by
  rw [natCast_eq]
  exact FinitePlace.norm_le_one F v _

theorem norm_absNorm_le (v : HeightOneSpectrum (RingOfIntegers F)) :
    ‖((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)‖
      ≤ (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  have := norm_le_of_lt v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) (-1) (by
    rw [natCast_eq, neg_add_cancel, zpow_zero, FinitePlace.norm_lt_one_iff_mem]
    exact Ideal.absNorm_mem _)
  simpa using this

theorem exists_denominator {F : Type} [Field F] [NumberField F]
    (H : HeightOneSpectrum (RingOfIntegers F) → NNReal) (h1 : ∀ v, (1 : NNReal) ≤ H v)
    (hfin : Set.Finite (Function.mulSupport H)) :
    ∃ d : ℕ, 0 < d ∧ (d : NNReal) ≤ ∏ᶠ v, H v ∧
      ∀ (v : HeightOneSpectrum (RingOfIntegers F)) (y : v.adicCompletion F),
        ‖y‖₊ ≤ H v → ‖(d : v.adicCompletion F) * y‖ ≤ (1 : ℝ) := by
  classical
  have hn : ∀ v : HeightOneSpectrum (RingOfIntegers F), ∃ n : ℕ,
      (Ideal.absNorm v.asIdeal : ℝ) ^ n ≤ H v ∧ (H v : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) ^ (n + 1) :=
    fun v => exists_nat_pow_near (by exact_mod_cast h1 v) (one_lt_norm v)
  choose n hle hlt using hn
  refine ⟨∏ v ∈ hfin.toFinset, Ideal.absNorm v.asIdeal ^ n v, ?_, ?_, ?_⟩
  · refine Finset.prod_pos fun v _ => pow_pos ?_ _
    exact lt_trans Nat.one_pos (NumberField.HeightOneSpectrum.one_lt_absNorm v)
  · rw [finprod_eq_prod_of_mulSupport_subset H (s := hfin.toFinset) (by simp), Nat.cast_prod]
    refine Finset.prod_le_prod' fun v _ => ?_
    have := hle v
    exact_mod_cast this
  · intro v y hy
    have hy' : ‖y‖ ≤ (H v : ℝ) := by exact_mod_cast hy
    rw [norm_mul]
    by_cases hv : v ∈ hfin.toFinset
    · have hq := one_lt_norm v
      have hq0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := lt_trans one_pos hq
      have h2 : ‖y‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ n v := by
        have := norm_le_of_lt v y (n v) (by
          have := lt_of_le_of_lt hy' (hlt v)
          exact_mod_cast this)
        simpa using this
      rw [← Finset.mul_prod_erase _ _ hv, Nat.cast_mul, norm_mul, Nat.cast_pow, norm_pow]
      have h3 : ‖((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)‖ ^ n v
          ≤ ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ n v :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_absNorm_le v) _
      calc _ ≤ (((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ n v * 1) * (Ideal.absNorm v.asIdeal : ℝ) ^ n v :=
            mul_le_mul (mul_le_mul h3 (norm_natCast_le v _) (norm_nonneg _) (by positivity)) h2
              (norm_nonneg _) (by positivity)
        _ = 1 := by
            rw [mul_one, ← mul_pow, inv_mul_cancel₀ hq0.ne', one_pow]
    · have h2 : H v = 1 := by simpa using hv
      rw [h2] at hy'
      exact mul_le_one₀ (norm_natCast_le v _) (norm_nonneg _) (by simpa using hy')

end GlobalTheory.AdicNormZpowEstimates
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryAdelicHeightCosetLeNormInfPow
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.SmoothForms.HeightCoset

open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies

theorem opNorm_le_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A‖ ≤ ∑ i, ∑ j, ‖A i j‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  refine (Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => norm_nonneg _).trans ?_
  gcongr
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have : (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A x) i = ∑ j, A i j * x j := rfl
  rw [this, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul]
  gcongr
  exact PiLp.norm_apply_le x j

variable {D : D7}

theorem infMat_mul' (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (V : HSp D) (g h : GA D V) :
    infMat D.sp.cm.sig V.gram θ (g * h) = infMat D.sp.cm.sig V.gram θ g * infMat D.sp.cm.sig V.gram θ h := by
  have : HA.mat (AF D.host.F) D.sp.cm.sig V.gram (g * h) =
    HA.mat (AF D.host.F) D.sp.cm.sig V.gram g * HA.mat (AF D.host.F) D.sp.cm.sig V.gram h := rfl
  simp only [infMat, this, Units.val_mul]
  rw [Matrix.map_mul, Matrix.map_mul]

theorem infMat_one' (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (V : HSp D) :
    infMat D.sp.cm.sig V.gram θ (1 : GA D V) = 1 := by
  have : HA.mat (AF D.host.F) D.sp.cm.sig V.gram (1 : GA D V) = 1 := rfl
  simp only [infMat, this, Units.val_one]
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]

theorem finMat_eq (V : HSp D) (g : GA D V) : finMat D.sp.cm.sig V.gram g = (finHom V g).1 := rfl

theorem finHt_mul (V : HSp D) (x g : GA D V) (hg : g ∈ GinfC V) (v) : finHt V v (x * g) = finHt V v x := by
  have h0 : finHom V g = 1 := hg
  have h1 : finMat D.sp.cm.sig V.gram (x * g) = finMat D.sp.cm.sig V.gram x := by
    rw [finMat_eq, finMat_eq, map_mul, h0, mul_one]
  have h2 : finMat D.sp.cm.sig V.gram (x * g)⁻¹ = finMat D.sp.cm.sig V.gram x⁻¹ := by
    rw [finMat_eq, finMat_eq, map_inv, map_inv, map_mul, h0, mul_one]
  simp only [finHt, finNorm, h1, h2]

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

theorem infNorm_mul_le (τ : D.what₂.Tau) (x g : GA D V) :
    infNorm θ V τ (x * g) ≤ infNorm θ V τ x * infNorm θ V τ g := by
  unfold infNorm
  rw [infMat_mul', map_mul]
  exact nnnorm_mul_le _ _

theorem infHt_mul_le (τ : D.what₂.Tau) (x g : GA D V) :
    infHt θ V τ (x * g) ≤ infHt θ V τ x * infHt θ V τ g := by
  refine max_le (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)) (max_le ?_ ?_)
  · refine (infNorm_mul_le θ V τ x g).trans (mul_le_mul' ?_ ?_) <;>
      exact le_max_of_le_right (le_max_left _ _)
  · rw [_root_.mul_inv_rev, mul_comm (infHt θ V τ x)]
    refine (infNorm_mul_le θ V τ g⁻¹ x⁻¹).trans (mul_le_mul' ?_ ?_) <;>
      exact le_max_of_le_right (le_max_right _ _)

theorem infNorm_le_normInf (τ : D.what₂.Tau) (g : GA D V) :
    (infNorm θ V τ g : ℝ) ≤ normInf θ V g ∧ (infNorm θ V τ g⁻¹ : ℝ) ≤ normInf θ V g := by
  have h : ∑ i, ∑ j, (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖)
      ≤ normInf θ V g :=
    Finset.single_le_sum (f := fun τ => ∑ i, ∑ j,
      (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖))
      (fun _ _ => by positivity) (Finset.mem_univ τ)
  constructor
  · refine (opNorm_le_sum _).trans (le_trans ?_ h)
    gcongr
    exact le_add_of_nonneg_right (norm_nonneg _)
  · refine (opNorm_le_sum _).trans (le_trans ?_ h)
    gcongr
    exact le_add_of_nonneg_left (norm_nonneg _)

theorem infHt_le_normInf (hV : 0 < V.rank) (τ : D.what₂.Tau) (g : GA D V) :
    (infHt θ V τ g : ℝ) ≤ normInf θ V g := by
  obtain ⟨h1, h2⟩ := infNorm_le_normInf θ V τ g
  haveI : Nonempty (Fin V.rank) := ⟨⟨0, hV⟩⟩
  have h3 : infNorm θ V τ 1 = 1 := by
    unfold infNorm
    rw [infMat_one', map_one]
    exact nnnorm_one
  have h4 : (1 : ℝ) ≤ infNorm θ V τ g * infNorm θ V τ g⁻¹ := by
    have := infNorm_mul_le θ V τ g g⁻¹
    rw [mul_inv_cancel, h3] at this
    exact_mod_cast this
  have h5 : 1 ≤ normInf θ V g := by
    by_contra hc
    push_neg at hc
    have a0 := (infNorm θ V τ g).coe_nonneg
    have b0 := (infNorm θ V τ g⁻¹).coe_nonneg
    nlinarith
  unfold infHt
  push_cast
  exact max_le h5 (max_le h1 h2)

theorem infHt_rank_zero (hV : V.rank = 0) (τ : D.what₂.Tau) (g : GA D V) : infHt θ V τ g = 1 := by
  haveI : IsEmpty (Fin V.rank) := by rw [hV]; infer_instance
  have h : ∀ g, infNorm θ V τ g ≤ 1 := fun g => by
    have := opNorm_le_sum (infMat D.sp.cm.sig V.gram (θ τ) g)
    rw [Finset.univ_eq_empty, Finset.sum_empty] at this
    exact_mod_cast this.trans zero_le_one
  exact max_eq_left (max_le (h g) (h g⁻¹))

theorem height_mul_le (x g : GA D V) (hg : g ∈ GinfC V) :
    height θ V (x * g) ≤ height θ V x * ∏ τ, infHt θ V τ g := by
  unfold height
  simp only [finHt_mul V x g hg]
  rw [mul_right_comm, ← Finset.prod_mul_distrib]
  gcongr with τ
  exact infHt_mul_le θ V τ x g

theorem height_le_normInf_pow (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) :
    ∃ M : ℕ, ∀ x : GA D V, ∃ C : ℝ, ∀ g ∈ GinfC V,
      (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V (x * g) : ℝ) ≤ C * normInf θ V g ^ M := by
  rcases Nat.eq_zero_or_pos V.rank with hV | hV
  · refine ⟨0, fun x => ⟨height θ V x, fun g hg => ?_⟩⟩
    have := height_mul_le θ V x g hg
    simp only [infHt_rank_zero θ V hV, Finset.prod_const_one] at this
    rw [pow_zero]
    exact_mod_cast this
  · refine ⟨Fintype.card D.what₂.Tau, fun x => ⟨height θ V x, fun g hg => ?_⟩⟩
    have : (height θ V (x * g) : ℝ) ≤ height θ V x * ∏ τ, (infHt θ V τ g : ℝ) := by
      exact_mod_cast height_mul_le θ V x g hg
    refine this.trans ?_
    gcongr
    rw [← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => NNReal.coe_nonneg _) fun τ _ => infHt_le_normInf θ V hV τ g

end GlobalTheory.SmoothForms.HeightCoset

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberValuesCongruencesModDegreeOnePrimeStatement
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weber_values_congruences_mod_degree_one_prime : ∀ (K : IntermediateField ℚ ℂ) [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) → ∀ (W : ValuationSubring ℂ) (π : 𝓞 K) (p : ℕ), p.Prime → 5 ≤ p → Ideal.absNorm (Ideal.span {π}) = p → ((π : K) : ℂ) ∈ W.nonunits → (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) ∈ W ∧ (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) - (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) ^ p ∈ W.nonunits ∧ ∀ (m : ℕ), ¬ p ∣ m → (∀ t, (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) ∈ W ∧ (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP (((π : K) : ℂ) * t)) - (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) ^ p ∈ W.nonunits) ∧ ((L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) ∉ W.nonunits → (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) - 1 ∉ W.nonunits → ∀ t t', (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → (m : ℂ) * t' ∈ L.lattice → t' ∉ L.lattice → (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) - (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t') ∈ W.nonunits → t - t' ∈ L.lattice ∨ t + t' ∈ L.lattice) := by
  first | exact @GlobalTheory.WeberCongruenceAnyOrder.weber_congruences | exact GlobalTheory.WeberCongruenceAnyOrder.weber_congruences | (intros; apply GlobalTheory.WeberCongruenceAnyOrder.weber_congruences <;> assumption)
end

