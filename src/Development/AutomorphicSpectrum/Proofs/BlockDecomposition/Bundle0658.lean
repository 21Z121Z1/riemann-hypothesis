import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupCosetDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0625
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0592
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0626
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0627
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyExhaustion.PropsExh
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0641
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0601
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0628
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0529
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0629
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0607

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaRegionMeasureBound
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.IwasawaShell

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem q_pos : (0 : ℝ) < residueCard F := by
  have h : 1 < residueCard F := one_lt_residueCard
  exact_mod_cast (by omega : 0 < residueCard F)

theorem modulus_unif_zpow (k : ℤ) :
    (modulus (((unifUnit F) ^ k : Fˣ) : F) : ℝ) = (residueCard F : ℝ) ^ (-k) := by
  have hq : (residueCard F : ℝ) ≠ 0 := q_pos.ne'
  have hu : (modulus ((unifUnit F : Fˣ) : F) : ℝ) = (residueCard F : ℝ)⁻¹ := by
    rw [modulus, if_neg (unifUnit F).ne_zero, ord_unifUnit]
    simp
  have hui : (modulus (((unifUnit F)⁻¹ : Fˣ) : F) : ℝ) = (residueCard F : ℝ) := by
    rw [Units.val_inv_eq_inv_val, modulus_inv]
    push_cast
    rw [hu, inv_inv]
  induction k using Int.induction_on with
  | zero => simp [modulus_one]
  | succ i ih =>
    rw [_root_.zpow_add_one, Units.val_mul, modulus_mul, NNReal.coe_mul, ih, hu, neg_add, zpow_add₀ hq, _root_.zpow_neg_one]
  | pred i ih =>
    rw [_root_.zpow_sub_one, Units.val_mul, modulus_mul, NNReal.coe_mul, ih, hui, neg_sub, sub_eq_add_neg, add_comm (1 : ℤ), zpow_add₀ hq, zpow_one]

theorem mem_integer_of_modulus_le (k : ℤ) {x : F}
    (hx : (modulus x : ℝ) ≤ (residueCard F : ℝ) ^ k) :
    (((unifUnit F) ^ k : Fˣ) : F) * x ∈ 𝒪[F] := by
  have hq : (residueCard F : ℝ) ≠ 0 := q_pos.ne'
  rw [← modulus_le_one_iff, ← NNReal.coe_le_coe, modulus_mul, NNReal.coe_mul, NNReal.coe_one,
    modulus_unif_zpow]
  calc (residueCard F : ℝ) ^ (-k) * (modulus x : ℝ)
      ≤ (residueCard F : ℝ) ^ (-k) * (residueCard F : ℝ) ^ k :=
        mul_le_mul_of_nonneg_left hx (zpow_nonneg q_pos.le _)
    _ = 1 := by rw [← zpow_add₀ hq]; simp

theorem uni2_mul_uni2_eq_uni2_add (x y : F) : Ad3.uni2 x * Ad3.uni2 y = Ad3.uni2 (x + y) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ad3.uni2, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem unipotent_integral_mem_compact {y : F} (hy : y ∈ 𝒪[F]) : Ad3.uni2 y ∈ GLnLocal.integralGL F 2 := by
  rw [GLnLocal.mem_integralGL_iff]
  have h0 : (0 : F) ∈ 𝒪[F] := zero_mem _
  have h1 : (1 : F) ∈ 𝒪[F] := one_mem _
  have hn : -y ∈ 𝒪[F] := neg_mem hy
  have hv : ((Ad3.uni2 y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, y; 0, 1] := rfl
  have hi : (((Ad3.uni2 y)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, -y; 0, 1] := rfl
  rw [hv, hi]
  constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;> simpa using by assumption

theorem unipotent_mul_torus_commute (α β : Fˣ) (x : F) :
    Ad3.uni2 x * Ad3.dg2 α β = Ad3.dg2 α β * Ad3.uni2 ((α : F)⁻¹ * β * x) := by
  have hα : (α : F) ≠ 0 := α.ne_zero
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ad3.uni2, Ad3.dg2, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

variable (F) in

def Q (j : ℤ) : Set (GL (Fin 2) F) :=
  {g | ∃ y : F, (modulus y : ℝ) ≤ (residueCard F : ℝ) ^ j ∧
    ∃ κ ∈ GLnLocal.integralGL F 2, g = Ad3.uni2 y * κ}

theorem Q_zero_subset : Q F 0 ⊆ (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F)) := by
  rintro g ⟨y, hy, κ, hκ, rfl⟩
  have hy' : y ∈ 𝒪[F] := by
    rw [← modulus_le_one_iff, ← NNReal.coe_le_coe]
    simpa using hy
  exact mul_mem (unipotent_integral_mem_compact hy') hκ

theorem Q_succ_subset {ϖ : Fˣ} {B : Finset F} (h : Ad3.R.Reps ϖ B) (j : ℕ) :
    Q F ((j + 1 : ℕ) : ℤ) ⊆ ⋃ b ∈ B,
      (fun g => Ad3.uni2 (-((((unifUnit F) ^ (-((j + 1 : ℕ) : ℤ)) : Fˣ) : F) * b)) * g) ⁻¹' Q F j := by
  have hq : (residueCard F : ℝ) ≠ 0 := q_pos.ne'
  rintro g ⟨y, hy, κ, hκ, rfl⟩
  set k : ℤ := ((j + 1 : ℕ) : ℤ) with hk
  have hX := mem_integer_of_modulus_le k hy
  set X : F := (((unifUnit F) ^ k : Fˣ) : F) * y with hXdef
  obtain ⟨b, ⟨hb, hb2⟩, -⟩ := h.2.2 X hX
  have hϖ : modulus (ϖ : F) = (residueCard F : NNReal)⁻¹ := by
    rw [modulus, if_neg ϖ.ne_zero, h.1]
    simp
  have h1 := modulus_le_one_iff.mpr hb2
  rw [modulus_mul, Units.val_inv_eq_inv_val, modulus_inv, hϖ, inv_inv] at h1
  have h2 : (residueCard F : ℝ) * (modulus (X - b) : ℝ) ≤ 1 := by exact_mod_cast h1
  simp only [Set.mem_iUnion, Set.mem_preimage]
  refine ⟨b, hb, y - (((unifUnit F) ^ (-k) : Fˣ) : F) * b, ?_, κ, hκ, ?_⟩
  · have e : y - (((unifUnit F) ^ (-k) : Fˣ) : F) * b = (((unifUnit F) ^ (-k) : Fˣ) : F) * (X - b) := by
      rw [mul_sub, hXdef, ← mul_assoc, ← Units.val_mul, ← _root_.zpow_add]
      simp
    rw [e, modulus_mul, NNReal.coe_mul, modulus_unif_zpow, neg_neg, hk]
    push_cast
    rw [zpow_add₀ hq, zpow_one, mul_assoc]
    have hp : (0 : ℝ) ≤ (residueCard F : ℝ) ^ (j : ℤ) := zpow_nonneg q_pos.le _
    calc (residueCard F : ℝ) ^ (j : ℤ) * ((residueCard F : ℝ) * (modulus (X - b) : ℝ))
        ≤ (residueCard F : ℝ) ^ (j : ℤ) * 1 := mul_le_mul_of_nonneg_left h2 hp
      _ = (residueCard F : ℝ) ^ (j : ℤ) := mul_one _
  · rw [← mul_assoc, uni2_mul_uni2_eq_uni2_add]
    congr 2
    ring

theorem measure_Q_le (μ : Measure (GL (Fin 2) F)) [μ.IsMulLeftInvariant] (j : ℕ) :
    μ (Q F j) ≤ (residueCard F : ℝ≥0∞) ^ j * μ (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F)) := by
  obtain ⟨ϖ, B, hB⟩ := GlobalTheory.CompanionTheory.RankinStepC.reps_exists (F := F)
  induction j with
  | zero =>
    simpa using measure_mono (μ := μ) Q_zero_subset
  | succ j ih =>
    calc μ (Q F ((j + 1 : ℕ) : ℤ))
        ≤ μ (⋃ b ∈ B,
            (fun g => Ad3.uni2 (-((((unifUnit F) ^ (-((j + 1 : ℕ) : ℤ)) : Fˣ) : F) * b)) * g) ⁻¹' Q F j) :=
          measure_mono (Q_succ_subset hB j)
      _ ≤ ∑ b ∈ B, μ
            ((fun g => Ad3.uni2 (-((((unifUnit F) ^ (-((j + 1 : ℕ) : ℤ)) : Fˣ) : F) * b)) * g) ⁻¹' Q F j) :=
          measure_biUnion_finset_le _ _
      _ = (residueCard F : ℝ≥0∞) * μ (Q F j) := by
          simp only [measure_preimage_mul, Finset.sum_const, nsmul_eq_mul,
            GlobalTheory.CompanionTheory.RankinStepC.reps_card hB]
      _ ≤ (residueCard F : ℝ≥0∞) *
            ((residueCard F : ℝ≥0∞) ^ j * μ (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F))) := by
          gcongr
      _ = (residueCard F : ℝ≥0∞) ^ (j + 1) * μ (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F)) := by
          rw [pow_succ', mul_assoc]

theorem shell_subset (m n L : ℤ) :
    {g : GL (Fin 2) F | ∃ x : F, (modulus x : ℝ) ≤ (residueCard F : ℝ) ^ (L - m) ∧
      ∃ κ ∈ GLnLocal.integralGL F 2, g = Ad3.uni2 x * Ad3.dg2 (unifUnit F ^ m) (unifUnit F ^ n) * κ} ⊆
    (fun g => (Ad3.dg2 (unifUnit F ^ m) (unifUnit F ^ n))⁻¹ * g) ⁻¹' Q F (L - n) := by
  have hq : (residueCard F : ℝ) ≠ 0 := q_pos.ne'
  rintro g ⟨x, hx, κ, hκ, rfl⟩
  refine ⟨(((unifUnit F ^ m : Fˣ) : F))⁻¹ * ((unifUnit F ^ n : Fˣ) : F) * x, ?_, κ, hκ, ?_⟩
  · rw [modulus_mul, modulus_mul, modulus_inv, NNReal.coe_mul, NNReal.coe_mul, NNReal.coe_inv,
      modulus_unif_zpow, modulus_unif_zpow, ← _root_.zpow_neg, neg_neg, ← zpow_add₀ hq]
    have e : L - n = (m + -n) + (L - m) := by ring
    rw [e, zpow_add₀ hq (m + -n)]
    exact mul_le_mul_of_nonneg_left hx (zpow_nonneg q_pos.le _)
  · rw [unipotent_mul_torus_commute]
    simp [mul_assoc]

theorem shell_open_volume : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (μ : Measure (GL (Fin 2) F)) [μ.IsMulLeftInvariant] (m n L : ℤ), IsOpen {g : GL (Fin 2) F | ∃ x : F, (modulus x : ℝ) ≤ (residueCard F : ℝ) ^ (L - m) ∧ ∃ κ ∈ GLnLocal.integralGL F 2, g = Ad3.uni2 x * Ad3.dg2 (unifUnit F ^ m) (unifUnit F ^ n) * κ} ∧ (n ≤ L → μ {g : GL (Fin 2) F | ∃ x : F, (modulus x : ℝ) ≤ (residueCard F : ℝ) ^ (L - m) ∧ ∃ κ ∈ GLnLocal.integralGL F 2, g = Ad3.uni2 x * Ad3.dg2 (unifUnit F ^ m) (unifUnit F ^ n) * κ} ≤ ENNReal.ofReal ((residueCard F : ℝ) ^ (L - n)) * μ (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F))) := by
  intro F _ _ _ _ μ _ m n L
  constructor
  · have e : {g : GL (Fin 2) F | ∃ x : F, (modulus x : ℝ) ≤ (residueCard F : ℝ) ^ (L - m) ∧
        ∃ κ ∈ GLnLocal.integralGL F 2, g = Ad3.uni2 x * Ad3.dg2 (unifUnit F ^ m) (unifUnit F ^ n) * κ} =
        ⋃ x : {x : F // (modulus x : ℝ) ≤ (residueCard F : ℝ) ^ (L - m)},
          (Homeomorph.mulLeft (Ad3.uni2 x.1 * Ad3.dg2 (unifUnit F ^ m) (unifUnit F ^ n))) ''
            (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F)) := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, Homeomorph.coe_mulLeft,
        Subtype.exists, SetLike.mem_coe, exists_prop]
      constructor
      · rintro ⟨x, hx, κ, hκ, rfl⟩
        exact ⟨x, hx, κ, hκ, rfl⟩
      · rintro ⟨x, hx, κ, hκ, rfl⟩
        exact ⟨x, hx, κ, hκ, rfl⟩
    rw [e]
    exact isOpen_iUnion fun x =>
      (Homeomorph.mulLeft _).isOpenMap _ (GLnLocal.isOpen_integralGL F 2)
  · intro hnL
    obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 hnL)
    calc _ ≤ μ ((fun g => (Ad3.dg2 (unifUnit F ^ m) (unifUnit F ^ n))⁻¹ * g) ⁻¹' Q F (L - n)) :=
          measure_mono (shell_subset m n L)
      _ = μ (Q F (L - n)) := measure_preimage_mul μ _ _
      _ = μ (Q F j) := by rw [hj]
      _ ≤ _ := measure_Q_le μ j
      _ = _ := by
          rw [hj, zpow_natCast, ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

end GlobalTheory.CompanionTheory.IwasawaShell
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityOfEquivStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_multiplicity_of_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W), Nonempty (π.Equiv σ) → jm x hd π = jm x hd σ := by
  first | exact @GlobalTheory.CompanionTheory.JacquetCongr.jm_congr_of_equiv | exact GlobalTheory.CompanionTheory.JacquetCongr.jm_congr_of_equiv | (intros; apply GlobalTheory.CompanionTheory.JacquetCongr.jm_congr_of_equiv <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetQuotientEigenvectorStatement
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_quotient_eigenvector : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.Published.StandardFunctorsFiniteLength → ∀ (d : Fin 2 → ℕ) (hd : ∑ a, d a = N), 0 < d 0 → 0 < d 1 → ∀ (μ : ℂ) (w : V), (Submodule.Quotient.mk w : Jacquet π (unipRad k (stdBlocks d hd))) ≠ 0 → (Submodule.Quotient.mk (π (Zls.diagPow k N (Zls.omegaVec N (d 0))) w) : Jacquet π (unipRad k (stdBlocks d hd))) = μ • (Submodule.Quotient.mk w : Jacquet π (unipRad k (stdBlocks d hd))) → ∃ (x : Fin 2 → IrrGL k) (hx : ∑ a, (x a).1 = N), (∀ a, (x a).1 = d a) ∧ Zc.jm x hx π ≠ 0 ∧ Zl.ScalarBy (x 0) (Zls.unifU k) (μ * (Nat.card 𝓀[k] : ℂ) ^ (((d 0 * d 1 : ℕ) : ℂ) / 2)) ∧ ∃ c1 : ℂ, Zl.ScalarBy (x 1) (Zls.unifU k) c1 := by
  first | exact @GlobalTheory.CompanionTheory.JacExp.exists_constituent_of_eigen | exact GlobalTheory.CompanionTheory.JacExp.exists_constituent_of_eigen | (intros; apply GlobalTheory.CompanionTheory.JacExp.exists_constituent_of_eigen <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetSubLeftOfAdmissibleStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_sub_left_of_admissible : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → JacquetSubLeft k := by
  first | exact @GlobalTheory.CompanionTheory.JacquetLeft.jacquetSubLeft | exact GlobalTheory.CompanionTheory.JacquetLeft.jacquetSubLeft | (intros; apply GlobalTheory.CompanionTheory.JacquetLeft.jacquetSubLeft <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinedBlockFormula
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem jnBl : JnBl := by
  intro D n t a r hn w v y
  unfold jn PositivityTheory.Rg.Rsw.L.mm
  rw [show bl hn (1 : Mx D r r) y (0 : Mx D t r) (1 : Mx D t t) =
      (Matrix.fromBlocks (1 : Mx D r r) y (0 : Mx D t r) (1 : Mx D t t)).submatrix
        (finSumFinEquiv.trans (finCongr hn)).symm (finSumFinEquiv.trans (finCongr hn)).symm from rfl]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromBlocks]
  simp

end GlobalTheory.CompanionTheory.ColumnSplitting
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinedProjectionFormula
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.CompanionTheory.ColumnSplitting.JnM

variable {D : D7} {a b r t n : ℕ}

theorem fromCols_mul_shear {R : Type} [Ring R] (w : Matrix (Fin a) (Fin r) R) (v : Matrix (Fin a) (Fin t) R)
    (y : Matrix (Fin r) (Fin t) R) :
    (Matrix.fromCols w v : Matrix (Fin a) (Fin r ⊕ Fin t) R) *
        (Matrix.fromBlocks 1 y 0 1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R) =
      Matrix.fromCols w (w * y + v) := by
  ext i (k | k) <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem mm_jn (hn : r + t = n) (A : Mx D b a) (x : Mx D a r) (v : Mx D a t) :
    mm A (jn hn x v) = jn hn (mm A x) (mm A v) := by
  ext i j
  simp only [jn, mm, Matrix.submatrix_apply, id, Matrix.mul_apply]
  rcases h : (finSumFinEquiv.trans (finCongr hn)).symm j with k | k <;>
    simp [Matrix.mul_apply]

theorem jn_add (hn : r + t = n) (x x' : Mx D a r) (v v' : Mx D a t) :
    jn hn x v + jn hn x' v' = jn hn (x + x') (v + v') := by
  ext i j
  simp only [jn, Matrix.add_apply, Matrix.submatrix_apply, id]
  rcases h : (finSumFinEquiv.trans (finCongr hn)).symm j with k | k <;> simp

theorem jn_c {W : HSp D} (hn : W.rank + t = n) (U : Mx D a n) :
    jn hn (c1 hn U) (c2 hn U) = U := by
  ext i j
  obtain ⟨s, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective j
  rcases s with k | k <;> simp [jn, c1, c2]

theorem shear_gen {R : Type} [Ring R] (hn : r + t = n) (w : Matrix (Fin a) (Fin r) R)
    (v : Matrix (Fin a) (Fin t) R) (y : Matrix (Fin r) (Fin t) R) :
    ((Matrix.fromCols w v).submatrix id (finSumFinEquiv.trans (finCongr hn)).symm : Matrix (Fin a) (Fin n) R) *
        ((Matrix.fromBlocks 1 y 0 1).submatrix (finSumFinEquiv.trans (finCongr hn)).symm
          (finSumFinEquiv.trans (finCongr hn)).symm : Matrix (Fin n) (Fin n) R) =
      (Matrix.fromCols w (w * y + v)).submatrix id (finSumFinEquiv.trans (finCongr hn)).symm := by
  rw [Matrix.submatrix_mul_equiv, fromCols_mul_shear]

theorem jn_bl (hn : r + t = n) (w : Mx D a r) (v : Mx D a t) (y : Mx D r t) :
    mm (jn hn w v) (bl hn 1 y 0 1) = jn hn w (mm w y + v) :=
  shear_gen hn w v y

end GlobalTheory.CompanionTheory.ColumnSplitting.JnM

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem jnPi_holds : JnPi := by
  intro D n t B W d hn x₀ g p
  obtain ⟨h, U, y⟩ := p
  have hX : XU d hn x₀ h U =
      jn hn (mm d.jX (c1 hn U) + mm d.j0 (ww W x₀ h)) (mm d.jX (c2 hn U)) := by
    unfold XU
    conv_lhs => rw [← JnM.jn_c (W := W) hn U]
    have h0 : mm d.j0 (0 : Mx D W.rank t) = 0 := Matrix.mul_zero _
    rw [JnM.mm_jn, JnM.mm_jn, JnM.jn_add, h0, add_zero]
  simp only [hX, JnM.jn_bl, JnM.mm_jn]
  rfl

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsFactorsDualReverseOrderedStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.langlands_factors_dual_reverse_ordered : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LSegDual k → ∀ (𝔪 : Multiset (Segment k)) {h : ℕ} (x : Fin h → IrrGL k), LFactors 𝔪 x → ∃ Γ : Fin h → Segment k, IsRevOrdered Γ ∧ ∀ i, IsLSeg (Γ i) (dualCl (x i)).rep := by
  first | exact @GlobalTheory.CompanionTheory.DualForms.exists_revOrdered_dual | exact GlobalTheory.CompanionTheory.DualForms.exists_revOrdered_dual | (intros; apply GlobalTheory.CompanionTheory.DualForms.exists_revOrdered_dual <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeCharacterIntegralValue
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom

noncomputable section

namespace GlobalTheory.CompanionTheory.LFUDom

theorem latchar1 : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), Ad3.IsStd ψ → ∀ A : GL (Fin 2) F,
  (∀ b, ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 b ∈ 𝒪[F]) →
  ∫ x, Set.indicator {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]} (fun x : Fin 2 → F => ((ψ (-x 1) : Circle) : ℂ)) x ∂Ad3.LFS.vol2 ψ =
    (((Ad3.LFS.vol2 ψ).real {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]} : ℝ) : ℂ) := by
  intro F _ _ _ _ _ _ ψ hψ A hA
  obtain ⟨hc, h1, h0⟩ := hψ
  have ht := isTrivialOn_addCharConductor hc h1
  rw [h0] at ht
  have hopen : IsOpen {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]} := by
    have hs : {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]} =
        ⋂ i, (fun x : Fin 2 → F => ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i) ⁻¹'
          (valBall F 0 : Set F) := by
      ext x
      simp [mem_valBall_zero_iff]
    rw [hs]
    refine isOpen_iInter_of_finite fun i => (isOpen_valBall _).preimage ?_
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    fun_prop
  have hf : Set.indicator {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]}
        (fun x : Fin 2 → F => ((ψ (-x 1) : Circle) : ℂ)) =
      Set.indicator {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]}
        (fun _ => (1 : ℂ)) := by
    refine Set.indicator_congr fun x hx => ?_
    have hx1 : x 1 = (((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ
        ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x)) 1 := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    have hint : x 1 ∈ 𝒪[F] := by
      have key : ∀ y : Fin 2 → F, (∀ i, y i ∈ 𝒪[F]) →
          (((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ y) 1 ∈ 𝒪[F] := fun y hy => by
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        exact add_mem (mul_mem (hA 0) (hy 0)) (mul_mem (hA 1) (hy 1))
      rw [hx1]
      exact key _ hx
    have hb : -x 1 ∈ valBall F 0 := mem_valBall_zero_iff.2 (neg_mem hint)
    rw [ht _ hb]
    simp
  rw [hf, integral_indicator_const _ hopen.measurableSet]
  simp

end GlobalTheory.CompanionTheory.LFUDom
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeCharacterIntegralZero
section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom

namespace GlobalTheory.CompanionTheory.LFUDom.LatChar

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem exists_psi_ne_one {ψ : AddChar F Circle} (hψ : Ad3.IsStd ψ) :
    ∃ w : F, w ≠ 0 ∧ -1 ≤ ord w ∧ ψ w ≠ 1 := by
  obtain ⟨hc, h1, h0⟩ := hψ
  have h := not_isTrivialOn_addCharConductor_sub_one hc h1
  rw [h0] at h
  simp only [IsTrivialOn, not_forall] at h
  obtain ⟨y, hy, hne⟩ := h
  have y0 : y ≠ 0 := by
    rintro rfl
    simp at hne
  exact ⟨y, y0, by simpa using (mem_valBall_iff_le_ord y0).1 hy, hne⟩

theorem mem_integers_iff {x : F} (hx : x ≠ 0) : x ∈ 𝒪[F] ↔ 0 ≤ ord x := by
  rw [← mem_valBall_iff_le_ord hx, mem_valBall_zero_iff]

theorem exists_lattice_witness {ψ : AddChar F Circle} (hψ : Ad3.IsStd ψ) (A : GL (Fin 2) F)
    (hA : ¬ ∀ b, ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 b ∈ 𝒪[F]) :
    ∃ y : Fin 2 → F, (∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ y) i ∈ 𝒪[F]) ∧ ψ (-y 1) ≠ 1 := by
  obtain ⟨w, w0, hw, hne⟩ := exists_psi_ne_one hψ
  simp only [not_forall] at hA
  obtain ⟨b, hb⟩ := hA
  set e := ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 b with he
  have e0 : e ≠ 0 := fun h => hb (h ▸ zero_mem _)
  have hord : ord e < 0 := by
    by_contra hc
    exact hb ((mem_integers_iff e0).2 (not_lt.1 hc))
  have ei : e⁻¹ ≠ 0 := inv_ne_zero e0
  have ht : -w * e⁻¹ ∈ 𝒪[F] := by
    have nw : -w ≠ 0 := neg_ne_zero.2 w0
    have hnw : ord (-w) = ord w := by simp [ord, Valuation.map_neg]
    refine (mem_integers_iff (mul_ne_zero nw ei)).2 ?_
    rw [ord_mul nw ei, ord_inv e0, hnw]
    omega
  refine ⟨((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ Pi.single b (-w * e⁻¹), ?_, ?_⟩
  · intro i
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    by_cases hi : i = b
    · subst hi; simpa using ht
    · simp [Pi.single_eq_of_ne hi, zero_mem]
  · have : (((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ Pi.single b (-w * e⁻¹)) 1 = -w := by
      have hg : ∀ (M : Matrix (Fin 2) (Fin 2) F) (t : F), (M *ᵥ Pi.single b t) 1 = M 1 b * t := by
        intro M t
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [hg, ← he]
      field_simp
    rw [this, neg_neg]
    exact hne

end GlobalTheory.CompanionTheory.LFUDom.LatChar

open GlobalTheory.CompanionTheory.LFUDom.LatChar in

theorem GlobalTheory.CompanionTheory.LFUDom.integral_lattice_char_eq_zero
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle) (hψ : Ad3.IsStd ψ) (A : GL (Fin 2) F)
    (hA : ¬ ∀ b, ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 b ∈ 𝒪[F]) :
    ∫ x, Set.indicator {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]}
      (fun x : Fin 2 → F => ((ψ (-x 1) : Circle) : ℂ)) x ∂Ad3.LFS.vol2 ψ = 0 := by
  obtain ⟨y, hy, hne⟩ := exists_lattice_witness hψ A hA
  have hv : (Ad3.LFS.vol2 ψ).IsAddHaarMeasure := by unfold Ad3.LFS.vol2; infer_instance
  set S := {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]} with hS
  set g : (Fin 2 → F) → ℂ := S.indicator (fun x : Fin 2 → F => ((ψ (-x 1) : Circle) : ℂ)) with hg
  have hmem : ∀ x, x + y ∈ S ↔ x ∈ S := by
    intro x
    simp only [hS, Set.mem_setOf_eq, Matrix.mulVec_add, Pi.add_apply]
    refine forall_congr' fun i => ?_
    constructor
    · intro h
      simpa using sub_mem h (hy i)
    · intro h
      exact add_mem h (hy i)
  have hshift : ∀ x, g (x + y) = ((ψ (-y 1) : Circle) : ℂ) * g x := by
    intro x
    by_cases hx : x ∈ S
    · rw [hg, Set.indicator_of_mem ((hmem x).2 hx), Set.indicator_of_mem hx, Pi.add_apply,
        neg_add, AddChar.map_add_eq_mul, Circle.coe_mul, mul_comm]
    · rw [hg, Set.indicator_of_notMem (fun h => hx ((hmem x).1 h)), Set.indicator_of_notMem hx,
        mul_zero]
  have h := integral_add_right_eq_self (μ := Ad3.LFS.vol2 ψ) g y
  simp only [hshift, integral_const_mul] at h
  have hc : ((ψ (-y 1) : Circle) : ℂ) ≠ 1 := fun h1 => hne (Circle.ext (by simpa using h1))
  have : (((ψ (-y 1) : Circle) : ℂ) - 1) * ∫ x, g x ∂Ad3.LFS.vol2 ψ = 0 := by
    rw [sub_mul, one_mul, h, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hc)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviMinimalIdeleHermitianBoundStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_minimal_idele_hermitian_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ m ∈ leviMin σ J X Y, m ∈ minParOne σ J X → ∀ j, ∃ s : GroundTheory.Global.IdeleGroup F, 1 ≤ (GroundTheory.Global.IdeleGroup.ideleModule F s : ℝ) ∧ ∀ ξ : Fin n → E, hR (AF F) σ (hermFam σ J X Y j) ((matHom _ σ J m⁻¹).1 *ᵥ ratV F ξ) ((matHom _ σ J m⁻¹).1 *ᵥ ratV F ξ) = algebraMap (AF F) (AF F ⊗[F] E) (s : AF F) * inclR (F := F) (AF F) (hE σ (hermFam σ J X Y j) ξ ξ) := by
  first | exact @GlobalTheory.CompanionTheory.ParCocompact.hermFam_levi_scale | exact GlobalTheory.CompanionTheory.ParCocompact.hermFam_levi_scale | (intros; apply GlobalTheory.CompanionTheory.ParCocompact.hermFam_levi_scale <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitListsStatement
section
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limit_lists : GlobalTheory.CompanionTheory.EGlue.ConvStrip → GlobalTheory.CompanionTheory.EGlue.ConvShift → GlobalTheory.CompanionTheory.EGlue.ConvComp → GlobalTheory.CompanionTheory.EGlue.LimLists := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.limLists | exact GlobalTheory.CompanionTheory.EGlue.limLists | (intros; apply GlobalTheory.CompanionTheory.EGlue.limLists <;> assumption)
end

