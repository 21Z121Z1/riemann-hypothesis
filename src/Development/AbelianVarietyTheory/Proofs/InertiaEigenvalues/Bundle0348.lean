import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0003
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0330
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0081
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0029
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0326
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0328
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BezoutEisensteinDerivativePrimePow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem bezout_Ep_derivative : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ (c : ℕ) (a b : Polynomial (Wq l bk.a)),
    a * bk.Ep + b * Polynomial.derivative bk.Ep = Polynomial.C ((l : Wq l bk.a) ^ c) := by
  intro l _ K bk
  haveI : CharZero (Wq l bk.a) := GlobalTheory.charZero_wittVector_of_field l (Fq l bk.a)
  have hirr : Irreducible (l : Wq l bk.a) := WittVector.irreducible l (k := Fq l bk.a)
  have hprime : Prime (l : Wq l bk.a) := hirr.prime
  have hP : (Ideal.span {(l : Wq l bk.a)}).IsPrime := (Ideal.span_singleton_prime hprime.ne_zero).2 hprime
  have hE : bk.Ep.IsEisensteinAt (Ideal.span {(l : Wq l bk.a)}) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [bk.monic.leadingCoeff, Ideal.mem_span_singleton]
      exact fun h => hirr.not_isUnit (isUnit_of_dvd_one h)
    · intro n hn
      exact Ideal.mem_span_singleton.2 (bk.dvd_coeff n hn)
    · obtain ⟨w, hw⟩ := bk.coeff_zero
      rw [hw, Ideal.span_singleton_pow, Ideal.mem_span_singleton, pow_two]
      intro h
      have h2 : (l : Wq l bk.a) ∣ (w : Wq l bk.a) := (mul_dvd_mul_iff_left hprime.ne_zero).1 h
      exact hirr.not_isUnit (isUnit_of_dvd_unit h2 w.isUnit)
  have hirrE : Irreducible bk.Ep := hE.irreducible hP bk.monic.isPrimitive bk.deg_pos
  let F := FractionRing (Wq l bk.a)
  haveI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective (Wq l bk.a) F)
  have hirrF : Irreducible (bk.Ep.map (algebraMap (Wq l bk.a) F)) :=
    (bk.monic.irreducible_iff_irreducible_map_fraction_map).1 hirrE
  obtain ⟨a, b, hab⟩ := hirrF.separable
  rw [Polynomial.derivative_map] at hab
  obtain ⟨⟨d₁, hd₁⟩, hA⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors (Wq l bk.a)) a
  obtain ⟨⟨d₂, hd₂⟩, hB⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors (Wq l bk.a)) b
  set A := IsLocalization.integerNormalization (nonZeroDivisors (Wq l bk.a)) a
  set B := IsLocalization.integerNormalization (nonZeroDivisors (Wq l bk.a)) b
  have hd : d₁ * d₂ ≠ 0 := mul_ne_zero (nonZeroDivisors.ne_zero hd₁) (nonZeroDivisors.ne_zero hd₂)
  have key : Polynomial.C d₂ * A * bk.Ep + Polynomial.C d₁ * B * Polynomial.derivative bk.Ep =
      Polynomial.C (d₁ * d₂) := by
    apply Polynomial.map_injective (algebraMap (Wq l bk.a) F) (IsFractionRing.injective (Wq l bk.a) F)
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hA, hB, Polynomial.derivative_map]
    simp only [Algebra.smul_def, Polynomial.algebraMap_apply, map_mul, Polynomial.C_mul]
    linear_combination (Polynomial.C (algebraMap (Wq l bk.a) F d₁) * Polynomial.C (algebraMap (Wq l bk.a) F d₂)) * hab
  obtain ⟨m, u, hu⟩ := WittVector.exists_eq_pow_p_mul' (p := l) (k := Fq l bk.a) (d₁ * d₂) hd
  refine ⟨m, Polynomial.C ((↑u⁻¹ : Wq l bk.a) * d₂) * A, Polynomial.C ((↑u⁻¹ : Wq l bk.a) * d₁) * B, ?_⟩
  have : Polynomial.C ((l : Wq l bk.a) ^ m) = Polynomial.C (↑u⁻¹ : Wq l bk.a) * Polynomial.C (d₁ * d₂) := by
    rw [hu, ← Polynomial.C_mul]
    congr 1
    rw [mul_comm, mul_assoc, Units.mul_inv, mul_one]
  rw [this, ← key]
  simp only [Polynomial.C_mul]
  ring

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimOfQlDimensionFormula
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.BkCoeff

open GlobalTheory.PstCoeff

theorem isModuleTopology_of_tower (R LL V : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Field LL] [Algebra R LL] [TopologicalSpace LL] [IsTopologicalRing LL] [IsModuleTopology R LL]
    [AddCommGroup V] [Module LL V] [Module R V] [IsScalarTower R LL V] [FiniteDimensional LL V]
    [TopologicalSpace V] [IsModuleTopology LL V] : IsModuleTopology R V := by
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd LL V
  let e : V ≃ₗ[LL] (Fin (finrank LL V) → LL) := (Module.finBasis LL V).equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let e' : (Fin (finrank LL V) → LL) ≃L[R] V :=
    { e.symm.restrictScalars R with continuous_toFun := h2, continuous_invFun := h1 }
  exact IsModuleTopology.iso e'

section Coeff

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l}
  {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
  (ρ : Representation LL ↥(GK K) V)

theorem actVB_resQ (g : ↥(GK K)) (x : V ⊗[ℚ_[l]] P.R.B) :
    actVB (P.PD K) (resQ ρ) g x = actVB (P.PD K) ρ g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem galoisInvariants_restrictScalarsToQl : H0V (resQ ρ) = (H0V ρ).restrictScalars ℚ_[l] := by
  ext x
  simp [H0V, Submodule.mem_iInf, sub_eq_zero]

theorem FilV_resQ (a : ℤ) :
    FilV (P.PD K) (LL := ℚ_[l]) (V := V) a = (FilV (P.PD K) (LL := LL) (V := V) a).restrictScalars ℚ_[l] := by
  have h : ∀ y, AlgebraTensorModule.map (LinearMap.id : V →ₗ[ℚ_[l]] V)
      (((P.PD K).Fil a).restrictScalars ℚ_[l]).subtype y =
      AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (((P.PD K).Fil a).restrictScalars ℚ_[l]).subtype y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  ext x
  simp only [FilV, Submodule.restrictScalars_mem, LinearMap.mem_range, h]

variable [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] [ContinuousConstSMul ℚ_[l] V]

theorem mem_finiteCocycles_restrictScalars_Ql (c : ↥(GK K) → V) : c ∈ finiteCocycles (P.PD K) (resQ ρ) ↔ c ∈ finiteCocycles (P.PD K) ρ := by
  show (c ∈ continuousCocycles (resQ ρ) ∧ ∃ x, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) (resQ ρ) g x - x) ↔
    (c ∈ continuousCocycles ρ ∧ ∃ x, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) ρ g x - x)
  simp only [actVB_resQ]
  exact Iff.rfl

def finiteCocyclesResEquiv : ↥(finiteCocycles (P.PD K) (resQ ρ)) ≃ₗ[ℚ_[l]] ↥(finiteCocycles (P.PD K) ρ) where
  toFun x := ⟨x.1, (mem_finiteCocycles_restrictScalars_Ql P ρ x.1).mp x.2⟩
  invFun x := ⟨x.1, (mem_finiteCocycles_restrictScalars_Ql P ρ x.1).mpr x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def h1fEquiv : FiniteCohomology (P.PD K) (resQ ρ) ≃ₗ[ℚ_[l]] FiniteCohomology (P.PD K) ρ :=
  (Submodule.Quotient.equiv _ (((B1 ρ).comap (finiteCocycles (P.PD K) ρ).subtype).restrictScalars ℚ_[l]) (finiteCocyclesResEquiv P ρ) (by
    rw [Submodule.map_equiv_eq_comap_symm]
    ext x
    exact Iff.rfl)).trans (Submodule.Quotient.restrictScalarsEquiv ℚ_[l] _)

end Coeff

end GlobalTheory.BkCoeff

namespace GlobalTheory

open GlobalTheory.PstCoeff GlobalTheory.BkCoeff

theorem bkADim_of_dimFormula : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l),
    GlobalTheory.Published.BlochKato.DimFormula (P.PD K) → Formalism.MainNotions.LocalSituation.bkADim (P.PD K) := by
  intro l _ P K hD LL _ _ _ O _ _ hO A hdR
  obtain ⟨-, hfin, hmt, htr, -⟩ := hO
  haveI := hfin
  haveI := hmt
  haveI := htr
  haveI : FiniteDimensional ℚ_[l] A.V := Module.Finite.trans LL A.V
  haveI : IsModuleTopology ℚ_[l] A.V := isModuleTopology_of_tower ℚ_[l] LL A.V
  obtain ⟨-, he⟩ := hD A.V (resQ (LL := LL) A.ρ) A.cont ((isDR_resQ_iff P A.ρ).mpr hdR)
  have hH1 : finrank ℚ_[l] (FiniteCohomology (P.PD K) (resQ A.ρ)) = finrank ℚ_[l] LL * finrank LL (FiniteCohomology (P.PD K) A.ρ) := by
    rw [(h1fEquiv P A.ρ).finrank_eq, finrank_mul_finrank]
  have hH0 : finrank ℚ_[l] ↥(H0V (resQ A.ρ)) = finrank ℚ_[l] LL * finrank LL ↥(H0V A.ρ) := by
    rw [galoisInvariants_restrictScalarsToQl, finrank_mul_finrank]
    rfl
  have hdR' : finrank ℚ_[l] ↥(DdR (P.PD K) (resQ A.ρ)) = finrank ℚ_[l] LL * finrank LL ↥(DdR (P.PD K) A.ρ) := by
    rw [DdR_resQ, finrank_mul_finrank]
    rfl
  have hF : finrank ℚ_[l] ↥(DdR (P.PD K) (resQ A.ρ) ⊓ FilV (P.PD K) (LL := ℚ_[l]) (V := A.V) 0) =
      finrank ℚ_[l] LL * finrank LL ↥(DdR (P.PD K) A.ρ ⊓ FilV (P.PD K) (LL := LL) (V := A.V) 0) := by
    rw [DdR_resQ, FilV_resQ P (LL := LL), ← Submodule.restrictScalars_inf, finrank_mul_finrank]
    rfl
  rw [hH1, hH0, hdR', hF] at he
  push_cast at he
  have hd : (finrank ℚ_[l] LL : ℤ) ≠ 0 := by exact_mod_cast (Module.finrank_pos (R := ℚ_[l]) (M := LL)).ne'
  refine mul_left_cancel₀ hd ?_
  rw [he]
  ring

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockTriangularExtensionCocycleTrivialDeRham
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.PMon.extCoc_dies_in_BdR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K : FinExt l) (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) → AdmDR P ρ → AdmDR P ρ₂ → ∀ m : ℕ, ∃ v : a × b → P.R.BdR, ∀ g : ↥(GK K), (fun i => kd P (fr l m (extCoc ρ₂ c g i))) = (matD P (homRep ρ₁ ρ₂) m g).mulVec (fun i => P.actQdR (g : GQ l) (v i)) - v := by
  intro l _ P AI T a b _ _ _ _ K ρ ρ₁ ρ₂ c hρ hQ hR m
  obtain ⟨Q, hQm⟩ := hQ m
  obtain ⟨R, hRm⟩ := hR m
  let f : ↥(MaximalUnramifiedExtension l) →+* P.R.BdR := (kd P).comp (fr l m)
  let σ : ↥(GK K) → P.R.BdR →+* P.R.BdR := fun g => ((P.actQdR (g : GQ l) : P.R.BdR ≃ₐ[ℚ_[l]] P.R.BdR) : P.R.BdR →+* P.R.BdR)

  let A : ↥(GK K) → Matrix a a P.R.BdR := fun g => (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)).map f
  let C : ↥(GK K) → Matrix a b P.R.BdR := fun g => (c g).map f
  let D : ↥(GK K) → Matrix b b P.R.BdR := fun g => (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l)).map f
  let Di : ↥(GK K) → Matrix b b P.R.BdR := fun g => (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l)).map f
  have hDDi : ∀ g, D g * Di g = 1 := fun g => by
    simp only [D, Di]
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero f) (map_one f)]
  have hDiD : ∀ g, Di g * D g = 1 := fun g => by
    simp only [D, Di]
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero f) (map_one f)]
  have hM : ∀ g, matD P ρ m g = Matrix.fromBlocks (A g) (C g) 0 (D g) := fun g => by
    show (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)).map f = _
    rw [hρ g, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero f)]
  let Qa : Matrix a (a ⊕ b) P.R.BdR := (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix Sum.inl id
  let Qb : Matrix b (a ⊕ b) P.R.BdR := (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix Sum.inr id
  have hb : ∀ g, D g * Qb.map (σ g) = Qb := fun g => by
    ext i j
    have h := congrFun (congrFun (hQm g) (Sum.inr i)) j
    rw [hM g] at h
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, Qb, σ] using h
  have ha : ∀ g, A g * Qa.map (σ g) + C g * Qb.map (σ g) = Qa := fun g => by
    ext i j
    have h := congrFun (congrFun (hQm g) (Sum.inl i)) j
    rw [hM g] at h
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, Qa, Qb, σ] using h
  have hRg : ∀ g, D g * (R : Matrix b b P.R.BdR).map (σ g) = R := fun g => hRm g
  let S : Matrix b b P.R.BdR := ((R⁻¹ : GL b P.R.BdR) : Matrix b b P.R.BdR)
  have hSR : S * R = 1 := by simp only [S]; rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hRS : (R : Matrix b b P.R.BdR) * S = 1 := by simp only [S]; rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hgSR : ∀ g, S.map (σ g) * (R : Matrix b b P.R.BdR).map (σ g) = 1 := fun g => by
    rw [← Matrix.map_mul, hSR, Matrix.map_one _ (map_zero _) (map_one _)]
  have hgRS : ∀ g, (R : Matrix b b P.R.BdR).map (σ g) * S.map (σ g) = 1 := fun g => by
    rw [← Matrix.map_mul, hRS, Matrix.map_one _ (map_zero _) (map_one _)]
  have hgS : ∀ g, S.map (σ g) = S * D g := fun g => by
    calc S.map (σ g) = (S * (D g * (R : Matrix b b P.R.BdR).map (σ g))) * S.map (σ g) := by
          rw [hRg g, hSR, Matrix.one_mul]
      _ = S * D g * ((R : Matrix b b P.R.BdR).map (σ g) * S.map (σ g)) := by
          simp only [Matrix.mul_assoc]
      _ = S * D g := by rw [hgRS g, Matrix.mul_one]
  have hgR : ∀ g, (R : Matrix b b P.R.BdR).map (σ g) = Di g * R := fun g => by
    symm
    conv_lhs => rw [← hRg g]
    rw [← Matrix.mul_assoc, hDiD g, Matrix.one_mul]
  obtain ⟨κ, hκdef⟩ : ∃ κ : Matrix b (a ⊕ b) P.R.BdR, κ = S * Qb := ⟨_, rfl⟩
  have hκ : ∀ g, κ.map (σ g) = κ := fun g => by
    rw [hκdef, Matrix.map_mul, hgS g, Matrix.mul_assoc, hb g]
  let Y : Matrix (a ⊕ b) b P.R.BdR :=
    (((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix id Sum.inr) * (R : Matrix b b P.R.BdR)
  have hQQ : (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) * ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hQb : Qb * (((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix id Sum.inr) = 1 := by
    ext i j
    have h := congrFun (congrFun hQQ (Sum.inr i)) (Sum.inr j)
    simpa [Matrix.mul_apply, Matrix.one_apply, Qb] using h
  have hY : κ * Y = 1 := by
    simp only [Y]
    rw [hκdef, Matrix.mul_assoc, ← Matrix.mul_assoc Qb, hQb, Matrix.one_mul, hSR]
  obtain ⟨Λ, hκΛ, hΛ⟩ := GlobalTheory.T.exists_invariant_right_inverse P.R.BdR (GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T).1 (↥(GK K)) σ (a ⊕ b) b κ Y hY hκ
  have hQbR : Qb = (R : Matrix b b P.R.BdR) * κ := by
    rw [hκdef, ← Matrix.mul_assoc, hRS, Matrix.one_mul]
  have hgQb : ∀ g, Qb.map (σ g) = (R : Matrix b b P.R.BdR).map (σ g) * κ := fun g => by
    conv_lhs => rw [hQbR]
    rw [Matrix.map_mul, hκ g]
  let Z : Matrix a b P.R.BdR := Qa * Λ
  have hAZ : ∀ g, A g * Z.map (σ g) = Z - C g * (R : Matrix b b P.R.BdR).map (σ g) := fun g => by
    have e : A g * Qa.map (σ g) = Qa - C g * ((R : Matrix b b P.R.BdR).map (σ g) * κ) := by
      rw [← hgQb g]
      exact eq_sub_of_add_eq (ha g)
    simp only [Z]
    rw [Matrix.map_mul, hΛ g, ← Matrix.mul_assoc, e, Matrix.sub_mul, Matrix.mul_assoc (C g),
      Matrix.mul_assoc ((R : Matrix b b P.R.BdR).map (σ g)), hκΛ, Matrix.mul_one]
  refine ⟨vecM (-(Z * S)), fun g => ?_⟩
  have hL : (fun i => kd P (fr l m (extCoc ρ₂ c g i))) = vecM (C g * Di g) := by
    show vecM ((c g * (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l))).map f) = _
    rw [Matrix.map_mul]
  have hR' : (matD P (homRep ρ₁ ρ₂) m g).mulVec (fun i => P.actQdR (g : GQ l) (vecM (-(Z * S)) i)) =
      vecM (A g * (-(Z * S)).map (σ g) * Di g) := by
    show (((homUnit (ρ₁ g) (ρ₂ g) : GL (a × b) ↥(MaximalUnramifiedExtension l)) : Matrix (a × b) (a × b) ↥(MaximalUnramifiedExtension l)).map f).mulVec
      (vecM ((-(Z * S)).map (σ g))) = _
    rw [homUnit_mulVec]
  rw [hL, hR']
  have hsub : ∀ X Y : Matrix a b P.R.BdR, vecM X - vecM Y = vecM (X - Y) := fun _ _ => rfl
  rw [hsub]
  congr 1
  have hneg : (-(Z * S)).map (σ g) = -(Z.map (σ g) * S.map (σ g)) := by
    rw [Matrix.map_neg _ (map_neg (σ g)), Matrix.map_mul]
  rw [hneg, hgS g, Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc (A g), hAZ g, hgR g]
  simp only [Matrix.sub_mul, Matrix.mul_assoc, hDDi g, hRS, Matrix.mul_one]
  abel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEisensteinImageTeichmullerPow
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.EisImage

theorem isUnit_of_constantCoeff {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [CharP O l] [PerfectRing O l]
    (c : WittVector l O) (h : IsUnit (WittVector.constantCoeff c)) : IsUnit c := by
  obtain ⟨u, hu⟩ := h
  have h1 : c * WittVector.teichmuller l ((u⁻¹ : Oˣ) : O) - 1 ∈ Ideal.span {(l : WittVector l O)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_mul, map_one, ← hu,
      WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, Units.mul_inv, sub_self]
  have h2 := IsAdicComplete.le_jacobson_bot (Ideal.span {(l : WittVector l O)}) h1
  have h3 := Ideal.isUnit_of_sub_one_mem_jacobson_bot _ h2
  exact isUnit_of_mul_isUnit_left h3

theorem exists_eq {R : Type} [CommRing R] (l : R) (P : Polynomial R) (hm : P.Monic) (hd : 0 < P.natDegree)
    (hc : ∀ i < P.natDegree, l ∣ P.coeff i) (w : R) (h0 : P.coeff 0 = l * w) :
    ∃ G : Polynomial R, P = Polynomial.X ^ P.natDegree +
      Polynomial.C l * (Polynomial.C w + Polynomial.X * G) := by
  have h1 : Polynomial.C l ∣ (P - Polynomial.X ^ P.natDegree).divX := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    rw [Polynomial.coeff_divX, Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    rcases lt_trichotomy (i + 1) P.natDegree with h | h | h
    · rw [if_neg h.ne, sub_zero]
      exact hc _ h
    · rw [if_pos h, h, hm.coeff_natDegree, sub_self]
      exact dvd_zero _
    · rw [if_neg h.ne', sub_zero, Polynomial.coeff_eq_zero_of_natDegree_lt h]
      exact dvd_zero _
  obtain ⟨G, hG⟩ := h1
  refine ⟨G, ?_⟩
  have h2 := Polynomial.X_mul_divX_add (P - Polynomial.X ^ P.natDegree)
  rw [hG, Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_neg hd.ne, sub_zero, h0, map_mul] at h2
  linear_combination -h2

theorem map_E_eq : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (O : Type) [CommRing O] [IsLocalRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O), ¬ IsUnit (ψ bk.flat) → ∃ w : WittVector l O, IsUnit w ∧ WittVector.map ψ (bk.ev bk.E) = WittVector.teichmuller l (ψ bk.flat) ^ bk.Ep.natDegree + ((l : ℕ) : WittVector l O) * w := by
  intro l _ K bk O _ _ _ _ ψ hψ
  obtain ⟨w₀, hw₀⟩ := bk.coeff_zero
  obtain ⟨G, hG⟩ := exists_eq (l : Wq l bk.a) bk.Ep bk.monic bk.deg_pos bk.dvd_coeff w₀ hw₀
  let f : Polynomial (Wq l bk.a) →+* WittVector l O :=
    (WittVector.map ψ).comp (bk.ev.comp (Polynomial.coeToPowerSeries.ringHom))
  have hX : f Polynomial.X = WittVector.teichmuller l (ψ bk.flat) := by
    change WittVector.map ψ (bk.ev ((Polynomial.X : Polynomial (Wq l bk.a)) : (Wq l bk.a)⟦X⟧)) = _
    rw [Polynomial.coe_X, bk.ev_X, WittVector.map_teichmuller]
  refine ⟨f (Polynomial.C (w₀ : Wq l bk.a) + Polynomial.X * G), ?_, ?_⟩
  · apply isUnit_of_constantCoeff
    have hu : IsUnit (WittVector.constantCoeff (f (Polynomial.C (w₀ : Wq l bk.a)))) :=
      ((w₀.isUnit.map Polynomial.C).map f).map _
    rw [map_add, map_mul, hX, map_add, map_mul, WittVector.constantCoeff_apply (WittVector.teichmuller l _),
      WittVector.teichmuller_coeff_zero]
    by_contra hn
    have h1 : ψ bk.flat * WittVector.constantCoeff (f G) ∈ IsLocalRing.maximalIdeal O :=
      Ideal.mul_mem_right _ _ hψ
    have h2 := Ideal.sub_mem _ (show _ ∈ IsLocalRing.maximalIdeal O from hn) h1
    rw [add_sub_cancel_right] at h2
    exact h2 hu
  · have h1 := congrArg f hG
    rw [map_add, map_pow, hX, map_mul, map_natCast Polynomial.C, map_natCast f] at h1
    exact h1

end GlobalTheory.BSP.EisImage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEvWIsUnitInjectiveDvd
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.BK

section Red

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K)

def evRed : bk.S →+* OCb l := (WittVector.constantCoeff (p := l) (R := OCb l)).comp bk.ev

theorem evRed_X : bk.evRed X = bk.flat := by
  simp [evRed, bk.ev_X, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]

theorem flat_ne_zero : bk.flat ≠ 0 := by
  intro h0
  have hX : bk.ev X = 0 := by rw [bk.ev_X, h0]; exact WittVector.teichmuller_zero l
  obtain ⟨w, hw⟩ := bk.coeff_zero
  have hE : bk.ev bk.E = (l : Ainf l) * wA l bk.a (w : Wq l bk.a) := by
    conv_lhs => rw [eq_X_mul_shift_add_const bk.E]
    rw [map_add, map_mul, hX, zero_mul, zero_add, bk.ev_C, Polynomial.constantCoeff_coe, hw, map_mul,
      map_natCast]
  have hl' : (l : Ainf l) ∈ RingHom.ker (Per.θ l) := by
    rw [← bk.span_ev, hE, Ideal.span_singleton_mul_right_unit ((w.isUnit).map (wA l bk.a))]
    exact Ideal.mem_span_singleton_self _
  rw [RingHom.mem_ker, map_natCast] at hl'
  exact Nat.cast_ne_zero.2 hl.out.ne_zero hl'

theorem dvd_of_evRed_eq_zero (x : bk.S) (hx : bk.evRed x = 0) : (l : bk.S) ∣ x := by
  set r := WittVector.constantCoeff (p := l) (R := Fq l bk.a) with hr
  by_cases h : PowerSeries.map r x = 0
  · exact dvd_of_map_eq_zero l bk.a x h
  exfalso
  set xb := PowerSeries.map r x with hxb
  set m := xb.order.toNat
  set vb := divXPowOrder xb
  have hvb : constantCoeff vb ≠ 0 := fun h' => h (constantCoeff_divXPowOrder_eq_zero_iff.1 h')
  let v : bk.S := PowerSeries.mk fun n => WittVector.teichmuller l (coeff n vb)
  have hv : PowerSeries.map r v = vb := by
    ext n
    simp [v, hr, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
  have hvu : IsUnit v := by
    rw [isUnit_iff_constantCoeff]
    have : constantCoeff v = WittVector.teichmuller l (constantCoeff vb) := by
      simp [v, ← coeff_zero_eq_constantCoeff]
    rw [this]
    exact (Ne.isUnit hvb).map _
  obtain ⟨y, hy⟩ := dvd_of_map_eq_zero l bk.a (x - X ^ m * v) (by
    rw [map_sub, map_mul, map_pow, PowerSeries.map_X, hv, X_pow_order_mul_divXPowOrder, sub_self])
  have h1 : bk.evRed x = bk.flat ^ m * bk.evRed v := by
    have : x = X ^ m * v + (l : bk.S) * y := by linear_combination hy
    rw [this, map_add, map_mul, map_mul, map_pow, evRed_X, map_natCast, CharP.cast_eq_zero, zero_mul, add_zero]
  rw [hx] at h1
  exact mul_ne_zero (pow_ne_zero _ bk.flat_ne_zero) (hvu.map bk.evRed).ne_zero h1.symm

theorem dvd_of_dvd_ev (x : bk.S) (h : (l : Ainf l) ∣ bk.ev x) : (l : bk.S) ∣ x := by
  apply bk.dvd_of_evRed_eq_zero
  obtain ⟨z, hz⟩ := h
  simp only [evRed, RingHom.comp_apply, hz, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

theorem eq_zero_of_forall_pow_dvd (w : Wq l bk.a) (h : ∀ n : ℕ, (l : Wq l bk.a) ^ n ∣ w) : w = 0 := by
  by_contra hw
  obtain ⟨m, b, hb0, hb⟩ := WittVector.exists_eq_pow_p_mul w hw
  obtain ⟨c, hc⟩ := h (m + 1)
  have hbc : b = (l : Wq l bk.a) * c := by
    apply mul_left_cancel₀ (pow_ne_zero m (WittVector.p_nonzero l (Fq l bk.a)))
    rw [← hb, hc]; ring
  apply hb0
  have := congrArg (WittVector.constantCoeff (p := l) (R := Fq l bk.a)) hbc
  rwa [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, WittVector.constantCoeff_apply] at this

theorem ev_injective : Function.Injective bk.ev := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have key : ∀ n : ℕ, ∀ x : bk.S, bk.ev x = 0 → (l : bk.S) ^ n ∣ x := by
    intro n
    induction n with
    | zero => intro x _; simp
    | succ n ih =>
      intro x hx
      obtain ⟨x', rfl⟩ := bk.dvd_of_dvd_ev x (by rw [hx]; exact dvd_zero _)
      have h2 : bk.ev x' = 0 := ainf_torsionFree _ (by rw [← map_natCast bk.ev, ← map_mul]; exact hx)
      obtain ⟨z, hz⟩ := ih x' h2
      exact ⟨z, by rw [hz, pow_succ]; ring⟩
  refine PowerSeries.ext fun k => ?_
  rw [map_zero]
  refine bk.eq_zero_of_forall_pow_dvd _ fun n => ?_
  obtain ⟨z, hz⟩ := key n x hx
  refine ⟨coeff k z, ?_⟩
  rw [hz, ← map_natCast (C : Wq l bk.a →+* (Wq l bk.a)⟦X⟧), ← map_pow, coeff_C_mul]

end Red

theorem evW_isUnit_injective_dvd : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K),
    IsUnit (bk.evW bk.E) ∧ Function.Injective bk.evW ∧
      ∀ x : bk.S, ((l : ℕ) : Ainf l) ∣ bk.ev x → ((l : ℕ) : bk.S) ∣ x :=
  fun _ _ _ bk => ⟨isUnit_inclW_of_span bk.span_ev, GlobalTheory.Prism.inclW_injective.comp bk.ev_injective,
    bk.dvd_of_dvd_ev⟩

end GlobalTheory.BSP.BK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardMulHerbrandPhiNatCastTotallyRamifiedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_mul_herbrandPhi_natCast_totallyRamified : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L], lowerRamificationGroup F L 0 = ⊤ → ∀ a : ℕ, (Nat.card (L ≃ₐ[F] L) : ℝ) * herbrandPhi F L a = ((∑ t ∈ Finset.range a, Nat.card ↥(wild F L t) : ℕ) : ℝ) := by
  first | exact @GlobalTheory.PMon.Ram.card_mul_herbrandPhi_natCast_of_totallyRamified | exact GlobalTheory.PMon.Ram.card_mul_herbrandPhi_natCast_of_totallyRamified | (intros; apply GlobalTheory.PMon.Ram.card_mul_herbrandPhi_natCast_of_totallyRamified <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralElementsFromIdempotentCoeffsStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_elements_from_idempotent_coeffs : StepCentral := by
  first | exact @GlobalTheory.Pass.CentralStep.main | exact GlobalTheory.Pass.CentralStep.main | (intros; apply GlobalTheory.Pass.CentralStep.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterModPrimePowKernelGeneratorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_mod_prime_pow_kernel_generator : ∀ (G : Type) [Group G] (p r : ℕ) (a : G → ℤ), p.Prime → (∀ σ τ, (p : ℤ) ^ r ∣ a (σ * τ) - a σ - a τ) → (∃ σ, ¬ (p : ℤ) ^ r ∣ a σ) → ∃ (J : Subgroup G) (_ : J.Normal) (σ₁ : G) (c : ℤ), (∀ σ, σ ∈ J ↔ (p : ℤ) ^ r ∣ a σ) ∧ c * (p : ℤ) ^ r = (J.index : ℤ) * a σ₁ ∧ ¬ (p : ℤ) ∣ c := by
  first | exact @GlobalTheory.PMon.Ram.character_kernel_generator | exact GlobalTheory.PMon.Ram.character_kernel_generator | (intros; apply GlobalTheory.PMon.Ram.character_kernel_generator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundarySemistableTensorColumnsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coboundary_semistableTensor_columns : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (ι : Type) [Fintype ι] [DecidableEq ι]
    (ρ₀ : ↥(GK K) →* GL ι ℚ_[l]) (c₀ : ↥(GK K) → ι → ℚ_[l]) (b : (ι → ℚ_[l]) ⊗[ℚ_[l]] Bst P),
    (∀ g, c₀ g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P (repOf ρ₀) g b - b) →
    ∃ β : ι → Bst P, ∀ g : ↥(GK K), (fun x => algebraMap ℚ_[l] (Bst P) (c₀ g x)) =
      ((ρ₀ g : Matrix ι ι ℚ_[l]).map (algebraMap ℚ_[l] (Bst P))).mulVec (fun x => actSt P (g : GQ l) (β x)) - β := by
  first | exact @GlobalTheory.PMonCob.coboundary_cols | exact GlobalTheory.PMonCob.coboundary_cols | (intros; apply GlobalTheory.PMonCob.coboundary_cols <;> assumption)
end

