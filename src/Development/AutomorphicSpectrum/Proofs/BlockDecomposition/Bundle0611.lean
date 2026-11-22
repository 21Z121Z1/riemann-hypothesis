import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0586
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryInverseReduction
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0587
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0588
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardPreimageHom
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0115
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0095
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0083
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0589
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0534
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0015
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerGaugeBound

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedCentralizerUnitaryIffStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_centralizer_unitary_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (δ : GL (Fin n) E) (H : Matrix (Fin n) (Fin n) E),
  (δ * thE E n δ).val.charpoly.Separable → IsUnit H.det →
  δ * thE E n δ ∈ UJ (IsCMField.complexConj E).toRingEquiv.toRingHom H →
  ∀ g : GL (Fin n) (Af E), g ∈ twCent (thF E n) (ratF E n δ) ↔
    g ∈ UJ (conjFin (IsCMField.complexConj E).toRingEquiv) (H.map (algebraMap E (Af E))) ∧
      g * ratF E n (δ * thE E n δ) = ratF E n (δ * thE E n δ) * g := by
  first | exact @GlobalTheory.CompanionTheory.TwCentNorm.mem_twCent_ratF_iff | exact GlobalTheory.CompanionTheory.TwCentNorm.mem_twCent_ratF_iff | (intros; apply GlobalTheory.CompanionTheory.TwCentNorm.mem_twCent_ratF_iff <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryInverseReductionStatement
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_inverse_reduction : PositivityTheory.SphericalProduct.InvStepU := by
  first | exact @GlobalTheory.CompanionTheory.InvStep.invStepU | exact GlobalTheory.CompanionTheory.InvStep.invStepU | (intros; apply GlobalTheory.CompanionTheory.InvStep.invStepU <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriOrbitalSupportStatement
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_iwahori_orbital_support : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w), IsWitt n w b → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifAt ϖ → ∀ (l : Fin (n / 2) → ℤ), Cone l → ∀ (γ : UL n w) (u : Fin n → (w.adicCompletion E)ˣ), (∀ i, ordL (u i : w.adicCompletion E) = wexp n l i) → γ.1 = b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹ → ∀ x ∈ iwU n w b, ∀ z ∈ iwU n w b, fU n w b ϖ l (x * γ * z) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.DiagCoset.fU_diag | exact GlobalTheory.CompanionTheory.DiagCoset.fU_diag | (intros; apply GlobalTheory.CompanionTheory.DiagCoset.fU_diag <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryJacquetNonzeroStatement
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_jacquet_nonzero : PositivityTheory.SphericalProduct.JacNeU := by
  first | exact @GlobalTheory.CompanionTheory.JacSph.jacNeU | exact GlobalTheory.CompanionTheory.JacSph.jacNeU | (intros; apply GlobalTheory.CompanionTheory.JacSph.jacNeU <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLevelSubgroupPropertiesStatement
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_level_subgroup_properties : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w), IsWitt n w b → ∀ (ϖ : (w.adicCompletion E)ˣ) (l : Fin (n / 2) → ℤ), IsUnifAt ϖ → Cone l → IsOpen (KL n w : Set (UL n w)) ∧ IsCompact (KL n w : Set (UL n w)) ∧ IsLevel (MonoidHom.id _) (KL n w) (iwU n w b) ∧ (iwU n w b).relIndex (KL n w) ≠ 0 ∧ IsCompact {g : UL n w | fU n w b ϖ l g ≠ 0} := by
  first | exact @GlobalTheory.CompanionTheory.IwLevels.levels_unitary | exact GlobalTheory.CompanionTheory.IwLevels.levels_unitary | (intros; apply GlobalTheory.CompanionTheory.IwLevels.levels_unitary <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedFormulaPolynomialGen
section
noncomputable section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.LocalDens Filter Topology Polynomial

namespace GlobalTheory.CompanionTheory.SiegLoc.UnimodSeries

variable {R : Type} [CommRing R]

theorem densAt_succ {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hU : IsUnrQuad R σ ϖ q ε) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) (hS : IsUnimod σ S) (hT : IsUnimod σ T) (b : ℕ) :
    densAt σ ϖ S T (0 + b + 1) = densAt σ ϖ S T (0 + b + 1 + 1) := by
  obtain ⟨hTc, hdet⟩ := hT
  obtain ⟨c, hc⟩ : ∃ c, c * T.det = ϖ ^ 0 := by
    obtain ⟨w, hw⟩ := hdet.exists_left_inv
    exact ⟨w, by simpa using hw⟩
  have hσ := hU.fix_ϖ
  have hfin : ∀ k, Finite (R ⧸ lev ϖ k) := fun k => finite_lev (by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hU.card]
    exact pow_ne_zero _ (by have := hU.one_lt; omega)) k
  have h1 : T * (c • T.adjugate) = ϖ ^ 0 • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, hc]
  have h2 : cT σ (c • T.adjugate) * T = ϖ ^ 0 • (1 : Matrix (Fin n) (Fin n) R) := by
    have := congrArg (cT σ) h1
    rw [cT_mul, hTc, cT_smul σ (ϖ ^ 0), cT_one, map_pow, hσ] at this
    exact this
  obtain ⟨t, ht⟩ : ∃ t, t + σ t = 1 := by
    obtain ⟨u, hu, -⟩ := hU.basis
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have h3 : (u - σ u) * σ w = -1 := by
      have := congrArg σ hw
      simp only [map_mul, map_sub, hU.inv, map_one] at this
      linear_combination -this
    have h4 : σ w = -w := by linear_combination (-σ w) * hw + w * h3
    refine ⟨u * w, ?_⟩
    rw [map_mul, h4]
    linear_combination hw
  refine dens_step hfin hU.inv hσ S T _ hS.1 hTc (fun h hh hk => ?_)
  rw [red_eq_iff] at hk
  choose C hC using hk
  have hhT : h = T + ϖ ^ (0 + b + 1) • Matrix.of C := by
    ext i j
    have := hC i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [← this]; ring
  have hCh : cT σ (Matrix.of C) = Matrix.of C := by
    ext i j
    have e1 := congrFun (congrFun (hh) i) j
    have e2 := congrArg σ (hC j i)
    have e3 := congrFun (congrFun hTc i) j
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply] at e1 e3
    simp only [map_sub, map_mul, map_pow, hσ, e1, e3] at e2
    have := (hU.reg.pow (0 + b + 1)) (a₁ := σ (C j i)) (a₂ := C i j) (by
      simp only [smul_eq_mul]
      rw [← e2, hC i j])
    simpa [cT] using this
  obtain ⟨g, h', hgh, hhg, hg⟩ := twist hσ ht hCh 0 b h1 h2
  rw [← hhT] at hg
  rw [solCount_eq, ← sol_congr σ ϖ S _ hg, ← solCount_eq]
  exact solCount_congr hσ S T g h' _ hgh hhg

theorem densAt_eq_densAt_one_of_isUnimod {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hU : IsUnrQuad R σ ϖ q ε) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) (hS : IsUnimod σ S) (hT : IsUnimod σ T)
    (k : ℕ) (hk : 1 ≤ k) : densAt σ ϖ S T k = densAt σ ϖ S T 1 := by
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    obtain ⟨b, rfl⟩ : ∃ b, k = 0 + b + 1 := ⟨k - 1, by omega⟩
    rw [← densAt_succ hU S T hS hT b, ih]

theorem densAt_eq_of_isDens {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hU : IsUnrQuad R σ ϖ q ε) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) (hS : IsUnimod σ S) (hT : IsUnimod σ T)
    {α : ℝ} (hα : IsDens σ ϖ S T α) (k : ℕ) (hk : 1 ≤ k) : densAt σ ϖ S T k = α := by
  have h1 : Tendsto (densAt σ ϖ S T) atTop (𝓝 (densAt σ ϖ S T 1)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with j hj
    exact (densAt_eq_densAt_one_of_isUnimod hU S T hS hT j hj).symm
  rw [densAt_eq_densAt_one_of_isUnimod hU S T hS hT k hk]
  exact tendsto_nhds_unique h1 hα

theorem isUnimod_one (σ : R →+* R) (m : ℕ) : IsUnimod σ (1 : Matrix (Fin m) (Fin m) R) :=
  ⟨cT_one σ, by simp⟩

theorem unrPoly : PositivityTheory.PfSWUS.Loc.UnrFormula → PositivityTheory.SiegelWeilFormula.Gen.UnrPoly := by
  intro hF R _ σ ϖ q ε hR ψ hψ n T hT k hk t
  classical
  have hfin : ∀ k, Finite (R ⧸ lev ϖ k) := fun k => finite_lev (by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hR.card]
    exact pow_ne_zero _ (by have := hR.one_lt; omega)) k
  letI : ∀ k, Fintype (R ⧸ lev ϖ k) := fun k => Fintype.ofFinite _
  haveI : Finite (Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) :=
    inferInstanceAs (Finite (Fin n → Fin n → R ⧸ lev ϖ k))
  haveI : Finite (hermMod σ ϖ n k) := Subtype.finite
  letI : Fintype (hermMod σ ϖ n k) := Fintype.ofFinite _
  have hq1 : 1 < q := hR.one_lt
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hε : (ε : ℂ) ^ 2 = 1 := by
    rcases hR.eps with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  have hnε : ‖(ε : ℂ)‖ = 1 := by
    rcases hR.eps with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  let P : ℂ[X] := ∑ B : hermMod σ ϖ n k,
    C (ψ k (Matrix.trace (red ϖ k T * B.1))) * X ^ Nat.log (q ^ 2) (nuAt ϖ B.1)
  let Q : ℂ[X] := ∏ i : Fin n, (1 - X * C (((ε : ℂ) * q) ^ (i : ℕ)))
  have hP : ∀ x : ℂ, P.eval x = ∑' B : hermMod σ ϖ n k,
      ψ k (Matrix.trace (red ϖ k T * B.1)) * x ^ Nat.log (q ^ 2) (nuAt ϖ B.1) := by
    intro x
    rw [tsum_fintype]
    simp [P, Polynomial.eval_finset_sum]
  have hQ : ∀ x : ℂ, Q.eval x = ∏ i : Fin n, (1 - x * ((ε : ℂ) * q) ^ (i : ℕ)) := by
    intro x
    simp [Q, Polynomial.eval_prod]
  have hval : ∀ m, n ≤ m → P.eval (((ε : ℂ) / q) ^ m) = Q.eval (((ε : ℂ) / q) ^ m) := by
    intro m hm
    have hS := isUnimod_one σ m
    have hs : siegAt ϖ σ ψ q ε m T k = ((densAt σ ϖ (1 : Matrix (Fin m) (Fin m) R) T k : ℝ) : ℂ) :=
      GlobalTheory.CompanionTheory.SiegLoc.level_identity R σ ϖ q ε hR ψ hψ m n k 1 T hS.1 hT.1
        (GlobalTheory.CompanionTheory.SiegLoc.HermOrth.orth_hermMod R σ ϖ q ε hR ψ hψ n k)
        (fun B hB => GlobalTheory.CompanionTheory.SiegLoc.gauss_full hR hψ hε k 1 hS B hB)
    have hc : ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) = ((ε : ℂ) / q) ^ m := by
      rw [div_pow, zpow_neg, zpow_natCast, div_eq_mul_inv]
    rw [hP, hQ]
    unfold siegAt at hs
    rw [hc] at hs
    rw [hs, densAt_eq_of_isDens hR 1 T hS hT (hF R σ ϖ q ε hR m n hm 1 T hS hT) k hk]
    push_cast
    refine Finset.prod_congr rfl fun i _ => ?_
    have hi : (i : ℕ) ≤ m := by have := i.2; omega
    have e1 : ((ε : ℂ) / q) ^ m = ((ε : ℂ) / q) ^ (m - (i : ℕ)) * ((ε : ℂ) / q) ^ (i : ℕ) := by
      rw [← pow_add, Nat.sub_add_cancel hi]
    have e2 : ((ε : ℂ) / q) ^ (i : ℕ) * ((ε : ℂ) * q) ^ (i : ℕ) = 1 := by
      rw [← mul_pow]
      have : (ε : ℂ) / q * ((ε : ℂ) * q) = 1 := by
        field_simp
        simpa using hε
      rw [this, one_pow]
    rw [e1, mul_assoc, e2, mul_one]
  have hinj : Function.Injective (fun j : ℕ => ((ε : ℂ) / q) ^ (n + j)) := by
    intro a b hab
    have h1 : ‖((ε : ℂ) / q) ^ (n + a)‖ = ‖((ε : ℂ) / q) ^ (n + b)‖ := congrArg norm hab
    have hnorm : ‖(ε : ℂ) / q‖ = (q : ℝ)⁻¹ := by
      rw [norm_div, hnε]
      simp
    rw [norm_pow, norm_pow, hnorm] at h1
    have hq0 : (0 : ℝ) < (q : ℝ)⁻¹ := by
      have : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
      positivity
    have hq2 : (q : ℝ)⁻¹ ≠ 1 := by
      have : (1 : ℝ) < q := by exact_mod_cast hq1
      exact (inv_lt_one_of_one_lt₀ this).ne
    have := pow_right_injective₀ hq0 hq2 h1
    omega
  have hPQ : P = Q := Polynomial.eq_of_infinite_eval_eq P Q
    (Set.infinite_of_injective_forall_mem hinj fun j => hval (n + j) (by omega))
  have := congrArg (Polynomial.eval t) hPQ
  rw [hP, hQ] at this
  exact this

end GlobalTheory.CompanionTheory.SiegLoc.UnimodSeries

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VectorLengthFormulaOfPartsStatement
section
open PositivityTheory.Rg.Mass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vector_length_formula_of_parts : CoCpt → LocMass → Prop1 := by
  first | exact @GlobalTheory.CompanionTheory.Mass.One.vector_length_formula_up_to_constant | exact GlobalTheory.CompanionTheory.Mass.One.vector_length_formula_up_to_constant | (intros; apply GlobalTheory.CompanionTheory.Mass.One.vector_length_formula_up_to_constant <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilActionBlockMatrixComponentsStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_action_block_matrix_components : ∀ (D : D7) (m r s : ℕ) (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E)
    (y₁ : Mx D m r) (y₂ : Mx D m s),
    xPart (HMul.hMul (zy (colJoin y₁ y₂)) ((repMat (D.sp.cm.sig : D.host.E →+* D.host.E) b a).map (incA D))) =
        -HMul.hMul (colJoin y₁ (0 : Mx D m s)) (rat a) ∧
      yPart (HMul.hMul (zy (colJoin y₁ y₂)) ((repMat (D.sp.cm.sig : D.host.E →+* D.host.E) b a).map (incA D))) =
        HMul.hMul (colJoin (-HMul.hMul y₁ (rat b)) y₂) (rat (cT (D.sp.cm.sig : D.host.E →+* D.host.E) a)⁻¹) := by
  first | exact @GlobalTheory.CompanionTheory.EisUnfold.Parts.parts | exact GlobalTheory.CompanionTheory.EisUnfold.Parts.parts | (intros; apply GlobalTheory.CompanionTheory.EisUnfold.Parts.parts <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerAdditiveCharacterEquivariance
section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.WhittakerPsi

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem det_left_unipotent_mul (x : F) (g : GL (Fin 2) F) :
    GeneralLinearGroup.det (uni2 x * g) = GeneralLinearGroup.det g := by
  rw [map_mul]
  have : GeneralLinearGroup.det (uni2 x) = 1 := by
    ext
    simp [uni2, GeneralLinearGroup.det, Matrix.det_fin_two]
  rw [this, one_mul]

theorem row_vector_mul_upper_unipotent (h y x : F) (g : GL (Fin 2) F) :
    ![h, h * y] ᵥ* ((uni2 x * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ![h, h * (y + x)] ᵥ* (g : Matrix (Fin 2) (Fin 2) F) := by
  rw [Units.val_mul, ← Matrix.vecMul_vecMul]
  congr 1
  exact GlobalTheory.CompanionTheory.PsiShift.vecMul_unipotent h y x

theorem whittaker_upper_unipotent_equivariance (ψ : AddChar F Circle) (μ₁ μ₂ : Fˣ →* ℂˣ) (φ : (Fin 2 → F) → ℂ) (x : F)
    (g : GL (Fin 2) F) :
    W2 ψ μ₁ μ₂ φ (uni2 x * g) = (ψ x : ℂ) * W2 ψ μ₁ μ₂ φ g := by
  have inner : ∀ h : Fˣ,
      (∫ y, φ (![(h : F), h * y] ᵥ* ((uni2 x * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) *
        (ψ (-y) : ℂ) ∂selfDualMeasure ψ) =
      (ψ x : ℂ) * ∫ y, φ (![(h : F), h * y] ᵥ* (g : Matrix (Fin 2) (Fin 2) F)) *
        (ψ (-y) : ℂ) ∂selfDualMeasure ψ := by
    intro h
    simp only [row_vector_mul_upper_unipotent]
    exact GlobalTheory.CompanionTheory.PsiShift.integral_add_right_mul_char (selfDualMeasure ψ) ψ
      (fun y => φ (![(h : F), h * y] ᵥ* (g : Matrix (Fin 2) (Fin 2) F))) x
  unfold W2
  rw [det_left_unipotent_mul]
  simp only [inner]
  have e : ∀ h : Fˣ, (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * mp h 1 *
      ((ψ x : ℂ) * ∫ y, φ (![(h : F), h * y] ᵥ* (g : Matrix (Fin 2) (Fin 2) F)) *
        (ψ (-y) : ℂ) ∂selfDualMeasure ψ) =
      (ψ x : ℂ) * ((((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * mp h 1 *
      ∫ y, φ (![(h : F), h * y] ᵥ* (g : Matrix (Fin 2) (Fin 2) F)) *
        (ψ (-y) : ℂ) ∂selfDualMeasure ψ) := fun h => by ring
  simp only [e]
  rw [integral_const_mul]
  ring

theorem sPsi : SPsi := by
  intro F _ _ _ _ _ _ ψ _ μ₁ μ₂ _ _ φ _ x g
  exact whittaker_upper_unipotent_equivariance ψ μ₁ μ₂ φ x g

end GlobalTheory.CompanionTheory.WhittakerPsi
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerCentralCharacter
section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.WhittakerCentral

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem mp_mul (x y : Fˣ) (s : ℂ) : mp (x * y) s = mp x s * mp y s := by
  simp only [mp, Units.val_mul, modulus_mul, NNReal.coe_mul, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) s

theorem mp_one_left (s : ℂ) : mp (1 : Fˣ) s = 1 := by
  simp [mp, modulus_one]

theorem mp_half_mul_self (a : Fˣ) : mp a (1 / 2) * mp a (1 / 2) = mp a 1 := by
  have h : ((modulus (a : F) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (by exact_mod_cast modulus_ne_zero a.ne_zero)
  simp only [mp]
  rw [← Complex.cpow_add _ _ h]
  norm_num

theorem mp_inv_mul_self (a : Fˣ) (s : ℂ) : mp a⁻¹ s * mp a s = 1 := by
  rw [← mp_mul, inv_mul_cancel, mp_one_left]

theorem det_scalar_diagonal_mul (a : Fˣ) (g : GL (Fin 2) F) :
    GeneralLinearGroup.det (dg2 a a * g) = a * a * GeneralLinearGroup.det g := by
  rw [map_mul]
  congr 1
  ext
  simp [dg2, GeneralLinearGroup.det, Matrix.det_fin_two]

theorem row_vector_scalar_diagonal_mul (a h : Fˣ) (x : F) (g : GL (Fin 2) F) :
    ![(h : F), h * x] ᵥ* ((dg2 a a * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ![((a * h : Fˣ) : F), ((a * h : Fˣ) : F) * x] ᵥ* (g : Matrix (Fin 2) (Fin 2) F) := by
  rw [Units.val_mul, ← Matrix.vecMul_vecMul]
  congr 1
  ext i
  fin_cases i <;> simp [dg2, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring

theorem whittaker_central_character_equivariance (ψ : AddChar F Circle) (μ₁ μ₂ : Fˣ →* ℂˣ) (φ : (Fin 2 → F) → ℂ) (a : Fˣ)
    (g : GL (Fin 2) F) :
    W2 ψ μ₁ μ₂ φ (dg2 a a * g) = ((μ₁ a * μ₂ a : ℂˣ) : ℂ) * W2 ψ μ₁ μ₂ φ g := by
  set Φ : Fˣ → ℂ := fun h => (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * mp h 1 *
      (∫ x, φ (![(h : F), h * x] ᵥ* (g : Matrix (Fin 2) (Fin 2) F)) * (ψ (-x) : ℂ)
        ∂selfDualMeasure ψ) with hΦ
  have hint : ∫ h : Fˣ, (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * mp h 1 *
      (∫ x, φ (![(h : F), h * x] ᵥ* ((dg2 a a * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) *
        (ψ (-x) : ℂ) ∂selfDualMeasure ψ) ∂multHaar F =
      (((μ₁ a * (μ₂ a)⁻¹ : ℂˣ) : ℂ) * mp a⁻¹ 1) * ∫ h : Fˣ, Φ h ∂multHaar F := by
    rw [← integral_mul_left_eq_self Φ a, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    simp only [hΦ, row_vector_scalar_diagonal_mul]
    have e : (((μ₁ (a * h))⁻¹ * μ₂ (a * h) : ℂˣ) : ℂ) =
        ((μ₁ a * (μ₂ a)⁻¹ : ℂˣ) : ℂ)⁻¹ * (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) := by
      rw [← Units.val_inv_eq_inv_val, ← Units.val_mul, map_mul, map_mul]
      congr 1
      simp only [mul_inv, inv_inv]
      exact mul_mul_mul_comm _ _ _ _ |>.trans (by simp [mul_comm, mul_left_comm, mul_assoc])
    rw [e, mp_mul]
    have hc : ((μ₁ a * (μ₂ a)⁻¹ : ℂˣ) : ℂ) * ((μ₁ a * (μ₂ a)⁻¹ : ℂˣ) : ℂ)⁻¹ = 1 :=
      mul_inv_cancel₀ (Units.ne_zero _)
    have hN : mp a⁻¹ 1 * mp a 1 = 1 := mp_inv_mul_self a 1
    generalize ((μ₁ a * (μ₂ a)⁻¹ : ℂˣ) : ℂ) = c at hc ⊢
    generalize mp a⁻¹ 1 = N at hN ⊢
    generalize mp a 1 = M at hN ⊢
    generalize (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) = X
    generalize mp h 1 = m
    generalize (∫ x, φ (![((a * h : Fˣ) : F), ((a * h : Fˣ) : F) * x] ᵥ*
      (g : Matrix (Fin 2) (Fin 2) F)) * (ψ (-x) : ℂ) ∂selfDualMeasure ψ) = I
    linear_combination (-(N * M * X * m * I)) * hc + (-(X * m * I)) * hN
  have hWg : W2 ψ μ₁ μ₂ φ g = ((μ₂ (GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
      mp (GeneralLinearGroup.det g) (1 / 2) * ∫ h : Fˣ, Φ h ∂multHaar F := rfl
  have hWa : W2 ψ μ₁ μ₂ φ (dg2 a a * g) =
      ((μ₂ (a * a * GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
        mp (a * a * GeneralLinearGroup.det g) (1 / 2) *
        ((((μ₁ a * (μ₂ a)⁻¹ : ℂˣ) : ℂ) * mp a⁻¹ 1) * ∫ h : Fˣ, Φ h ∂multHaar F) := by
    rw [← hint, ← det_scalar_diagonal_mul]
    rfl
  rw [hWa, hWg, mp_mul, mp_mul, mp_half_mul_self, map_mul, map_mul]
  have hB : ((μ₂ a : ℂˣ) : ℂ) * (((μ₂ a)⁻¹ : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hN : mp a⁻¹ 1 * mp a 1 = 1 := mp_inv_mul_self a 1
  simp only [Units.val_mul]
  generalize (((μ₂ a)⁻¹ : ℂˣ) : ℂ) = B' at hB ⊢
  generalize ((μ₂ a : ℂˣ) : ℂ) = B at hB ⊢
  generalize mp a⁻¹ 1 = N at hN ⊢
  generalize mp a 1 = M at hN ⊢
  generalize ((μ₁ a : ℂˣ) : ℂ) = A
  generalize ((μ₂ (GeneralLinearGroup.det g) : ℂˣ) : ℂ) = D
  generalize mp (GeneralLinearGroup.det g) (1 / 2) = P
  generalize (∫ h : Fˣ, Φ h ∂multHaar F) = J
  linear_combination (B * B * B' * D * P * A * J) * hN + (B * D * P * A * J) * hB

theorem sCen : Ad3.SchwartzSpaceL2.SCen := by
  intro F _ _ _ _ _ _ ψ _ μ₁ μ₂ _ _ φ _ a g
  exact whittaker_central_character_equivariance ψ μ₁ μ₂ φ a g

end GlobalTheory.CompanionTheory.WhittakerCentral
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerGaugeBoundStatement
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_gauge_bound : Ad3.SchwartzSpaceL2.SBound := by
  first | exact @GlobalTheory.CompanionTheory.DampedWhittakerGauge.whittaker_torus_gauge_estimate | exact GlobalTheory.CompanionTheory.DampedWhittakerGauge.whittaker_torus_gauge_estimate | (intros; apply GlobalTheory.CompanionTheory.DampedWhittakerGauge.whittaker_torus_gauge_estimate <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerLocalTateIntegral
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.TateFE

theorem quasiCharExponent_eq_zero_of_unit {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {χ : Fˣ →* ℂˣ} (hχ : IsUnit1 χ) : quasiCharExponent χ = 0 := by
  unfold quasiCharExponent
  rw [hχ.2]
  simp

theorem first_form {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
    {ψ : AddChar F Circle} (hψ : IsStd ψ) {χ : Fˣ →* ℂˣ} (hχ : IsUnit1 χ)
    {f : F → ℂ} (hf : f ∈ schwartzBruhat F) {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    localZeta (localFourier (selfDualMeasure ψ) ψ f) χ⁻¹ (1 - s) = gam ψ χ s * localZeta f χ s := by
  have he := quasiCharExponent_eq_zero_of_unit hχ
  have hs1 : -quasiCharExponent χ < s.re := by rw [he]; simpa using h0
  have hs2 : s.re < 1 - quasiCharExponent χ := by rw [he]; simpa using h1
  have hs' : -quasiCharExponent χ⁻¹ < (1 - s).re := by
    rw [quasiCharExponent_inv, Complex.sub_re, Complex.one_re]
    linarith
  have hL1 := localLFactor_ne_zero hχ.1 hs1
  have hL2 := localLFactor_ne_zero (continuous_quasiChar_inv hχ.1) hs'
  have hfe := localZeta_functionalEquation hψ.1 hψ.2.1 hχ.1 hf hs1 hs2
  unfold gam
  rw [div_eq_iff hL2] at hfe
  rw [hfe]
  field_simp

theorem second_form {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
    {ψ : AddChar F Circle} (hψ : IsStd ψ) {χ : Fˣ →* ℂˣ} (hχ : IsUnit1 χ)
    {f : F → ℂ} (hf : f ∈ schwartzBruhat F) {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    localZeta f χ⁻¹ (1 - s) =
      ((χ (-1) : ℂˣ) : ℂ) * gam ψ χ s * localZeta (localFourier (selfDualMeasure ψ) ψ f) χ s := by
  have hc := hψ.1
  have hn := hψ.2.1
  set T := localFourier (selfDualMeasure ψ) ψ with hT
  have m1 : T f ∈ schwartzBruhat F := localFourier_mem_schwartzBruhat (selfDualMeasure ψ) hc hn hf
  have m2 : T (T f) ∈ schwartzBruhat F := localFourier_mem_schwartzBruhat (selfDualMeasure ψ) hc hn m1
  have m3 : T (T (T f)) ∈ schwartzBruhat F :=
    localFourier_mem_schwartzBruhat (selfDualMeasure ψ) hc hn m2
  have e1 : T (T (T f)) = fun x => T f (-x) :=
    funext fun x => localFourier_localFourier_selfDual hc hn m1 x
  have e2 : T (T (T (T f))) = f := funext fun x => by
    have a1 : T (T (T (T f))) x = T (T f) (-x) := localFourier_localFourier_selfDual hc hn m2 x
    have a2 : T (T f) (-x) = f (- -x) := localFourier_localFourier_selfDual hc hn hf (-x)
    rw [a1, a2, neg_neg]
  have key := first_form hψ hχ m3 h0 h1
  rw [← hT, e2, e1, localZeta_comp_neg] at key
  rw [key]
  ring

theorem sTate : STate := by
  intro F _ _ _ _ _ _ ψ hψ χ hχ f hf s h0 h1
  exact ⟨first_form hψ hχ hf h0 h1, second_form hψ hχ hf h0 h1⟩

end GlobalTheory.CompanionTheory.TateFE
end

