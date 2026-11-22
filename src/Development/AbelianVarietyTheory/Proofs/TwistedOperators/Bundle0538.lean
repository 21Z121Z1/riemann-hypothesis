import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0287
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0085
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEmbeddingStabilizer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0339
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0209
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0419
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0413
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0216
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0210
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0219
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0532
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0453
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0218
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0322
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0490
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0303
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0328
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0517
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0011
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0522
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSignatureMatrixExtension
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PackFrame

open GlobalTheory.PackLoc

section Lin

variable {m N : ℕ} (e : Option (Fin m) ≃ Fin N)

theorem embOpt_mul (h k : Matrix (Fin m) (Fin m) ℂ) : embOpt e (h * k) = embOpt e h * embOpt e k := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  rw [Matrix.mul_apply, ← e.sum_comp, Fintype.sum_option]
  cases a <;> cases b <;> simp [embOpt, Matrix.mul_apply]

theorem embOpt_ct (h : Matrix (Fin m) (Fin m) ℂ) : embOpt e hᴴ = (embOpt e h)ᴴ := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  cases a <;> cases b <;> simp [embOpt]

theorem embOpt_Jm {εA : Fin m → Bool} {ε : Fin N → Bool} (h0 : ε (e none) = true) (h1 : ∀ i, ε (e (some i)) = εA i) :
    Formalism.REAL.Jm ε = embOpt e (Formalism.REAL.Jm εA) := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  cases a <;> cases b <;> simp [embOpt, Formalism.REAL.Jm, Matrix.diagonal_apply, h0, h1]

theorem embOpt_unit {h : Matrix (Fin m) (Fin m) ℂ} (hh : IsUnit h) : IsUnit (embOpt e h) := by
  obtain ⟨k, hk⟩ := hh.exists_right_inv
  exact IsUnit.of_mul_eq_one (embOpt e k) (by rw [← embOpt_mul, hk, embOpt_one])

theorem embOpt_inv {h : Matrix (Fin m) (Fin m) ℂ} (hh : IsUnit h) : (embOpt e h)⁻¹ = embOpt e h⁻¹ :=
  Matrix.inv_eq_right_inv (by
    rw [← embOpt_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hh), embOpt_one])

theorem Jm_unit (ε : Fin m → Bool) : IsUnit (Formalism.REAL.Jm ε) := by
  refine IsUnit.of_mul_eq_one (Formalism.REAL.Jm ε) ?_
  rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext a; split_ifs <;> simp

def vecOpt (y : Fin m → ℂ) (a : ℂ) : Fin N → ℂ := fun b => (e.symm b).elim a y

theorem embOpt_vec (h : Matrix (Fin m) (Fin m) ℂ) (y : Fin m → ℂ) (a : ℂ) :
    embOpt e h *ᵥ vecOpt e y a = vecOpt e (h *ᵥ y) a := by
  funext b
  obtain ⟨b, rfl⟩ := e.surjective b
  rw [Matrix.mulVec, dotProduct, ← e.sum_comp, Fintype.sum_option]
  cases b <;> simp [embOpt, vecOpt, Matrix.mulVec, dotProduct]

theorem eu_vecOpt (y : Fin m → ℂ) (a : ℂ) : eu (vecOpt e y a) ^ 2 = eu y ^ 2 + ‖a‖ ^ 2 := by
  unfold eu
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), ← e.sum_comp, Fintype.sum_option, add_comm]
  simp [vecOpt]

theorem vecOpt_zero_one : vecOpt e 0 1 = Pi.single (e none) 1 := by
  funext b
  obtain ⟨b, rfl⟩ := e.surjective b
  cases b <;> simp [vecOpt, Pi.single_apply]

def colM (F : Matrix (Fin N) (Fin m) ℂ) (z : Matrix (Fin N) (Fin 1) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i b => (e.symm b).elim (z i 0) (F i)

variable (F : Matrix (Fin N) (Fin m) ℂ) (z : Matrix (Fin N) (Fin 1) ℂ)

theorem colM_vec (y : Fin m → ℂ) (a : ℂ) : colM e F z *ᵥ vecOpt e y a = F *ᵥ y + a • fun i => z i 0 := by
  funext i
  rw [Matrix.mulVec, dotProduct, ← e.sum_comp, Fintype.sum_option]
  simp [colM, vecOpt, Matrix.mulVec, dotProduct, add_comm, mul_comm]

theorem mul_colM (g : Matrix (Fin N) (Fin N) ℂ) : g * colM e F z = colM e (g * F) (g * z) := by
  ext i b
  obtain ⟨b, rfl⟩ := e.surjective b
  cases b <;> simp [colM, Matrix.mul_apply]

theorem colM_mul (h : Matrix (Fin m) (Fin m) ℂ) : colM e F z * embOpt e h = colM e (F * h) z := by
  ext i b
  obtain ⟨b, rfl⟩ := e.surjective b
  rw [Matrix.mul_apply, ← e.sum_comp, Fintype.sum_option]
  cases b <;> simp [colM, embOpt, Matrix.mul_apply]

theorem colM_gram (J : Matrix (Fin N) (Fin N) ℂ) (h1 : Fᴴ * J * z = 0) (h2 : zᴴ * J * F = 0) (h3 : zᴴ * J * z = 1) :
    (colM e F z)ᴴ * J * colM e F z = embOpt e (Fᴴ * J * F) := by
  rw [Matrix.mul_assoc] at h1 h2 h3 ⊢
  rw [Matrix.mul_assoc, mul_colM]
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  cases a with
  | none => cases b with
    | none => simpa [colM, embOpt, Matrix.mul_apply (M := _ᴴ)] using congrFun (congrFun h3 0) 0
    | some b => simpa [colM, embOpt, Matrix.mul_apply (M := _ᴴ)] using congrFun (congrFun h2 0) b
  | some a => cases b with
    | none => simpa [colM, embOpt, Matrix.mul_apply (M := _ᴴ)] using congrFun (congrFun h1 a) 0
    | some b => simp [colM, embOpt, Matrix.mul_apply (M := _ᴴ)]

theorem exists_frame (J : Matrix (Fin N) (Fin N) ℂ) (h1 : Fᴴ * J * z = 0) (h2 : zᴴ * J * F = 0) (h3 : zᴴ * J * z = 1)
    (εA : Fin m → Bool) (A : Matrix (Fin m) (Fin m) ℂ) (ε : Fin N → Bool) (hA : IsUnit A)
    (hG : Aᴴ * Formalism.REAL.Jm εA * A = Fᴴ * J * F) (h0 : ε (e none) = true) (hε : ∀ i, ε (e (some i)) = εA i) :
    ∃ B : Matrix (Fin N) (Fin N) ℂ, IsUnit B ∧ Bᴴ * Formalism.REAL.Jm ε * B = J ∧
      (∀ (y : Fin m → ℂ) (a : ℂ), eu (B *ᵥ (F *ᵥ y + a • fun i => z i 0)) ^ 2 = eu (A *ᵥ y) ^ 2 + ‖a‖ ^ 2) ∧
      B *ᵥ (fun i => z i 0) = Pi.single (e none) 1 ∧
      ∀ (g : Matrix (Fin N) (Fin N) ℂ) (h : Matrix (Fin m) (Fin m) ℂ), g * F = F * h → g * z = z →
        B * g * B⁻¹ = embOpt e (A * h * A⁻¹) := by
  set M := colM e F z with hM
  set C := embOpt e A with hC
  have hCu : IsUnit C := embOpt_unit e hA
  have hg : Mᴴ * J * M = Cᴴ * Formalism.REAL.Jm ε * C := by
    rw [hM, colM_gram e F z J h1 h2 h3, ← hG, embOpt_mul, embOpt_mul, embOpt_ct, embOpt_Jm e h0 hε]
  have hMu : IsUnit M := by
    have : IsUnit (Mᴴ * J * M) := by
      rw [hg]; exact (((Matrix.isUnit_conjTranspose _).2 hCu).mul (Jm_unit ε)).mul hCu
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at this
    exact (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right this)
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hMu
  have hMi : IsUnit M⁻¹ := Matrix.isUnit_nonsing_inv_iff.2 hMu
  have key : ∀ y a, (C * M⁻¹) *ᵥ (F *ᵥ y + a • fun i => z i 0) = vecOpt e (A *ᵥ y) a := by
    intro y a
    rw [← colM_vec e, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul_cancel_right _ _ hd, embOpt_vec]
  refine ⟨C * M⁻¹, hCu.mul hMi, ?_, fun y a => ?_, ?_, fun g h e1 e2 => ?_⟩
  · calc (C * M⁻¹)ᴴ * Formalism.REAL.Jm ε * (C * M⁻¹) = (M⁻¹)ᴴ * (Cᴴ * Formalism.REAL.Jm ε * C) * M⁻¹ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = (M * M⁻¹)ᴴ * J * (M * M⁻¹) := by
          rw [← hg, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [Matrix.mul_nonsing_inv _ hd]; simp
  · rw [key, eu_vecOpt]
  · have := key 0 1
    simpa [vecOpt_zero_one] using this
  · have e3 : g * M = M * embOpt e h := by rw [hM, mul_colM, colM_mul, e1, e2]
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hd, embOpt_mul, embOpt_mul, ← embOpt_inv e hA, ← hC]
    calc C * M⁻¹ * g * (M * C⁻¹) = C * (M⁻¹ * (g * M)) * C⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [e3, Matrix.nonsing_inv_mul_cancel_left _ _ hd]

end Lin

variable {D : D7}

theorem map_cT_tau (τ : D.what₂.Tau) {m n : ℕ} (X : Matrix (Fin m) (Fin n) D.host.E) :
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X).map (tauE D τ) = (X.map (tauE D τ))ᴴ := by
  ext a b
  exact GlobalTheory.FockCompare.tauE_star τ _

theorem map_incA_tau {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {m n : ℕ} (X : Matrix (Fin m) (Fin n) D.host.E) :
    (X.map (incA D)).map ((θ τ).comp (infPart D)) = X.map (tauE D τ) := by
  ext a b
  exact GlobalTheory.FockCompare.comp_incA hθ τ _

theorem exists_adapted_frame : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (τ : D.what₂.Tau)
  (εA : Fin Y.rank → Bool) (A : Matrix (Fin Y.rank) (Fin Y.rank) ℂ) (ε : Fin V.rank → Bool)
  (e : Option (Fin Y.rank) ≃ Fin V.rank),
  IsUnit A → Aᴴ * Formalism.REAL.Jm εA * A = gramAt D Y τ → ε (e none) = true → (∀ i, ε (e (some i)) = εA i) →
  ∃ B : Matrix (Fin V.rank) (Fin V.rank) ℂ, IsUnit B ∧ Bᴴ * Formalism.REAL.Jm ε * B = gramAt D V τ ∧
    (∀ (y : Fin Y.rank → ℂ) (a : ℂ),
      eu (B *ᵥ ((frameMat V Y d.ι).map (tauE D τ) *ᵥ y + a • fun i => tauE D τ (zv d i))) ^ 2 = eu (A *ᵥ y) ^ 2 + ‖a‖ ^ 2) ∧
    B *ᵥ (fun i => tauE D τ (zv d i)) = Pi.single (e none) 1 ∧
    (∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ), GlobalTheory.PackLoc.embAt θ d τ h ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) ∧
    ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ), B * GlobalTheory.PackLoc.embAt θ d τ h * B⁻¹ = GlobalTheory.PackLoc.embOpt e (A * h * A⁻¹) := by
  intro D θ hθ Y V d τ εA A ε e hA hG h0 hε
  have h1 := congrArg (fun X => X.map (tauE D τ)) d.perp
  have h2 := congrArg (fun X => X.map (tauE D τ)) (GlobalTheory.UnitaryEmbeddingGroup.perp' d)
  have h3 := congrArg (fun X => X.map (tauE D τ)) d.gram
  have h4 := congrArg (fun X => X.map (tauE D τ)) (GlobalTheory.AutFunCounterexample.gram_pull V Y d.ι d.isom)
  simp only [Matrix.map_mul, map_cT_tau, Matrix.map_zero _ (map_zero _)] at h1 h2 h3 h4
  have h5 : (antiDiagonalSignGramMatrix 1 (1 : D.host.E)).map (tauE D τ) = 1 := by
    ext a b
    rw [Subsingleton.elim a 0, Subsingleton.elim b 0]; simp [antiDiagonalSignGramMatrix]
  rw [h5] at h3
  obtain ⟨B, b1, b2, b3, b4, b5⟩ := exists_frame e _ _ _ h1 h2 h3 εA A ε hA (hG.trans h4.symm) h0 hε
  refine ⟨B, b1, b2, b3, b4, fun h _ => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V _ τ, fun h hh => b5 _ h ?_ ?_⟩
  · have k1 := congrArg (fun X => X.map ((θ τ).comp (infPart D))) ((embRel_iff d (atTau θ Y τ h) _).2 rfl).1
    have k2 := (GlobalTheory.PointAtPlaceHom.atTau_spec hθ Y τ hh).2.1
    simp only [Matrix.map_mul, map_incA_tau hθ] at k1
    rw [GlobalTheory.FockCompare.RealAction.infMat_eq] at k2
    exact k1.trans (congrArg _ k2)
  · have k1 := congrArg (fun X => X.map ((θ τ).comp (infPart D))) (GlobalTheory.UnitaryEmbeddingGroup.unitaryEmbedding_fixes_vectors d (atTau θ Y τ h))
    simp only [Matrix.map_mul, map_incA_tau hθ] at k1
    exact k1

end GlobalTheory.PackFrame

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteZetaIntegralThetaLiftEqPartialLValue
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinZeta

variable {D : D7}

theorem hasSum_of_eq {ι M : Type} [NormedAddCommGroup M] {f g : ι → M} {a b : M} (h : HasSum f a) (hf : ∀ i, g i = f i)
    (ha : b = a) : HasSum g b := by
  rwa [funext hf, ha]

theorem l2_smul_left {X : Type} [MeasurableSpace X] (μ : Measure X) (𝓕 : Set X) (c : ℂ) (f g : X → ℂ) :
    l2 μ 𝓕 (c • f) g = c * l2 μ 𝓕 f g := by
  simp only [l2, Formalism.IndefR.Lift.pet, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

theorem l2_self_eq_setIntegral_norm_sq {a b : ℕ} (μ : Measure (Mx D a b)) (𝓕 : Set (Mx D a b)) (f : Mx D a b → ℂ) :
    l2 μ 𝓕 f f = (nrm2 μ 𝓕 f : ℂ) := by
  simp only [l2, Formalism.IndefR.Lift.pet, nrm2, Complex.mul_conj, Complex.normSq_eq_norm_sq, integral_complex_ofReal]

theorem mult_values (hP : GlobalTheory.Published.CuspRapidDecay) {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} (hθ : IsInfFam θ)
    {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} {U : MMap M} (hU : U ∈ Mult θ M J χ) (x : M.Vec) :
    U x ∈ bddAut V ∧ ∀ k ∈ J, ∀ g, U x (g * k) = χ k * U x g := by
  induction hU using Submodule.span_induction with
  | mem U h => exact ⟨⟨(h.aut x).cont, (h.aut x).left, GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ (h.aut x) (h.cusp x)⟩, h.lev x⟩
  | zero => exact ⟨zero_mem _, fun _ _ _ => by simp⟩
  | add a b _ _ ha hb => exact ⟨add_mem ha.1 hb.1, fun k hk g => by simp [ha.2 k hk, hb.2 k hk, mul_add]⟩
  | smul c a _ ha => exact ⟨(bddAut V).smul_mem c ha.1, fun k hk g => by simp [ha.2 k hk, mul_left_comm]⟩

theorem part_eigen {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ}
    {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))} {c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ} {U : MMap M}
    (hU : U ∈ partFull θ M J χ Sb c) (x : M.Vec) (w d R) (h : Hecke₂ V J χ Sb w d R) :
    heckeLin V R (U x) = c w d • U x := by
  have h1 := hU.2
  simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h1
  exact congrArg (fun T : MMap M => T x) (h1 w d R h)

theorem isParamVec_sub {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)} {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    {h : w.under (𝓞 F) = v} {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (GLoc σ J v) X} {ρ' : Representation ℂ (GLoc σ J v) Y} (f : X →ₗ[ℂ] Y)
    (hf : ∀ g y, f (ρ g y) = ρ' g (f y)) (hi : Function.Injective f) {x : X} {B : Multiset ℂˣ}
    (hx : IsParamVec σ J L h ρ' (f x) B) : IsParamVec σ J L h ρ x B := by
  rcases hx with ⟨hv, e, he, hx⟩ | ⟨hw, c, ϖ, e, α, hU, he, hx, hB⟩
  · exact Or.inl ⟨hv, e, he, IsSatVecGL.of_map f (fun g y => hf _ y) hi hx⟩
  · exact Or.inr ⟨hw, c, ϖ, e, α, hU, he, IsSatVecU.of_map hU f (fun g y => hf _ y) hi hx, hB⟩

def satur (V : HSp D) (J : Subgroup (GA D V)) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Subgroup (GA D V) where
  carrier := {g | g ∈ GfC V ∧ ∃ k ∈ J, ∀ v ∈ S, projV V v g = projV V v k}
  one_mem' := ⟨one_mem _, 1, one_mem _, fun _ _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨ha, k, hk, h⟩ ⟨hb, k', hk', h'⟩
    exact ⟨mul_mem ha hb, k * k', mul_mem hk hk', fun v hv => by rw [map_mul, map_mul, h v hv, h' v hv]⟩
  inv_mem' := by
    rintro a ⟨ha, k, hk, h⟩
    exact ⟨inv_mem ha, k⁻¹, inv_mem hk, fun v hv => by rw [map_inv, map_inv, h v hv]⟩

set_option maxHeartbeats 1000000 in

theorem zeta_sum (hG : GlobalTheory.Published.UnramifiedDoublingGL) {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om) (rS : S.rank = D.R.nV)
    (rT : T.rank = D.R.r) {μ : Measure (WO S T)} {𝓧 : Set (WO S T)} (hμ : IsCovolOne (ratL T S) μ 𝓧)
    {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))}
    (hu : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ Sb → UnrAt χS w ∧ UnrAt χT w)
    {K J : Subgroup (GA D T)} {χ : GA D T → ℂ} (hKJ : K ≤ J) (hidx : K.relIndex J ≠ 0) (hJf : J ≤ GfC T)
    (hJ : ∀ g ∈ GfC T, g ∈ J ↔ (∃ k ∈ J, ∀ v ∈ Sb, projV T v g = projV T v k) ∧ ∀ v ∉ Sb, projV T v g ∈ Kv T v)
    (hfin : ∀ g : GA D T, {v | projV T v g ∉ Kv T v}.Finite) (hχ : ∀ k ∈ J, ‖χ k‖ = 1)
    {f : WO S T → ℂ} (hvac : ∀ v ∉ Sb, VacFin ψ S T v f) (hlaw : ∀ k ∈ J, om (1, k) f = χ k • f)
    (hvan : ∀ g ∈ GfC T, g ∉ satur T J Sb → l2 μ 𝓧 (om (1, g) f) f = 0)
    {ν : Measure (GA D T)} {𝓕 : Set (GA D T)} (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ T) 𝓕 ν)
    (F₁ F₂ : bddAut T) (hlev : ∀ k ∈ J, ∀ g, F₁.1 (g * k) = χ k * F₁.1 g) {B : Fam D.host.E} (hB : IsParamFunV T Sb F₁.1 B)
    (hb : Bounded (above D.host.E (Sb : Set (HeightOneSpectrum (𝓞 D.host.F)))) B D.R.r (((D.R.r : ℝ) - 1) / 2))
    (hc : Converges (above D.host.E (Sb : Set (HeightOneSpectrum (𝓞 D.host.F)))) (twist B (val χS)⁻¹) ((1 + (D.R.t : ℂ)) / 2)) :
    HasSum (fun y : FinCos T K => l2 μ 𝓧 (om (1, y.rep) f) f * starRingEnd ℂ (l2 ν 𝓕 (rTr T y.rep F₁) F₂))
      ((K.relIndex J : ℂ) * (nrm2 μ 𝓧 f : ℂ) * (LSD D Sb B χS ((1 + (D.R.t : ℂ)) / 2) / (dOff D Sb : ℂ)) *
        starRingEnd ℂ (l2 ν 𝓕 F₁ F₂)) := by
  obtain ⟨hun, hℓ⟩ := GlobalTheory.T.boundedAutomorphicRightTranslation_unitarisable_bounded D T
  obtain ⟨ℓ, hℓ, hbd⟩ := hℓ ν 𝓕 hν h𝓕 F₂
  obtain ⟨C, hC⟩ := hbd F₁
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
  choose φ hφ hφ' using fun v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} =>
    GlobalTheory.T.weilMatrixCoefficient_vacua_unramifiedPlace D ψ S T χS χT om hW μ 𝓧 hμ v.1 fun w h => hu w (h ▸ v.2)
  rw [rS] at hφ
  obtain ⟨A, hA, hA'⟩ := GlobalTheory.T.localZetaSums_absolutely_convergent_uniform hG D T rT (val χS) (norm_val χS) Sb φ hφ
  let co : GA D T → ℂ := fun g => l2 μ 𝓧 (om (1, g) f) f
  let Ψ : GA D T → ℂ := fun g => co g * starRingEnd ℂ (ℓ (bddRep T g F₁))
  have hmul : ∀ g k : GA D T, om (1, g * k) f = om (1, g) (om (1, k) f) := fun g k => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  have co1 : ∀ g, ∀ k ∈ J, co (g * k) = χ k * co g := fun g k hk => by
    simp only [co, hmul, hlaw k hk, map_smul, l2_smul_left]
  have F1 : ∀ k ∈ J, bddRep T k F₁ = χ k • F₁ := fun k hk => Subtype.ext (funext fun g => hlev k hk g)
  have Ψ1 : ∀ g, ∀ k ∈ J, Ψ (g * k) = Ψ g := fun g k hk => by
    have h1 : χ k * starRingEnd ℂ (χ k) = 1 := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hχ k hk]; simp
    simp only [Ψ, co1 g k hk, map_mul, Module.End.mul_apply, F1 k hk, map_smul, smul_eq_mul]
    linear_combination (co g * starRingEnd ℂ (ℓ (bddRep T g F₁))) * h1
  have co2 : ∀ (v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb}) g, projV T v.1 g = 1 → ∀ a,
      co (g * embV T v.1 a) = φ v a * co g := fun v g hg a => by
    simp only [co]
    rw [← (commute_emb D.sp.cm.sig T.gram a hg).eq, hmul]
    exact hφ' v a _ _ (GlobalTheory.T.weilOperator_keeps_latticeVacuum_of_trivialAt D ψ S T χS χT om hW v.1 g hg f (hvac v.1 v.2)) (hvac v.1 v.2)
  have hJH : J ≤ satur T J Sb := fun k hk => ⟨hJf hk, k, hk, fun _ _ => rfl⟩
  have key := GlobalTheory.T.hasSum_cosets_eulerProduct_alt (fun v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} => embV T v.1) (fun v => projV T v.1)
    (fun v => Kv T v.1) J (satur T J Sb) hJH (fun v a => proj_emb_self _ _ _ _)
    (fun u v h a => proj_emb_ne _ _ (fun e => h (Subtype.ext e)) a)
    (fun v a => ⟨mem_finPts.2 (projInf_emb _ _ _ _), 1, one_mem _, fun u hu' => by
      rw [map_one]; exact proj_emb_ne _ _ (fun e : u = v.1 => v.2 (e ▸ hu')) a⟩)
    (fun v a g hg => commute_emb _ _ a hg)
    (fun g hg => (hJ g hg.1).trans ⟨fun h v => h.2 v.1 v.2, fun h => ⟨hg.2, fun v hv => h ⟨v, hv⟩⟩⟩)
    (fun g _ => (hfin g).preimage Subtype.val_injective.injOn)
    Ψ (fun g => C * ‖co g‖) _ A _ (fun g _ => Ψ1 g) (fun g _ k hk => by rw [co1 g k hk, norm_mul, hχ k hk, one_mul])
    (fun g _ => by
      simp only [Ψ, norm_mul, RCLike.norm_conj]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (hC g) (norm_nonneg _))
    (fun v g _ hg => by
      have h1 := GlobalTheory.T.hasSum_localSphericalZeta_unramified hG D T rT χS (rS ▸ hW.resS) v.1 (fun w h => (hu w (h ▸ v.2)).1) (φ v) (hφ v) _
        ((bddRep T).comp (embV T v.1)) (by
          obtain ⟨b, b1, b2, b3⟩ := hun
          exact ⟨b, b1, b2, fun g => b3 _⟩) F₁ B
        (fun w h => ⟨isParamVec_sub (bddAut T).subtype (fun _ _ => rfl) Subtype.val_injective (hB v.1 v.2 w h),
          (hb w (show w.under (𝓞 D.host.F) ∉ (Sb : Set _) from h ▸ v.2)).2⟩) (ℓ ∘ₗ bddRep T g)
        ⟨C, fun a => by
          have := hC (g * embV T v.1 a)
          rwa [map_mul] at this⟩
      refine hasSum_of_eq (h1.mul_left (co g)) (fun a => ?_) ?_
      · simp only [Ψ, co2 v g hg, map_mul, Module.End.mul_apply, LinearMap.comp_apply, MonoidHom.comp_apply]
        ring
      · simp only [Ψ, LinearMap.comp_apply]
        ring)
    (fun v g _ hg => by
      refine hasSum_of_eq ((hA' v).mul_right (C * ‖co g‖)) (fun a => ?_) rfl
      rw [co2 v g hg, norm_mul]
      ring)
    hA (GlobalTheory.T.hasProd_localTwistedLFactor_div_unitaryLocalFactor D Sb B χS hc)
  have fin := GlobalTheory.T.hasSum_cosets_smaller_level_relIndex_mul_alt K J (satur T J Sb) (GfC T) hKJ hJH (fun g hg => hg.1) hidx Ψ _
    (fun g hg hg' => by simp only [Ψ, co, hvan g hg hg', zero_mul]) (fun g _ => Ψ1 g) key
  refine hasSum_of_eq fin (fun y => ?_) ?_
  · simp only [Ψ, co, hℓ, coe_bddRep, FinCos.rep]
  · have : ((1, 1) : GA D S × GA D T) = 1 := rfl
    simp only [Ψ, co, this, map_one, Module.End.one_apply, l2_self_eq_setIntegral_norm_sq, hℓ]
    ring

set_option maxHeartbeats 1000000 in

theorem finiteZetaL : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.UnramifiedDoublingGL →
    ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
      [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), FiniteZetaL R F := by
  classical
  intro hP _ hG D G _ _ Pl0 T A Ks _ _ _ R F i t σ s P cμ cη m ω BW f₀ f c io hd μ 𝓧 hμ ev hne
  obtain ⟨hft, hvac⟩ := GlobalTheory.T.levelVector_finiteDatum_isTheta_vacuum_off R F i t σ s P cμ cη m ω BW f₀ f c io hd
  have hlaw := GlobalTheory.T.finiteLevelDatumVector_transforms_by_levelCharacter R F i t σ s P cμ cη m ω BW f₀ f c io hd
  obtain ⟨hC, -, -, -, hch, hW, -, hf, -⟩ := hd
  obtain ⟨-, e, he, hΘ⟩ := isLevelVec_iff.1 hf
  have rV : (Vc D i).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have sdV := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i)
  have sdW := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i)
  obtain ⟨a, bV⟩ := hC.lev.βV i
  obtain ⟨b, bW⟩ := hC.lev.βW i
  rw [one_pow] at bV bW
  obtain ⟨hs, hJ, hfin, hχ⟩ := GlobalTheory.T.datumLevel_hyperspecial_off_finite_places D (Wc D i) (R.βW i) (R.ΛW i) (R.datWp i P) (finS R t) bW fun PP h =>
    Finset.mem_image_of_mem _ (Finset.mem_union_left _ (h.resolve_right (Finset.notMem_empty _)))
  obtain ⟨hKJ, hidx, hidx'⟩ := GlobalTheory.T.principalLevel_relIndex_liftLevel_eq_card D T R.toLevCh A.μ0 hC.lev _ e he Finset.subset_union_left i P
  have hu := (GlobalTheory.T.conjugatedThetaCharacters_restriction_ramification R hC.lev i t s cμ cη m hch).2.2
  have hvan : ∀ g ∈ GfC (Wc D i), g ∉ satur (Wc D i) (levG _ (R.βW i) (R.datWp i P)) (finS R t) →
      l2 μ 𝓧 (ω (1, g) f) f = 0 := fun g hg hg' => by
    refine GlobalTheory.T.thetaTranslate_orthogonal_of_support_moved_off D _ _ _ _ _ ω hW _ _ sdV sdW _ e he f₀ _ f (GlobalTheory.T.levelFiniteDatum_isSchwartzBruhat_half D _ _ _ _ _ _ _ _ _ _ e sdV sdW bV.1 bW.1 he) hΘ hft μ 𝓧 hμ g hg
      fun x hx => by_contra fun hx' => hg' ⟨hg, ?_⟩
    obtain ⟨k, hk, h⟩ := GlobalTheory.T.mem_level_of_levelDatum_ne_zero_translate D _ _ _ _ _ _ _ _ _ e sdW bW.1 (by rw [rV, rW]; exact Nat.le_add_right _ _) rfl he
      (fun PP => Finset.mem_union) g hg x hx hx'
    refine ⟨k, hk, fun v hv => ?_⟩
    obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hv
    exact h PP hPP
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hU0 : (R.HW i σ).e x ≠ 0 := fun h => hx0 ((hC.models.HW i σ).1 (h.trans (map_zero _).symm))
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, (R.HW i σ).e x v₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hU0 (MultilinearMap.ext h)
  obtain ⟨m1, m2⟩ := mult_values hP hC.models.inf hx.1 v₀
  obtain ⟨B, hB, hb⟩ := GlobalTheory.T.exists_satake_parameters_bounded_eigenfunction D (Wc D i) _ _ (finS R t) hs _ m1 hv₀ m2 ev (part_eigen hx v₀)
  have hsys := (isParamFunV_iff_of_mem_partFull hs hx hv₀ B).1 hB
  rw [rW] at hb
  have hconv := hb.converges_twist_val cμ (s := (1 + (D.R.t : ℂ)) / 2) (by
    have h5 : (D.R.r : ℝ) + 5 ≤ D.R.t := by exact_mod_cast D.R.rank_add_five_le
    have : ((1 + (D.R.t : ℂ)) / 2).re = (1 + (D.R.t : ℝ)) / 2 := by
      rw [show (1 + (D.R.t : ℂ)) / 2 = (((1 + (D.R.t : ℝ)) / 2 : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_re]
    rw [this]
    linarith)
  refine ⟨B, rW ▸ hsys, fun w hw => (hb w (offS_iff.1 hw)).2, hconv, fun U₁ h₁ U₂ h₂ v₁ v₂ => ?_⟩
  by_cases h0 : U₁ v₁ = 0
  · have : ∀ g, rTr (Wc D i) g 0 = 0 := fun _ => rfl
    simp only [h0, this, petW, l2, Formalism.IndefR.Lift.pet, Pi.zero_apply, zero_mul, integral_zero, map_zero, mul_zero]
    exact hasSum_zero
  obtain ⟨n1, n2⟩ := mult_values hP hC.models.inf h₁.1 v₁
  rw [← hidx]
  exact zeta_sum hG hW rV rW hμ hu hKJ (hidx ▸ hidx') (fun k hk => hk.1) hJ hfin hχ hvac hlaw hvan (hC.models.νW i).1.1
    (hC.models.νW i).2 ⟨_, n1⟩ ⟨_, (mult_values hP hC.models.inf h₂ v₂).1⟩ n2
    ((isParamFunV_iff_of_mem_partFull hs h₁ h0 B).2 hsys) hb hconv

end GlobalTheory.FinZeta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockCompTranslate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FockTranslate

theorem compAt_fin {D : D7} (θ : InfFam D) (τ : D.what₂.Tau) {V : HSp D} (g : GA D V) (hg : g ∈ Formalism.L2.Theta.GfC V) :
    Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V g) = 1 := by
  have h6 : (Formalism.L2.Theta.mt V g).map (Formalism.L2.Theta.infPart D) = 1 :=
    congrArg Units.val (show Formalism.L2.Theta.infHom V g = 1 from hg)
  unfold Formalism.IndefR.Datum.compAt
  rw [show (Formalism.L2.Theta.mt V g).map (fun a => θ τ (Formalism.L2.Theta.infPart D a)) =
    ((Formalism.L2.Theta.mt V g).map (Formalism.L2.Theta.infPart D)).map (θ τ) from (Matrix.map_map).symm, h6]
  exact Matrix.map_one _ (θ τ).map_zero (θ τ).map_one

theorem fockComp_translate : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (B : VertexFrames G) (t : T) (j : ℕ),
    j + 1 ≤ D.R.m → ∀ (f : WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ),
    IsThetaFunO W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) f →
    ∀ (a k₁ : FinPt G (.top j)) (b k₂ : FinPt G (.top (j + 1))),
      fockComp W B (.top t j) f (a * k₁) (b * k₂) =
        fockComp W B (.top t j) (W.om (.top t j) ((k₁ : GA D (G.V (.top j))), (k₂ : GA D (G.V (.top (j + 1))))) f) a b := by
  intro D T L sc G W B t j hj f hf a k₁ b k₂
  have hom := W.om_is (.top t j) hj
  have hcomm : ∀ P, W.om (.top t j) ((k₁ : GA D (G.V (.top j))), (k₂ : GA D (G.V (.top (j + 1)))))
      (fockIn W B (.top t j) f P) = fockIn W B (.top t j) (W.om (.top t j) ((k₁ : GA D (G.V (.top j))), (k₂ : GA D (G.V (.top (j + 1))))) f) P := by
    intro P
    unfold fockIn
    refine Formalism.IndefR.Eqv.KerDiag.comm_pureTensorO W.ψ_std W.θ W.θ_is _ _ _ _ _ (fun τ z g hg => ?_) hf P
    rw [GlobalTheory.OrientedHeis.om_dRho hom W.θ_is _ _ τ z hg, compAt_fin W.θ τ _ k₂.2, compAt_fin W.θ τ _ (inv_mem k₁.2),
      Matrix.one_mul, Matrix.mul_one]
  unfold fockComp
  congr 1
  funext M
  unfold jetTab kerFin GridData.Weil.ker
  simp only [GridData.toPair, thetaKO, Subgroup.coe_mul]
  rw [show ((a : GA D (G.V (.top j))) * k₁, (b : GA D (G.V (.top (j + 1)))) * k₂) =
    ((a : GA D (G.V (.top j))), (b : GA D (G.V (.top (j + 1))))) * ((k₁ : GA D (G.V (.top j))), (k₂ : GA D (G.V (.top (j + 1))))) from rfl,
    map_mul, Module.End.mul_apply, hcomm]

end GlobalTheory.FockTranslate

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridDownArrowThetaFunctionFockDenseOfLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridDownArrow_thetaFunction_fock_dense_of_level : ∀ (D : D7) (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ (t : T) i j, i ≤ D.R.m → j < D.R.m → ∀ (U : AddSubgroup (WO (G.V i j).V (G.V i (j + 1)).V)), IsOpen (U : Set (WO (G.V i j).V (G.V i (j + 1)).V)) → ∀ Φ ∈ GlobalTheory.Size.thetaLevel R.ψ (G.V i j).V (G.V i (j + 1)).V U, ∀ (μ : Measure (WO (G.V i j).V (G.V i (j + 1)).V)) (𝓕 : Set (WO (G.V i j).V (G.V i (j + 1)).V)), IsCovolOne (ratL (G.V i (j + 1)).V (G.V i j).V) μ 𝓕 → ∀ (d : ℕ) (ε : ℝ), 0 < ε → ∃ (n : ℕ) (fs : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ)) (ps : Fin n → PolF D (G.V i (j + 1)).V.rank (G.V i j).V.rank), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l)) ∧ (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) ∈ GlobalTheory.Size.thetaLevel R.ψ (G.V i j).V (G.V i (j + 1)).V U ∧ GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d ((∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) - Φ) < ENNReal.ofReal ε := by
  first | exact @GlobalTheory.ArrowFockDense.dense_level | exact GlobalTheory.ArrowFockDense.dense_level | (intros; apply GlobalTheory.ArrowFockDense.dense_level <;> assumption)
end

