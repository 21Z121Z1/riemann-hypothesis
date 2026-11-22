import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0355
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0550
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0558
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0503
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0548
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0350
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0352
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0373
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0422
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0489
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0545
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0220
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComponentWachLetterBasisFiltration
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDiscExistsConstAddXMul
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.DiscSer

variable (l : ℕ) {W : Type} [CommRing W] (ρ : ℝ≥0)

def shiftX (s : W⟦X⟧) : W⟦X⟧ := PowerSeries.mk fun n => coeff (n + 1) s

theorem coeff_shiftX (s : W⟦X⟧) (n : ℕ) : coeff n (shiftX s) = coeff (n + 1) s := coeff_mk _ _

theorem X_mul_shiftX (s : W⟦X⟧) : X * shiftX s = s - C (coeff 0 s) := by
  ext n
  rcases n with _ | n
  · simp
  · rw [coeff_succ_X_mul, coeff_shiftX, map_sub, coeff_C]; simp

theorem eq_zero_of_X_mul_eq_zero {t : W⟦X⟧} (h : X * t = 0) : t = 0 := by
  ext n
  have := congrArg (coeff (n + 1)) h
  rwa [coeff_succ_X_mul, map_zero] at this

theorem exists_rep (y : PreDisc l (X : W⟦X⟧) ρ) : ∃ (c : ℕ) (s : W⟦X⟧),
    y = algebraMap _ _ s * IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c := by
  obtain ⟨c, s, hs⟩ := IsLocalization.Away.surj (l : W⟦X⟧) y
  exact ⟨c, s, by rw [← hs, mul_assoc, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]⟩

theorem aPre_rep (n c : ℕ) (s : W⟦X⟧) :
    aPre l ρ n (algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) s *
      IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c) =
      algebraMap W (PreDisc l (0 : W) 1) (coeff n s) *
        IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W) ^ c := by
  rw [aPre_apply, map_mul, phi_alg, map_pow, phi_inv, ← map_pow, coeff_mul_C, coeff_map]

theorem eq_zero_of_X_mul (z : PreDisc l (X : W⟦X⟧) ρ)
    (h : algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) (X : W⟦X⟧) * z = 0) : z = 0 := by
  obtain ⟨c, t, rfl⟩ := exists_rep l ρ z
  have hu : IsUnit (IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧)) :=
    IsUnit.of_mul_eq_one_right (algebraMap _ _ (l : W⟦X⟧)) (IsLocalization.Away.mul_invSelf _)
  rw [← mul_assoc, ← map_mul] at h
  have h2 : algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) (X * t) = 0 := (hu.pow c).mul_left_eq_zero.1 h
  obtain ⟨⟨m, hm⟩, hm'⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (l : W⟦X⟧)) _ _).1 h2
  obtain ⟨k, rfl⟩ := hm
  have h3 : (l : W⟦X⟧) ^ k * t = 0 :=
    eq_zero_of_X_mul_eq_zero (by rw [mul_left_comm]; exact hm')
  have h4 : algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) t = 0 := by
    have h5 := congrArg (algebraMap _ (PreDisc l (X : W⟦X⟧) ρ)) h3
    rw [map_mul, map_zero] at h5
    rw [map_pow] at h5
    exact ((IsLocalization.Away.algebraMap_isUnit (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧)).pow k).mul_right_eq_zero.1 h5
  rw [h4, zero_mul]

abbrev c0 (y : PreDisc l (X : W⟦X⟧) ρ) : PreDisc l (X : W⟦X⟧) ρ :=
  preMap l (0 : W) 1 (X : W⟦X⟧) ρ C (aPre l ρ 0 y)

theorem X_mul_rep (c : ℕ) (s : W⟦X⟧) :
    algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) (X : W⟦X⟧) * (algebraMap _ _ (shiftX s) *
      IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c) =
    algebraMap _ _ s * IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c -
      c0 l ρ (algebraMap _ _ s * IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c) := by
  rw [c0, aPre_rep, map_mul, preMap_alg, map_pow, preMap_inv, ← mul_assoc, ← map_mul, X_mul_shiftX, map_sub,
    sub_mul]

def dFun (y : PreDisc l (X : W⟦X⟧) ρ) : PreDisc l (X : W⟦X⟧) ρ :=
  algebraMap _ _ (shiftX (exists_rep l ρ y).choose_spec.choose) *
    IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ (exists_rep l ρ y).choose

theorem X_mul_dFun (y : PreDisc l (X : W⟦X⟧) ρ) :
    algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) (X : W⟦X⟧) * dFun l ρ y = y - c0 l ρ y := by
  have hy := (exists_rep l ρ y).choose_spec.choose_spec
  rw [dFun, X_mul_rep, ← hy]

theorem dFun_eq (y z : PreDisc l (X : W⟦X⟧) ρ)
    (h : algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) (X : W⟦X⟧) * z = y - c0 l ρ y) : dFun l ρ y = z :=
  sub_eq_zero.1 (eq_zero_of_X_mul l ρ _ (by rw [mul_sub, X_mul_dFun, h, sub_self]))

theorem dFun_rep (c : ℕ) (s : W⟦X⟧) :
    dFun l ρ (algebraMap _ _ s * IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c) =
      algebraMap _ _ (shiftX s) * IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c :=
  dFun_eq l ρ _ _ (X_mul_rep l ρ c s)

def DPre : PreDisc l (X : W⟦X⟧) ρ →+ PreDisc l (X : W⟦X⟧) ρ :=
  AddMonoidHom.mk' (dFun l ρ) fun y z => dFun_eq l ρ _ _ (by
    rw [mul_add, X_mul_dFun, X_mul_dFun, c0, c0, c0, map_add, map_add]; abel)

theorem DPre_apply (y : PreDisc l (X : W⟦X⟧) ρ) : DPre l ρ y = dFun l ρ y := rfl

theorem aPre_DPre (n : ℕ) (y : PreDisc l (X : W⟦X⟧) ρ) : aPre l ρ n (DPre l ρ y) = aPre l ρ (n + 1) y := by
  obtain ⟨c, s, rfl⟩ := exists_rep l ρ y
  rw [DPre_apply, dFun_rep, aPre_rep, aPre_rep, coeff_shiftX]

theorem norm_DPre_le [Fact l.Prime] (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (y : PreDisc l (X : W⟦X⟧) ρ) :
    ‖DPre l ρ y‖ ≤ (ρ : ℝ)⁻¹ * ‖y‖ := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hρ : (0 : ℝ) < ρ := by exact_mod_cast hρ0
  refine norm_le_of_aPre l ρ hρ0 hρ1 _ _ (by positivity) fun n => ?_
  rw [aPre_DPre, inv_mul_eq_div, le_div_iff₀ hρ, mul_assoc, ← pow_succ]
  exact norm_aPre_le l ρ hl hρ1.le y (n + 1)

theorem continuous_DPre [Fact l.Prime] (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : Continuous (DPre l ρ (W := W)) :=
  AddMonoidHomClass.continuous_of_bound _ _ (norm_DPre_le l ρ hρ0 hρ1)

theorem exists_const_add_X_mul [Fact l.Prime] (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (κ : Disc l (0 : W) 1 →+* Disc l (X : W⟦X⟧) ρ) (hκ : IsDiscMap (C : W →+* W⟦X⟧) κ)
    (x : Disc l (X : W⟦X⟧) ρ) :
    ∃ (c : Disc l (0 : W) 1) (x₁ : Disc l (X : W⟦X⟧) ρ), x = κ c + toDisc l (X : W⟦X⟧) ρ X * x₁ := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  let A0 := (aPre l ρ 0 (W := W)).completion (continuous_aPre l ρ hl hρ0 hρ1.le 0)
  let D := (DPre l ρ (W := W)).completion (continuous_DPre l ρ hρ0 hρ1)
  have hA : ∀ y, A0 (ofPre l (X : W⟦X⟧) ρ y) = ofPre l (0 : W) 1 (aPre l ρ 0 y) := fun y =>
    AddMonoidHom.completion_coe _ _ y
  have hD : ∀ y, D (ofPre l (X : W⟦X⟧) ρ y) = ofPre l (X : W⟦X⟧) ρ (DPre l ρ y) := fun y =>
    AddMonoidHom.completion_coe _ _ y
  have hκc : Continuous κ :=
    AddMonoidHomClass.continuous_of_bound _ 1 fun y => (hκ.norm_le y).trans (one_mul _).ge
  have e : κ.comp (ofPre l (0 : W) 1) = (ofPre l (X : W⟦X⟧) ρ).comp (preMap l (0 : W) 1 (X : W⟦X⟧) ρ C) :=
    IsLocalization.ringHom_ext (Submonoid.powers (l : W)) (RingHom.ext fun a => by
      simp only [RingHom.comp_apply]; rw [preMap_alg]; exact hκ.ext a)
  refine ⟨A0 x, D x, ?_⟩
  refine (denseRange_ofPre l (X : W⟦X⟧) ρ).induction_on x
    (isClosed_eq continuous_id ((hκc.comp (AddMonoidHom.continuous_completion _ _)).add
      (continuous_const.mul (AddMonoidHom.continuous_completion _ _)))) fun y => ?_
  rw [hA, hD, show κ (ofPre l (0 : W) 1 (aPre l ρ 0 y)) = _ from RingHom.congr_fun e _, RingHom.comp_apply,
    show toDisc l (X : W⟦X⟧) ρ X = ofPre l (X : W⟦X⟧) ρ (algebraMap _ _ X) from rfl, ← map_mul, ← map_add,
    DPre_apply, X_mul_dFun]
  congr 1
  abel

end GlobalTheory.BSP.DiscSer

namespace GlobalTheory.BSP

theorem exists_const_add_X_mul_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 →
    ∀ (κ : Disc l (0 : Wq l bk.a) 1 →+* bk.DS ρ), IsDiscMap (C : Wq l bk.a →+* bk.S) κ →
    ∀ x : bk.DS ρ, ∃ (c : Disc l (0 : Wq l bk.a) 1) (x₁ : bk.DS ρ), x = κ c + toDisc l (X : bk.S) ρ X * x₁ :=
  fun l _ _ _ ρ hρ0 hρ1 κ hκ x => DiscSer.exists_const_add_X_mul l ρ hρ0 hρ1 κ hκ x

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinMuPowSmulFrobeniusMemAinf
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.LiftStep

theorem ev_eis_mul_mu {l : ℕ} [Fact l.Prime] (a : ℕ) [NeZero a] {e : ℕ} [NeZero e] (ϖ : PiSys l e)
    {ε δ : OCb l} (hε : IsEps ε) (hδ : δ ^ l = ε) :
    ∃ u : Ainf l, IsUnit u ∧ ϖ.ev a (eis l a e) * muOf δ = u * muOf ε := by
  obtain ⟨⟨ξ, hξ, hμ⟩, -⟩ := (GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).2 ε δ hε hδ
  have h : Associated (ϖ.ev a (eis l a e)) ξ := by
    rw [← Ideal.span_singleton_eq_span_singleton, hξ, PiSys.span_ev_eis]
  obtain ⟨v, hv⟩ := h
  refine ⟨((v⁻¹ : (Ainf l)ˣ) : Ainf l), Units.isUnit _, ?_⟩
  rw [hμ, ← hv]
  linear_combination (-(ϖ.ev a (eis l a e) * muOf δ)) * v.inv_mul

section Integral

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type} [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι)

theorem E_pow_mul_iW (n : ℕ) (f : ZMod a → invE l e (A O K)) (hf : ∀ τ, E K l e ^ n * (f τ : K⟦X⟧) ∈ A O K) :
    inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ n * ϖ.iW t K f = inclO l O (ϖ.iTot t K fun τ => ⟨_, hf τ⟩) := by
  have h1 : inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) = ϖ.iW t K (fun _ => EIn l e (invE l e (A O K))) := by
    rw [← ϖ.iTot_E t K, ← ϖ.iW_of_mem t K]
    rfl
  rw [h1, ← map_pow, ← map_mul, ← ϖ.iW_of_mem t K]
  congr 1

theorem integral (α β : ℕ) (hL : ∀ m ∈ P.L, E K l e ^ α • m ∈ P.M) (hM : ∀ m ∈ P.M, E K l e ^ β • m ∈ P.L) :
    (∀ i j, ∃ c : OA l O, inclO l O c = inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ α * frobMat t ϖ P i j) ∧
    (∀ i j, ∃ c : OA l O, inclO l O c = inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ β * frobMatInv t ϖ P i j) ∧
    ∀ y : ME P, y.1 ∈ P.EM α → ∀ i, ∃ c : OA l O, inclO l O c = inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ α * toW t ϖ P y i := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun y hy i => ?_⟩
  · have hm : (fun τ k => P.mx τ k j) ∈ P.L := mem_tot.2 fun τ => Submodule.subset_span ⟨j, rfl⟩
    have h := mem_tot.1 (hL _ hm)
    exact ⟨_, (E_pow_mul_iW t ϖ α _ fun τ => h τ i).symm⟩
  · have hm : (fun (_ : ZMod a) (k : ι) => if k = j then (1 : K⟦X⟧) else 0) ∈ P.M :=
      mem_tot.2 fun τ k => by split_ifs <;> simp [Mc, mem_vecs]
    have h := fun τ => P.mem_extc_iff.1 (mem_tot.1 (hM _ hm) τ) i
    refine ⟨_, (E_pow_mul_iW t ϖ β (fun τ => ((P.mat τ)⁻¹ : GL ι (invE l e (A O K))) i j) fun τ => ?_).symm⟩
    simpa [Matrix.mulVec, dotProduct, PhiMod.mxInv, mul_comm] using h τ
  · have h : ∀ τ, E K l e ^ α * (y.1 τ i) ∈ A O K := fun τ => by simpa using mem_tot.1 hy τ i
    refine ⟨ϖ.iTot t K fun τ => ⟨_, h τ⟩, ?_⟩
    rw [toW_apply]
    exact (E_pow_mul_iW t ϖ α (fun τ => ⟨y.1 τ i, mem_tot.1 y.2 τ i⟩) h).symm

end Integral

end GlobalTheory.BKGal.LiftStep

theorem GlobalTheory.BKGal.LiftStep.alg_step {S ι : Type} [CommRing S] [Fintype ι] (Ui Ew N Mh : S) (α β : ℕ)
    (hMN : Mh = Ui * Ew ^ (β + α) * N) (Xi : Matrix ι ι S) (m y : ι → S) (Yc : ι → ι → S) (yc : ι → S)
    (hY : ∀ i j, Yc i j = Ew ^ β * Xi i j) (hy : ∀ j, yc j = Ew ^ α * y j) :
    Mh • (Xi *ᵥ (m + y)) = (Matrix.of fun i j => Ui * Ew ^ α * Yc i j) *ᵥ (N • m) +
      fun i => Ui * ∑ j, Yc i j * (N * yc j) := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.of_apply, hY, hy, hMN,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

open GlobalTheory.BKGal.LiftStep in

theorem GlobalTheory.BKGal.LiftStep.mu_pow_smul_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (α β : ℕ), (∀ m ∈ P.L, E K l e ^ α • m ∈ P.M) → (∀ m ∈ P.M, E K l e ^ β • m ∈ P.L) → ∀ ε δ : OCb l, IsEps ε → δ ^ l = ε → ∀ (y : ME P), y.1 ∈ P.EM α → ∀ m₀, phiW t ϖ P m₀ - m₀ = toW t ϖ P y → inclO l O (1 ⊗ₜ (muOf δ ^ (β + α))) • m₀ ∈ MA P ∧ inclO l O (1 ⊗ₜ (muOf ε ^ (β + α))) • phiW t ϖ P m₀ ∈ LA t ϖ P := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I α β hL hM ε δ hε hδ y hy m₀ hm₀
  classical
  obtain ⟨u, hu, hEu⟩ := ev_eis_mul_mu a ϖ hε hδ
  have hfr : WittVector.frobenius (muOf δ) = muOf ε := ((GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).2 ε δ hε hδ).2.1
  obtain ⟨-, hXi, hyI⟩ := integral t ϖ P α β hL hM
  choose cXi hcXi using hXi
  choose cy hcy using hyI y hy
  set ui : Ainf l := ((hu.unit⁻¹ : (Ainf l)ˣ) : Ainf l) with hui
  have hμ : muOf ε = ui * ϖ.ev a (eis l a e) * muOf δ := by
    rw [mul_assoc, hEu, ← mul_assoc, hui, IsUnit.val_inv_mul, one_mul]
  set Ew := inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) with hEw
  set N := inclO l O (1 ⊗ₜ (muOf δ ^ (β + α))) with hN
  set Mh := inclO l O (1 ⊗ₜ (muOf ε ^ (β + α))) with hMh
  set Ui := inclO l O (1 ⊗ₜ (ui ^ (β + α))) with hUi
  have hMN : Mh = Ui * Ew ^ (β + α) * N := by
    rw [hMh, hUi, hEw, hN, ← map_pow, ← map_mul, ← map_mul, Algebra.TensorProduct.tmul_pow, one_pow,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul, hμ, mul_pow, mul_pow]
  have hFN : frobOW l O N = Mh := by
    rw [hN, frobOW_inclO, frobOA_tmul, map_pow, hfr]
  set y' := toW t ϖ P y with hy'
  have hF : (fun i => frobOW l O (m₀ i)) = frobMatInv t ϖ P *ᵥ (m₀ + y') := by
    have h1 : frobMat t ϖ P *ᵥ (fun i => frobOW l O (m₀ i)) = m₀ + y' := by
      rw [← phiW_apply]; exact sub_eq_iff_eq_add'.1 hm₀
    rw [← h1, Matrix.mulVec_mulVec, frobMatInv_mul, Matrix.one_mulVec]
  set z : ι → OW l O := N • m₀ with hz
  have hFz : (fun i => frobOW l O (z i)) = Mh • (fun i => frobOW l O (m₀ i)) := by
    funext i
    simp only [hz, Pi.smul_apply, smul_eq_mul, map_mul, hFN]
  set Y : Matrix ι ι (OA l O) := fun i j => (1 ⊗ₜ (ui ^ (β + α))) * (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ α * cXi i j
  set w : ι → OA l O := fun i => (1 ⊗ₜ (ui ^ (β + α))) * ∑ j, cXi i j * ((1 ⊗ₜ (muOf δ ^ (β + α))) * cy j)
  have heq : (fun i => frobOW l O (z i)) = (Y.map (inclO l O)) *ᵥ z + (fun i => inclO l O (w i)) := by
    rw [hFz, hF, alg_step Ui Ew N Mh α β hMN (frobMatInv t ϖ P) m₀ y' (fun i j => inclO l O (cXi i j))
      (fun j => inclO l O (cy j)) hcXi hcy]
    congr 2
    · ext i j
      change _ = inclO l O ((1 ⊗ₜ (ui ^ (β + α))) * (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ α * cXi i j)
      rw [map_mul, map_mul, map_pow]
      rfl
    · funext i
      simp only [w, map_mul, map_sum]
      rfl
  have hint := GlobalTheory.T.frobenius_integrality_coeffTensorAinf_vector l O ι Y w z heq
  choose c hc using hint
  refine ⟨⟨c, funext fun i => hc i⟩, ⟨fun i => frobOA l O (c i), ?_⟩⟩
  rw [inclL_apply, phiW_apply, ← Matrix.mulVec_smul, ← hFz]
  congr 1
  funext i
  rw [← frobOW_inclO]
  exact congrArg _ (hc i)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCharacterJumpsOfExactDegreeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_character_jumps_of_exact_degree : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ μ : ↥(GK K) →* (↥LL.1)ˣ, Continuous (fun g : ↥(GK K) => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → ∀ d : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ, (∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ w ∈ DcrisL (P.PD K) (charRep μ) (τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)), ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ) ∧ ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∉ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ + 1)) → IsCrys (P.PD K) (charRep μ) → ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ), multV (P.PD K) (charRep μ) τ b = if b = d τ then 1 else 0 := by
  first | exact @GlobalTheory.Per.CharJumps.jumps_of_exact_degree | exact GlobalTheory.Per.CharJumps.jumps_of_exact_degree | (intros; apply GlobalTheory.Per.CharJumps.jumps_of_exact_degree <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeDiscSpanFrobeniusStable
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP

theorem mulVec_frob_of_unit {R D : Type} [CommRing R] [CommRing D] {d : ℕ} (j : R →+* D) (Φ : D →+* D)
    (Ψ : R →+* R) (h : ∀ r, j (Ψ r) = Φ (j r)) (c : Rˣ) (W : Matrix (Fin d) (Fin d) D)
    (B : Matrix (Fin d) (Fin d) R) (hW : j c • W.map Φ = W * B.map j) (x : Fin d → R) :
    W *ᵥ (fun a => j (((c⁻¹ : Rˣ) : R) * (B *ᵥ fun b => Ψ (x b)) a)) =
      fun a => Φ ((W *ᵥ fun b => j (x b)) a) := by
  have e1 : (fun a => j (((c⁻¹ : Rˣ) : R) * (B *ᵥ fun b => Ψ (x b)) a)) =
      j ((c⁻¹ : Rˣ) : R) • (B.map j *ᵥ fun b => Φ (j (x b))) := by
    funext a
    simp [Matrix.mulVec, dotProduct, map_sum, h]
  have e2 : (fun a => Φ ((W *ᵥ fun b => j (x b)) a)) = W.map Φ *ᵥ fun b => Φ (j (x b)) := by
    funext a
    simp [Matrix.mulVec, dotProduct, map_sum]
  rw [e1, e2, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← hW, Matrix.smul_mulVec, smul_smul, ← map_mul,
    Units.inv_mul, map_one, one_smul]

theorem seed_span_frobenius_stable : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∀ y, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) y → (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) (fun a => WittVector.frobenius (y a)) := by
  intro l hl K bk τ hτ d ρ hρ s y ⟨x, hx⟩
  obtain ⟨-, -, ⟨h0, h1, -⟩, -⟩ := GlobalTheory.T.breuilKisin_flat_radius_ideal_facts l K bk
  have hpow : bk.ρ₀ ^ l ≤ bk.ρ₀ := pow_le_of_le_one h0.le h1.le hl.out.ne_zero
  obtain ⟨Ψ, hΨ⟩ := exists_discMap_of_pow_dvd l bk.S bk.S (frobS l bk.a) X X bk.ρ₀ bk.ρ₀ l h0
    (by rw [frobS_X]) hpow
  obtain ⟨Φ, hΦ⟩ := exists_discMap_of_pow_dvd l (Ainf l) (Ainf l) WittVector.frobenius (bk.ev X) (bk.ev X)
    bk.ρ₀ bk.ρ₀ l h0 (by rw [← bk.ev_frob, frobS_X, map_pow]) hpow
  have hu : IsUnit (((l : ℕ) : bk.DS bk.ρ₀) ^ (s.c₁ + s.c₂) *
      toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a bk.E) ^ s.N) :=
    ((isUnit_l_disc l (X : bk.S) bk.ρ₀).pow _).mul ((isUnit_toDisc_frobS_E l K bk).pow _)
  obtain ⟨c, hc⟩ := hu
  refine ⟨fun a => ((c⁻¹ : (bk.DS bk.ρ₀)ˣ) : bk.DS bk.ρ₀) *
    ((s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map (toDisc l (X : bk.S) bk.ρ₀) *ᵥ
      fun b => Ψ (x b)) a, fun j hj => ?_⟩
  have hcomm : j.comp Ψ = Φ.comp j := by
    refine IsDiscMap.unique (DiscBasic.isDiscMap_comp l _ _ hΨ hj) ?_
    have e : bk.ev.comp (frobS l bk.a) = (WittVector.frobenius : Ainf l →+* Ainf l).comp bk.ev :=
      RingHom.ext bk.ev_frob
    rw [e]
    exact DiscBasic.isDiscMap_comp l _ _ hj hΦ
  have hW := GlobalTheory.T.discPeriods_map_frobenius_eq_mul l K bk τ hτ d ρ hρ s Φ hΦ
  rw [mulVec_frob_of_unit j Φ Ψ (RingHom.congr_fun hcomm) c s.W _ ?_ x, hx j hj]
  · funext a
    exact hΦ.ext _
  · rw [hc, map_mul, map_pow, map_pow, map_natCast, hj.ext, Matrix.map_map]
    refine hW.trans ?_
    congr 2
    funext a
    exact (hj.ext a).symm

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeFrobeniusInverseMatrix
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP.crystallineLattice_frobenius_inverse_matrix

theorem frob_inverse {R : Type} [CommRing R] [IsDomain R] {d : ℕ} (Φ : R →+* R)
    (W W' B : Matrix (Fin d) (Fin d) R) (t e lam : R) (ht : t ≠ 0)
    (hW : W * W' = t • (1 : Matrix (Fin d) (Fin d) R)) (hB : lam • W.map Φ = W * B) (hΦ : Φ t = e * t) :
    B * W'.map Φ = (lam * e) • W' := by
  have hdet : W.det ≠ 0 := by
    intro h
    have h1 := congrArg Matrix.det hW
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    exact pow_ne_zero _ ht h1.symm
  have h2 : W.map Φ * W'.map Φ = (e * t) • (1 : Matrix (Fin d) (Fin d) R) := by
    rw [← Matrix.map_mul, hW, ← hΦ]
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  have h3 : W * (B * W'.map Φ - (lam * e) • W') = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← hB, Matrix.smul_mul, h2, Matrix.mul_smul, hW, smul_smul, smul_smul,
      mul_assoc, sub_self]
  have h4 : W.det • (B * W'.map Φ - (lam * e) • W') = 0 := by
    rw [← Matrix.one_mul (B * W'.map Φ - (lam * e) • W'), ← Matrix.smul_mul, ← Matrix.adjugate_mul,
      Matrix.mul_assoc, h3, Matrix.mul_zero]
  rw [← sub_eq_zero]
  ext i j
  have h5 := congrFun (congrFun h4 i) j
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h5
  exact (mul_eq_zero.1 h5).resolve_left hdet

theorem radius_mem (l : ℕ) [hl : Fact l.Prime] (K : FinExt l) (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  have h1 : (1 : ℝ≥0) < (l : ℝ≥0) := by exact_mod_cast hl.out.one_lt
  have h2 : (0 : ℝ) < (bk.Ep.natDegree : ℝ) := by exact_mod_cast bk.deg_pos
  refine ⟨NNReal.rpow_pos (lt_trans zero_lt_one h1), ?_⟩
  exact NNReal.rpow_lt_one_of_one_lt_of_neg h1 (neg_lt_zero.2 (one_div_pos.2 h2))

end GlobalTheory.BSP.crystallineLattice_frobenius_inverse_matrix

theorem GlobalTheory.BSP.seed_frob_inverse : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap WittVector.frobenius Φ → (s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map bk.iS * s.W'.map Φ = (((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) * bk.iS bk.E ^ (2 * s.N)) • s.W' := by
  intro l _ K bk τ hτ d ρ hρ s Φ hΦ
  obtain ⟨h0, h1⟩ := GlobalTheory.BSP.crystallineLattice_frobenius_inverse_matrix.radius_mem l K bk
  haveI := (GlobalTheory.T.breuilKisin_ainfDisc_isDomain_norm_bounds l K bk bk.ρ₀ h0 h1).1
  have hτ0 := (GlobalTheory.T.breuilKisin_period_isUnit_wittTilt_and_ne_zero l K bk τ hτ).2.1
  refine GlobalTheory.BSP.crystallineLattice_frobenius_inverse_matrix.frob_inverse Φ s.W s.W' _ (bk.iA τ ^ (2 * s.N)) _ _ (pow_ne_zero _ hτ0) s.W_mul
    (GlobalTheory.T.discPeriods_map_frobenius_eq_mul l K bk τ hτ d ρ hρ s Φ hΦ) ?_
  have h2 : Φ (bk.iA τ) = bk.iS bk.E * bk.iA τ := by
    have h3 := hΦ.ext τ
    rw [hτ.1, map_mul] at h3
    exact h3
  rw [map_pow, h2, mul_pow]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeHodgeTateJumpsFinite
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.JumpsFinite

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem jumps_finite : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL), ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ →
    (Jumps (PD := (D.loc l).PD K) T).Finite := by
  intro D HW l _ K s LL h T hcrys
  have hP := GlobalTheory.NL.Points.points D HW l K s LL h
  have hfin : Finite (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hP.2.2.2.1]
    haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
    exact Module.finrank_pos.ne'
  have hsub : Jumps (PD := (D.loc l).PD K) T ⊆
      ⋃ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, {a | IsJumpV ((D.loc l).PD K) T.ρ τ a} := by
    rintro a ⟨τ, hτ⟩
    exact Set.mem_iUnion.2 ⟨τ, hτ⟩
  refine (Set.finite_iUnion fun τ => ?_).subset hsub
  obtain ⟨i, ζ, hpt⟩ := hP.2.2.1 τ
  obtain ⟨-, hemb, ι, hcomp⟩ := hP.2.1 i ζ τ hpt
  have hC := GlobalTheory.NL.CompD.component D HW l K s LL h T hcrys i ζ τ ι hcomp hemb
  have hrank := hC.2.2.2
  set Dm := Di (HW l) h T i with hDm
  have hDfin : FiniteDimensional ↥LL.1 ↥Dm := by
    rcases Nat.eq_zero_or_pos (Module.finrank ↥LL.1 T.V) with h0 | hpos
    · have hV : Subsingleton T.V := Module.finrank_zero_iff.1 h0
      have hVB : Subsingleton (T.V ⊗[ℚ_[l]] (D.loc l).R.B) := by
        refine ⟨fun x y => ?_⟩
        have hz : ∀ z : T.V ⊗[ℚ_[l]] (D.loc l).R.B, z = 0 := by
          intro z
          induction z using TensorProduct.induction_on with
          | zero => rfl
          | tmul v b => rw [Subsingleton.elim v 0, TensorProduct.zero_tmul]
          | add x y hx hy => rw [hx, hy, add_zero]
        rw [hz x, hz y]
      infer_instance
    · exact Module.finite_of_finrank_pos (hrank ▸ hpos)
  let S : ℤ → Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] (D.loc l).R.B) := fun a =>
    Dm ⊓ (FilAt ((D.loc l).PD K) T τ a).comap (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V))
  have hSanti : Antitone S := by
    refine antitone_int_of_succ_le fun a => inf_le_inf_left _ (Submodule.comap_mono ?_)
    exact sup_le_sup_right (GlobalTheory.Pst.filDR_succ_le ((D.loc l).PD K) T.ρ τ a) _
  let f : ℤ → ℕ := fun a => Module.finrank ↥LL.1 ↥(S a)
  have hfS : ∀ a, Module.finrank ↥LL.1 ↥(S a) ≤ Module.finrank ↥LL.1 ↥Dm := fun a =>
    Submodule.finrank_mono inf_le_left
  have hlt : ∀ a b, IsJumpV ((D.loc l).PD K) T.ρ τ a → a < b → f b < f a := by
    intro a b ha hab
    obtain ⟨d, hd, h1, h2⟩ := GlobalTheory.T.exists_crystallineLetter_of_hodgeJump D HW l K s LL h T hcrys i ζ τ hpt a ha
    have hle : S b ≤ S (a + 1) := hSanti (by omega)
    have hlt' : S (a + 1) < S a := by
      refine lt_of_le_of_ne (hSanti (by omega)) fun heq => h2 ?_
      have : d ∈ S a := ⟨hd, h1⟩
      rw [← heq] at this
      exact this.2
    haveI : FiniteDimensional ↥LL.1 ↥(S a) :=
      Submodule.finiteDimensional_of_le (inf_le_left : S a ≤ Dm)
    exact lt_of_le_of_lt (Submodule.finrank_mono hle) (Submodule.finrank_lt_finrank_of_lt hlt')
  refine Set.Finite.of_finite_image (f := f) ((Set.finite_Iic (Module.finrank ↥LL.1 ↥Dm)).subset ?_) ?_
  · rintro _ ⟨a, -, rfl⟩
    exact hfS a
  · intro a ha b hb hab
    rcases lt_trichotomy a b with hh | hh | hh
    · exact absurd hab (hlt a b ha hh).ne'
    · exact hh
    · exact absurd hab (hlt b a hb hh).ne

end GlobalTheory.NL.JumpsFinite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineRestrictFiniteExtensionJumpsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_restrict_finite_extension_jumps : ∀ D : D7, Formalism.MainNotions.ElementDenominator.adm12 D := by
  first | exact @GlobalTheory.Per.ResFinite.adm12_elementDenominator | exact GlobalTheory.Per.ResFinite.adm12_elementDenominator | (intros; apply GlobalTheory.Per.ResFinite.adm12_elementDenominator <;> assumption)
end

