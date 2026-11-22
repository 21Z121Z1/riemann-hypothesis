import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
import Formalism.HermitianCurvature.StatementC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JointInstanceTheoremA
import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0032
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WordMonicExtraction

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSnChain
section
namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def ChainBd : Prop :=
  ∀ (k r : ℕ) (V E' : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] (Ψ : V → E'), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ →
    ∀ (F : Mat k r → V) (U K : Set (Mat k r)), IsOpen U → CkOn ⊤ (U ∩ GV k r) F → K ⊆ U → K ⊆ GV k r →
    ∀ Bg : ℝ, 0 ≤ Bg →
    (∀ m : ℕ, ∃ C : ℝ, ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
      u.length + v.length ≤ m → ∀ g ∈ K, ‖dLR u v F g‖ ≤ C * gN g ^ (Bg * m)) →
    ∀ m : ℕ, ∃ C : ℝ, ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
      u.length + v.length ≤ m → ∀ g ∈ K, ‖dLR u v (fun g => Ψ (F g)) g‖ ≤ C * gN g ^ (Bg * m)

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FourthWeightDensityOfParts
section
open Matrix Formalism.FourierDecayAlt MeasureTheory
open scoped ENNReal

namespace Formalism.FourierDecayAlt.P

theorem fourth_weight_density_of_parts : C2.SliceDensityOfChangeOfVariables := by
  intro hR hL s M t φ hs hM ht hφ
  obtain ⟨p, rfl⟩ : ∃ p, s = p + 1 := ⟨s - 1, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, M = q + 2 := ⟨M - 2, by omega⟩
  have e1 : p + 1 - 1 = p := by omega
  have e2 : q + 2 - 2 = q := by omega
  have e3 : q + 2 + (p + 1) - 2 = q + p + 1 := by omega
  have e4 : q + 2 + (p + 1) - 3 = q + p := by omega
  simp only [e1, e2, e3, e4]
  set T := ‖t‖ with hT
  have hTpos : 0 < T := norm_pos_iff.mpr ht
  have hsR : (0 : ℝ) < ((p + 1 : ℕ) : ℝ) := by positivity
  set f : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (‖z‖ ^ (2 * p ^ 2)) * φ z with hf
  set S : ℂ → ℝ≥0∞ := fun D => ((Polynomial.nthRoots (p + 1) D).map f).sum with hS
  set ψ : ℂ → ℝ≥0∞ := fun D =>
    ENNReal.ofReal (T ^ (2 * p) * ((((p + 1 : ℕ) : ℝ)) ^ 2)⁻¹) * (ENNReal.ofReal (‖D‖ ^ (2 * q)) * S D) with hψ

  have hA : ∀ c : ℂ, ENNReal.ofReal (T ^ (2 * p * (q + p + 1)) * ‖c‖ ^ (2 * q) * (T ^ (2 * p ^ 2))⁻¹ *
      ((((p + 1 : ℕ) : ℝ)) ^ 2)⁻¹) * ((Polynomial.nthRoots (p + 1) (c * t ^ p)).map f).sum = ψ (t ^ p * c) := by
    intro c
    simp only [hψ, hS, mul_comm c (t ^ p)]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [norm_mul, norm_pow, mul_pow, ← pow_mul, ← hT]
    have : T ^ (2 * p * (q + p + 1)) = T ^ (2 * p) * T ^ (2 * p ^ 2) * T ^ (p * (2 * q)) := by
      rw [← pow_add, ← pow_add]; congr 1; ring
    rw [this]
    have hT2 : T ^ (2 * p ^ 2) ≠ 0 := pow_ne_zero _ hTpos.ne'
    field_simp
  simp only [hA]

  have htp : t ^ p ≠ 0 := pow_ne_zero _ ht
  rw [hL (t ^ p) ψ htp]

  have hC : ∫⁻ D, ψ D = ENNReal.ofReal (T ^ (2 * p) * ((((p + 1 : ℕ) : ℝ)) ^ 2)⁻¹) *
      ∫⁻ D, ENNReal.ofReal (‖D‖ ^ (2 * q)) * S D := by
    simp only [hψ]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  rw [hC, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have hconst : (‖t ^ p‖ ^ 2)⁻¹ * (T ^ (2 * p) * ((((p + 1 : ℕ) : ℝ)) ^ 2)⁻¹) = ((((p + 1 : ℕ) : ℝ)) ^ 2)⁻¹ := by
    rw [norm_pow, ← hT, ← pow_mul]
    have : T ^ (p * 2) ≠ 0 := pow_ne_zero _ hTpos.ne'
    rw [mul_comm p 2]; field_simp
  rw [hconst]

  set g : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (‖z‖ ^ (2 * (p + 1) * q + 2 * p ^ 2)) * φ z with hg
  have hD : ∀ D : ℂ, ENNReal.ofReal (‖D‖ ^ (2 * q)) * S D = ((Polynomial.nthRoots (p + 1) D).map g).sum := by
    intro D
    simp only [hS]
    rw [← Multiset.sum_map_mul_left]
    congr 1
    apply Multiset.map_congr rfl
    intro z hz
    rw [Polynomial.mem_nthRoots (by omega : 0 < p + 1)] at hz
    simp only [hf, hg]
    rw [← hz, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), norm_pow, ← pow_mul, ← pow_add]
    congr 3
    ring
  simp only [hD]

  have hgm : Measurable g := by
    simp only [hg]
    exact (Measurable.ennreal_ofReal ((continuous_norm.pow _).measurable)).mul hφ
  rw [hR (p + 1) g (by omega) hgm]
  simp only [e1]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext z
  simp only [hg]
  rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  have hs2 : ((((p + 1 : ℕ) : ℝ)) ^ 2) ≠ 0 := by positivity
  rw [show (((p + 1 : ℕ) : ℝ) ^ 2)⁻¹ * (((p + 1 : ℕ) : ℝ) ^ 2 * ‖z‖ ^ (2 * p)) = ‖z‖ ^ (2 * p) by
      field_simp, ← pow_add]
  congr 1
  ring

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HsVecApply
section
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.HilbertSchmidtVectorization

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def hsInv (v : PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) : Wq →L[ℂ] Wp :=
  LinearMap.toContinuousLinearMap ((stdOrthonormalBasis ℂ Wq).toBasis.constr ℂ (fun i => v i))

lemma hsInv_basis (v : PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) (i : Fin (Module.finrank ℂ Wq)) :
    hsInv v (stdOrthonormalBasis ℂ Wq i) = v i := by
  have := (stdOrthonormalBasis ℂ Wq).toBasis.constr_basis ℂ (fun i => v i) i
  simpa [hsInv] using this

lemma hsVec_apply' (A : Wq →L[ℂ] Wp) (i : Fin (Module.finrank ℂ Wq)) :
    hsVec A i = A (stdOrthonormalBasis ℂ Wq i) := rfl

lemma hsInv_hsVec (A : Wq →L[ℂ] Wp) : hsInv (hsVec A) = A := by
  apply ContinuousLinearMap.coe_injective
  apply (stdOrthonormalBasis ℂ Wq).toBasis.ext
  intro i
  simp only [ContinuousLinearMap.coe_coe, OrthonormalBasis.coe_toBasis]
  rw [hsInv_basis, hsVec_apply']

lemma hsVec_hsInv (v : PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) : hsVec (hsInv v) = v := by
  ext i
  rw [hsVec_apply', hsInv_basis]

def hsE : (Wq →L[ℂ] Wp) ≃ₗ[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) where
  toFun := hsVec
  map_add' A B := by ext i; simp [hsVec_apply']
  map_smul' c A := by ext i; simp [hsVec_apply']
  invFun := hsInv
  left_inv := hsInv_hsVec
  right_inv := hsVec_hsInv

def conjE (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) :
    PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) →L[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) :=
  LinearMap.toContinuousLinearMap (hsE.toLinearMap ∘ₗ T.toLinearMap ∘ₗ hsE.symm.toLinearMap)

def adjH (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  LinearMap.toContinuousLinearMap
    (hsE.symm.toLinearMap ∘ₗ (ContinuousLinearMap.adjoint (conjE T)).toLinearMap ∘ₗ hsE.toLinearMap)

lemma hsE_adjH (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) (B : Wq →L[ℂ] Wp) :
    hsVec (adjH T B) = ContinuousLinearMap.adjoint (conjE T) (hsVec B) := by
  show hsE (hsE.symm _) = _
  rw [LinearEquiv.apply_symm_apply]; rfl

lemma conjE_hsVec (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) (A : Wq →L[ℂ] Wp) :
    conjE T (hsVec A) = hsVec (T A) := by
  show hsE (T (hsE.symm (hsE A))) = _
  rw [LinearEquiv.symm_apply_apply]; rfl

theorem adjH_spec (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) (A B : Wq →L[ℂ] Wp) :
    hsInner (T A) B = hsInner A (adjH T B) := by
  unfold hsInner
  rw [hsE_adjH, ContinuousLinearMap.adjoint_inner_left, conjE_hsVec]

lemma adjH_add (T S : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) : adjH (T + S) = adjH T + adjH S := by
  ext B : 1
  apply hsE.injective
  simp only [ContinuousLinearMap.add_apply, map_add]
  show hsVec (adjH (T + S) B) = hsVec (adjH T B) + hsVec (adjH S B)
  rw [hsE_adjH, hsE_adjH, hsE_adjH]
  have : conjE (T + S) = conjE T + conjE S := by
    ext v : 1; simp [conjE]
  rw [this, map_add, ContinuousLinearMap.add_apply]

lemma adjH_smulC (c : ℂ) (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) : adjH (c • T) = (starRingEnd ℂ c) • adjH T := by
  ext B : 1
  apply hsE.injective
  show hsVec (adjH (c • T) B) = hsE (((starRingEnd ℂ c) • adjH T) B)
  rw [ContinuousLinearMap.smul_apply, map_smul]
  show _ = (starRingEnd ℂ c) • hsVec (adjH T B)
  rw [hsE_adjH, hsE_adjH]
  have : conjE (c • T) = c • conjE T := by
    ext v : 1; simp [conjE]
  rw [this, map_smulₛₗ, ContinuousLinearMap.smul_apply]

lemma adjH_smul (c : ℝ) (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) : adjH (c • T) = c • adjH T := by
  rw [← Complex.coe_smul, adjH_smulC, Complex.conj_ofReal, Complex.coe_smul]

def adjR : ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) →L[ℝ] ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) :=
  LinearMap.toContinuousLinearMap
    { toFun := adjH
      map_add' := adjH_add
      map_smul' := adjH_smul }

lemma adjR_apply (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) : adjR T = adjH T := rfl

end Formalism.FourierDecayAlt.P.HilbertSchmidtVectorization
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelZeroEstimateProduct
section
namespace Formalism.FourierDecayAlt.P

open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C

open scoped ComplexOrder

noncomputable section

open Classical

namespace Cx1

theorem psd_pullback {α β : Type} (Y : Finset α) (φ : α → β) (k : β → β → ℂ) (Z : Finset β)
    (hZ : ∀ x ∈ Y, φ x ∈ Z) (h : TB.PSDOn Z k) : TB.PSDOn Y (fun x y => k (φ x) (φ y)) := by
  simp only [TB.PSDOn] at h ⊢
  exact h.submatrix (fun x : Y => (⟨φ x, hZ x x.2⟩ : Z))

theorem psd_zero {α : Type} (Y : Finset α) : TB.PSDOn Y (fun _ _ => (0 : ℂ)) := by
  simp only [TB.PSDOn]
  exact Matrix.PosSemidef.zero

end Cx1

theorem gram_positive_semidefinite : C.GramPSDOfParts := by
  intro E _ _ _ Wp Wq _ _ _ _ S hP _ Kr hK0 Th e ε hε i w Y
  show TB.PSDOn Y (S.gram ε i w.1)
  have prodPSD : ∀ (s : Finset (Fin S.f)) (k : Fin S.f → TB.Pt E → TB.Pt E → ℂ),
      (∀ v, TB.PSDOn Y (k v)) → TB.PSDOn Y (fun p q => ∏ v ∈ s, k v p q) := by
    intro s k hk
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, TB.PSDOn]
      let A : Matrix Unit Y ℂ := Matrix.of fun _ _ => 1
      have h2 := Matrix.posSemidef_conjTranspose_mul_self A
      convert h2 using 1
      ext x y
      simp [A, Matrix.mul_apply]
    | @insert a s ha ih =>
      simp only [TB.PSDOn] at ih ⊢
      have h1 : (Matrix.of fun x y : Y => ∏ v ∈ insert a s, k v x y) =
          (Matrix.of fun x y : Y => k a x y).hadamard (Matrix.of fun x y : Y => ∏ v ∈ s, k v x y) := by
        ext x y
        simp [Finset.prod_insert ha, Matrix.hadamard]
      rw [h1]
      exact (hk a).hadamard ih
  by_cases hi : i ≤ S.G.r + 1
  · have hg : S.gram ε i w.1 =
        fun p q => ∏ v, S.gramLoc v ε i (w.1 v) (loc (S.σ v) p) (loc (S.σ v) q) := by
      funext p q
      simp [Formalism.FourierDecayAlt.C.HidaSetting.gram, hi]
    rw [hg]
    exact prodPSD Finset.univ _ fun v =>
      Cx1.psd_pullback Y (loc (S.σ v)) _ _ (fun x hx => Finset.mem_image_of_mem _ hx)
        (hP v ε hε i hi w _)
  · have hg : S.gram ε i w.1 = fun _ _ => 0 := by
      funext p q
      simp [Formalism.FourierDecayAlt.C.HidaSetting.gram, hi]
    rw [hg]
    exact Cx1.psd_zero Y

theorem words_pos_of_parts : C.WordsPosOfParts := by
  intro E _ _ _ Wp Wq _ _ _ _ S hG Kr hK0 Th e w
  show 0 < Word.size S.P w.1
  unfold Word.size
  apply Finset.prod_pos
  intro v _
  apply List.prod_pos
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  apply abs_pos.mpr
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ha
  have hadm := w.2.1.1 v j hj
  by_cases hb : ((w.1 v)[j]'hj).1 = true
  · rw [if_pos hb] at hadm
    have hy : (∃ a, ((w.1 v)[j]'hj).2 ∈ S.grid v a) ∨ ((w.1 v)[j]'hj).2 ∈ S.grid1 v := by
      rcases Finset.mem_union.mp hadm with h | h
      · exact Or.inl ⟨_, h⟩
      · exact Or.inr h
    exact ((hG v).2.2.2.2.2 _ hy).2.2.1
  · rw [if_neg hb] at hadm
    have hy : (∃ a, ((w.1 v)[j]'hj).2 - 1 ∈ S.grid v a) ∨ ((w.1 v)[j]'hj).2 - 1 ∈ S.grid1 v := by
      rcases Finset.mem_union.mp hadm with h | h
      · exact Or.inl ⟨_, h⟩
      · exact Or.inr h
    have := ((hG v).2.2.2.2.2 _ hy).2.2.2
    rwa [sub_add_cancel] at this

theorem wave_estimate_of_integral : C.EstWaveOfParts := by
  intro E _ _ _ Wp Wq _ _ _ _ S hG hI hP Kr hK0 Th e ε hε i hi1 hi2 w hw hcnt
  obtain ⟨θ, hθ, hb⟩ := hP ε hε i hi1 hi2 w hw hcnt
  exact ⟨θ, hθ, fun Y hY κ hκ => ⟨(hI ε hε i hi1 hi2 w Y hY κ hκ).2,
    fun l hl hl0 => ⟨S.bigPlaces i l, hb Y hY κ hκ l hl hl0⟩⟩⟩

theorem lift_estimate_of_base : C.EstLiftOfParts := by
  intro E _ _ _ Wp Wq _ _ _ _ S h Kr hK0 Th e
  exact h

theorem block_estimate_of_base : C.EstBlockOfParts := by
  intro E _ _ _ Wp Wq _ _ _ _ S C₄ h Kr hK0 Th e
  exact h

theorem level_zero_estimate_product : C.EstEOfParts := by
  intro E _ _ _ Wp Wq _ _ _ _ S jv hG hE Kr hK0 Th e w _
  have hgram : ∀ ε, (S.mkData Kr hK0 Th e).gram ε 0 w [] [] = ∏ v, (S.pd v).RR ε 0 (w.1 v) [] [] := by
    intro ε
    show S.gram ε 0 w.1 [] [] = _
    simp [HidaSetting.gram, HidaSetting.gramLoc, loc, nLoc, nAux]
  have hsize : (S.mkData Kr hK0 Th e).wt w = ∏ v, S.sizeAt v (w.1 v) := rfl
  have hpos : 0 < ∏ v, S.sizeAt v (w.1 v) := by
    rw [← hsize]
    exact words_pos_of_parts E Wp Wq S hG Kr hK0 Th e w
  have hlim : Tendsto (fun ε => ∏ v, (S.pd v).RR ε 0 (w.1 v) [] []) (𝓝[>] 0)
      (𝓝 (∏ v, ((S.sizeAt v (w.1 v) * jv v : ℝ) : ℂ))) :=
    tendsto_finsetProd _ (fun v _ => hE w v)
  have hre := ((Complex.continuous_re.tendsto _).comp hlim).div_const (∏ v, S.sizeAt v (w.1 v))
  have key : (∏ v, ((S.sizeAt v (w.1 v) * jv v : ℝ) : ℂ)).re /
      (∏ v, S.sizeAt v (w.1 v)) = ∏ v, jv v := by
    rw [← Complex.ofReal_prod, Complex.ofReal_re, Finset.prod_mul_distrib,
      mul_div_cancel_left₀ _ hpos.ne']
  rw [key] at hre
  simp_rw [hgram, hsize]
  exact hre

theorem cutoff_of_parts : C.CutoffOfParts := by
  intro E _ _ _ Wp Wq _ _ _ _ S H _ _ Vt hPG Kr hK0 Th e Y hY
  filter_upwards [hPG Y hY] with ε hε p hp q hq _
  exact hε p hp q hq

end

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ModelLevelMultiplier
section
noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

namespace Qx1

theorem model_level_multiplier (P : M.Par) (L : R.LevelData (M.A P) P.r) (hL : M.IsModelLevel P L) (Y : ℂ) :
    L.m0 Y = M.m0A P Y := by
  obtain ⟨-, -, -, -, -, -, hz, -, -, -, -, hGGi, -, hnabs, -⟩ := hL
  simp only [R.LevelData.m0, M.m0A, hz, hGGi, hnabs]

theorem model_level_lowering (P : M.Par) (L : R.LevelData (M.A P) P.r) (hL : M.IsModelLevel P L) (Y : ℂ) :
    L.l0 Y = M.l0A P Y := by
  obtain ⟨-, -, -, -, -, -, -, -, hzb, -, -, hGGi, hnab, -, -⟩ := hL
  simp only [R.LevelData.l0, M.l0A, hzb, hGGi, hnab]

end Qx1

theorem model_is_normal_form : Formalism.FourierDecayAlt.Q.ModelIsNF := by
  intro P L hL Y
  have hm := Qx1.model_level_multiplier P L hL Y
  have hl := Qx1.model_level_lowering P L hL Y
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGG, hGGi, -, -, -⟩ := hL
  simp only [NFData.QQ, hm, hl, hGG, hGGi]
  rfl

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PolynomialDegreeExpansion
section
namespace Formalism.FourierDecayAlt.P.PolynomialDegreeExpansion

open Finset Polynomial Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.RealWeightedForms
open scoped Matrix

theorem first_polynomial_expansion_formula : PositionExpansionTopCoefficients := by
  intro A S V _ _ _ _ _ _ _ _ _ _ ρ QQ q f fi s w n vA vB vAv vBv K sl x Ξ y hData hΞ
  obtain ⟨-, -, -, -, hinj, hnew, -, -, -, -, hx⟩ := hData
  have h := Formalism.FourierDecayAlt.P.FreeActionExpansion.expand ρ QQ f s w vA vB vAv vBv x Ξ hΞ hx (Lp sl y) ?_ ?_ ?_ 1 1
  · simp only [one_smul] at h
    unfold WK
    rw [h]
    congr 1
    simp [Lp, List.map_ofFn, Function.comp_def]
  · intro l hl
    simp only [Lp, List.mem_ofFn] at hl
    obtain ⟨a, rfl⟩ := hl
    simp
  · simp only [Lp, List.map_ofFn]
    exact List.nodup_ofFn.mpr hinj
  · intro l hl
    simp only [Lp, List.mem_ofFn] at hl
    obtain ⟨a, rfl⟩ := hl
    exact hnew a

theorem first_polynomial_degree : GridDegreeIdentity := by
  intro A S V _ _ _ _ _ _ _ _ _ _ ρ QQ q f fi s w n vA vB vAv vBv K sl x grid hData hinj
  obtain ⟨-, -, -, -, -, -, -, hsh1, hsh2, -, -⟩ := id hData
  have h := Formalism.FourierDecayAlt.P.plane_wave_word_formula A (Ix S → V) (frmS ρ (RRw QQ w * Vw f s w)) n K
    (fun _ => ⟨vA, vB, vAv, vBv, s⟩) grid x x (fun _ => ⟨hsh1, hsh2⟩) hinj
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, frmS_apply] at h
  have he : frm ρ (RRw QQ w * Vw f s w) x x = frm ρ (RRw QQ w) (act (Vw f s w) x) x := by
    simp only [frm, act_mul]
  rw [← he, h]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact (first_polynomial_expansion_formula A S V ρ QQ q f fi s w n vA vB vAv vBv K sl x (frmS ρ (RRw QQ w * Vw f s w))
    (fun a => grid a (j a)) hData (fun _ _ => rfl)).symm

theorem u72 : CombinedDegreeSizeBound := by
  intro A S V _ _ _ _ _ _ _ _ _ _ ρ QQ q f fi s w n vA vB vAv vBv K sl x α β grid hData hG0 hImp
    hinj hadm
  have hdeg := first_polynomial_degree A S V ρ QQ q f fi s w n vA vB vAv vBv K sl x grid hData hinj
  calc ‖s‖ ^ K * ‖frm ρ (RRw QQ w) (act (Vw f s w) x) x‖
      = ‖s ^ K * frm ρ (RRw QQ w) (act (Vw f s w) x) x‖ := by rw [norm_mul, norm_pow]
    _ = ‖∑ j : Fin K → Fin (2 * n + 1), ((∏ a, F7.lagCo (grid a) (j a) : ℝ) : ℂ) *
          WK ρ QQ f s w vA vB vAv vBv sl (fun a => grid a (j a)) x‖ := by rw [hdeg]
    _ ≤ ∑ j : Fin K → Fin (2 * n + 1), ‖((∏ a, F7.lagCo (grid a) (j a) : ℝ) : ℂ) *
          WK ρ QQ f s w vA vB vAv vBv sl (fun a => grid a (j a)) x‖ := norm_sum_le _ _
    _ ≤ _ := by
      refine Finset.sum_le_sum fun j _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Finset.abs_prod]
      refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun a _ => abs_nonneg _)
      have h := Real.abs_le_sqrt (first_polynomial_size A S V ρ QQ q f fi s w n vA vB vAv vBv K sl x α β
        (fun a => grid a (j a)) hData hG0 hImp (hadm j).1 (hadm j).2)
      rwa [abs_norm] at h

theorem first_polynomial_degree_of_parts : DegreeIdentityOfParts := fun _ _ _ => first_polynomial_degree

theorem unipotent_degree_of_parts : CombinedBoundOfDegreeSize := fun _ _ => u72

end Formalism.FourierDecayAlt.P.PolynomialDegreeExpansion

theorem Formalism.FourierDecayAlt.P.first_polynomial_expansion_identity : Formalism.FourierDecayAlt.FormPairingAction.PositionExpansionTopCoefficients := Formalism.FourierDecayAlt.P.PolynomialDegreeExpansion.first_polynomial_expansion_formula
theorem Formalism.FourierDecayAlt.P.first_polynomial_degree_identity : Formalism.FourierDecayAlt.FormPairingAction.GridDegreeIdentity := Formalism.FourierDecayAlt.P.PolynomialDegreeExpansion.first_polynomial_degree
theorem Formalism.FourierDecayAlt.P.unipotent_degree_bound : Formalism.FourierDecayAlt.FormPairingAction.CombinedDegreeSizeBound := Formalism.FourierDecayAlt.P.PolynomialDegreeExpansion.u72
theorem Formalism.FourierDecayAlt.P.first_polynomial_degree_of_clauses : Formalism.FourierDecayAlt.FormPairingAction.DegreeIdentityOfParts := Formalism.FourierDecayAlt.P.PolynomialDegreeExpansion.first_polynomial_degree_of_parts
theorem Formalism.FourierDecayAlt.P.unipotent_degree_of_clauses : Formalism.FourierDecayAlt.FormPairingAction.CombinedBoundOfDegreeSize := Formalism.FourierDecayAlt.P.PolynomialDegreeExpansion.unipotent_degree_of_parts
end

