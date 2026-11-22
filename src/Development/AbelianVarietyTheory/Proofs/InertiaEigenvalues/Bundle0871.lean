import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0652
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0866
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0764
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0607
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0624
import GroundTheory.AutomorphicForms.FourierWhittaker
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0375
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1438
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1435
import Development.AbelianVarietyTheory.Definitions.Divisors.MemL2OfSmoothVector
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import GroundTheory.AutomorphicForms.ReductionFinite
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WordAppendSingle
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NegOneNotMemNatLat
import GroundTheory.GlobalFields.Adele.Compact
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0867
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0026
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0743
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGenerationThetaFunctionsTwistPlace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0689
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0865
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalWhittakerCoeffEqIteratedColumnTransform
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.WhitCols

open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker

variable {E : Type} [Field E] [NumberField E]

theorem avg_eq_setIntegral {ι : Type} [Fintype ι] (Φ : (ι → Ad E) → ℂ) (hΦ : Per (ratV E ι) Φ) :
    avg (ratV E ι) Φ = ∫ x in vecDomain E ι, Φ x ∂vecMeasure E ι := by
  have hF : IsAddFundamentalDomain (ratV E ι) (vecDomain E ι) (vecMeasure E ι) := isAddFundamentalDomain_vecDomain
  obtain ⟨-, -, -, h⟩ := GlobalTheory.CuspGeneric.setIntegral_eq_mass_mul_avg (ι → Ad E) (ratV E ι) (isCoLat_ratV E ι)
    (vecMeasure E ι) (vecDomain E ι) inferInstance hF Φ hΦ
  rw [h, vecMeasure_vecDomain]
  simp

theorem diagonal_eq_ratGL (n : ℕ) (γ : GL (Fin n) E) : AdelicGLn.diagonal E n γ = ratGL E n γ := rfl

def colIx {a k : ℕ} (hk : k < a) : Fin k ≃ UnipotentBlockColumnIndex a k k where
  toFun i := ⟨(⟨i.1, by omega⟩, ⟨k, hk⟩), i.2, le_rfl, le_rfl⟩
  invFun t := ⟨t.1.1.1, t.2.1⟩
  left_inv i := rfl
  right_inv t := by
    obtain ⟨⟨i, j⟩, h1, h2, h3⟩ := t
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      dsimp only at h1 h2 h3 ⊢
      omega

def colHom {a k : ℕ} (hk : k < a) : (Fin k → Ad E) ≃ₜ+ (UnipotentBlockColumnIndex a k k → Ad E) where
  toFun x := fun t => x ((colIx hk).symm t)
  invFun y := fun i => y (colIx hk i)
  left_inv x := by funext i; simp
  right_inv y := by funext t; simp
  map_add' x y := rfl
  continuous_toFun := continuous_pi fun t => continuous_apply _
  continuous_invFun := continuous_pi fun i => continuous_apply _

theorem colHom_mem_iff {a k : ℕ} (hk : k < a) (x : Fin k → Ad E) :
    colHom hk x ∈ ratV E (UnipotentBlockColumnIndex a k k) ↔ x ∈ ratV E (Fin k) := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun i => c (colIx hk i), funext fun i => ?_⟩
    have := congrFun hc (colIx hk i)
    simpa [colHom] using this
  · rintro ⟨c, rfl⟩
    exact ⟨fun t => c ((colIx hk).symm t), rfl⟩

theorem blkU_colHom {a k : ℕ} (hk : k < a) (x : Fin k → Ad E) :
    (blkU (colHom hk x) : GL (Fin a) (Ad E)) = colGL k x := by
  refine Units.ext ?_
  ext i j
  rw [blkU_apply]
  simp only [colGL, coe_uGL, uMat_apply, colX_apply, Matrix.one_apply, colHom, colIx]
  split_ifs <;> first | rfl | simp_all
  all_goals (exfalso; simp only [Fin.ext_iff, Fin.lt_def, Fin.le_def] at *; omega)

theorem dot_colHom {a k : ℕ} (hk : k < a) (x : Fin k → Ad E) :
    dot (eLast a k) (colHom hk x) = pair (lastVec k) x := by
  rw [dot, pair, ← (colIx hk).sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [colHom, eLast, lastVec, colIx, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
  by_cases h : (i : ℕ) + 1 = k <;> simp [h]

theorem colT_eq_stepCoeff {a k : ℕ} (hk : k < a) {F : GA E a → ℂ} (hc : Continuous F)
    (hl : ∀ (ξ : Fin k → E) g, F (AdelicGLn.diagonal E a (colGL k ξ) * g) = F g) (g : GA E a) :
    colT (GlobalTheory.StdCharConductor.psi E) k F g = stepCoeff k F g := by
  have hψ := GlobalTheory.StdCharConductor.stdPsi_psi E
  have hl' : ∀ (c : UnipotentBlockColumnIndex a k k → E) g, F (ratGL E a (blkU c) * g) = F g := by
    intro c g
    have e : ratGL E a (blkU c) = AdelicGLn.diagonal E a (colGL k (fun i => c (colIx hk i))) := by
      rw [ratGL_blkU, diagonal_colGL, ← blkU_colHom hk]
      congr 1
      funext t
      simp [colHom]
    rw [e, hl]
  have hP := per_coef hψ (eLast a k) hc hl' g
  have hP' : Per (ratV E (Fin k)) (fun x => (fun y : UnipotentBlockColumnIndex a k k → Ad E =>
      GlobalTheory.StdCharConductor.psi E (-dot (eLast a k) y) * F (blkU y * g)) (colHom hk x)) := by
    refine ⟨hP.1.comp (colHom hk).continuous_toFun, fun γ hγ x => ?_⟩
    simp only [map_add]
    exact hP.2 _ ((colHom_mem_iff hk γ).2 hγ) _
  unfold colT coefF
  rw [← avg_equiv (Fin k → Ad E) (UnipotentBlockColumnIndex a k k → Ad E) (ratV E (Fin k)) (ratV E (UnipotentBlockColumnIndex a k k)) (isCoLat_ratV E _)
    (isCoLat_ratV E _) (colHom hk) (colHom_mem_iff hk) _ hP, avg_eq_setIntegral _ hP']
  unfold stepCoeff vecCoeff
  refine setIntegral_congr_fun measurableSet_vecDomain fun x _ => ?_
  simp only [blkU_colHom, dot_colHom, GlobalTheory.StdCharConductor.psi_apply]
  ring

def IsUU {j : ℕ} (h : Matrix (Fin j) (Fin j) E) : Prop :=
  ∀ i l : Fin j, l ≤ i → h i l = (1 : Matrix (Fin j) (Fin j) E) i l

theorem IsUU.isLastRowUnit {j : ℕ} {h : Matrix (Fin j) (Fin j) E} (hh : IsUU h) : IsLastRowUnit h := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · funext c; exact c.elim0
  · funext c
    have hc : c ≤ (⟨j - 1, by omega⟩ : Fin j) := by rw [Fin.le_def]; show (c : ℕ) ≤ j - 1; omega
    rw [vecMul_lastVec _ _ hj, hh _ _ hc, Matrix.one_apply]
    simp only [lastVec, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)

omit [NumberField E] in
theorem isUU_blockMat {j : ℕ} {h : Matrix (Fin j) (Fin j) E} (hh : IsUU h) :
    IsUU (blockMat (n := j + 1) (Nat.le_succ j) h) := by
  intro i l hli
  rw [blockMat_apply]
  split_ifs with ha hb
  · rw [hh _ _ (by rw [Fin.le_def] at hli ⊢; exact hli), Matrix.one_apply, Matrix.one_apply]
    simp only [Fin.ext_iff]
  · exfalso; rw [Fin.le_def] at hli; omega
  all_goals simp_all [Matrix.one_apply]

omit [NumberField E] in
theorem isUU_colX {j : ℕ} (ξ : Fin j → E) : IsUU (uMat (colX (n := j + 1) j ξ)) := by
  intro i l hli
  rw [uMat_apply, Matrix.one_apply]
  split_ifs <;> first | rfl | (exfalso; simp only [Fin.lt_def, Fin.le_def] at *; omega)

theorem partialCoeff_uu {n : ℕ} {f : GA E n → ℂ}
    (hf : ∀ γ ∈ mirU E n 0, ∀ g, f (ratGL E n γ * g) = f g) :
    ∀ (m j : ℕ), n - j = m → ∀ (hj : j ≤ n) (h : GL (Fin j) E), IsUU (h : Matrix (Fin j) (Fin j) E) → ∀ g,
      partialCoeff f j (AdelicGLn.diagonal E n (blockGL hj h) * g) = partialCoeff f j g := by
  intro m
  induction m with
  | zero =>
    intro j hjm hj h hh g
    obtain rfl : j = n := by omega
    rw [partialCoeff_self]
    have : blockGL hj h = h := Units.ext (by rw [coe_blockGL]; exact blockMat_self _)
    rw [this]
    exact hf h (mem_mirU.2 fun i k _ hk => hh i k hk) g
  | succ m ih =>
    intro j hjm hj h hh g
    have hjn : j < n := by omega
    rw [partialCoeff_of_lt f hjn]
    have hB : ∀ g, partialCoeff f (j + 1) (AdelicGLn.diagonal E n (blockGL hjn.le h) * g) =
        partialCoeff f (j + 1) g := by
      intro g
      rw [← blockGL_blockGL (Nat.le_succ j) hjn]
      exact ih (j + 1) (by omega) hjn _ (isUU_blockMat hh) g
    have hC : ∀ (ξ : Fin j → E) g, partialCoeff f (j + 1) (AdelicGLn.diagonal E n (colGL j ξ) * g) =
        partialCoeff f (j + 1) g := by
      intro ξ g
      rw [colGL_eq_blockGL (Nat.lt_succ_self j) hjn]
      exact ih (j + 1) (by omega) hjn _ (isUU_colX _) g
    rw [stepCoeff_diagonal_blockGL hjn h hB hC g, hh.isLastRowUnit]
    rfl

theorem colT_partialCoeff {m : ℕ} {f : GA E (m + 1) → ℂ} (hc : Continuous f)
    (hf : ∀ γ ∈ mirU E (m + 1) 0, ∀ g, f (ratGL E (m + 1) γ * g) = f g) {k : ℕ} (hk : k < m + 1) :
    colT (GlobalTheory.StdCharConductor.psi E) k (partialCoeff f (k + 1)) = partialCoeff f k := by
  funext g
  rw [partialCoeff_of_lt f hk]
  refine colT_eq_stepCoeff hk (continuous_partialCoeff hc _) (fun ξ g => ?_) g
  rw [colGL_eq_blockGL (Nat.lt_succ_self k) hk]
  exact partialCoeff_uu hf _ (k + 1) rfl hk _ (isUU_colX _) g

theorem whit_partialCoeff {m : ℕ} {f : GA E (m + 1) → ℂ} (hc : Continuous f)
    (hf : ∀ γ ∈ mirU E (m + 1) 0, ∀ g, f (ratGL E (m + 1) γ * g) = f g) :
    ∀ i, i ≤ m → GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) i (partialCoeff f (i + 1)) = partialCoeff f 1
  | 0, _ => rfl
  | i + 1, hi => by
    rw [GlobalTheory.CuspGeneric.whit_succ, colT_partialCoeff hc hf (by omega : i + 1 < m + 1),
      whit_partialCoeff hc hf i (by omega)]

theorem whit_eq_colWhit : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (f : GA E (m + 1) → ℂ), Continuous f →
    (∀ γ ∈ mirU E (m + 1) 0, ∀ g, f (ratGL E (m + 1) γ * g) = f g) →
    ∀ g, GlobalTheory.JSW.whit f g = GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m f g := by
  intro E _ _ m f hc hf g
  rw [GlobalTheory.JSW.whit, whittaker_eq_partialCoeff hc (Nat.succ_pos m), ← whit_partialCoeff hc hf m le_rfl,
    partialCoeff_self]

end GlobalTheory.WhitCols
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodSmoothDecayModerateGrowthRightTranslate
section
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

noncomputable section

namespace GlobalTheory.RtGood

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def conjL (y : GL (Fin a) (Cinf E)) (X : Lie E a) : Lie E a := toL ((y⁻¹).val * Matrix.of X * y.val)

theorem lie_mul_rt (y : GL (Fin a) (Cinf E)) (k : GL (Fin a) (Af E)) (X : Lie E a) :
    lie E a X * rt E a (infGL E a y * finGL E a k) = rt E a (infGL E a y * finGL E a k) * lie E a (conjL y X) := by
  have h1 := GlobalTheory.CapAdInv.rt_lie y ((y⁻¹).val * Matrix.of X * y.val)
  have e : toL (y.val * ((y⁻¹).val * Matrix.of X * y.val) * (y⁻¹).val) = X := by
    simp [mul_assoc]
  rw [e] at h1
  have h2 := lie_rt_fin (conjL y X) k
  have h1' : lie E a X * rt E a (infGL E a y) = rt E a (infGL E a y) * lie E a (conjL y X) := h1.symm
  calc lie E a X * rt E a (infGL E a y * finGL E a k)
      = lie E a X * rt E a (infGL E a y) * rt E a (finGL E a k) := by rw [map_mul, mul_assoc]
    _ = rt E a (infGL E a y) * (lie E a (conjL y X) * rt E a (finGL E a k)) := by rw [h1', mul_assoc]
    _ = rt E a (infGL E a y * finGL E a k) * lie E a (conjL y X) := by rw [h2, map_mul, mul_assoc]

theorem word_rt (y : GL (Fin a) (Cinf E)) (k : GL (Fin a) (Af E)) (l : List (Lie E a)) (φ : Sm E a) :
    GlobalTheory.GLFin.word l (rt E a (infGL E a y * finGL E a k) φ) =
      rt E a (infGL E a y * finGL E a k) (GlobalTheory.GLFin.word (l.map (conjL y)) φ) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    rw [List.map_cons, GlobalTheory.MSpanDecay.word_cons, GlobalTheory.MSpanDecay.word_cons, ih, ← Module.End.mul_apply,
      lie_mul_rt, Module.End.mul_apply]

theorem height_conj_le (y : GL (Fin a) (Cinf E)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : GL (Fin a) (Cinf E), height (y⁻¹ * u * y) ≤ K * height u := by
  set M : ℝ := ‖rmul (toL y.val)‖ * ‖lmul (toL (y⁻¹).val)‖ with hM
  have hM0 : 0 ≤ M := by positivity
  have key : ∀ u : GL (Fin a) (Cinf E), ‖toL (y⁻¹ * u * y).val‖ ≤ M * ‖toL u.val‖ := by
    intro u
    have e : toL (y⁻¹ * u * y).val = rmul (toL y.val) (lmul (toL (y⁻¹).val) (toL u.val)) := rfl
    rw [e, hM, mul_assoc]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
  refine ⟨1 + M, by positivity, fun u => ?_⟩
  have hi : (y⁻¹ * u * y)⁻¹ = y⁻¹ * u⁻¹ * y := by group
  have k1 := key u
  have k2 := key u⁻¹
  have n1 := norm_nonneg (toL u.val)
  have n2 := norm_nonneg (toL (u⁻¹).val)
  unfold height
  rw [hi]
  nlinarith

theorem decays_rt {G : GA E a → ℂ} (hG : GlobalTheory.ShortVecDecay.Decays G) (h : GA E a) :
    GlobalTheory.ShortVecDecay.Decays (fun g => G (g * h)) := fun L hL C₀ hC₀ N => by
  obtain ⟨C, hC⟩ := hG L hL (C₀ * {h}) (hC₀.mul isCompact_singleton) N
  refine ⟨C, fun g c hc ξ hξ hm => ?_⟩
  have := hC g (c * h) (Set.mul_mem_mul hc (Set.mem_singleton h)) ξ hξ hm
  show ‖G (g * c * h)‖ ≤ _
  rw [mul_assoc]
  exact this

theorem growth_rt {G : GA E a → ℂ} (hG : GlobalTheory.MSpanDecay.Growth G) (h : GA E a) :
    GlobalTheory.MSpanDecay.Growth (fun g => G (g * h)) := by
  obtain ⟨y, k, rfl⟩ : ∃ y k, infGL E a y * finGL E a k = h := ⟨_, _, infGL_mul_finGL h⟩
  obtain ⟨K, hK0, hK⟩ := height_conj_le y
  intro g
  obtain ⟨C, N, hC⟩ := hG (g * (infGL E a y * finGL E a k))
  refine ⟨|C| * K ^ N, N, fun u => ?_⟩
  have hz : y * (y⁻¹ * u * y) = u * y := by group
  have e : g * infGL E a u * (infGL E a y * finGL E a k) =
      g * (infGL E a y * finGL E a k) * infGL E a (y⁻¹ * u * y) := by
    rw [mul_assoc g (infGL E a y * finGL E a k), mul_assoc (infGL E a y), ← infGL_comm (y⁻¹ * u * y) k,
      ← mul_assoc (infGL E a y), ← map_mul, hz, map_mul]
    simp only [mul_assoc]
  show ‖G (g * infGL E a u * (infGL E a y * finGL E a k))‖ ≤ _
  rw [e]
  have h1 := one_le_height u
  have h2 := hK u
  have h3 : 0 ≤ height (y⁻¹ * u * y) := (zero_le_one.trans (one_le_height _))
  calc _ ≤ C * height (y⁻¹ * u * y) ^ N := hC _
    _ ≤ |C| * height (y⁻¹ * u * y) ^ N := mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg h3 N)
    _ ≤ |C| * (K * height u) ^ N := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h3 h2 N) (abs_nonneg C)
    _ = |C| * K ^ N * height u ^ N := by rw [mul_pow, mul_assoc]

theorem good_mul_right : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ)
    (h : GA E a), GlobalTheory.MSpanDecay.Good F → GlobalTheory.MSpanDecay.Good (fun g => F (g * h)) := by
  intro E _ _ _ a F h hF
  obtain ⟨y, k, rfl⟩ : ∃ y k, infGL E a y * finGL E a k = h := ⟨_, _, infGL_mul_finGL h⟩
  obtain ⟨hS, hl⟩ := hF
  refine ⟨rt_mem_Sm _ F hS, fun l => ?_⟩
  have e : (⟨fun g => F (g * (infGL E a y * finGL E a k)), rt_mem_Sm _ F hS⟩ : Sm E a) =
      rt E a (infGL E a y * finGL E a k) ⟨F, hS⟩ := rfl
  rw [e, word_rt]
  obtain ⟨hd, hg⟩ := hl (l.map (conjL y))
  exact ⟨decays_rt hd _, growth_rt hg _⟩

end GlobalTheory.RtGood

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KSpan
section
noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.MSpanDecay

variable (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)

def kSpan : Submodule ℂ (GA E a → ℂ) :=
  Submodule.span ℂ {F | ∃ (X : Type) (_ : MeasurableSpace X) (ν : Measure X) (_ : SFinite ν) (k : X → ℂ)
    (γ : X → GL (Fin a) (Cinf E)) (G : GA E a → ℂ), GlobalTheory.JSW.IsRapidInf ν k γ ∧ Good G ∧
      F = fun g => ∫ x, k x * G (g * infGL E a (γ x)) ∂ν}

end GlobalTheory.MSpanDecay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowCongruenceDetWeightMeasurableInvariant
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.ZUnfWt

open GlobalTheory.ZUnf

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {m : ℕ}

omit [IsTotallyComplex E] in

theorem lastRow_mul_of_mem {h : GA E (m + 1)} (hh : h ∈ mirU (Ad E) (m + 1) m) (g : GA E (m + 1)) :
    GlobalTheory.ZEul.lastRow (h * g) = GlobalTheory.ZEul.lastRow g := by
  funext j
  simp only [GlobalTheory.ZEul.lastRow, Units.val_mul, Matrix.mul_apply]
  rw [Finset.sum_eq_single (Fin.last m)]
  · rw [(mem_mirU_last.1 hh) (Fin.last m), if_pos rfl, one_mul]
  · intro l _ hl
    rw [(mem_mirU_last.1 hh) l, if_neg hl, zero_mul]
  · simp

omit [NumberField E] [IsTotallyComplex E] in

theorem det_blkU {R : Type} [CommRing R] {a k : ℕ} (y : UnipotentBlockColumnIndex a k k → R) : (blkU y : GL (Fin a) R).val.det = 1 := by
  have h := mem_mirU_zero.1 (blkU_mem_mirU 0 y)
  rw [Matrix.det_of_upperTriangular (fun i j hij => h.1 i j hij)]
  simp [h.2]

omit [IsTotallyComplex E] in
theorem detPow_blkU (x : ℝ) {k : ℕ} (y : UnipotentBlockColumnIndex (m + 1) k k → Ad E) : detPow E (m + 1) x (blkU y) = 1 := by
  have hd : Matrix.GeneralLinearGroup.det (blkU y : GA E (m + 1)) = 1 := Units.ext (det_blkU y)
  unfold detPow chiDet
  rw [MonoidHom.comp_apply, hd, map_one]
  simp

omit [IsTotallyComplex E] in

theorem isClosed_natLat (N : ℕ) : IsClosed (natLat E N) := by
  haveI : T2Space (Af E) := inferInstanceAs (T2Space (RestrictedProduct _ _ _))
  have e : natLat E N = (fun z => (N : Af E) * z) '' (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
  rw [e]
  exact ((GroundTheory.Global.isCompact_integralFiniteAdeles E).image (continuous_const.mul continuous_id)).isClosed

omit [IsTotallyComplex E] in
theorem continuous_yFin : Continuous (yFin (E := E) (m := m)) :=
  continuous_pi fun i => (continuous_snd : Continuous (GlobalTheory.RSJ.pFin E)).comp
    ((Units.continuous_val : Continuous fun g : GA E (m + 1) => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E))).matrix_elem
      (Fin.last m) i)

omit [IsTotallyComplex E] in
theorem continuous_detPow (x : ℝ) : Continuous (detPow E (m + 1) x) :=
  continuous_norm.comp (Units.continuous_val.comp
    ((GlobalTheory.HeckeGal.Model.absPow E x).2.1.comp Matrix.GeneralLinearGroup.continuous_det))

omit [IsTotallyComplex E] in
theorem measurable_wt (N : ℕ) (x : ℝ) : Measurable (wt (E := E) (m := m) N x) := by
  let S : Set (Fin (m + 1) → Af E) := {y | ∀ i : Fin (m + 1), y i - (if (i : ℕ) + 1 = m + 1 then 1 else 0) ∈ natLat E N}
  have hS : IsClosed S := by
    have e : S = ⋂ i : Fin (m + 1),
        (fun y : Fin (m + 1) → Af E => y i - (if (i : ℕ) + 1 = m + 1 then 1 else 0)) ⁻¹' natLat E N := by
      ext y; simp [S]
    rw [e]
    exact isClosed_iInter fun i => (isClosed_natLat N).preimage ((continuous_apply i).sub continuous_const)
  have hm : MeasurableSet {g : GA E (m + 1) | yFin g ∈ S} := (hS.preimage continuous_yFin).measurableSet
  have hind : Measurable fun g : GA E (m + 1) => indN N (yFin g) := by
    unfold indN
    exact Measurable.ite hm measurable_const measurable_const
  exact ((Complex.measurable_re.comp hind).mul (continuous_detPow x).measurable).real_toNNReal

theorem wt_measurable_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m N : ℕ) (x : ℝ),
    Measurable (GlobalTheory.ZUnf.wt (E := E) (m := m) N x) ∧
    (∀ γ ∈ mirU E (m + 1) m, ∀ g, GlobalTheory.ZUnf.wt N x (ratGL E (m + 1) γ * g) = GlobalTheory.ZUnf.wt N x g) ∧
    ∀ (k : ℕ) (y : UnipotentBlockColumnIndex (m + 1) k k → Ad E) (g : GA E (m + 1)), GlobalTheory.ZUnf.wt N x (blkU y * g) = GlobalTheory.ZUnf.wt N x g := by
  intro E _ _ _ m N x
  refine ⟨measurable_wt N x, fun γ hγ g => ?_, fun k y g => ?_⟩
  · refine wt_of_lastRow_of_detPow (lastRow_mul_of_mem (map_mem_mirU _ hγ) g) ?_
    rw [GlobalTheory.RSJ.Model.detPow_mul, GlobalTheory.RSJ.Model.detPow_ratGL, one_mul]
  · refine wt_of_lastRow_of_detPow (lastRow_mul_of_mem (blkU_mem_mirU m y) g) ?_
    rw [GlobalTheory.RSJ.Model.detPow_mul, detPow_blkU, one_mul]

end GlobalTheory.ZUnfWt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftBaseDataIsGoodTwistStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftBaseData_isGood_twist : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (F3 : Face3 D A3), Rl.Char3 F3 → ∀ (j : Fin D.R.m) (F : Frame (Vc D j) (Wc D j)) (hF : F.Good) (de : Twist D Circle), de.Good → PlacesOK Rl.Pg de.Q → ∃ (w : Weight D (Vc D j).rank) (mu : ResChars D Circle), (∀ τ, w.ap τ = aPl D j ((Wc D j).sig (tauE D τ)).1 τ) ∧ (∀ τ, w.am τ = aMi D j ((Wc D j).sig (tauE D τ)).1 ((Wc D j).sig (tauE D τ)).2 τ) ∧ ∀ P : LevelP Rl.Pg (Wc D j).rank ℂ, (⟨hF.rank_le, F, ⟨Rl.Pg, P, mu⟩, de, w, Rl.mu0 ((j : ℕ) + 1), Rl.eta⟩ : Base (Vc D j) (Wc D j)).Good := by
  first | exact @GlobalTheory.SeriesTie.BaseGood.base_good | exact GlobalTheory.SeriesTie.BaseGood.base_good | (intros; apply GlobalTheory.SeriesTie.BaseGood.base_good <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGenerationThetaFunctionsTwistPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localGeneration_thetaFunctions_twistPlace : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (v : HeightOneSpectrum (𝓞 D.host.F)), v ∈ Sb → (∀ PP ∈ R.Pg, ¬ GlobalTheory.DownLift.GenFinite.Over PP v) → (∃ PP ∈ R.Q t, GlobalTheory.DownLift.GenFinite.Over PP v) → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), GlobalTheory.DownLift.GenFinite.TypeIn R i t Sb f → GlobalTheory.DownLift.GenFinite.CleanIn R i t Sb f → GlobalTheory.DownLift.GenFinite.LikeOff R i t Sb f → f ∈ Submodule.span ℂ (GlobalTheory.DownLift.GenFinite.StepGen R i t (GlobalTheory.DownLift.GenFinite.dropPl Sb v)) := by
  first | exact @GlobalTheory.DownLift.GenTwist.step_twist | exact GlobalTheory.DownLift.GenTwist.step_twist | (intros; apply GlobalTheory.DownLift.GenTwist.step_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLatticeIndexCartanDecompositionEqNormPowStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LFun (IsSplitChart IsInertChart KGL)
open GlobalTheory.AdelicU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localLatticeIndex_cartanDecomposition_eq_normPow : ∀ (D : D7) (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (a : GL (Fin T.rank) (w.adicCompletion D.host.E)), GlobalTheory.LFun.IsFrameAt w (frameLat T) a → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin T.rank → ℤ) (t : GL (Fin T.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w T.rank, ∀ k₂ ∈ KGL w T.rank, ∀ g : GlobalTheory.FinZeta.Gv T v, GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h g = a * (k₁ * t * k₂) * a⁻¹ → GlobalTheory.LocKerMod.idxAt T w h g = qV D.host.E w ^ (∑ i, max (d i) 0).toNat := by
  first | exact @GlobalTheory.LocKerMod.FrameIdx.idxAt_eq_pow | exact GlobalTheory.LocKerMod.FrameIdx.idxAt_eq_pow | (intros; apply GlobalTheory.LocKerMod.FrameIdx.idxAt_eq_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixCoeffFinitePlaceOffLevelConstMulStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixCoeff_finitePlace_offLevel_const_mul : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ v f, IsFinIdem D v f → (∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f', IsPrimeIdem P e f' → f' ≠ f) → ∀ k, SuppF (Wc D i) f k → ∃ c : ℂ, ∀ γ ∈ GfC (Wc D i), TrivAt (Wc D i) f γ → thetaIP μ 𝓕 (R.ωP i t (1, γ * k) (R.vP i t)) (R.vP i t) = c * thetaIP μ 𝓕 (R.ωP i t (1, γ) (R.vP i t)) (R.vP i t) := by
  first | exact @GlobalTheory.RawLift.GoodFactor.finmult_good | exact GlobalTheory.RawLift.GoodFactor.finmult_good | (intros; apply GlobalTheory.RawLift.GoodFactor.finmult_good <;> assumption)
end

