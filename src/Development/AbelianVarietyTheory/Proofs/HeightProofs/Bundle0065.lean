import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0242
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0241
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0004
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPageRunRecord
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0061
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.ConclOfInputs4
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.HasFDerivAtDerFamProdExp
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

namespace GlobalTheory.TypeSum

variable {n : ℕ} {ε : Fin n → Bool}

theorem FamGrowth.bdd_of_isCompact {N : ℕ} {F : List (Mx n) → Mx n → ℂ} (hG : FamGrowth ε N F)
    {w : List (Mx n)} (hw : ∀ Y ∈ w, Y ∈ lieSet ε) {K : Set (Mx n)} (hK : IsCompact K) (hKU : K ⊆ UJset ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ K, ‖F w y‖ ≤ B := by
  obtain ⟨C, hC⟩ := hG w hw
  obtain ⟨M, hM⟩ := hK.bddAbove_image continuous_hs.continuousOn
  refine ⟨|C| * (1 + max M 0) ^ N, by positivity, fun y hy => ?_⟩
  have h1 : hs y ≤ max M 0 := (hM ⟨y, hy, rfl⟩).trans (le_max_left _ _)
  have h0 : 0 ≤ hs y := hs_nonneg y
  calc ‖F w y‖ ≤ C * (1 + hs y) ^ N := hC y (hKU hy)
    _ ≤ |C| * (1 + hs y) ^ N := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (1 + max M 0) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) N) (abs_nonneg C)

def expSweep (K : Set (Mx n)) (X : Mx n) : Set (Mx n) :=
  (fun p : Mx n × ℝ => p.1 * NormedSpace.exp (p.2 • X)) '' (K ×ˢ Set.Icc (-1 : ℝ) 1)

theorem isCompact_expSweep {K : Set (Mx n)} (hK : IsCompact K) (X : Mx n) : IsCompact (expSweep K X) :=
  (hK.prod (isCompact_Icc (a := (-1 : ℝ)) (b := 1))).image
    (continuous_fst.matrix_mul ((continuous_exp_smul X).comp continuous_snd))
theorem expSweep_sub {K : Set (Mx n)} (hKU : K ⊆ UJset ε) {X : Mx n} (hX : X ∈ lieSet ε) :
    expSweep K X ⊆ UJset ε := by
  rintro _ ⟨⟨z, s⟩, ⟨hz, -⟩, rfl⟩
  exact mul_mem_UJ (hKU hz) (exp_mem_UJ hX s)

theorem mem_expSweep {K : Set (Mx n)} {z : Mx n} (hz : z ∈ K) (X : Mx n) {s : ℝ} (hs : s ∈ Set.Icc (-1 : ℝ) 1) :
    z * NormedSpace.exp (s • X) ∈ expSweep K X := ⟨(z, s), ⟨hz, hs⟩, rfl⟩

theorem exp_zero_smul_mx (X : Mx n) : NormedSpace.exp ((0 : ℝ) • X) = 1 := by
  rw [zero_smul, NormedSpace.exp_zero]

theorem IsDerFam.norm_sub_exp_le {F : List (Mx n) → Mx n → ℂ} (hF : IsDerFam ε F) {w : List (Mx n)}
    (hw : ∀ Y ∈ w, Y ∈ lieSet ε) {X : Mx n} (hX : X ∈ lieSet ε) {z : Mx n} (hz : z ∈ UJset ε) {B : ℝ}
    (hB : ∀ s ∈ Set.Icc (-1 : ℝ) 1, ‖F (X :: w) (z * NormedSpace.exp (s • X))‖ ≤ B) {t : ℝ} (ht : |t| ≤ 1) :
    ‖F w (z * NormedSpace.exp (t • X)) - F w z‖ ≤ B * |t| := by
  have h := norm_sub_le_of_deriv_Icc (f := fun s => F w (z * NormedSpace.exp (s • X)))
    (fun s => hF.hasDerivAt_exp hw hX hz s) zero_le_one hB (t := t) (abs_le.1 ht)
  simpa only [exp_zero_smul_mx, Matrix.mul_one] using h

theorem IsDerFam.norm_taylor_exp_le {F : List (Mx n) → Mx n → ℂ} (hF : IsDerFam ε F) {w : List (Mx n)}
    (hw : ∀ Y ∈ w, Y ∈ lieSet ε) {X : Mx n} (hX : X ∈ lieSet ε) {z : Mx n} (hz : z ∈ UJset ε) {B : ℝ}
    (hB : ∀ s ∈ Set.Icc (-1 : ℝ) 1, ‖F (X :: X :: w) (z * NormedSpace.exp (s • X))‖ ≤ B) {t : ℝ} (ht : |t| ≤ 1) :
    ‖F w (z * NormedSpace.exp (t • X)) - F w z - t • F (X :: w) z‖ ≤ B * t ^ 2 := by
  have hXw : ∀ Y ∈ X :: w, Y ∈ lieSet ε := by
    intro Y hY
    rcases List.mem_cons.1 hY with rfl | hY
    exacts [hX, hw Y hY]
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨by norm_num, by norm_num⟩)
  have h1 : ∀ s ∈ Set.Icc (-|t|) |t|,
      ‖F (X :: w) (z * NormedSpace.exp (s • X)) - F (X :: w) z‖ ≤ B * |t| := by
    intro s hs
    have hs1 : |s| ≤ |t| := abs_le.2 hs
    exact (hF.norm_sub_exp_le hXw hX hz hB (hs1.trans ht)).trans (mul_le_mul_of_nonneg_left hs1 hB0)
  have hd : ∀ s, HasDerivAt (fun s : ℝ => F w (z * NormedSpace.exp (s • X)) - s • F (X :: w) z)
      (F (X :: w) (z * NormedSpace.exp (s • X)) - F (X :: w) z) s := by
    intro s
    have := (hF.hasDerivAt_exp hw hX hz s).fun_sub ((hasDerivAt_id s).smul_const (F (X :: w) z))
    simpa only [id, one_smul] using this
  have h := norm_sub_le_of_deriv_Icc hd (abs_nonneg t) h1 (t := t) ⟨neg_abs_le t, le_abs_self t⟩
  simp only [exp_zero_smul_mx, Matrix.mul_one, zero_smul, sub_zero, NormedSpace.exp_zero] at h
  have e : F w (z * NormedSpace.exp (t • X)) - F w z - t • F (X :: w) z =
      F w (z * NormedSpace.exp (t • X)) - t • F (X :: w) z - F w z := by abel
  rw [e]
  calc _ ≤ B * |t| * |t| := h
    _ = B * t ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

theorem lie_cons {Y : Mx n} {w : List (Mx n)} (hY : Y ∈ lieSet ε) (hw : ∀ Z ∈ w, Z ∈ lieSet ε) :
    ∀ Z ∈ Y :: w, Z ∈ lieSet ε := by
  intro Z hZ
  rcases List.mem_cons.1 hZ with rfl | hZ
  exacts [hY, hw Z hZ]

theorem IsDerFam.taylor_prod {N : ℕ} {F : List (Mx n) → Mx n → ℂ} (hF : IsDerFam ε F) (hG : FamGrowth ε N F)
    {l : List (Mx n)} (hl : ∀ Y ∈ l, Y ∈ lieSet ε) : ∀ (d : ℕ) (b : Fin d → Mx n), (∀ i, b i ∈ lieSet ε) →
    ∀ K : Set (Mx n), IsCompact K → K ⊆ UJset ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ t : Fin d → ℝ, ‖t‖ ≤ 1 →
      ‖F l (z * (List.ofFn fun i => NormedSpace.exp (t i • b i)).prod) - F l z - ∑ i, t i • F (b i :: l) z‖ ≤
        C * ‖t‖ ^ 2 := by
  intro d
  induction d with
  | zero =>
    intro b hb K hK hKU
    refine ⟨0, le_rfl, fun z _ t _ => ?_⟩
    simp
  | succ d ih =>
    intro b hb K hK hKU
    have hX := hb 0
    have hK' := isCompact_expSweep hK (b 0)
    have hK'U := expSweep_sub hKU hX
    obtain ⟨C', hC'0, hC'⟩ := ih (fun i => b i.succ) (fun i => hb _) _ hK' hK'U
    obtain ⟨B0, hB00, hB0⟩ := hG.bdd_of_isCompact (lie_cons hX (lie_cons hX hl)) hK' hK'U
    have hBi : ∀ i : Fin d, ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ expSweep K (b 0), ‖F (b 0 :: b i.succ :: l) y‖ ≤ B :=
      fun i => hG.bdd_of_isCompact (lie_cons hX (lie_cons (hb _) hl)) hK' hK'U
    choose B hBnn hB using hBi
    have hBs : 0 ≤ ∑ i, B i := Finset.sum_nonneg fun i _ => hBnn i
    refine ⟨C' + ∑ i, B i + B0, by positivity, fun z hz t ht => ?_⟩
    have hzU := hKU hz
    have hti : ∀ i, |t i| ≤ ‖t‖ := fun i => by simpa using norm_le_pi_norm t i
    have ht0 : t 0 ∈ Set.Icc (-1 : ℝ) 1 := abs_le.1 ((hti 0).trans ht)
    have ht' : ‖(fun i : Fin d => t i.succ)‖ ≤ ‖t‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg t)).2 fun i => norm_le_pi_norm t i.succ
    have hz1 := mem_expSweep hz (b 0) ht0
    have hprod : z * (List.ofFn fun i => NormedSpace.exp (t i • b i)).prod =
        z * NormedSpace.exp (t 0 • b 0) * (List.ofFn fun i : Fin d => NormedSpace.exp (t i.succ • b i.succ)).prod := by
      rw [List.ofFn_succ, List.prod_cons, Matrix.mul_assoc]
    rw [hprod, Fin.sum_univ_succ]
    set z1 := z * NormedSpace.exp (t 0 • b 0) with hz1def
    have h1 := hC' z1 hz1 (fun i => t i.succ) (ht'.trans ht)
    have h2 : ‖∑ i : Fin d, t i.succ • (F (b i.succ :: l) z1 - F (b i.succ :: l) z)‖ ≤ (∑ i, B i) * ‖t‖ ^ 2 := by
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [norm_smul, Real.norm_eq_abs]
      have hd := hF.norm_sub_exp_le (lie_cons (hb i.succ) hl) hX hzU
        (fun s hs => hB i _ (mem_expSweep hz (b 0) hs)) (abs_le.2 ht0)
      calc |t i.succ| * ‖F (b i.succ :: l) z1 - F (b i.succ :: l) z‖ ≤ ‖t‖ * (B i * ‖t‖) :=
            mul_le_mul (hti _) (hd.trans (mul_le_mul_of_nonneg_left (hti 0) (hBnn i))) (norm_nonneg _)
              (norm_nonneg _)
        _ = B i * ‖t‖ ^ 2 := by ring
    have h3 := hF.norm_taylor_exp_le hl hX hzU (fun s hs => hB0 _ (mem_expSweep hz (b 0) hs)) (abs_le.2 ht0)
    have h3' : B0 * t 0 ^ 2 ≤ B0 * ‖t‖ ^ 2 := by
      refine mul_le_mul_of_nonneg_left ?_ hB00
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hti 0) 2
    have h1' : C' * ‖(fun i : Fin d => t i.succ)‖ ^ 2 ≤ C' * ‖t‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ht' 2) hC'0
    have e : F l (z1 * (List.ofFn fun i : Fin d => NormedSpace.exp (t i.succ • b i.succ)).prod) - F l z -
        (t 0 • F (b 0 :: l) z + ∑ i : Fin d, t i.succ • F (b i.succ :: l) z) =
        (F l (z1 * (List.ofFn fun i : Fin d => NormedSpace.exp (t i.succ • b i.succ)).prod) - F l z1 -
          ∑ i : Fin d, t i.succ • F (b i.succ :: l) z1) +
        ∑ i : Fin d, t i.succ • (F (b i.succ :: l) z1 - F (b i.succ :: l) z) +
        (F l z1 - F l z - t 0 • F (b 0 :: l) z) := by
      simp only [smul_sub, Finset.sum_sub_distrib]
      abel
    rw [e]
    refine (norm_add₃_le).trans ?_
    have : (C' + ∑ i, B i + B0) * ‖t‖ ^ 2 = C' * ‖t‖ ^ 2 + (∑ i, B i) * ‖t‖ ^ 2 + B0 * ‖t‖ ^ 2 := by ring
    rw [this]
    exact add_le_add_three (h1.trans h1') h2 (h3.trans h3')

theorem hasFDerivAt_derFam_prodExp : ∀ (n : ℕ) (ε : Fin n → Bool) (N : ℕ) (F : List (GlobalTheory.TypeSum.Mx n) → GlobalTheory.TypeSum.Mx n → ℂ),
    GlobalTheory.TypeSum.IsDerFam ε F → GlobalTheory.TypeSum.FamGrowth ε N F →
    ∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ (d : ℕ) (b : Fin d → GlobalTheory.TypeSum.Mx n), (∀ i, b i ∈ lieSet ε) →
    ∀ g ∈ UJset ε, HasFDerivAt (fun t : Fin d → ℝ => F l (g * (List.ofFn fun i => NormedSpace.exp (t i • b i)).prod))
      (∑ i, (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).smulRight (F (b i :: l) g)) 0 := by
  intro n ε N F hF hG l hl d b hb g hg
  obtain ⟨C, -, hC⟩ := hF.taylor_prod hG hl d b hb {g} isCompact_singleton (Set.singleton_subset_iff.2 hg)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have e0 : (List.ofFn fun i => NormedSpace.exp ((0 : Fin d → ℝ) i • b i)).prod = 1 := by
    simp [List.prod_ofFn]
  refine Asymptotics.IsBigO.trans_isLittleO ?_ (Asymptotics.isLittleO_norm_pow_id (n := 2) one_lt_two)
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : Fin d → ℝ) one_pos] with h hh
  rw [mem_closedBall_zero_iff] at hh
  simp only [zero_add, e0, Matrix.mul_one, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, norm_pow, norm_norm]
  exact hC g rfl h hh

end GlobalTheory.TypeSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.HostSzOfSizes
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldSize

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2
open Formalism.MainNotions.Gaps.EtaleWeightGaps.Num
open scoped IntermediateField

theorem scale_le_rank {D : D7} {L : SizeData₂ D} (S : SizesAt L) : L.sc.x ≤ (D.R.r : ℝ) := by
  have hx1 := L.sc.one_lt_alt.le
  have he := L.sc.eps_pos
  have h1 : L.sc.x ≤ L.sc.x ^ (9 / 2 + 10 * L.sc.eps - szTh L) := by
    calc L.sc.x = L.sc.x ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by unfold szTh; linarith)
  exact (h1.trans S.2.2.1.1).trans (Pm.k_le_r D)

theorem hostSz_of_sizes : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (_Tp : ParamsT D L Pm), SizesAt L →
    (∀ i, Real.log (D.host.g i) ≤ 9 * L.sc.L + 1) → (10 : ℝ) ^ 60 ≤ L.sc.x →
    HostSz D.host L.sc.L ∧ (Sz (FO D) (poR D.R L.sc.L) (poR D.R L.sc.L) → FieldSmall D L) := by
  intro D L P _ S hg hx
  have hL := Pm.one_le_L L
  have h6 := Pm.six_le_r D
  have hf := Pm.two_le_f D
  refine ⟨⟨?_, ?_, ?_, hg, P.pde_log, ?_⟩, fun h => h.2⟩
  · have h : ((62 : ℕ) : ℝ) ≤ D.R.r := le_trans (by norm_num) (hx.trans (scale_le_rank S))
    exact_mod_cast h
  · have h1 := Pm.log_r_le P
    have h2 : Real.log 2 ≤ Real.log (D.R.r : ℝ) := Real.log_le_log (by norm_num) (by linarith)
    linarith [Real.log_two_gt_d9]
  · linarith [Pm.log_f_le P]
  · have h : Real.log |((discr D.host.E : ℤ) : ℝ)| ≤ 2 * D.R.f * L.sc.L := logdE_le_two_f_L P
    rw [div_le_iff₀ (by linarith)]
    nlinarith

end GlobalTheory.FieldSize
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.HostXiOrderBounds
section
set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize

theorem card_GL_zmod_le (r g : ℕ) (hg : g ≠ 0) : Nat.card (GL (Fin r) (ZMod g)) ≤ g ^ (r ^ 2) := by
  have : NeZero g := ⟨hg⟩
  have h := Nat.card_le_card_of_injective (Units.val : GL (Fin r) (ZMod g) → Matrix (Fin r) (Fin r) (ZMod g))
    Units.val_injective
  refine h.trans (le_of_eq ?_)
  unfold Matrix
  rw [Nat.card_fun, Nat.card_fun, Nat.card_zmod, ← pow_mul]
  simp [sq]

theorem card_units_quot_le (E : Type) [Field E] [NumberField E] (N : ℕ) (hN : N ≠ 0) :
    0 < Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ ∧
      Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ ≤ N ^ Module.finrank ℚ E := by
  have hc : Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) = N ^ Module.finrank ℚ E := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  have : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  exact ⟨Nat.card_pos, hc ▸ Nat.card_le_card_of_injective _ Units.val_injective⟩

theorem roots_sizes (P : Pre) (L : ℝ) (h : HostSz P.host L) :
    Real.log P.restRowsFiniteGroupCard ≤ P.R.f * (P.R.r : ℝ) ^ 2 * (18 * L + 2) ∧
      (∀ p ∈ [P.host.pde, P.host.pde'], 0 < xiOrd P.host (P.host.g 0 * P.host.g 1 * p) ∧
        Real.log (xiOrd P.host (P.host.g 0 * P.host.g 1 * p)) ≤
          1 + Real.log (classNumber P.host.E) + 2 * P.R.f * (21 * L)) ∧ 8 ≤ P.R.f ∧ 2 * P.R.m ≤ P.R.r := by
  have hg : ∀ k, P.host.g k ≠ 0 := fun k => (P.host.g_prime k).ne_zero
  have hg' : ∀ k, (P.host.g k : ℝ) ≠ 0 := fun k => Nat.cast_ne_zero.2 (hg k)
  have h0 := h.g 0
  have h1 := h.g 1
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hle : P.restRowsFiniteGroupCard ≤ (P.host.g 0 * P.host.g 1) ^ (P.R.f * P.R.r ^ 2) := by
      unfold Pre.restRowsFiniteGroupCard
      rw [Fin.prod_univ_two, mul_pow, mul_comm P.R.f, pow_mul, pow_mul]
      exact Nat.mul_le_mul (Nat.pow_le_pow_left (card_GL_zmod_le _ _ (hg 0)) _)
        (Nat.pow_le_pow_left (card_GL_zmod_le _ _ (hg 1)) _)
    have hpos : (0 : ℝ) < P.restRowsFiniteGroupCard := Nat.cast_pos.2 P.restRowsFiniteGroupCard_pos
    refine (Real.log_le_log hpos (Nat.cast_le.2 hle)).trans ?_
    rw [Nat.cast_pow, Real.log_pow, Nat.cast_mul (P.host.g 0), Real.log_mul (hg' 0) (hg' 1)]
    push_cast
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · intro p hp
    have hp' : p ≠ 0 ∧ Real.log p ≤ L := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨(P.level_prime _ P.host.pde_level.1).ne_zero, h.p.1⟩
      · exact ⟨(P.level_prime _ P.host.pde_level.2).ne_zero, h.p.2⟩
    have hN : P.host.g 0 * P.host.g 1 * p ≠ 0 := mul_ne_zero (mul_ne_zero (hg 0) (hg 1)) hp'.1
    obtain ⟨hu, hu'⟩ := card_units_quot_le P.host.E _ hN
    have hE : Module.finrank ℚ P.host.E = 2 * P.R.f := by
      rw [P.host.finrank_cmField, Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
      ring
    have hh : 0 < classNumber P.host.E := classNumber_pos _
    refine ⟨by unfold xiOrd; positivity, ?_⟩
    unfold xiOrd
    generalize Nat.card (𝓞 P.host.E ⧸
        Ideal.span {((P.host.g 0 * P.host.g 1 * p : ℕ) : 𝓞 P.host.E)})ˣ = c at hu hu' ⊢
    have hu1 : (0 : ℝ) < c := Nat.cast_pos.2 hu
    have hh1 : (0 : ℝ) < classNumber P.host.E := Nat.cast_pos.2 hh
    have h2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have h3 := Real.log_le_log hu1 (Nat.cast_le.2 hu')
    have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hp'.1
    rw [hE, Nat.cast_pow, Real.log_pow, Nat.cast_mul (P.host.g 0 * P.host.g 1), Nat.cast_mul (P.host.g 0),
      Real.log_mul (mul_ne_zero (hg' 0) (hg' 1)) hp0, Real.log_mul (hg' 0) (hg' 1), Nat.cast_mul,
      Nat.cast_ofNat] at h3
    have h4 : 2 * (P.R.f : ℝ) * (Real.log (P.host.g 0) + Real.log (P.host.g 1) + Real.log p) ≤
        2 * P.R.f * (21 * L) :=
      mul_le_mul_of_nonneg_left (by linarith [h.len, hp'.2]) (by positivity)
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by positivity) hu1.ne',
      Real.log_mul two_ne_zero hh1.ne']
    linarith
  · have he := P.host.two_le_e
    have : 2 ^ 2 ≤ 2 ^ P.R.e := Nat.pow_le_pow_right two_pos he
    have h2 := P.R.toFrame.two_pow_le_ord
    unfold Ranks.f Ranks.n
    omega
  · have := P.R.m_add_three_le_k
    unfold Ranks.r
    omega

end GlobalTheory.FieldSize
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.MeasurableDerFamComp
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

namespace GlobalTheory.TypeSum

theorem measurable_derFam_comp (n : ℕ) (ε : Fin n → Bool) (F : List (GlobalTheory.TypeSum.Mx n) → GlobalTheory.TypeSum.Mx n → ℂ)
    (hF : GlobalTheory.TypeSum.IsDerFam ε F) (h0 : ContinuousOn (F []) (UJset ε)) :
    ∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) →
    ∀ (T : Type) [TopologicalSpace T] [MeasurableSpace T] [OpensMeasurableSpace T] (φ : T → GlobalTheory.TypeSum.Mx n),
      Continuous φ → (∀ t, φ t ∈ UJset ε) → Measurable (fun t => F l (φ t)) := by
  intro l
  induction l with
  | nil =>
    intro _ T _ _ _ φ hφ hφU
    exact (h0.comp_continuous hφ hφU).measurable
  | cons X l ih =>
    intro hl T _ _ _ φ hφ hφU
    have hX : X ∈ lieSet ε := hl X (List.mem_cons_self ..)
    have hl' : ∀ Y ∈ l, Y ∈ lieSet ε := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)

    let q : ℕ → T → ℂ := fun m t =>
      (((m : ℝ) + 1)⁻¹)⁻¹ • (F l (φ t * NormedSpace.exp ((((m : ℝ) + 1)⁻¹) • X)) - F l (φ t))
    have hq : ∀ m, Measurable (q m) := by
      intro m
      have h1 : Measurable (fun t => F l (φ t * NormedSpace.exp ((((m : ℝ) + 1)⁻¹) • X))) :=
        ih hl' T (fun t => φ t * NormedSpace.exp ((((m : ℝ) + 1)⁻¹) • X))
          (hφ.mul continuous_const) (fun t => mul_mem_UJ (hφU t) (exp_mem_UJ hX _))
      have h2 : Measurable (fun t => F l (φ t)) := ih hl' T φ hφ hφU
      exact (h1.sub h2).const_smul ((((m : ℝ) + 1)⁻¹)⁻¹ : ℝ)
    have hlim : ∀ t, Tendsto (fun m => q m t) atTop (𝓝 (F (X :: l) (φ t))) := by
      intro t
      have hd := hF l hl' X hX (φ t) (hφU t)
      have hs := hd.tendsto_slope_zero
      have hseq : Tendsto (fun m : ℕ => ((m : ℝ) + 1)⁻¹) atTop (𝓝[≠] (0 : ℝ)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun m => ?_⟩
        · simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; positivity
      have := hs.comp hseq
      refine this.congr fun m => ?_
      simp [q, Function.comp, zero_add]
    exact measurable_of_tendsto_metrizable hq (tendsto_pi_nhds.2 hlim)

end GlobalTheory.TypeSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.PeterssonSquareIntegrableDefiniteOfLaws
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin2.L2

theorem norm_complexEmbedding_traceElement_const (D : D7) (τ : D.host.E →+* ℂ) : ‖τ D.host.xi0‖ = xiR D := by
  unfold xiR
  have hs : ∀ σ : D.host.E →+* ℂ, ‖σ D.host.sqrtMinusD‖ ^ 2 = ‖(D.host.d : ℂ)‖ := fun σ => by
    rw [← norm_pow, ← map_pow, D.host.sqrtMinusD_sq, map_neg, map_natCast, norm_neg]
  have hn : ‖τ D.host.sqrtMinusD‖ = ‖D.host.φ₀ D.host.sqrtMinusD‖ :=
    (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ((hs τ).trans (hs _).symm)
  rw [show D.host.xi0 = -1 / ((Ideal.absNorm D.host.ccK : D.host.E) * D.host.sqrtMinusD) from rfl]
  simp only [map_div₀, map_neg, map_one, map_mul, map_natCast, norm_div, norm_neg, norm_one, norm_mul, hn]

theorem petersson_squareIntegrable_definite_of_laws : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ) (V : HSp D) (hr : V.rank = r) ι Kf χ (dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r) mu x₀, V.SigOK → GoodEmb c σ → SupDef Xo c U → PkgLaws V hr ι Kf χ (U σ) dict mu x₀ → FinVol V ∧ (∀ k (τ : D.host.E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xiR D) ∧ ∃ h : CuspL2 U σ V dict mu, L2DefiniteCuspForms U σ V dict mu h := by
  intro D H Dw l Xo c r U σ V hr ι Kf χ dict mu x₀ hs hσ hsup P
  obtain ⟨g, e, F, ik, φ, th, -, hd, -⟩ := P.dictLaws
  have hA : AdelAut V dict mu := P.adelAut
  obtain ⟨hP, hV⟩ := GlobalTheory.FinalJoin2.volPairEx_and_finVol D V hs
  have hL : CuspL2 U σ V dict mu :=
    cusp_L2_of_measurable hσ (dict_dom_of hd) P.muUnit (adelMeas_of_aut Xo c hA)
  refine ⟨hV, fun k τ => ?_, hL, l2Def_of_cusp hσ hsup (aeDom_of hA hV hP P.muUnit hd) hL⟩
  exact (congrArg (fun z => ‖τ z‖) (P.modelW k).2).trans
    (by rw [map_neg, norm_neg]; exact norm_complexEmbedding_traceElement_const D τ)

end GlobalTheory.FinalJoin2.L2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.RunNumericalConditionsOfIndexBoundBeyondThresholStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.runNumericalConditions_of_indexBound_beyond_threshold : ∀ Z₀ : ℝ → ℝ → ℝ, ∃ x₀ : ℝ → ℝ → ℝ, ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), InR D j → PageRun large₂ X H C2 A2 CT ka wL wF Tn nP nW h0 → x₀ H.CA H.CK ≤ large₂.sc.x → PageOK large₂ X H C2 A2 CT ka wL wF Tn nP nW h0 ∧ Z₀ H.CA H.CK ≤ zBase large₂ := by
  first | exact @GlobalTheory.FinalJoin.pageOK_of_pageRun_beyond | exact GlobalTheory.FinalJoin.pageOK_of_pageRun_beyond | (intros; apply GlobalTheory.FinalJoin.pageOK_of_pageRun_beyond <;> assumption)
end

