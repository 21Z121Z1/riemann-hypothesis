import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1169
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1165
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1154
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1146
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1149
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1245
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1134
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1133
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0232
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1354
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1360
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1361
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1326
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1327
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1362

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityOneAlt
section
noncomputable section
open scoped TensorProduct

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.SteepMult

theorem multOne : GlobalTheory.RealLift.MultOne := by
  intro R S M Λ v hv hgen hsteep w hw
  classical
  have hML : IsKLieAct M.act := fun Y Z _ _ => M.lie Y Z
  obtain ⟨hfin, hlie, hwts, hvN, hgenN⟩ := GlobalTheory.T.generated_submodule_highest_weight_structure R S M Λ v hv
  have hN : KStable M.act (GlobalTheory.BlockReps.gen M.act v) := GlobalTheory.BlockReps.stable_gen (act := M.act) v
  set N := GlobalTheory.BlockReps.gen M.act v with hNdef
  haveI : FiniteDimensional ℂ N := hfin
  set A := restrAct M.act N hN with hA
  set v₀ : N := ⟨v, GlobalTheory.BlockReps.mem_gen v⟩ with hv₀
  obtain ⟨B, hB⟩ := GlobalTheory.T.highest_weight_module_unitary_form R S N A Λ v₀ hlie hwts hvN hgenN
  set c : ℚ := GlobalTheory.BlockReps.casVal Λ with hc

  have hcasN : ∀ x : N, GlobalTheory.BlockReps.casK A x = ((c : ℚ) : ℂ) • x := by
    have hker := GlobalTheory.BlockReps.stable_ker (act := A) hlie ((c : ℚ) : ℂ) 1
    have hv1 : v₀ ∈ LinearMap.ker ((GlobalTheory.BlockReps.casK A - ((c : ℚ) : ℂ) • 1) ^ 1) := by
      rw [pow_one, LinearMap.mem_ker, LinearMap.sub_apply, GlobalTheory.BlockReps.casK_hw hlie hvN.2]
      simp [hc]
    have htop := GlobalTheory.BlockReps.gen_le hv1 hker
    rw [hgenN] at htop
    intro x
    have := htop (Submodule.mem_top (x := x))
    rw [pow_one, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
    simpa using this
  set P1 := (LinearMap.ker (phiN M.act N 1)).orthogonalBilin (formT 1 B) with hP1
  have hU1 := GlobalTheory.T.isUnitary_tAct_formT_of_isUnitary R S 1 N A B hB

  have hpos : ∀ x ∈ P1, x ≠ 0 → ((((R + S : ℕ) : ℚ) + c : ℚ) : ℝ) * (formT 1 B x x).re <
      (formT 1 B x (GlobalTheory.BlockReps.casK (tAct 1 A) x)).re := by
    have hL1 := GlobalTheory.T.tensor_action_is_lie_action R S 1 N A hlie
    have hW1 := GlobalTheory.T.tensor_action_weight_decomposition R S 1 N A hwts
    have hkerS : KStable (tAct 1 A) (LinearMap.ker (phiN M.act N 1)) := fun Z hZ x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      rw [GlobalTheory.T.filtration_map_equivariant R S M N hN 1 Z hZ, hx, map_zero]
    have hPS := (GlobalTheory.T.unitary_form_orthogonal_complement R S _ (tAct 1 A) (formT 1 B) hU1 _ hkerS).1
    refine GlobalTheory.T.casimir_lower_bound_on_stable_subspace R S _ (tAct 1 A) (formT 1 B) _ hL1 hW1 hU1 P1 hPS ?_
    intro ν y hyP hy
    obtain ⟨a, b, hab, rfl⟩ := GlobalTheory.T.highest_weight_tensor_root_shift R S N A Λ v₀ hlie hwts hvN hgenN ν y hy
    have hφ0 : phiN M.act N 1 y ≠ 0 := by
      intro h0
      have h1 := (Submodule.mem_orthogonalBilin_iff.1 hyP) y (LinearMap.mem_ker.2 h0)
      have hp := hU1.2.1 y hy.1
      have h1' : formT 1 B y y = 0 := h1
      rw [h1'] at hp
      simp at hp
    have hhw : IsHW M.act (GlobalTheory.RealLift.addRoot Λ a b) (phiN M.act N 1 y) := by
      refine ⟨hφ0, ?_⟩
      have hy2 := GlobalTheory.TensorHW.mem_hw.1 hy.2
      refine GlobalTheory.TensorHW.mem_hw.2 ⟨fun d => ?_, fun d e hde => ?_⟩
      · rw [← GlobalTheory.T.filtration_map_equivariant R S M N hN 1 _ (GlobalTheory.TensorHW.isKC_Eab (GlobalTheory.TensorHW.same_refl d)), hy2.1 d, map_smul]
      · rw [← GlobalTheory.T.filtration_map_equivariant R S M N hN 1 _ (GlobalTheory.TensorHW.isKC_Eab (GlobalTheory.TensorHW.same_of_pos hde)), hy2.2 d e hde, map_zero]
    have := hsteep a b hab _ hhw
    rw [GlobalTheory.T.block_casimir_eq_real_casimir, hc, GlobalTheory.T.block_casimir_eq_real_casimir]
    linarith

  have hno : ∀ (k : ℕ) (Ψ : (Fin (k + 1) → NC R S) → N), Ψ ≠ 0 → Ψ ∈ hwSub (tAct (k + 1) A) Λ →
      (∀ i g, section1 Ψ i g ∈ P1) → False := by
    intro k Ψ hΨ hhw hsec
    set tm : ((Fin 1 → NC R S) → N) → ℝ := fun x => (formT 1 B x (GlobalTheory.BlockReps.casK (tAct 1 A) x)).re -
        ((R + S : ℕ) : ℝ) * (formT 1 B x x).re - (formT 1 B x (fun h => GlobalTheory.BlockReps.casK A (x h))).re with htm
    have hsc : ∀ x : (Fin 1 → NC R S) → N, (formT 1 B x (fun h => GlobalTheory.BlockReps.casK A (x h))).re =
        (c : ℝ) * (formT 1 B x x).re := by
      intro x
      have e : (fun h => GlobalTheory.BlockReps.casK A (x h)) = ((c : ℚ) : ℂ) • x := funext fun h => hcasN _
      rw [e, map_smul, smul_eq_mul]
      have : ((c : ℚ) : ℂ) = ((c : ℝ) : ℂ) := by push_cast; rfl
      rw [this, Complex.re_ofReal_mul]
    have hterm : ∀ x ∈ P1, 0 ≤ tm x ∧ (x ≠ 0 → 0 < tm x) := by
      intro x hx
      have hpos' : x ≠ 0 → 0 < tm x := fun hne => by
        have := hpos x hx hne
        simp only [htm, hsc]
        push_cast at this ⊢
        linarith
      refine ⟨?_, hpos'⟩
      by_cases h0 : x = 0
      · simp [htm, h0]
      · exact (hpos' h0).le
    have hI := GlobalTheory.T.casimir_section_sum_identity R S (k + 1) N A B hB Ψ
    have hcasT : GlobalTheory.BlockReps.casK (tAct (k + 1) A) Ψ = ((c : ℚ) : ℂ) • Ψ :=
      GlobalTheory.BlockReps.casK_hw (GlobalTheory.T.tensor_action_is_lie_action R S (k + 1) N A hlie) hhw
    have hpt : (fun g => GlobalTheory.BlockReps.casK A (Ψ g)) = ((c : ℚ) : ℂ) • Ψ := funext fun g => hcasN _
    rw [hcasT, hpt, sub_self, mul_zero] at hI
    obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 hΨ
    have hne : section1 Ψ 0 g₀ ≠ 0 := by
      intro h
      have := congrFun h (fun _ => g₀ 0)
      simp only [section1, Function.update_eq_self, Pi.zero_apply] at this
      exact hg₀ this
    have hpos2 : 0 < ∑ i, ∑ g, tm (section1 Ψ i g) := by
      refine Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun g _ => (hterm _ (hsec i g)).1) ⟨0, Finset.mem_univ _, ?_⟩
      exact Finset.sum_pos' (fun g _ => (hterm _ (hsec 0 g)).1) ⟨g₀, Finset.mem_univ _, (hterm _ (hsec 0 g₀)).2 hne⟩
    exact absurd hI (not_le.2 hpos2)

  have hdesc : ∀ k, w ∈ filt M.act N k → w ∈ N := by
    intro k
    induction k with
    | zero => exact fun h => (GlobalTheory.T.filtration_stable_and_increasing R S M N hN 0).2.2 h
    | succ k ih =>
      intro hk
      by_cases hwk : w ∈ filt M.act N k
      · exact ih hwk
      exfalso
      obtain ⟨hFs, hFeq, -⟩ := GlobalTheory.T.filtration_stable_and_increasing R S M N hN k
      rw [hFeq, sup_comm] at hk
      obtain ⟨Ψ, hΨP, hΨ0, hΨhw⟩ := GlobalTheory.T.exists_highestWeight_orthogonal_comap_of_mem_range_sup R S ((Fin (k + 1) → NC R S) → N) (tAct (k + 1) A) (formT (k + 1) B) M.V
        M.act (phiN M.act N (k + 1)) (filt M.act N k) Λ w (GlobalTheory.T.isUnitary_tAct_formT_of_isUnitary R S (k + 1) N A B hB) hFs
        (fun Z hZ x => GlobalTheory.T.filtration_map_equivariant R S M N hN (k + 1) Z hZ x) hk hw hwk
      exact hno k Ψ hΨ0 hΨhw (GlobalTheory.T.section_orthogonal_kernel R S M N hN B k Ψ hΨP)
  obtain ⟨k, hk⟩ := GlobalTheory.T.generated_module_filtration_exhaustive R S M Λ v hv hgen w
  have hwN := hdesc k hk
  by_cases hw0 : w = 0
  · exact ⟨0, by simp [hw0]⟩
  obtain ⟨-, hspan⟩ := GlobalTheory.BlockReps.hw_unique hML hN (GlobalTheory.BlockReps.mem_gen v) hv hwN ⟨hw0, hw⟩
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1 hspan
  exact ⟨d, hd.symm⟩

end GlobalTheory.SteepMult

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParamSubgroupGeneratorsExist
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section
open Matrix

namespace GlobalTheory.RealLiftGen

theorem map_star_mul {l m n : Type} [Fintype m] (A : Matrix l m ℂ) (B : Matrix m n ℂ) :
    (A * B).map star = A.map star * B.map star := by
  ext i j; simp [Matrix.mul_apply, Matrix.map_apply, star_sum]

theorem map_star_star {m n : Type} (A : Matrix m n ℂ) : (A.map star).map star = A := by
  ext i j; simp

theorem Jm_map_star (R S : ℕ) : (Jm R S).map star = Jm R S := by
  rw [Jm, Formalism.UG.P.Jpq_eq_diagonal]; ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.diagonal_apply] <;> split_ifs <;> simp

theorem Jm_mul_Jm (R S : ℕ) : Jm R S * Jm R S = 1 := Formalism.UG.P.Jpq_mul_self R S

theorem gen_of_cont {n : Type} [Fintype n] [DecidableEq n] (N : ℝ → Matrix n n ℂ) (hc : Continuous N)
    (h0 : N 0 = 1) (hm : ∀ s t, N (s + t) = N s * N t) : ∃ Y : Matrix n n ℂ, ∀ t : ℝ, N t = NormedSpace.exp (t • Y) :=
  GlobalTheory.T.matrix_oneParameterGroup_eq_exp_of_continuous N hc h0 hm

theorem cont_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {β : Type} [Fintype β] [DecidableEq β] {J : Matrix β β (AE F E)} (γ : Multiplicative ℝ →* UG (cA σ) J)
    (hγ : Continuous γ) (w : InfinitePlace F) (τ : EmbOver E w) :
    Continuous (fun t : ℝ => ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf τ)) :=
  GlobalTheory.T.continuous_unitaryOneParameter_realPlaceComponent γ hγ w τ

theorem piInf_cA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (x : AE F E) :
    piInf τ (cA σ x) = star (piInf τ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, star_add]
  | tmul a e =>
    have := h.1
    have h3 := InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w) (evInf F w a)
    simp only [piInf, cA, compInf, RingHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, AlgHom.id_apply, infEmb_tmul]
    rw [star_mul', h.2.2.2 τ.1 e, ← h3, Complex.star_def, Complex.conj_ofReal]

theorem mem_upq_of {R S : ℕ} (Y : Mat R S)
    (h : ∀ t : ℝ, (NormedSpace.exp (t • Y))ᵀ * Jm R S * (NormedSpace.exp (t • Y)).map star = Jm R S) :
    Y ∈ upq R S := by
  have key : Yᵀ * Jm R S + Jm R S * Y.map star = 0 := by
    letI : NormedRing (Matrix (Ix R S) (Ix R S) ℂ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℝ (Matrix (Ix R S) (Ix R S) ℂ) := Matrix.linftyOpNormedAlgebra
    have hs : ∀ A : Matrix (Ix R S) (Ix R S) ℂ, A.map star = Aᴴᵀ := fun A => by ext i j; rfl
    have e1 : ∀ t : ℝ, (NormedSpace.exp (t • Y))ᵀ = NormedSpace.exp (t • Yᵀ) := fun t => by
      rw [← Matrix.exp_transpose, Matrix.transpose_smul]
    have e2 : ∀ t : ℝ, (NormedSpace.exp (t • Y)).map star = NormedSpace.exp (t • Y.map star) := fun t => by
      rw [hs, hs, ← Matrix.exp_conjTranspose, ← Matrix.exp_transpose, Matrix.conjTranspose_smul, Matrix.transpose_smul,
        star_trivial]
    have h1 := ((hasDerivAt_exp_smul_const (Yᵀ) (0:ℝ)).mul_const (Jm R S)).mul
      (hasDerivAt_exp_smul_const (Y.map star) (0:ℝ))
    simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h1
    have hc : ((fun y : ℝ => NormedSpace.exp (y • Yᵀ) * Jm R S) * fun u : ℝ => NormedSpace.exp (u • Y.map star)) =
        fun _ => Jm R S := funext fun t => by
      show NormedSpace.exp (t • Yᵀ) * Jm R S * NormedSpace.exp (t • Y.map star) = Jm R S
      rw [← e1, ← e2]; exact h t
    have h2 : HasDerivAt (fun _ : ℝ => Jm R S) (Yᵀ * Jm R S * 1 + Jm R S * Y.map star) 0 :=
      h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => (congrFun hc t).symm)
    have h3 := h2.unique (hasDerivAt_const (0:ℝ) (Jm R S))
    simpa only [mul_one] using h3
  have h5 : (Yᵀ * Jm R S + Jm R S * Y.map star).map star = 0 := by rw [key]; ext; simp
  rw [Matrix.map_add _ (fun a b => star_add a b), map_star_mul, map_star_mul, map_star_star, Jm_map_star] at h5
  show Yᴴ * Jm R S + Jm R S * Y = 0
  exact h5

theorem genEx : GlobalTheory.RealLift.GenEx := by
  intro F E _ _ _ _ _ σ β _ _ R S τ J b C hcm hC γ hγ
  choose A' hA' using fun w => (hC w).2
  set K : InfinitePlace F → Matrix β β ℂ := fun w => b • J.map (piInf (τ w)) with hK
  have hF : ∀ w, (C w)ᵀ * K w * (C w).map star = Jm R S := fun w => (hC w).1
  have hAC : ∀ w, A' w * C w = 1 := by
    intro w
    have h1 : (Jm R S * (C w)ᵀ * K w) * (C w).map star = 1 := by
      rw [Matrix.mul_assoc (Jm R S), Matrix.mul_assoc (Jm R S), hF, Jm_mul_Jm]
    have h2 : (Jm R S * (C w)ᵀ * K w).map star * C w = 1 := by
      have := congrArg (fun X => X.map star) h1
      rw [map_star_mul, map_star_star] at this
      rw [this]; ext i j; simp [Matrix.one_apply]
    calc A' w * C w = ((Jm R S * (C w)ᵀ * K w).map star * C w) * A' w * C w := by rw [h2, Matrix.one_mul]
      _ = (Jm R S * (C w)ᵀ * K w).map star * C w := by rw [Matrix.mul_assoc _ (C w), hA', Matrix.mul_one]
      _ = 1 := h2
  set M : InfinitePlace F → ℝ → Matrix β β ℂ :=
    fun w t => ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf (τ w)) with hM
  have hMm : ∀ w s t, M w (s + t) = M w s * M w t := by
    intro w s t
    simp only [hM, ofAdd_add, map_mul, Subgroup.coe_mul, Units.val_mul]
    exact Matrix.map_mul
  have hM0 : ∀ w, M w 0 = 1 := by
    intro w
    simp only [hM, ofAdd_zero, map_one, OneMemClass.coe_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hMu : ∀ w t, (M w t)ᵀ * K w * (M w t).map star = K w := by
    intro w t
    have hg := (γ (Multiplicative.ofAdd t)).2
    change (((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)))ᵀ * J *
      (((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E))).map (cA σ) = J at hg
    have h2 := congrArg (fun X => X.map (piInf (τ w))) hg
    simp only [Matrix.map_mul, Matrix.map_map] at h2
    have h3 : (piInf (τ w)) ∘ (cA σ) = star ∘ (piInf (τ w)) := funext fun x => piInf_cA hcm (τ w) x
    rw [h3, ← Matrix.map_map] at h2
    have h4 : (M w t)ᵀ * J.map (piInf (τ w)) * (M w t).map star = J.map (piInf (τ w)) := by
      simp only [hM]; rw [← Matrix.transpose_map]; exact h2
    simp only [hK, Matrix.mul_smul, Matrix.smul_mul]
    rw [h4]
  set N : InfinitePlace F → ℝ → Mat R S := fun w t => A' w * M w t * C w with hN
  have hCN : ∀ w t, C w * N w t = M w t * C w := by
    intro w t; simp only [hN, ← Matrix.mul_assoc, hA', Matrix.one_mul]
  have hNc : ∀ w, Continuous (N w) := fun w =>
    (continuous_const.matrix_mul (cont_map γ hγ.1 w (τ w))).matrix_mul continuous_const
  have hN0 : ∀ w, N w 0 = 1 := by intro w; simp only [hN, hM0, Matrix.mul_one, hAC]
  have hNm : ∀ w s t, N w (s + t) = N w s * N w t := by
    intro w s t
    simp only [hN, hMm]
    calc A' w * (M w s * M w t) * C w = A' w * M w s * (C w * A' w) * M w t * C w := by
          rw [hA', Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  choose Y hY using fun w => gen_of_cont (N w) (hNc w) (hN0 w) (hNm w)
  refine ⟨Y, fun w => mem_upq_of (Y w) fun t => ?_, fun t w => ?_⟩
  · rw [← hY w t, ← hF w]
    calc (N w t)ᵀ * ((C w)ᵀ * K w * (C w).map star) * (N w t).map star
        = (C w * N w t)ᵀ * K w * (C w * N w t).map star := by
          simp only [Matrix.transpose_mul, map_star_mul, Matrix.mul_assoc]
      _ = (C w)ᵀ * ((M w t)ᵀ * K w * (M w t).map star) * (C w).map star := by
          simp only [hCN, Matrix.transpose_mul, map_star_mul, Matrix.mul_assoc]
      _ = _ := by rw [hMu]
  · show M w t * C w = _
    rw [← hCN, hY]

end GlobalTheory.RealLiftGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicEmbeddingValuationSubring
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.ClsReg

theorem classes_finite : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), (∀ (y : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y * h) ≠ 0 → (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ∧ FixL G v β y z) → (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧ (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable) → sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ P : Polynomial G.F, ∃ Y : Finset (grp G β), ∀ y : grp G β, minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = P → (∃ a : Dat G v β, FixL G v β y a.2.1 ∧ f (a.1.1⁻¹ * toAfF G β x t hx y * a.1.1) * f' (a.1.2⁻¹ * toP1 G β y * a.1.2) ≠ 0) → ∃ y₀ ∈ Y, ∃ γ : grp G β, y = γ * y₀ * γ⁻¹ := by
  intro p _ G _ v _ L f hf K' f' _ β x t hx hreg hβ _ P
  by_cases hne : ∃ y₀ : grp G β, minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = P ∧
      ∃ a : Dat G v β, FixL G v β y₀ a.2.1 ∧
        f (a.1.1⁻¹ * toAfF G β x t hx y₀ * a.1.1) * f' (a.1.2⁻¹ * toP1 G β y₀ * a.1.2) ≠ 0
  swap
  · exact ⟨∅, fun y hy ha => absurd ⟨y, hy, ha⟩ hne⟩
  obtain ⟨y₀, hP₀, a₀, hfix₀, ha₀⟩ := hne
  obtain ⟨hdeg₀, hsep₀⟩ := hreg y₀ a₀.1.1 (left_ne_zero_of_mul ha₀) ⟨a₀.2.1, a₀.2.2, hfix₀⟩
  obtain ⟨hy₀, -⟩ := y₀.prop
  obtain ⟨S, hS⟩ := GlobalTheory.T.harrisTaylor_regular_conjugate_local_scalar_norm p G L f hf β x t hx hβ y₀ hsep₀ hdeg₀
  obtain ⟨A, hA⟩ := GlobalTheory.T.finite_fixed_unit_classes_centralizer_regular p G β hβ ((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) (((y₀ : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) hy₀ hsep₀ hdeg₀ S
  have key : ∀ y : grp G β, minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = P → ∀ g : G.GAf,
      f (g⁻¹ * toAfF G β x t hx y * g) ≠ 0 → ∃ a' ∈ A, ∃ b : Bool, ∃ (c : G.Cˣ) (r : ℚˣ) (e : G.Cˣ),
        (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C) ∧
        Commute (e : G.C) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∧ decide (0 < (r : ℚ)) = b ∧
        (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) = algebraMap ℚ G.C (r : ℚ) * ((e : G.C) * a' * ((β : G.C) * sh G (e : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) := by
    intro y hy g hg
    obtain ⟨c, hc⟩ := units_conj_of_minpoly_eq_of_separable G ((y : G.Cˣ × ℚˣ).1) ((y₀ : G.Cˣ × ℚˣ).1)
      (by rw [hy, hP₀]) hsep₀ hdeg₀
    have h2 := GlobalTheory.grp_factor_eq_of_conj p G β y y₀ c hc
    obtain ⟨hu, hcm, hfix⟩ := GlobalTheory.grp_conj_unit_props p G β hβ y y₀ c hc h2
    obtain ⟨a', ha', r, e, he, hre⟩ := hA _ hu hcm hfix (fun ℓ _ hℓ => hS y g hg c hc ℓ hℓ)
    exact ⟨a', ha', decide (0 < (r : ℚ)), c, r, e, hc, he, rfl, hre⟩
  let D : G.C × Bool → grp G β → Prop := fun ab y => ∃ (c : G.Cˣ) (r : ℚˣ) (e : G.Cˣ),
        (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C) ∧
        Commute (e : G.C) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∧ decide (0 < (r : ℚ)) = ab.2 ∧
        (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) = algebraMap ℚ G.C (r : ℚ) * ((e : G.C) * ab.1 * ((β : G.C) * sh G (e : G.C) * ((β⁻¹ : G.Cˣ) : G.C)))
  let ρ : G.C × Bool → grp G β := fun ab => if h : ∃ y, D ab y then h.choose else 1
  refine ⟨(A ×ˢ (Finset.univ : Finset Bool)).image ρ, ?_⟩
  rintro y hy ⟨a, _, ha⟩
  obtain ⟨a', ha', b, hD⟩ := key y hy a.1.1 (left_ne_zero_of_mul ha)
  have hex : ∃ y, D (a', b) y := ⟨y, hD⟩
  refine ⟨ρ (a', b), Finset.mem_image_of_mem _ (Finset.mem_product.2 ⟨ha', Finset.mem_univ _⟩), ?_⟩
  have hρ : ρ (a', b) = hex.choose := dif_pos hex
  rw [hρ]
  obtain ⟨c', r', e', hc', he', hb', hre'⟩ := hex.choose_spec
  dsimp only at hb' hre'
  obtain ⟨c, r, e, hc, he, hb, hre⟩ := hD
  have h2 : (hex.choose : G.Cˣ × ℚˣ).2 = (y : G.Cˣ × ℚˣ).2 := by
    rw [GlobalTheory.grp_factor_eq_of_conj p G β _ y₀ c' hc', GlobalTheory.grp_factor_eq_of_conj p G β y y₀ c hc]
  refine GlobalTheory.Div.conj_of_twist p G β hex.choose y ((y₀ : G.Cˣ × ℚˣ).1) c' c (e * e'⁻¹) ((r : ℚ) / r') hc' hc h2 ?_ ?_ ?_
  · rw [Units.val_mul]
    exact he.mul_left he'.units_inv_left
  · have hr : (0 < (r : ℚ)) ↔ (0 < (r' : ℚ)) := by
      rw [← decide_eq_decide, hb, hb']
    rcases lt_or_gt_of_ne r'.ne_zero with h | h
    · have hn : ¬ (0 < (r : ℚ)) := fun h0 => absurd (hr.1 h0) (not_lt.2 h.le)
      exact div_pos_of_neg_of_neg (lt_of_le_of_ne (not_lt.1 hn) r.ne_zero) h
    · exact div_pos (hr.2 h) h
  · rw [hre', hre]
    exact conj_rel_alg' G β e e' a' r r'

end GlobalTheory.LKCx.ClsReg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PencilLinePolynomialNatDegreeLeAndCoeffStatement
section
open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pencilLinePolynomial_natDegree_le_and_coeff : ∀ (F R : Type) [CommRing F] [CommRing R] [Algebra F R] (D N δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) F), IsMultiHomogeneous (fun _ => δ) f → ∀ (u : Fin D → Fin N → R) (a b : Fin N → R), (GlobalTheory.PencilDisc.line u a b f).natDegree ≤ δ ∧ (GlobalTheory.PencilDisc.line u a b f).coeff δ = MvPolynomial.aeval (GlobalTheory.HSChoice.join u b) f := by
  first | exact @GlobalTheory.PencilDisc.line_natDegree_le_and_coeff | exact GlobalTheory.PencilDisc.line_natDegree_le_and_coeff | (intros; apply GlobalTheory.PencilDisc.line_natDegree_le_and_coeff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodCoordinatesFrameRationalIsometryStatement
section
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_coordinates_frame_rational_isometry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (a : GL (Fin r) E) (h : IsMatch X X' a) (x : Frame X.Ψ r) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ), Formalism.L2.PjFree.perFr X' (lact a (castFr h.psi x)) ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i = Formalism.L2.PjFree.perFr X x v τ i := by
  first | exact @GlobalTheory.GeoLevel.perFr_lact_of_isMatch | exact GlobalTheory.GeoLevel.perFr_lact_of_isMatch | (intros; apply GlobalTheory.GeoLevel.perFr_lact_of_isMatch <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmFieldStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placeConjugation_properties_cmField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ w : Pl E, Continuous (cj w) ∧ (∀ x, cj w (cj w x) = x) ∧ (∀ x, Valued.v (cj w x) = Valued.v x) ∧ (¬ IsSplitAt w → (∀ x : E, cj w (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) ∧ (∃ ϖ q, IsUnramInv ϖ (cj w) q ∧ qV E w = q ^ 2) ∧ (∀ x : Af E, pLoc E w (conjFin (IsCMField.complexConj E).toRingEquiv x) = cj w (pLoc E w x)) ∧ ∀ (s : w.adicCompletion E →+* w.adicCompletion E), (∀ x, Valued.v (s x) = Valued.v x) → (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → s = cj w) ∧ ∀ (s : w.adicCompletion E →+* w.adicCompletion E), (∀ x, Valued.v (s x) = Valued.v x) → (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → ¬ IsSplitAt w := by
  first | exact @GlobalTheory.ConjAtPlace.main | exact GlobalTheory.ConjAtPlace.main | (intros; apply GlobalTheory.ConjAtPlace.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceSplitOrInert
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc

namespace GlobalTheory.KFinLoc

theorem split_or_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ v : Pl F, Nonempty (E →ₐ[F] Fv F v) ∨ ∃ w : HeightOneSpectrum (𝓞 E), Formalism.UG.IsInertAt F E v w := by
  intro F E _ _ _ _ _ σ B hB v
  have hUn := hB.unram
  have hU : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v := by
    refine GlobalTheory.LFun.isUnram_iff.2 fun w _ => ?_
    exact Ideal.ramificationIdx_eq_one w.asIdeal (𝓞 F)
  rcases GlobalTheory.LFun.InertChart.isSplit_or_isInertAt hU with hs | hi
  · left
    obtain ⟨w, w', hne, h1, h2⟩ := GlobalTheory.LFun.isSplit_iff.1 hs
    exact ⟨(GlobalTheory.AdelicU.existsUnique_splitPrime_eq hB.cm hne h1 h2).exists.choose⟩
  · exact Or.inr hi

end GlobalTheory.KFinLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEval
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section

namespace GlobalTheory.CCRFock

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def polEval {ι : Type} (m : ι → Module.End ℂ V) (hm : ∀ i j, m i * m j = m j * m i) (f₀ : V) :
    MvPolynomial ι ℂ →ₗ[ℂ] V :=
  letI : CommRing (Algebra.adjoin ℂ (Set.range m)) :=
    Algebra.adjoinCommRingOfComm ℂ (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact hm i j)
  (LinearMap.applyₗ f₀ ∘ₗ (Algebra.adjoin ℂ (Set.range m)).val.toLinearMap) ∘ₗ
    (MvPolynomial.aeval (fun i => (⟨m i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ : Algebra.adjoin ℂ (Set.range m)))).toLinearMap

def polMap (W Λ : Type) [Fintype W] [DecidableEq W] :
    (⨂[ℂ] _ : W, MvPolynomial Λ ℂ) →ₗ[ℂ] MvPolynomial (W × Λ) ℂ :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ W (MvPolynomial (W × Λ) ℂ)).compLinearMap
    fun w => (MvPolynomial.rename (Prod.mk w)).toLinearMap)

def unitAt {W : Type} [DecidableEq W] {P Q R S : ℕ} (j : W × (Ix P Q × Ix R S)) (z : ℂ) :
    W → Matrix (Ix P Q) (Ix R S) ℂ :=
  Pi.single j.1 (Matrix.single j.2.1 j.2.2 z)

def fockM {W : Type} [DecidableEq W] {P Q R S : ℕ} (H : (W → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ V)
    (j : W × (Ix P Q × Ix R S)) : Module.End ℂ V :=
  (2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ •
    (H (unitAt j 1) - (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAt j Complex.I))

def fockD {W : Type} [DecidableEq W] {P Q R S : ℕ} (H : (W → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ V)
    (j : W × (Ix P Q × Ix R S)) : Module.End ℂ V :=
  -((2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ •
    (H (unitAt j 1) + (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAt j Complex.I)))

def coefM (z ε : ℂ) : ℂ := (z.re : ℂ) + ε * Complex.I * (z.im : ℂ)

def coefD (z ε : ℂ) : ℂ := -(z.re : ℂ) + ε * Complex.I * (z.im : ℂ)

end GlobalTheory.CCRFock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyFunMemSmoothVectorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polyFun_mem_smooth_vectors : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), RealPoints θ V → ∀ P : PolyE V, polyFun θ V P ∈ SmF θ V := by
  first | exact @GlobalTheory.CentralOps.polyFun_mem_smF | exact GlobalTheory.CentralOps.polyFun_mem_smF | (intros; apply GlobalTheory.CentralOps.polyFun_mem_smF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfVectorMultiplicationsMemFiltrationLattiStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.productOfVectorMultiplications_mem_filtration_lattice : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (j t : ℕ), j + t ≤ S.T → (∀ (u : Fin t → Fin S.N → F), ∀ x ∈ S.V j, word S.mul u x ∈ S.V (j + t)) ∧ ∀ (e : Fin t → Fin S.n), ∀ x ∈ S.M j, ∃ g ∈ S.M (j + t), (g : A) = word S.mul (fun i => S.w.col (e i)) x := by
  first | exact @GlobalTheory.HSShort.wordMem | exact GlobalTheory.HSShort.wordMem | (intros; apply GlobalTheory.HSShort.wordMem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexIdealSmulFractionalIdealEqAbsNormNumberFStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_ideal_smul_fractionalIdeal_eq_absNorm_numberField : ∀ (F : Type) [Field F] [NumberField F] (I : Submodule (𝓞 F) F) (p : Ideal (𝓞 F)), p ≠ ⊥ → I ≠ ⊥ → (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ y ∈ I, c • y ∈ (1 : Submodule (𝓞 F) F)) → (p • I).toAddSubgroup.relIndex I.toAddSubgroup = Ideal.absNorm p := by
  first | exact @GlobalTheory.FracIdealIndex.relIndex_smul_eq_absNorm | exact GlobalTheory.FracIdealIndex.relIndex_smul_eq_absNorm | (intros; apply GlobalTheory.FracIdealIndex.relIndex_smul_eq_absNorm <;> assumption)
end

