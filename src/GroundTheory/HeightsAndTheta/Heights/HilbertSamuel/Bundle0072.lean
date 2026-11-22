import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0061
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0057
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0040
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0058
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import GroundTheory.HeightsAndTheta.Heights.Intersections.ProjLineRankTwoPushforwardHypotheses
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlock
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Inhabit
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwistIntersectionInt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

namespace TwistIntersectionInt

theorem proof (hPc : EmbeddingPieces.Statement) (hDG : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement) :
    TwistIntersectionInt.Statement := by
  intro K _ ι _ Ω _ F _ _ _ y D A B II Λ _ hII hP hbir hA hBa hB hΛ hex hloc
  classical
  have hI : IsIntersectionFamily (II K ι) := hII K ι
  have hC : IsSmoothHerm (A.tensor B) := hA.mul hB
  have hopen : IsOpen {u : (Σ k, ι k) → ℂ | ∀ k, ∃ i, u ⟨k, i⟩ ≠ 0} := by
    simp only [Set.ofPred_forall, Set.ofPred_exists]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  have hCloc : ∀ z ∈ mcPts (mCoordIdeal y), ∃ c : ℝ,
      ∀ᶠ u in 𝓝 z, Real.log ((A.tensor B).h u) = Real.log (A.h u) + c := by
    intro z hz
    obtain ⟨sg, hsg, -⟩ := hex z hz
    refine ⟨Real.log (Λ sg), ?_⟩
    filter_upwards [hloc z hz sg hsg, hopen.mem_nhds hz.1] with u hu hu'
    show Real.log (A.h u * B.h u) = _
    rw [hu, Real.log_mul (A.pos u hu').ne' (hΛ sg).ne']
  let L : Finset (Fin (D + 1)) → Fin (D + 1) → HermLine ι := fun S i => if i ∈ S then A.tensor B else A
  have hLs : ∀ S i, IsSmoothHerm (L S i) := by
    intro S i
    dsimp only [L]
    split_ifs
    exacts [hC, hA]
  have hLpot : ∀ S i, ∀ z ∈ mcPts (mCoordIdeal y), ∃ c : ℝ,
      ∀ᶠ u in 𝓝 z, Real.log ((L S i).h u) = Real.log (A.h u) + c := by
    intro S i z hz
    dsimp only [L]
    split_ifs
    · exact hCloc z hz
    · exact ⟨0, Eventually.of_forall fun u => by rw [add_zero]⟩
  have step : ∀ (S : Finset (Fin (D + 1))) (j : Fin (D + 1)), j ∉ S →
      II K ι (mCoordIdeal y) (D + 1) (L (insert j S)) = II K ι (mCoordIdeal y) (D + 1) (L S) +
        -ptsIntegral (mCoordIdeal y) (pot fun _ : Fin D => A) (logNorm B 1) := by
    intro S j hj
    set σ : Equiv.Perm (Fin (D + 1)) := Equiv.swap j (Fin.last D) with hσ
    set M : Fin D → HermLine ι := Fin.init (L S ∘ σ) with hMdef
    have hσl : σ (Fin.last D) = j := Equiv.swap_apply_right _ _
    have hne : ∀ i : Fin D, σ (Fin.castSucc i) ≠ j := by
      intro i h'
      rw [← hσl] at h'
      exact (Fin.castSucc_lt_last i).ne (σ.injective h')
    have hM : Fin.init (L (insert j S) ∘ σ) = M := by
      funext i
      simp only [hMdef, Fin.init, Function.comp, L, Finset.mem_insert, hne i, false_or]
    have e0 : L S ∘ σ = Fin.snoc M A := by
      have h0 := Fin.snoc_init_self (q := L S ∘ σ)
      have hl : (L S ∘ σ) (Fin.last D) = A := by simp [L, hσl, hj]
      rw [hl] at h0
      exact h0.symm
    have e1 : L (insert j S) ∘ σ = Fin.snoc M (A.tensor B) := by
      have h0 := Fin.snoc_init_self (q := L (insert j S) ∘ σ)
      have hl : (L (insert j S) ∘ σ) (Fin.last D) = A.tensor B := by simp [L, hσl]
      rw [hl, hM] at h0
      exact h0.symm
    have hMs : ∀ i, IsSmoothHerm (M i) := fun i => hLs S _
    have hint : ptsIntegral (mCoordIdeal y) (pot M) (logNorm B 1) =
        ptsIntegral (mCoordIdeal y) (pot fun _ : Fin D => A) (logNorm B 1) :=
      TwistIntersection.ptsIntegral_add_locConst _ (fun i z hz => hLpot S (σ (Fin.castSucc i)) z hz) _
    rw [← hI.1 _ (D + 1) (L (insert j S)) σ hP (hLs _), ← hI.1 _ (D + 1) (L S) σ hP (hLs S), e0, e1,
      hI.2.1 _ D M A B hP hMs hA hB, TwistIntersection.I_snoc_degZero hI hP hMs hB hBa, hint]
  have hall : ∀ S : Finset (Fin (D + 1)), II K ι (mCoordIdeal y) (D + 1) (L S) =
      II K ι (mCoordIdeal y) (D + 1) (L ∅) +
        S.card * -ptsIntegral (mCoordIdeal y) (pot fun _ : Fin D => A) (logNorm B 1) := by
    intro S
    refine Finset.induction_on S (by simp) ?_
    intro j S hj ih
    rw [step S j hj, ih, Finset.card_insert_of_notMem hj]
    push_cast
    ring
  have hL0 : L ∅ = fun _ => A := by
    funext i
    simp [L]
  have hLu : L Finset.univ = fun _ => A.tensor B := by
    funext i
    simp [L]
  have hw : ∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z →
      logNorm B 1 =ᶠ[𝓝 z] fun _ => (fun sg => -Real.log (Λ sg)) sg := by
    intro z hz sg hsg
    filter_upwards [hloc z hz sg hsg] with u hu
    simp [logNorm, hu, Real.log_inv]
  have hpc := hPc K ι Ω F y D (fun _ => A) (fun sg => -Real.log (Λ sg)) (logNorm B 1) hP hbir
    (fun _ => hA) hex hw
  have hg : ptsIntegral (mCoordIdeal y) (pot fun _ : Fin D => A) (fun _ => 1) =
      (genDeg (mCoordIdeal y) D A.a : ℝ) := by
    rw [hDG K ι (mCoordIdeal y) D (fun _ => A) hP (fun _ => hA)]
    unfold genDeg
    congr
  have := hall Finset.univ
  rw [hL0, hLu, Finset.card_univ, Fintype.card_fin] at this
  rw [this, hpc, hg, Finset.sum_neg_distrib]
  push_cast
  ring

end TwistIntersectionInt

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockChainSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.IdxAsm Filter Asymptotics

noncomputable section

theorem TwoBlockChainSum.gridSum_chain (D i : ℕ) (hi : i ≤ D) :
    (fun n : ℕ => (∑ j ∈ Finset.range n,
        ((n - j - 1 : ℕ) : ℝ) ^ i * (j : ℝ) ^ (D - i) / ((i.factorial : ℝ) * ((D - i).factorial : ℝ))) -
      (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ D := by
  refine (GridSum.proof D i hi).congr_left fun n => ?_
  congr 1
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj := Finset.mem_range.mp hj
  have e1 : n - 1 - (n - j - 1) = j := by omega
  have e2 : n - 1 - j = n - j - 1 := by omega
  simp only [e1, e2]

theorem TwoBlockChainSum.gPoly_chain (D : ℕ) (c : ℕ → ℝ) :
    (fun n : ℕ => ∑ j ∈ Finset.range n, gPoly D c (n - j - 1) j -
      (∑ i ∈ Finset.range (D + 1), c i) * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ D := by
  refine (IsBigO.fun_sum fun i hi => (TwoBlockChainSum.gridSum_chain D i
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).const_mul_left (c i)).congr_left fun n => ?_
  unfold gPoly
  rw [Finset.sum_comm, Finset.sum_mul, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_sub, Finset.mul_sum]
  ring

theorem TwoBlockChainSum.proof (hL : TwoBlockStepLocal.Statement) (hB : TwoBlockStepBound.Statement) :
    TwoBlockChainSum.Statement := by
  intro D Ω _ _ κ _ I x B m m' hI hX hx hBi hm hm' hsp
  obtain ⟨a₀, C, hC⟩ := hL D Ω κ I x B m m' hI hX hx hBi hm hm' hsp
  obtain ⟨K, hK⟩ := hB D Ω κ x B hX hx hBi hsp
  rw [← sum_twoBlockCoeff]
  generalize twoBlockCoeff I x (matAct B x) m m' D = c at hC ⊢
  generalize twoBlockStep x (matAct B x) = s at hC hK ⊢
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = ∑ i ∈ Finset.range (D + 1), |c i| := ⟨_, rfl⟩
  have hG0 : 0 ≤ G := hG ▸ Finset.sum_nonneg fun i _ => abs_nonneg _

  have hterm : ∀ n j : ℕ, j < n →
      |s (n - j - 1) j - gPoly D c (n - j - 1) j| ≤
        if a₀ ≤ n - j - 1 ∧ a₀ ≤ j then |C| * ((n : ℝ) ^ D / n) else (|K| + G) * (n : ℝ) ^ D := by
    intro n j hj
    have hn : ((n - j - 1 : ℕ) : ℝ) + (j : ℝ) + 1 = n := by
      have : n - j - 1 + j + 1 = n := by omega
      exact_mod_cast this
    have hpow : 0 ≤ (n : ℝ) ^ D := by positivity
    split_ifs with h
    · have h1 := hC (n - j - 1) j h.1 h.2
      rw [hn] at h1
      refine le_trans h1 ?_
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    · have hg := abs_gPoly_le D c (n - j - 1) j
      have hn' : ((n - j - 1 + j : ℕ) : ℝ) + 1 = n := by rw [Nat.cast_add]; exact hn
      rw [hn', ← hG] at hg
      have hk := hK (n - j - 1) j
      rw [hn] at hk
      have hk' : K * (n : ℝ) ^ D ≤ |K| * (n : ℝ) ^ D := mul_le_mul_of_nonneg_right (le_abs_self K) hpow
      calc _ ≤ |s (n - j - 1) j| + |gPoly D c (n - j - 1) j| := abs_sub _ _
        _ ≤ _ := by linarith

  have h1 : (fun n : ℕ => ∑ j ∈ Finset.range n, (s (n - j - 1) j - gPoly D c (n - j - 1) j)) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ D := by
    refine IsBigO.of_bound (|C| + 2 * a₀ * (|K| + G)) (Eventually.of_forall fun n => ?_)
    have hpow : 0 ≤ (n : ℝ) ^ D := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpow]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun j hj => hterm n j (Finset.mem_range.mp hj)).trans ?_
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    have hgood : ((Finset.filter (fun j => a₀ ≤ n - j - 1 ∧ a₀ ≤ j) (Finset.range n)).card : ℝ) ≤ n := by
      exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_range n).le
    have hbad : ((Finset.filter (fun j => ¬(a₀ ≤ n - j - 1 ∧ a₀ ≤ j)) (Finset.range n)).card : ℝ) ≤ 2 * a₀ := by
      have hsub : Finset.filter (fun j => ¬(a₀ ≤ n - j - 1 ∧ a₀ ≤ j)) (Finset.range n) ⊆
          Finset.range a₀ ∪ Finset.Ico (n - a₀) n := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_range] at hj
        simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
        omega
      have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      rw [Finset.card_range, Nat.card_Ico] at hc
      have hc' : (Finset.filter (fun j => ¬(a₀ ≤ n - j - 1 ∧ a₀ ≤ j)) (Finset.range n)).card ≤ 2 * a₀ := by
        omega
      exact_mod_cast hc'
    have hcn : (n : ℝ) * ((n : ℝ) ^ D / n) ≤ (n : ℝ) ^ D := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp only [Nat.cast_zero, zero_mul]
        positivity
      · rw [mul_div_cancel₀]
        exact_mod_cast hn.ne'
    have hq : 0 ≤ (n : ℝ) ^ D / n := by positivity
    have hKG : 0 ≤ (|K| + G) * (n : ℝ) ^ D := mul_nonneg (add_nonneg (abs_nonneg K) hG0) hpow
    have e1 := mul_le_mul_of_nonneg_right hgood (mul_nonneg (abs_nonneg C) hq)
    have e2 := mul_le_mul_of_nonneg_right hbad hKG
    have e3 := mul_le_mul_of_nonneg_left hcn (abs_nonneg C)
    nlinarith
  refine (h1.add (TwoBlockChainSum.gPoly_chain D c)).congr_left fun n => ?_
  simp only [Finset.sum_sub_distrib]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockFnField
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

theorem TwoBlockFnField.ratio_mem {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] (x : Ix κ → Ω)
    (p q : Ix κ) : x p / x q ∈ blockFnField (ι := GlobalTheory κ) x :=
  IntermediateField.subset_adjoin ℚ _ ⟨p, q, Subsingleton.elim _ _, rfl⟩

theorem TwoBlockFnField.matAct_le {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] (x : Ix κ → Ω)
    (A : Matrix (Ix κ) (Ix κ) ℚ) :
    blockFnField (ι := GlobalTheory κ) (matAct A x) ≤ blockFnField (ι := GlobalTheory κ) x := by
  rw [blockFnField, IntermediateField.adjoin_le_iff]
  rintro t ⟨p, q, -, rfl⟩
  by_cases h0 : ∀ j, x j = 0
  · have : matAct A x p = 0 := by simp [matAct, h0]
    rw [this, zero_div]
    exact zero_mem _
  · obtain ⟨c, hc⟩ := not_forall.mp h0
    have key : ∀ i, matAct A x i / x c ∈ blockFnField (ι := GlobalTheory κ) x := by
      intro i
      have : matAct A x i / x c = ∑ j, (A i j : Ω) * (x j / x c) := by
        simp only [matAct, Finset.sum_div, mul_div_assoc]
      rw [this]
      refine sum_mem fun j _ => mul_mem ?_ (TwoBlockFnField.ratio_mem x j c)
      simp
    have : matAct A x p / matAct A x q = (matAct A x p / x c) / (matAct A x q / x c) := by
      rw [div_div_div_cancel_right₀ hc]
    rw [this]
    exact div_mem (key p) (key q)

theorem TwoBlockFnField.matAct_eq {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (hB : IsInvMat B) :
    blockFnField (ι := GlobalTheory κ) (matAct B x) = blockFnField (ι := GlobalTheory κ) x := by
  classical
  obtain ⟨B', -, h⟩ := isInvMat_mul hB
  refine le_antisymm (TwoBlockFnField.matAct_le x B) ?_
  have := TwoBlockFnField.matAct_le (matAct B x) B'
  rwa [matAct_matAct h] at this

theorem TwoBlockFnField.proof : TwoBlockFnField.Statement := by
  intro Ω _ _ κ _ x B hB
  have hE := TwoBlockFnField.matAct_eq x B hB
  refine ⟨le_antisymm ?_ ?_, hE⟩
  · rw [blockFnField, IntermediateField.adjoin_le_iff]
    rintro t ⟨p, q, hpq, rfl⟩
    obtain ⟨b, i⟩ := p
    obtain ⟨b', j⟩ := q
    simp only at hpq
    subst hpq
    by_cases hb : b = 0
    · subst hb
      simpa [pair] using TwoBlockFnField.ratio_mem x ⟨(), i⟩ ⟨(), j⟩
    · simp only [pair, hb, if_false]
      rw [← hE]
      exact TwoBlockFnField.ratio_mem (matAct B x) ⟨(), i⟩ ⟨(), j⟩
  · refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro t ⟨⟨u, i⟩, ⟨u', j⟩, -, rfl⟩
    cases u; cases u'
    refine IntermediateField.subset_adjoin ℚ _ ⟨⟨0, i⟩, ⟨0, j⟩, rfl, ?_⟩
    simp [pair]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PUniformBergmanBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights

noncomputable section

lemma gaussDiscMass_pos {lam R : ℝ} (hlam : 0 ≤ lam) (hR : 0 < R) : 0 < gaussDiscMass lam R := by
  unfold gaussDiscMass
  split_ifs with h
  · positivity
  · have hl : 0 < lam := lt_of_le_of_ne hlam (Ne.symm h)
    have : Real.exp (-lam * R ^ 2) < 1 :=
      (Real.exp_lt_exp.2 (by nlinarith [sq_pos_of_pos hR] : -lam * R ^ 2 < 0)).trans_eq Real.exp_zero
    have : 0 < 1 - Real.exp (-lam * R ^ 2) := by linarith
    positivity

theorem UniformBergmanBound.proof (hP : PolydiscSubmean.Statement)
    (hC : ChartTaylorCover.Statement) : UniformBergmanBound.Statement := by
  intro D X _ _ _ _ _ A L W₀ W₁ dV _ _
  obtain ⟨r, hr, M, c, hc, hcov⟩ := hC A L W₀ W₁ dV
  set M' := max M 0 with hM'
  have hM'0 : 0 ≤ M' := le_max_right _ _
  have hI : 0 < gaussDiscMass M' r := gaussDiscMass_pos hM'0 hr
  have hK : 0 < c * gaussDiscMass M' r ^ D := by positivity
  refine ⟨(c * gaussDiscMass M' r ^ D)⁻¹, fun n hn t ht V _ hV x => ?_⟩
  have hn0 : 0 < n := hn
  have hnD : 0 < (n : ℝ) ^ D := by positivity
  obtain ⟨j, hxj, hball, hdens, hW⟩ := hcov x
  obtain ⟨ℓ₀, h₀⟩ := hW W₀ (by simp)
  obtain ⟨ℓ₁, h₁⟩ := hW W₁ (by simp)
  set e := A.chart j
  set y := e x
  set ψ : (Fin D → ℂ) → ℝ := (W₀.lerp W₁ t).φ j ∘ e.symm with hψ
  have hψy : ψ y = (W₀.lerp W₁ t).φ j x := by simp [hψ, y, e.left_inv hxj]
  have hsub : Metric.closedBall y r ⊆ e.target ∩ e.symm ⁻¹' e.source :=
    fun w hw => ⟨hball hw, e.map_target (hball hw)⟩

  have hT : ∀ z : Fin D → ℂ, ‖z‖ ≤ r →
      ψ (y + z) ≤ ψ y + (ℓ₀ + t • (ℓ₁ - ℓ₀)) z + M' * ∑ i, ‖z i‖ ^ 2 := by
    intro z hz
    have a₀ := h₀ z hz
    have a₁ := h₁ z hz
    have hS : 0 ≤ ∑ i, ‖z i‖ ^ 2 := by positivity
    have hMM : M * ∑ i, ‖z i‖ ^ 2 ≤ M' * ∑ i, ‖z i‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hS
    rw [hψy]
    simp only [hψ, Function.comp, Weight.lerp, FunLike.coe_add,
      FunLike.coe_smul, FunLike.coe_sub, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul]
    have ht0 : 0 ≤ t := ht.1
    have ht1 : 0 ≤ 1 - t := by linarith [ht.2]
    nlinarith [mul_le_mul_of_nonneg_left a₀ ht1, mul_le_mul_of_nonneg_left a₁ ht0]

  refine ciSup_le fun s => ?_
  have hs : (s : Fin A.n → X → ℂ) ∈ L.sections n := hV s.2
  have hs' : _ ∧ _ ∧ _ := hs
  set F : (Fin D → ℂ) → ℂ := (s : Fin A.n → X → ℂ) j ∘ e.symm with hF
  have hFa : AnalyticOnNhd ℂ F (Metric.closedBall y r) := ((hs'.1 j) j).mono hsub
  have hψc : ContinuousOn ψ (Metric.closedBall y r) :=
    (((W₀.lerp W₁ t).smooth j) j).continuousOn.mono hsub
  have hloc := gauss_local hP hn0 hr hM'0 hFa hψc (ℓ₀ + t • (ℓ₁ - ℓ₀)) hT
  have hρr : r / Real.sqrt n ≤ r := div_le_self hr.le (Real.one_le_sqrt.2 (by exact_mod_cast hn))
  have hBr : Metric.closedBall y (r / Real.sqrt n) ⊆ Metric.closedBall y r :=
    Metric.closedBall_subset_closedBall hρr
  have hlow := le_l2NormSq_of_chart (W₀.lerp W₁ t) dV hs j
    Metric.isClosed_closedBall.measurableSet (hBr.trans hball) hc.le
    (fun w hw => hdens w (hBr hw))
  have hpt : ptNormSq (W₀.lerp W₁ t) n s x = ‖F y‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y) := by
    rw [ptNormSq_eq_of_mem _ hs j hxj, hψy]
    simp [hF, y, e.left_inv hxj]
  have hmain : ptNormSq (W₀.lerp W₁ t) n s x * ((n : ℝ) ^ D)⁻¹ * gaussDiscMass M' r ^ D * c ≤
      sectionL2NormSq (W₀.lerp W₁ t) dV n s := by
    rw [hpt]
    calc _ = c * (‖F y‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y) * ((n : ℝ) ^ D)⁻¹ *
          gaussDiscMass M' r ^ D) := by ring
      _ ≤ c * ∫ w in Metric.closedBall y (r / Real.sqrt n), ‖F w‖ ^ 2 * Real.exp (-(n : ℝ) * ψ w) :=
          mul_le_mul_of_nonneg_left hloc hc.le
      _ = _ := rfl
      _ ≤ _ := hlow
  have hl0 : 0 ≤ sectionL2NormSq (W₀.lerp W₁ t) dV n s := sectionL2NormSq_nonneg _ _ _ _
  rcases hl0.eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]; positivity
  rw [div_le_iff₀ hpos]
  have hp0 : 0 ≤ ptNormSq (W₀.lerp W₁ t) n s x := ptNormSq_nonneg _ _ _ _
  calc ptNormSq (W₀.lerp W₁ t) n s x
      = (c * gaussDiscMass M' r ^ D)⁻¹ * (n : ℝ) ^ D *
          (ptNormSq (W₀.lerp W₁ t) n s x * ((n : ℝ) ^ D)⁻¹ * gaussDiscMass M' r ^ D * c) := by
        field_simp
    _ ≤ (c * gaussDiscMass M' r ^ D)⁻¹ * (n : ℝ) ^ D * sectionL2NormSq (W₀.lerp W₁ t) dV n s :=
        mul_le_mul_of_nonneg_left hmain (by positivity)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsAddBlockIsometric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

section Objects

variable {K : Type} {ι : K → Type}

def oldV (N : ℕ) : (Σ k, ι k) → (Σ k, addIdx ι N k) := fun p => ⟨some p.1, p.2⟩

theorem isBlockMap_oldV (N : ℕ) :
    ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap (ι := ι) (ι' := addIdx ι N) some (oldV N) := by
  refine ⟨Option.some_injective K, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨k, i⟩ ⟨k', i'⟩ h
    have h1 : k = k' := Option.some_injective K (congrArg Sigma.fst h)
    subst h1
    have h2 : i = i' := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    rw [h2]
  · rintro ⟨_ | k, i⟩ ⟨k', hk'⟩
    · exact absurd hk' (Option.some_ne_none k')
    · exact ⟨⟨k, i⟩, rfl⟩

end Objects

def AddBlockIsometric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (m N : ℕ) (v : Fin N → Ω) (B L : HermLine (addIdx ι N)),
    IsArithVar (mCoordIdeal y) (D + 1) → 1 ≤ m →
    (∀ j, v j ∈ chartLat y A.a m) → KH.GeneratesOn y (fun k => (m : ℤ) * A.a k) v →
    B.a = unitDeg (none : Option K) →
    L.a = ReciprocityTheory.ChartRestriction.G.AI.I1.pullDeg some (fun k => (m : ℤ) * A.a k) →
    (∀ z, L.h z = A.h (basePart₂ z) ^ m) →
    (∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ j : Fin N,
      secNormAt y A m (v j) (basePart₂ z) * B.h z = ‖z ⟨none, j⟩‖) →
    IsIsometricOn (mCoordIdeal (addBlock y v)) B L

namespace PowerBlockProjectiveLine

open ProjLine

def fsOldPull : HermLine (addIdx (GlobalTheory (Fin 2)) 2) :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.pullHerm (isBlockMap_oldV (ι := GlobalTheory (Fin 2)) 2) fsLine1

end PowerBlockProjectiveLine

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedEffectiveSection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GeneratedEffectiveSection.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver F ι)) (a : K → ℤ),
    IsMultiProjPrime V → KH.GeneratedV F V a →
    ∃ f g : MRingOver F ι, IsRatSection V a f g ∧ ∀ W, 0 ≤ ratDiv V f g W

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

