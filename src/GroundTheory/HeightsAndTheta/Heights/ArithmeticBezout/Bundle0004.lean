import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PKernelProjMeasurable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology ContinuousLinearMap

noncomputable section

namespace KernelProjMeasurable

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace E] [CompleteSpace F]

def shifted (A : E →L[ℂ] F) (ε : ℝ) : E →L[ℂ] E :=
  (ContinuousLinearMap.adjoint A) ∘L A + (ε : ℂ) • (1 : E →L[ℂ] E)

theorem re_inner_shifted (A : E →L[ℂ] F) (ε : ℝ) (u : E) :
    RCLike.re (inner ℂ u (shifted A ε u)) = ‖A u‖ ^ 2 + ε * ‖u‖ ^ 2 := by
  simp only [shifted, add_apply, comp_apply, smul_apply, one_apply, inner_add_right,
    inner_smul_right, adjoint_inner_right, inner_self_eq_norm_sq_to_K, map_add]
  simp [← Complex.ofReal_pow]

theorem inner_shifted_of_apply_eq_zero (A : E →L[ℂ] F) (ε : ℝ) (u : E) {z : E} (hz : A z = 0) :
    inner ℂ z (shifted A ε u) = (ε : ℂ) * inner ℂ z u := by
  simp [shifted, inner_add_right, inner_smul_right, adjoint_inner_right, hz]

theorem shifted_apply_of_apply_eq_zero (A : E →L[ℂ] F) (ε : ℝ) {z : E} (hz : A z = 0) :
    shifted A ε z = (ε : ℂ) • z := by
  simp [shifted, hz]

theorem mul_norm_le_norm_shifted (A : E →L[ℂ] F) {ε : ℝ} (hε : 0 < ε) (u : E) :
    ε * ‖u‖ ≤ ‖shifted A ε u‖ := by
  have h1 := re_inner_shifted A ε u
  have h2 := re_inner_le_norm (𝕜 := ℂ) u (shifted A ε u)
  rcases eq_or_lt_of_le (norm_nonneg u) with h | h
  · rw [← h, mul_zero]; exact norm_nonneg _
  · have h3 : (ε * ‖u‖) * ‖u‖ ≤ ‖shifted A ε u‖ * ‖u‖ := by
      nlinarith [sq_nonneg ‖A u‖]
    exact le_of_mul_le_mul_right h3 h

theorem isUnit_shifted (A : E →L[ℂ] F) {ε : ℝ} (hε : 0 < ε) : IsUnit (shifted A ε) := by
  have hinj : Function.Injective (shifted A ε : E →ₗ[ℂ] E) := by
    intro a b hab
    have h := mul_norm_le_norm_shifted A hε (a - b)
    have hab' : shifted A ε a = shifted A ε b := hab
    rw [map_sub, hab', sub_self, norm_zero] at h
    have h0 : ‖a - b‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (a - b)]) (norm_nonneg _)
    exact sub_eq_zero.1 (norm_eq_zero.1 h0)
  refine ⟨(LinearEquiv.ofInjectiveEndo _ hinj).toContinuousLinearEquiv.toUnit, ?_⟩
  ext v
  rfl

theorem exists_norm_le_norm_shifted (A : E →L[ℂ] F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 ≤ ε → ∀ u ∈ (LinearMap.ker (A : E →ₗ[ℂ] F))ᗮ, ‖u‖ ≤ C * ‖shifted A ε u‖ := by
  set K := LinearMap.ker (A : E →ₗ[ℂ] F)
  have hinj : Function.Injective ((A : E →ₗ[ℂ] F).comp Kᗮ.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have h1 : (u : E) ∈ K := hu
    have h2 : (u : E) ∈ K ⊓ Kᗮ := ⟨h1, u.2⟩
    rw [K.inf_orthogonal_eq_bot, Submodule.mem_bot] at h2
    exact Subtype.ext h2
  obtain ⟨c, -, hc⟩ := ((A : E →ₗ[ℂ] F).comp Kᗮ.subtype).injective_iff_antilipschitz.1 hinj
  refine ⟨(c : ℝ) ^ 2, sq_nonneg _, fun ε hε u hu => ?_⟩
  have h1 : ‖u‖ ≤ c * ‖A u‖ := by
    simpa using hc.le_mul_norm (map_zero _) ⟨u, hu⟩
  have h2 := re_inner_shifted A ε u
  have h3 := re_inner_le_norm (𝕜 := ℂ) u (shifted A ε u)
  have hc0 : (0 : ℝ) ≤ c := c.2
  rcases eq_or_lt_of_le (norm_nonneg u) with h | h
  · rw [← h]; positivity
  · have hAu : ‖u‖ ^ 2 ≤ (c : ℝ) ^ 2 * ‖A u‖ ^ 2 := by
      have := mul_le_mul h1 h1 (norm_nonneg _) (by positivity)
      nlinarith
    have h4 : (c : ℝ) ^ 2 * ‖A u‖ ^ 2 ≤ (c : ℝ) ^ 2 * (‖u‖ * ‖shifted A ε u‖) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      nlinarith [mul_nonneg hε (sq_nonneg ‖u‖)]
    have h5 : ‖u‖ * ‖u‖ ≤ ((c : ℝ) ^ 2 * ‖shifted A ε u‖) * ‖u‖ := by nlinarith
    exact le_of_mul_le_mul_right h5 h

def resolvent (A : E →L[ℂ] F) (ε : ℝ) : E →L[ℂ] E :=
  (ε : ℂ) • Ring.inverse (shifted A ε)

theorem exists_norm_resolvent_sub_le (A : E →L[ℂ] F) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε →
      ‖resolvent A ε - (LinearMap.ker (A : E →ₗ[ℂ] F)).starProjection‖ ≤ C * ε := by
  obtain ⟨C, hC, hCb⟩ := exists_norm_le_norm_shifted A
  refine ⟨2 * C, fun ε hε => ?_⟩
  set K := LinearMap.ker (A : E →ₗ[ℂ] F)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  set u := (resolvent A ε - K.starProjection) v with hu_def
  have hinv : shifted A ε (Ring.inverse (shifted A ε) v) = v := by
    have := Ring.mul_inverse_cancel _ (isUnit_shifted A hε)
    exact congrArg (fun T : E →L[ℂ] E => T v) this
  have hPv : A (K.starProjection v) = 0 := K.starProjection_apply_mem v
  have hTu : shifted A ε u = (ε : ℂ) • (v - K.starProjection v) := by
    rw [hu_def, resolvent, sub_apply, smul_apply, map_sub, map_smul, hinv,
      shifted_apply_of_apply_eq_zero A ε hPv, smul_sub]
  have hu : u ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal]
    intro z hz
    have h1 := inner_shifted_of_apply_eq_zero A ε u hz
    rw [hTu, inner_smul_right,
      (Submodule.mem_orthogonal _ _).1 (K.sub_starProjection_mem_orthogonal v) z hz, mul_zero] at h1
    have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
    exact (mul_eq_zero.1 h1.symm).resolve_left hε'
  have hvP : ‖v - K.starProjection v‖ ≤ 2 * ‖v‖ :=
    (norm_sub_le _ _).trans (by linarith [K.norm_starProjection_apply_le v])
  calc ‖u‖ ≤ C * ‖shifted A ε u‖ := hCb ε hε.le u hu
    _ = C * (ε * ‖v - K.starProjection v‖) := by
      rw [hTu, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    _ ≤ C * (ε * (2 * ‖v‖)) := by gcongr
    _ = 2 * C * ε * ‖v‖ := by ring

theorem tendsto_resolvent (A : E →L[ℂ] F) :
    Tendsto (fun j : ℕ => resolvent A (1 / ((j : ℝ) + 1))) atTop
      (𝓝 (LinearMap.ker (A : E →ₗ[ℂ] F)).starProjection) := by
  obtain ⟨C, hC⟩ := exists_norm_resolvent_sub_le A
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun j => hC _ (by positivity)) ?_
  simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C

theorem continuous_resolvent {X : Type*} [TopologicalSpace X] {A : X → E →L[ℂ] F} (hA : Continuous A) {ε : ℝ} (hε : 0 < ε) :
    Continuous fun x => resolvent (A x) ε := by
  have hadj : Continuous fun x => ContinuousLinearMap.adjoint (A x) :=
    ContinuousLinearMap.adjoint.continuous.comp hA
  have hT : Continuous fun x => shifted (A x) ε := by
    simp only [shifted]
    exact (hadj.clm_comp hA).add continuous_const
  have hI : Continuous fun x => Ring.inverse (shifted (A x) ε) := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    have h := NormedRing.inverse_continuousAt (isUnit_shifted (A x) hε).unit
    rw [IsUnit.unit_spec] at h
    exact ContinuousAt.comp (g := Ring.inverse) (f := fun x => shifted (A x) ε) h hT.continuousAt
  show Continuous fun x => (ε : ℂ) • Ring.inverse (shifted (A x) ε)
  exact hI.const_smul (ε : ℂ)

end KernelProjMeasurable

theorem KernelProjMeasurable.proof : KernelProjMeasurable.Statement := by
  intro X _ _ _ n k L hL
  let A : X → EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin k) :=
    fun x => LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (L x))
  have hA : Continuous A := by
    rw [continuous_clm_apply]
    intro v
    change Continuous fun x => (WithLp.toLp 2 (Matrix.mulVec (L x) (WithLp.ofLp v)) : EuclideanSpace ℂ (Fin k))
    exact (PiLp.continuous_toLp 2 _).comp (hL.matrix_mulVec continuous_const)
  refine measurable_of_tendsto_metrizable
    (f := fun j x => KernelProjMeasurable.resolvent (A x) (1 / ((j : ℝ) + 1)))
    (fun j => (KernelProjMeasurable.continuous_resolvent hA (by positivity)).measurable) ?_
  rw [tendsto_pi_nhds]
  intro x
  exact KernelProjMeasurable.tendsto_resolvent (A x)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PPiQuotCokerFiniteLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem PiQuotCokerFiniteLength.proof : PiQuotCokerFiniteLength.Statement := by
  intro B _ _ _ J hJ hQ
  have : Finite J.minimalPrimes := (J.finite_minimalPrimes_of_isNoetherianRing B).to_subtype
  let : Fintype J.minimalPrimes := Fintype.ofFinite _
  classical
  have hfac : ∀ (P : J.minimalPrimes) (x : B),
      quotToPiMinimalPrimes J (Submodule.Quotient.mk x) P = Ideal.Quotient.mk (P : Ideal B) x :=
    fun _ _ => rfl
  refine ⟨(injective_iff_map_eq_zero _).mpr fun y hy => ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hxP : ∀ P : J.minimalPrimes, x ∈ (P : Ideal B) := fun P => by
      have h1 := congrFun hy P
      rwa [hfac, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem] at h1
    have hx : x ∈ sInf J.minimalPrimes := Submodule.mem_sInf.mpr fun p hp => hxP ⟨p, hp⟩
    rw [Ideal.sInf_minimalPrimes, hJ.radical] at hx
    exact (Submodule.Quotient.mk_eq_zero _).mpr hx

  have hkey : ∀ Q : Ideal B, Q.IsPrime → ∀ P P' : J.minimalPrimes, P ≠ P' →
      (P : Ideal B) ≤ Q → (P' : Ideal B) ≤ Q → Q = IsLocalRing.maximalIdeal B := by
    intro Q hQp P P' hne hPQ hP'Q
    rcases hQ Q hQp (P.2.1.2.trans hPQ) with hmin | hm
    · exfalso
      apply hne
      have e1 : (P : Ideal B) = Q := le_antisymm hPQ (hmin.2 P.2.1 hPQ)
      have e2 : (P' : Ideal B) = Q := le_antisymm hP'Q (hmin.2 P'.2.1 hP'Q)
      exact Subtype.ext (e1.trans e2.symm)
    · exact hm
  let IP : J.minimalPrimes → Ideal B := fun P =>
    (Finset.univ.filter (· ≠ P)).inf fun P' : J.minimalPrimes => (P' : Ideal B)
  let I : Ideal B := Finset.univ.inf fun P => IP P ⊔ (P : Ideal B)
  have hI : ∀ Q : Ideal B, Q.IsPrime → I ≤ Q → Q = IsLocalRing.maximalIdeal B := by
    intro Q hQp hIQ
    obtain ⟨P, -, hPQ⟩ := hQp.inf_le'.mp hIQ
    obtain ⟨P', hP', hP'Q⟩ := hQp.inf_le'.mp (le_sup_left.trans hPQ)
    exact hkey Q hQp P P' (Finset.mem_filter.mp hP').2.symm (le_sup_right.trans hPQ) hP'Q
  have htors : Module.IsTorsionBySet B
      (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J))
      (I : Set B) := by
    intro c z
    obtain ⟨y, hy⟩ := z
    show y • c = 0
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    have hyP : ∀ P, y ∈ IP P ⊔ (P : Ideal B) := fun P =>
      Submodule.mem_finsetInf.mp hy P (Finset.mem_univ _)
    choose a ha b hb hab using fun P => Submodule.mem_sup.mp (hyP P)
    choose x hx using fun P => Ideal.Quotient.mk_surjective (v P)
    refine ⟨Submodule.Quotient.mk (∑ P, a P * x P), ?_⟩
    funext Q
    rw [hfac, Pi.smul_apply, ← hx Q, map_sum, Finset.sum_eq_single Q]
    · rw [← hab Q, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_add, map_mul,
        Ideal.Quotient.eq_zero_iff_mem.mpr (hb Q), add_zero]
    · intro P _ hPQ
      have hle : IP P ≤ (Q : Ideal B) :=
        Finset.inf_le (Finset.mem_filter.mpr ⟨Finset.mem_univ Q, hPQ.symm⟩)
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ (hle (ha P)))
    · intro h
      exact absurd (Finset.mem_univ Q) h
  by_cases hItop : I = ⊤
  · haveI : Subsingleton
        (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J)) :=
      ⟨fun c d => by
        have hc := @htors c ⟨1, by rw [hItop]; trivial⟩
        have hd := @htors d ⟨1, by rw [hItop]; trivial⟩
        rw [one_smul] at hc hd
        rw [hc, hd]⟩
    exact IsFiniteLength.of_subsingleton
  have hmax : IsLocalRing.maximalIdeal B ∈ I.minimalPrimes :=
    ⟨⟨inferInstance, IsLocalRing.le_maximalIdeal hItop⟩, fun q hq _ => (hI q hq.1 hq.2).ge⟩
  have : IsArtinianRing (B ⧸ I) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I hmax
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  refine ⟨inferInstance, ?_⟩
  let := htors.module
  have : IsScalarTower B (B ⧸ I)
      (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J)) :=
    htors.isScalarTower
  have : Module.Finite (B ⧸ I)
      (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J)) :=
    Module.Finite.of_restrictScalars_finite B _ _
  have : IsArtinian (B ⧸ I)
      (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J)) :=
    isArtinian_of_fg_of_artinian'
  exact isArtinian_of_surjective_algebraMap (R := B ⧸ I) Ideal.Quotient.mk_surjective

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PTrdegAdjoinLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Algebra Cardinal Set AlgebraicIndependent

noncomputable section

section TrdegRank

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

theorem matroid_subalgebra_eq_comap (S : Subalgebra K Ω) :
    AlgebraicIndependent.matroid K S = (AlgebraicIndependent.matroid K Ω).comap ((↑) : S → Ω) := by
  refine Matroid.ext_indep (by simp) fun I _ => ?_
  have hinj : InjOn ((↑) : S → Ω) I := Subtype.val_injective.injOn
  rw [Matroid.comap_indep_iff, matroid_indep_iff, matroid_indep_iff]
  simp only [hinj, and_true]
  change AlgebraicIndependent K (fun i : I => (i : S)) ↔
    AlgebraicIndependent K (fun x : (((↑) : S → Ω) '' I) => (x : Ω))
  rw [← algebraicIndependent_image hinj]
  exact (S.val.algebraicIndependent_iff Subtype.val_injective).symm

theorem trdeg_adjoin_eq_cRk (A : Set Ω) :
    Algebra.trdeg K (Algebra.adjoin K A) = (AlgebraicIndependent.matroid K Ω).cRk A := by
  rw [← matroid_cRank_eq, matroid_subalgebra_eq_comap, ← Matroid.cRk_ground, Matroid.comap_ground_eq,
    Matroid.cRk_comap, matroid_e, preimage_univ, image_univ, Subtype.range_coe]
  refine le_antisymm ?_ (Matroid.cRk_le_of_subset _ Algebra.subset_adjoin)
  refine (Matroid.cRk_le_of_subset _ ?_).trans_eq (Matroid.cRk_closure _ A)
  intro x hx
  rw [matroid_closure_eq]
  exact isAlgebraic_algebraMap (⟨x, hx⟩ : Algebra.adjoin K A)

end TrdegRank

theorem TrdegAdjoinLe.proof : TrdegAdjoinLe.Statement := by
  intro K Ω _ _ _ s ι _ t ι' w hw
  set M := AlgebraicIndependent.matroid K Ω
  rw [trdeg_adjoin_eq_cRk, trdeg_adjoin_eq_cRk]
  have hcl : range w ⊆ M.closure (s ∪ range t) := by
    rintro _ ⟨i, rfl⟩
    rw [matroid_closure_eq]
    exact hw i
  calc M.cRk (range w) ≤ M.cRk (M.closure (s ∪ range t)) := M.cRk_le_of_subset hcl
    _ = M.cRk (s ∪ range t) := M.cRk_closure _
    _ ≤ M.cRk (s ∩ range t) + M.cRk (s ∪ range t) := le_add_self
    _ ≤ M.cRk s + M.cRk (range t) := M.cRk_inter_add_cRk_union_le s (range t)
    _ ≤ M.cRk s + #(range t) := by gcongr; exact M.cRk_le_cardinalMk _
    _ ≤ M.cRk s + #ι := by gcongr; exact mk_range_le
    _ = M.cRk s + Fintype.card ι := by rw [mk_fintype]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PTrdegBaseAlgebraic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Cardinal

theorem TrdegBaseAlgebraic.proof : TrdegBaseAlgebraic.Statement := by
  intro F K Ω _ _ _ _ _ _ _ hKF ι z
  obtain ⟨A, hA⟩ : ∃ A : Subalgebra F Ω, A = Algebra.adjoin F (Set.range z) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Subalgebra K Ω, B = Algebra.adjoin K (Set.range z) := ⟨_, rfl⟩
  rw [← hA, ← hB]
  have hAB : ∀ w ∈ A, w ∈ B := by
    intro w hw
    rw [hA] at hw
    rw [hB]
    induction hw using Algebra.adjoin_induction with
    | mem w hw => exact Algebra.subset_adjoin hw
    | algebraMap c =>
      rw [IsScalarTower.algebraMap_apply F K Ω c]
      exact Subalgebra.algebraMap_mem _ _
    | add u v _ _ hu hv => exact Subalgebra.add_mem _ hu hv
    | mul u v _ _ hu hv => exact Subalgebra.mul_mem _ hu hv

  let i : A →+* B :=
    { toFun := fun a => ⟨a, hAB a a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have : FaithfulSMul F A :=
    (faithfulSMul_iff_algebraMap_injective F A).mpr (algebraMap F A).injective
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis F A
  let x : t → B := fun a => i a
  set C : Subalgebra K B := Algebra.adjoin K (Set.range x) with hC

  have hFC : ∀ r ∈ Algebra.adjoin F (Set.range ((↑) : t → A)), i r ∈ C := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem r hr =>
      obtain ⟨a, rfl⟩ := hr
      exact Algebra.subset_adjoin ⟨a, rfl⟩
    | algebraMap c =>
      have : i (algebraMap F A c) = algebraMap K B (algebraMap F K c) := by
        apply Subtype.ext
        exact (IsScalarTower.algebraMap_apply F K Ω c)
      rw [this]
      exact C.algebraMap_mem _
    | add r s _ _ hr hs =>
      rw [map_add]
      exact C.add_mem hr hs
    | mul r s _ _ hr hs =>
      rw [map_mul]
      exact C.mul_mem hr hs
  let f : Algebra.adjoin F (Set.range ((↑) : t → A)) →+* C :=
    { toFun := fun r => ⟨i r, hFC r r.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun c : C => ((c : B) : Ω)) hab
  have key : ∀ (w : Ω), w ∈ Algebra.adjoin K (Set.range z) →
      ∀ (hw : w ∈ B), IsAlgebraic C (⟨w, hw⟩ : B) := by
    intro w hw'
    induction hw' using Algebra.adjoin_induction with
    | mem w hw' =>
      intro hw
      obtain ⟨m, rfl⟩ := hw'
      have hzA : z m ∈ A := hA ▸ Algebra.subset_adjoin ⟨m, rfl⟩
      have h1 : IsAlgebraic (Algebra.adjoin F (Set.range ((↑) : t → A))) (⟨z m, hzA⟩ : A) :=
        ht.isAlgebraic.isAlgebraic _
      exact h1.ringHom_of_comp_eq f i hf (RingHom.ext fun _ => rfl)
    | algebraMap k =>
      intro hw
      exact (hKF.isAlgebraic k).ringHom_of_comp_eq ((algebraMap K C).comp (algebraMap F K))
        (algebraMap K B) (RingHom.injective _) (RingHom.ext fun _ => rfl)
    | add u v hu' hv' hu hv =>
      intro hw
      exact (hu (hB ▸ hu')).add (hv (hB ▸ hv'))
    | mul u v hu' hv' hu hv =>
      intro hw
      exact (hu (hB ▸ hu')).mul (hv (hB ▸ hv'))
  have alg : Algebra.IsAlgebraic C B := ⟨fun b => key b.1 (hB ▸ b.2) b.2⟩
  calc Algebra.trdeg K B ≤ #(Set.range x) := Algebra.IsAlgebraic.trdeg_le_cardinalMk K (Set.range x)
    _ ≤ #t := Cardinal.mk_range_le
    _ = Algebra.trdeg F A := ht.cardinalMk_eq_trdeg

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.RenameProdMapMul
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

section Swap

variable {F : Type*} [Field F] {n k : ℕ}

theorem comp_mem_incidence {I : Ideal (MvPolynomial (Fin n) F)} {u : Fin k × Fin n → AlgebraicClosure F}
    (hu : u ∈ incidence I k) (τ : Equiv.Perm (Fin k)) : u ∘ Prod.map τ id ∈ incidence I k := by
  obtain ⟨x, hx, hI, hlin⟩ := hu
  exact ⟨x, hx, hI, fun i => by simpa using hlin (τ i)⟩

theorem IsChowForm.dvd_rename {I : Ideal (MvPolynomial (Fin n) F)} {f : MvPolynomial (Fin k × Fin n) F}
    (hf : IsChowForm I k f) (τ : Equiv.Perm (Fin k)) : f ∣ rename (Prod.map τ id) f := by
  refine (hf.2 _).mp fun u hu => ?_
  rw [aeval_rename]
  exact (hf.2 f).mpr dvd_rfl _ (comp_mem_incidence hu τ)

theorem rename_prodMap_mul (σ τ : Equiv.Perm (Fin k)) (p : MvPolynomial (Fin k × Fin n) F) :
    rename (Prod.map (σ * τ) id) p = rename (Prod.map σ id) (rename (Prod.map τ id) p) := by
  rw [rename_rename]
  rfl

theorem rename_prodMap_one (p : MvPolynomial (Fin k × Fin n) F) :
    rename (Prod.map ⇑(1 : Equiv.Perm (Fin k)) id) p = p := by
  have : Prod.map ⇑(1 : Equiv.Perm (Fin k)) (id : Fin n → Fin n) = id := by
    funext ij
    rfl
  rw [this]
  exact rename_id_apply p

theorem IsChowForm.rename_eq_C_mul {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) (τ : Equiv.Perm (Fin k)) :
    ∃ c : F, rename (Prod.map τ id) f = C c * f := by
  obtain ⟨a, ha⟩ := hf.dvd_rename τ
  obtain ⟨b, hb⟩ := hf.dvd_rename (τ⁻¹ : Equiv.Perm (Fin k))
  have hback : rename (Prod.map τ id) (rename (Prod.map ⇑(τ⁻¹ : Equiv.Perm (Fin k)) id) f) = f := by
    rw [← rename_prodMap_mul, mul_inv_cancel, rename_prodMap_one]
  have hab : a * rename (Prod.map τ id) b = 1 := by
    have h1 : f * (a * rename (Prod.map τ id) b) = f * 1 := by
      rw [mul_one, ← mul_assoc, ← ha]
      conv_rhs => rw [← hback, hb]
      rw [map_mul]
    exact mul_left_cancel₀ hf.1 h1
  obtain ⟨c, -, rfl⟩ := (isUnit_iff_eq_C_of_isReduced (P := a)).mp (IsUnit.of_mul_eq_one _ hab)
  exact ⟨c, by rw [ha, mul_comm]⟩

theorem IsChowForm.rename_swap {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) (x y : Fin k) :
    ∃ c : F, c ^ 2 = 1 ∧ rename (Prod.map (Equiv.swap x y) id) f = C c * f := by
  obtain ⟨c, hc⟩ := hf.rename_eq_C_mul (Equiv.swap x y)
  refine ⟨c, ?_, hc⟩
  have h2 : rename (Prod.map (Equiv.swap x y * Equiv.swap x y) id) f = C (c ^ 2) * f := by
    rw [rename_prodMap_mul, hc, map_mul, rename_C, hc, ← mul_assoc, ← C_mul, sq]
  rw [Equiv.swap_mul_self, rename_prodMap_one] at h2
  have h3 : (C (c ^ 2) - 1) * f = 0 := by
    rw [sub_mul, ← h2, one_mul, sub_self]
  have h4 : C (c ^ 2) - 1 = (0 : MvPolynomial (Fin k × Fin n) F) :=
    (mul_eq_zero.mp h3).resolve_right hf.1
  rw [sub_eq_zero, ← C_1] at h4
  exact C_injective _ _ h4

theorem chowFormSwap : ChowFormSwap.Statement := by
  intro F _ n k I f hf τ
  induction τ using Equiv.Perm.swap_induction_on with
  | one => exact ⟨1, one_pow 2, by rw [C_1, one_mul, rename_prodMap_one]⟩
  | swap_mul σ x y _ ih =>
    obtain ⟨c, hc2, hc⟩ := ih
    obtain ⟨d, hd2, hd⟩ := hf.rename_swap x y
    refine ⟨d * c, by rw [mul_pow, hc2, hd2, one_mul], ?_⟩
    rw [rename_prodMap_mul, hc, map_mul, rename_C, hd, C_mul]
    ring

end Swap

end

end GroundTheory.Heights₂.Heights
end

