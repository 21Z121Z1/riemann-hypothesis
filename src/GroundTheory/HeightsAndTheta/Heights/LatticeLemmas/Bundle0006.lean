import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Statements
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Extension

-- bundled from GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PHadamardMean
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField Matrix GroundTheory.Heights₂.Heights

noncomputable section

section GramHadamard

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem norm_sub_starProjection_le {ι : Type*} [Fintype ι] (v : ι → V) (y : V) :
    ‖y - (Submodule.span ℂ (Set.range v)).starProjection y‖ ≤ ‖y‖ := by
  set U := Submodule.span ℂ (Set.range v)
  calc ‖y - U.starProjection y‖ ≤ ‖y - ((0 : U) : V)‖ := by
        rw [Submodule.starProjection_minimal]
        exact ciInf_le ⟨0, fun _ ⟨_, h⟩ ↦ h ▸ norm_nonneg _⟩ (0 : U)
    _ = ‖y‖ := by simp

theorem re_det_gram_le_prod_fin : ∀ (n : ℕ) (c : Fin n → V),
    (det (gram ℂ c)).re ≤ ∏ i, ‖c i‖ ^ 2 := by
  intro n
  induction n with
  | zero => intro c; simp
  | succ n ih =>
    intro c
    let e : Fin n ⊕ Unit ≃ Fin (n + 1) :=
      (Equiv.sumCongr (Equiv.refl _) finOneEquiv.symm).trans finSumFinEquiv
    have he : c ∘ e = Sum.elim (fun i ↦ c i.castSucc) (fun _ : Unit ↦ c (Fin.last n)) := by
      funext b
      rcases b with i | u
      · rfl
      · simp only [Function.comp_apply, Sum.elim_inr]
        congr 1
    have key : det (gram ℂ c) = det (gram ℂ fun i : Fin n ↦ c i.castSucc) *
        ((‖c (Fin.last n) - (Submodule.span ℂ (Set.range fun i : Fin n ↦ c i.castSucc)).starProjection
          (c (Fin.last n))‖ ^ 2 : ℝ) : ℂ) := by
      rw [← det_gram_comp_equiv e c, he, det_gram_sumElim_eq, det_gram_unique]
    rw [key, Complex.re_mul_ofReal, Fin.prod_univ_castSucc]
    exact mul_le_mul (ih _)
      (pow_le_pow_left₀ (norm_nonneg _) (norm_sub_starProjection_le _ _) 2) (sq_nonneg _)
      (Finset.prod_nonneg fun i _ ↦ sq_nonneg _)

theorem re_det_gram_le_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → V) :
    (det (gram ℂ c)).re ≤ ∏ i, ‖c i‖ ^ 2 := by
  let e := (Fintype.equivFin ι).symm
  have h := re_det_gram_le_prod_fin (Fintype.card ι) (c ∘ e)
  rw [det_gram_comp_equiv e c] at h
  refine h.trans_eq ?_
  exact Fintype.prod_equiv e _ _ fun _ ↦ rfl

end GramHadamard

theorem HadamardMean.intersectionNumber_baseChange : HadamardMean.Statement := by
  intro K _ _ M ι _ x hx hcard
  classical
  have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  rw [HermitianBundle.deg, HermitianBundle.arithDegree, arithDegree_eq M.metric hx hcard, degreeWith]
  refine (div_le_div_iff_of_pos_right hn).mpr ?_
  have hσ : ∀ σ : K →+* ℂ,
      Real.log (gramDet M.metric σ x) ≤ 2 * ∑ i, Real.log (M.normAt σ (x i)) := by
    intro σ
    have hne : ∀ i, fibreVec M.metric σ (x i) ≠ 0 := fun i ↦
      (linearIndependent_fibreVec M.metric σ hx).ne_zero i
    have h1 : gramDet M.metric σ x ≤ ∏ i, ‖fibreVec M.metric σ (x i)‖ ^ 2 :=
      re_det_gram_le_prod _
    calc Real.log (gramDet M.metric σ x)
        ≤ Real.log (∏ i, ‖fibreVec M.metric σ (x i)‖ ^ 2) :=
          Real.log_le_log (gramDet_pos M.metric σ hx) h1
      _ = ∑ i, Real.log (‖fibreVec M.metric σ (x i)‖ ^ 2) := by
          rw [Real.log_prod]
          intro i _
          exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (hne i))
      _ = 2 * ∑ i, Real.log (M.normAt σ (x i)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [Real.log_pow, HermitianBundle.normAt]
          push_cast
          rfl
  have hsum : ∑ σ : K →+* ℂ, Real.log (gramDet M.metric σ x) ≤
      2 * ∑ i, ∑ σ : K →+* ℂ, Real.log (M.normAt σ (x i)) := by
    rw [Finset.sum_comm (f := fun i σ ↦ Real.log (M.normAt σ (x i))), Finset.mul_sum]
    exact Finset.sum_le_sum fun σ _ ↦ hσ σ
  have hc := Real.log_natCast_nonneg
    (Nat.card (M.carrier ⧸ Submodule.span (𝓞 K) (Set.range x)))
  linarith

theorem HadamardMean.proof (_h1 : Sublattice.Statement) : HadamardMean.Statement :=
  HadamardMean.intersectionNumber_baseChange

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PHadamardMeanQuotient
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField GroundTheory.Heights₂.Heights Submodule Cardinal TensorProduct

universe u v w

noncomputable section

variable {K : Type u} [Field K] [NumberField K]

theorem normAt_mkQ_le (M : HermitianBundle.{v} K) (F : Submodule (𝓞 K) M.carrier)
    (hF : M.Saturated F) (σ : K →+* ℂ) (e : M.carrier) :
    (M.quot F hF).normAt σ (F.mkQ e) ≤ M.normAt σ e := by
  have h := HermitianBundle.quot_norm_eq_iInf M F hF σ ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] F.mkQ e)
  refine (le_of_eq h).trans ?_
  exact ciInf_le ⟨0, by rintro _ ⟨y, rfl⟩; exact norm_nonneg _⟩
    (⟨(1 : ComplexAt σ) ⊗ₜ[𝓞 K] e, by simp⟩ :
      {y : Fibre σ M.carrier // F.mkQ.lTensor (ComplexAt σ) y = (1 : ComplexAt σ) ⊗ₜ[𝓞 K] F.mkQ e})

theorem exists_linearIndependent_mkQ (M : HermitianBundle.{v} K) (F : Submodule (𝓞 K) M.carrier)
    {ι : Type w} (x : ι → M.carrier)
    (hx : Module.finrank (𝓞 K) (span (𝓞 K) (Set.range x)) = Module.finrank (𝓞 K) M.carrier) :
    ∃ s : Fin (Module.finrank (𝓞 K) (M.carrier ⧸ F)) → ι,
      LinearIndependent (𝓞 K) (fun j ↦ F.mkQ (x (s j))) := by
  classical
  let v : ι → M.carrier ⧸ F := fun i ↦ F.mkQ (x i)
  obtain ⟨s, hs, hmax⟩ := exists_maximal_linearIndepOn (𝓞 K) v
  set N := span (𝓞 K) (v '' s)
  have hS : Module.IsTorsion (𝓞 K) (M.carrier ⧸ span (𝓞 K) (Set.range x)) := by
    rw [← Module.finrank_eq_zero_iff_isTorsion]
    have := Submodule.finrank_quotient_add_finrank (span (𝓞 K) (Set.range x))
    omega
  have hv : span (𝓞 K) (Set.range x) ≤
      (torsion (𝓞 K) ((M.carrier ⧸ F) ⧸ N)).comap (N.mkQ ∘ₗ F.mkQ) := by
    rw [span_le]
    rintro _ ⟨i, rfl⟩
    by_cases hi : i ∈ s
    · have : N.mkQ (v i) = 0 := by
        rw [mkQ_apply, Quotient.mk_eq_zero]
        exact subset_span ⟨i, hi, rfl⟩
      simp only [SetLike.mem_coe, mem_comap, LinearMap.coe_comp, Function.comp_apply]
      exact this ▸ zero_mem _
    · obtain ⟨a, ha, hav⟩ := hmax i hi
      simp only [SetLike.mem_coe, mem_comap, LinearMap.coe_comp, Function.comp_apply]
      rw [mem_torsion_iff]
      refine ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩, ?_⟩
      rw [Submonoid.smul_def, ← map_smul, mkQ_apply, Quotient.mk_eq_zero]
      exact hav
  have hT : Module.IsTorsion (𝓞 K) ((M.carrier ⧸ F) ⧸ N) := by
    intro q
    obtain ⟨q, rfl⟩ := N.mkQ_surjective q
    obtain ⟨m, rfl⟩ := F.mkQ_surjective q
    obtain ⟨a, ha⟩ := hS (x := (span (𝓞 K) (Set.range x)).mkQ m)
    rw [Submonoid.smul_def, ← map_smul, mkQ_apply, Quotient.mk_eq_zero] at ha
    obtain ⟨b, hb⟩ := (mem_torsion_iff _).mp (hv ha)
    refine ⟨b * a, ?_⟩
    rw [Submonoid.smul_def] at hb ⊢
    simpa [mul_smul, map_smul] using hb
  have hrank : Module.rank (𝓞 K) (M.carrier ⧸ F) ≤ #(v '' s) := by
    have h := rank_quotient_add_rank_of_isDomain N
    rw [Module.rank_eq_zero_iff_isTorsion.mpr hT, zero_add] at h
    exact h ▸ rank_span_le _
  have hle : lift.{w} #(Fin (Module.finrank (𝓞 K) (M.carrier ⧸ F))) ≤ lift.{0} #s := by
    have h1 := (lift_le.{w}).mpr hrank
    have h2 := mk_image_le_lift (f := v) (s := s)
    rw [← Module.finrank_eq_rank, lift_natCast] at h1
    rw [mk_fin, lift_natCast, lift_uzero]
    exact (lift_le.{v}).mp (by simpa using h1.trans h2)
  obtain ⟨e⟩ := lift_mk_le'.mp hle
  exact ⟨fun j ↦ (e j : ι), hs.comp e e.injective⟩

theorem HadamardMeanQuotient.proof (h1 : HadamardMean.Statement.{u, v, 0}) :
    HadamardMeanQuotient.Statement.{u, v, w} := by
  intro K _ _ M F hF ι x hx
  obtain ⟨s, hs⟩ := exists_linearIndependent_mkQ M F x hx
  refine ⟨s, hs, le_trans ?_ (h1 K (M.quot F hF) (fun j ↦ F.mkQ (x (s j))) hs
    (by rw [Fintype.card_fin]; rfl))⟩
  gcongr with j _ σ _
  have hne : HermitianBundle.normAt (M.quot F hF) σ (F.mkQ (x (s j))) ≠ 0 := by
    have := (linearIndependent_fibreVec (M.quot F hF).metric σ hs).ne_zero j
    exact norm_ne_zero_iff.mpr this
  have hpos : 0 < HermitianBundle.normAt (M.quot F hF) σ (F.mkQ (x (s j))) :=
    (norm_nonneg _).lt_of_ne' hne
  all_goals first
    | exact hpos
    | exact normAt_mkQ_le M F hF σ _

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PHadamardQuotient
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Module Submodule
open GroundTheory.Heights₂.Heights

universe u v w

noncomputable section

namespace HadamardQuotient

theorem exists_subfamily_card_eq_finrank {R M : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] (F : Submodule R M)
    {ι : Type*} (x : ι → M) (hx : finrank R (span R (Set.range x)) = finrank R M) :
    ∃ s : Set ι, LinearIndepOn R (F.mkQ ∘ x) s ∧ Finite s ∧ Nat.card s = finrank R (M ⧸ F) := by
  classical
  set y : ι → M ⧸ F := F.mkQ ∘ x with hy_def
  obtain ⟨s, hs, hmax⟩ := exists_maximal_linearIndepOn R y
  have hfin : Finite s := LinearIndependent.finite_of_isNoetherian hs
  set S : Submodule R (M ⧸ F) := span R (y '' s) with hS_def

  have hy : ∀ i, S.mkQ (y i) ∈ torsion R ((M ⧸ F) ⧸ S) := by
    intro i
    by_cases hi : i ∈ s
    · have h0 : S.mkQ (y i) = 0 :=
        (Submodule.Quotient.mk_eq_zero S).mpr (subset_span ⟨i, hi, rfl⟩)
      rw [h0]
      exact zero_mem _
    · obtain ⟨a, ha, h⟩ := hmax i hi
      refine ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩, ?_⟩
      change a • S.mkQ (y i) = 0
      rw [← map_smul, mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact h
  have hspan : span R (Set.range y) ≤ (torsion R ((M ⧸ F) ⧸ S)).comap S.mkQ :=
    span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hy i)

  set N : Submodule R M := span R (Set.range x) with hN_def
  have hN : finrank R (M ⧸ N) = 0 := by
    have h := rank_quotient_add_rank_of_isDomain N
    rw [← finrank_eq_rank, ← finrank_eq_rank, ← finrank_eq_rank] at h
    norm_cast at h
    omega

  have hQS : finrank R ((M ⧸ F) ⧸ S) = 0 := by
    rw [Module.finrank_eq_zero_iff]
    intro q
    obtain ⟨q, rfl⟩ := S.mkQ_surjective q
    obtain ⟨m, rfl⟩ := F.mkQ_surjective q
    obtain ⟨a, ha, ham⟩ := Module.finrank_eq_zero_iff.mp hN (N.mkQ m)
    have h1 : a • m ∈ N := by
      rw [← map_smul, mkQ_apply, Submodule.Quotient.mk_eq_zero] at ham
      exact ham
    have h2 : F.mkQ (a • m) ∈ span R (Set.range y) := by
      have h := Submodule.mem_map_of_mem (f := F.mkQ) h1
      rwa [hN_def, Submodule.map_span, ← Set.range_comp] at h
    obtain ⟨⟨b, hb⟩, hbm⟩ := hspan h2
    refine ⟨b * a, mul_ne_zero (nonZeroDivisors.ne_zero hb) ha, ?_⟩
    change b • S.mkQ (F.mkQ (a • m)) = 0 at hbm
    rw [mul_smul, ← map_smul, ← map_smul, ← map_smul, ← map_smul]
    rw [map_smul, map_smul] at hbm
    rw [map_smul, map_smul]
    exact hbm
  have hadd := rank_quotient_add_rank_of_isDomain S
  rw [← finrank_eq_rank, ← finrank_eq_rank, ← finrank_eq_rank] at hadd
  norm_cast at hadd
  have := Fintype.ofFinite s
  have hSr : finrank R S = Nat.card s := by
    rw [hS_def, Set.image_eq_range, Nat.card_eq_fintype_card]
    exact finrank_span_eq_card hs
  exact ⟨s, hs, hfin, by omega⟩

variable {K : Type*} [Field K] [NumberField K]

theorem normAt_mkQ_le (M : HermitianBundle K) (F : Submodule (𝓞 K) M.carrier) (hF : M.Saturated F)
    (σ : K →+* ℂ) (x : M.carrier) :
    (M.quot F hF).normAt σ (F.mkQ x) ≤ M.normAt σ x := by
  have h := HermitianBundle.quot_norm_eq_iInf M F hF σ
    ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] (F.mkQ x : M.carrier ⧸ F))
  refine (le_of_eq h).trans ?_
  exact ciInf_le ⟨0, by rintro _ ⟨y, rfl⟩; exact norm_nonneg _⟩
    (⟨(1 : ComplexAt σ) ⊗ₜ[𝓞 K] x, rfl⟩ :
      {y : Fibre σ M.carrier // F.mkQ.lTensor (ComplexAt σ) y = (1 : ComplexAt σ) ⊗ₜ[𝓞 K] F.mkQ x})

end HadamardQuotient

theorem HadamardQuotient.proof (h1 : Hadamard.Statement.{u, v, w}) :
    HadamardQuotient.Statement.{u, v, w} := by
  intro K _ _ M F hF ι x La hx hLa
  obtain ⟨s, hs, hfin, hcard⟩ := exists_subfamily_card_eq_finrank F x hx
  have := Fintype.ofFinite s
  exact h1 K (M.quot F hF) (ι := s) (fun i ↦ F.mkQ (x i)) La hs
    (by rw [← Nat.card_eq_fintype_card]; exact hcard)
    (fun i σ ↦ (normAt_mkQ_le M F hF σ (x i)).trans (hLa i σ))

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PNormComparison
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
open GroundTheory.Heights₂.Heights
open scoped ComplexOrder MatrixOrder

noncomputable section

theorem re_det_le_of_posSemidef_smul_sub {n : Type*} [Fintype n] [DecidableEq n]
    {G G' : Matrix n n ℂ} (hG : G.PosDef) (hG' : G'.PosSemidef) (c : ℝ)
    (hc : (c • G - G').PosSemidef) : (det G').re ≤ c ^ Fintype.card n * (det G).re := by
  obtain ⟨P, hP⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hG.posSemidef.nonneg
  rw [star_eq_conjTranspose] at hP
  have hdetG : det G = star (det P) * det P := by
    rw [hP, det_mul, det_conjTranspose]
  have hPne : det P ≠ 0 := by
    intro h0
    have := hG.det_pos.ne'
    rw [hdetG, h0, mul_zero] at this
    exact this rfl
  have hU : IsUnit (det P) := isUnit_iff_ne_zero.mpr hPne
  set Q := P⁻¹ with hQ
  have hQP : Q * P = 1 := nonsing_inv_mul P hU
  have hPQ : P * Q = 1 := mul_nonsing_inv P hU
  set B := Qᴴ * G' * Q with hB
  have hBpsd : B.PosSemidef := hG'.conjTranspose_mul_mul_same Q
  have hG'eq : G' = Pᴴ * B * P := by
    calc G' = (Q * P)ᴴ * G' * (Q * P) := by rw [hQP, conjTranspose_one, one_mul, mul_one]
      _ = Pᴴ * B * P := by rw [conjTranspose_mul, hB]; simp only [Matrix.mul_assoc]
  have hQGQ : Qᴴ * G * Q = 1 := by
    calc Qᴴ * G * Q = (P * Q)ᴴ * (P * Q) := by
          rw [hP, conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPQ, conjTranspose_one, one_mul]
  have hCB : (c • (1 : Matrix n n ℂ) - B).PosSemidef := by
    have := hc.conjTranspose_mul_mul_same Q
    rwa [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hQGQ] at this
  have heig : ∀ i, hBpsd.1.eigenvalues i ≤ c := by
    intro i
    set u : n → ℂ := ⇑(hBpsd.1.eigenvectorBasis i)
    have h1 := hCB.re_dotProduct_nonneg u
    have hu : star u ⬝ᵥ u = 1 := by
      rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
        hBpsd.1.eigenvectorBasis.orthonormal.1 i]
      simp
    rw [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul, hu, map_sub,
      ← hBpsd.1.eigenvalues_eq i] at h1
    simpa using h1
  have hdetB : (det B).re ≤ c ^ Fintype.card n := by
    rw [hBpsd.1.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod]
    change (((∏ i, hBpsd.1.eigenvalues i : ℝ) : ℂ)).re ≤ _
    rw [Complex.ofReal_re]
    calc ∏ i, hBpsd.1.eigenvalues i ≤ ∏ _i : n, c :=
          Finset.prod_le_prod (fun i _ ↦ hBpsd.eigenvalues_nonneg i) (fun i _ ↦ heig i)
      _ = c ^ Fintype.card n := by rw [Finset.prod_const, Finset.card_univ]
  have hstar : star (det P) * det P = ((Complex.normSq (det P) : ℝ) : ℂ) := by
    rw [mul_comm]; exact Complex.mul_conj (det P)
  have hdetG' : det G' = det B * ((Complex.normSq (det P) : ℝ) : ℂ) := by
    rw [hG'eq, det_mul, det_mul, det_conjTranspose, ← hstar]; ring
  rw [hdetG', hdetG, hstar, Complex.re_mul_ofReal, Complex.ofReal_re]
  exact mul_le_mul_of_nonneg_right hdetB (Complex.normSq_nonneg _)

variable {K : Type*} [Field K] [NumberField K]

theorem gramDet_le_of_norm_le {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
    [Module.Projective (𝓞 K) E] (h h' : HermitianMetric K E) (σ : K →+* ℂ) (A : ℝ)
    (hA : ∀ x : Fibre σ E, ‖FibreSpace.equiv h' σ x‖ ≤ A * ‖FibreSpace.equiv h σ x‖)
    {r : ℕ} {s : Fin r → E} (hs : LinearIndependent (𝓞 K) s) :
    gramDet h' σ s ≤ (max A 0 ^ 2) ^ r * gramDet h σ s := by
  let L : FibreSpace h σ →ₗ[ℂ] FibreSpace h' σ :=
    (FibreSpace.equiv h' σ).toLinearMap ∘ₗ (FibreSpace.equiv h σ).symm.toLinearMap
  have hL : ∀ y, ‖L y‖ ≤ A * ‖y‖ := by
    intro y
    have := hA ((FibreSpace.equiv h σ).symm y)
    rwa [LinearEquiv.apply_symm_apply] at this
  let f := L.mkContinuous A hL
  have hf : ‖f‖ ≤ max A 0 := LinearMap.mkContinuous_norm_le' L hL
  set v : Fin r → FibreSpace h σ := fun i ↦ fibreVec h σ (s i)
  have hfv : (⇑f ∘ v) = fun i ↦ fibreVec h' σ (s i) := rfl
  have hpsd := posSemidef_opNorm_smul_gram_sub_gram v f
  rw [hfv] at hpsd
  have hmain := re_det_le_of_posSemidef_smul_sub
    (posDef_gram_of_linearIndependent (linearIndependent_fibreVec h σ hs))
    (posSemidef_gram ℂ _) _ hpsd
  rw [Fintype.card_fin] at hmain
  have hg : 0 < gramDet h σ s := gramDet_pos h σ hs
  calc gramDet h' σ s ≤ (‖f‖ ^ 2) ^ r * gramDet h σ s := hmain
    _ ≤ (max A 0 ^ 2) ^ r * gramDet h σ s := by
      gcongr

theorem NormComparison.proof : NormComparison.Statement := by
  intro K _ _ M h' A hA
  obtain ⟨s, hs⟩ := exists_linearIndependent_fin (K := K) (E := M.carrier)
  have hlog : ∀ σ : K →+* ℂ, Real.log (gramDet h' σ s) ≤
      2 * (Module.finrank (𝓞 K) M.carrier : ℝ) * Real.log (A σ) + Real.log (gramDet M.metric σ s) := by
    intro σ
    have hle := gramDet_le_of_norm_le M.metric h' σ (A σ) (hA σ) hs
    have hg : 0 < gramDet M.metric σ s := gramDet_pos _ σ hs
    have hg' : 0 < gramDet h' σ s := gramDet_pos _ σ hs
    rcases Nat.eq_zero_or_pos (Module.finrank (𝓞 K) M.carrier) with hr | hr
    · have h1 : (max (A σ) 0 ^ 2) ^ Module.finrank (𝓞 K) M.carrier = 1 := by rw [hr, pow_zero]
      have h0 : ((Module.finrank (𝓞 K) M.carrier : ℕ) : ℝ) = 0 := by exact_mod_cast hr
      rw [h1, one_mul] at hle
      rw [h0, mul_zero, zero_mul, zero_add]
      exact Real.log_le_log hg' hle
    · have hpos : 0 < (max (A σ) 0 ^ 2) ^ Module.finrank (𝓞 K) M.carrier :=
        (pos_iff_pos_of_mul_pos (lt_of_lt_of_le hg' hle)).mpr hg
      have hmax : 0 < max (A σ) 0 := by
        rcases (le_max_right (A σ) 0).lt_or_eq with h1 | h1
        · exact h1
        · rw [← h1] at hpos; simp [zero_pow (Nat.pos_iff_ne_zero.mp hr)] at hpos
      have hApos : 0 < A σ := by
        rcases le_or_gt (A σ) 0 with h1 | h1
        · rw [max_eq_right h1] at hmax; exact absurd hmax (lt_irrefl 0)
        · exact h1
      rw [max_eq_left hApos.le] at hle
      calc Real.log (gramDet h' σ s) ≤
            Real.log ((A σ ^ 2) ^ Module.finrank (𝓞 K) M.carrier * gramDet M.metric σ s) :=
            Real.log_le_log hg' hle
        _ = 2 * (Module.finrank (𝓞 K) M.carrier : ℝ) * Real.log (A σ) + Real.log (gramDet M.metric σ s) := by
          rw [Real.log_mul (by positivity) hg.ne', ← pow_mul, Real.log_pow]
          push_cast; ring
  simp only [HermitianBundle.deg, HermitianBundle.arithDegree]
  rw [arithDegree_eq M.metric hs (Fintype.card_fin _), arithDegree_eq h' hs (Fintype.card_fin _)]
  simp only [degreeWith]
  rw [← sub_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hsum : ∑ σ : K →+* ℂ, Real.log (gramDet h' σ s) ≤
      2 * (Module.finrank (𝓞 K) M.carrier : ℝ) * ∑ σ : K →+* ℂ, Real.log (A σ) + ∑ σ : K →+* ℂ, Real.log (gramDet M.metric σ s) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun σ _ ↦ hlog σ
  linarith

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
end

