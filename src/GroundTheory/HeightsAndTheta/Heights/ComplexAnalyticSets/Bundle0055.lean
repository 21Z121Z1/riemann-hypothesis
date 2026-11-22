import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0035
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0020
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0030
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0036
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0048
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegularOffHypersurface
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

theorem exists_ringKrullDim_quotient_eq_nat {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (hJ : J.IsPrime) :
    ∃ d : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d := by
  have : J.IsPrime := hJ
  have hge : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) :=
    ringKrullDim_nonneg_of_nontrivial
  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (n : WithBot ℕ∞) := by
    refine (ringKrullDim_quotient_le J).trans ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card,
      Fintype.card_fin, zero_add]
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = x at hge hle
  induction x using WithBot.recBotCoe with
  | bot => exact absurd hge (by simp)
  | coe m =>
    induction m using ENat.recTopCoe with
    | top => exact absurd hle (by norm_cast)
    | coe d => exact ⟨d, rfl⟩

theorem analyticOnNhd_of_differentiableOn_fin {d : ℕ} {σ : Type} [Fintype σ] {U : Set (Fin d → ℂ)}
    {G : (Fin d → ℂ) → σ → ℂ} (hU : IsOpen U) (hG : DifferentiableOn ℂ G U) : AnalyticOnNhd ℂ G U := by
  intro y hy
  refine AnalyticAt.pi fun s => ?_
  have hs : DifferentiableOn ℂ (fun x => G x s) U :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) s).differentiable.comp_differentiableOn hG
  refine analyticOnNhd_of_continuousOn_of_separately hU hs.continuousOn (fun z hz i => ?_) y hy
  have h1 : DifferentiableAt ℂ (fun x => G x s) (Function.update z i (z i)) := by
    rw [Function.update_eq_self]
    exact hs.differentiableAt (hU.mem_nhds hz)
  exact h1.comp (z i) (hasFDerivAt_update (𝕜 := ℂ) z (z i)).differentiableAt

theorem RegularOffHypersurface.proof (hG : FrameGraphGeneric.Statement) : RegularOffHypersurface.Statement := by
  intro σ _ I hI
  set n := Fintype.card σ
  set e : σ ≃ Fin n := Fintype.equivFin σ
  set φ : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial σ ℂ := renameEquiv ℂ e.symm
  set J : Ideal (MvPolynomial (Fin n) ℂ) := I.comap φ
  have hJ : J.IsPrime := Ideal.IsPrime.comap _
  have hφ : ∀ (x : σ → ℂ) (q : MvPolynomial (Fin n) ℂ), eval x (φ q) = eval (x ∘ e.symm) q := fun x q => by
    simp [φ, eval_rename]
  obtain ⟨d, hd⟩ := exists_ringKrullDim_quotient_eq_nat J hJ
  let b := EuclideanSpace.basisFun (Fin n) ℂ
  obtain ⟨I₀, q, hcard, hqJ, hreg⟩ := hG n d J hJ hd b

  let T : (σ → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    ((EuclideanSpace.equiv (Fin n) ℂ).symm : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)).comp
      (ContinuousLinearMap.pi fun i : Fin n => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) (e.symm i))
  let S : EuclideanSpace ℂ (Fin n) →L[ℂ] (σ → ℂ) :=
    (ContinuousLinearMap.pi fun s : σ => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) (e s)).comp
      ((EuclideanSpace.equiv (Fin n) ℂ : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ)))
  have hT : ∀ x i, T x i = x (e.symm i) := fun x i => rfl
  have hS : ∀ w s, S w s = w (e s) := fun w s => rfl
  have hST : ∀ x, S (T x) = x := fun x => funext fun s => by simp [hS, hT]
  have hTS : ∀ w, T (S w) = w := fun w => by ext i; simp [hS, hT]
  have hZ : ∀ x : σ → ℂ, x ∈ zeroSetIn I ↔ T x ∈ zeroSetEuc J := by
    intro x
    have hx : (fun i => T x i) = x ∘ e.symm := rfl
    simp only [zeroSetIn, zeroSetEuc, Set.mem_ofPred_eq, hx]
    constructor
    · intro h p hp
      rw [← hφ]
      exact h _ (Ideal.mem_comap.mp hp)
    · intro h p hp
      have := h (φ.symm p) (by simpa [J, Ideal.mem_comap] using hp)
      rwa [← hφ, AlgEquiv.apply_symm_apply] at this
  refine ⟨φ q, fun h => hqJ (Ideal.mem_comap.mpr h), ?_⟩
  intro z hz hzh
  obtain ⟨Ω, V, g, hΩ, hV, hzV, hg, hproj, hgraph⟩ :=
    hreg (T z) ((hZ z).mp hz) (by rwa [hφ] at hzh)
  let eI : I₀ ≃ Fin d := I₀.equivFinOfCardEq hcard
  let Ψ : (Fin d → ℂ) →L[ℂ] (I₀ → ℂ) :=
    ContinuousLinearMap.pi fun i : I₀ => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) (eI i)
  let A : (σ → ℂ) →L[ℂ] (Fin d → ℂ) :=
    ContinuousLinearMap.pi fun k : Fin d =>
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) (e.symm (eI.symm k))
  have hΨ : ∀ y i, Ψ y i = y (eI i) := fun y i => rfl
  have hA : ∀ x k, A x k = x (e.symm (eI.symm k)) := fun x k => rfl
  have hO : IsOpen (Ψ ⁻¹' Ω) := hΩ.preimage Ψ.continuous
  refine ⟨hz, d, A, Ψ ⁻¹' Ω, T ⁻¹' V, fun y => S (g (Ψ y)), hO, hV.preimage T.continuous, hzV, ?_, ?_, ?_⟩
  · exact analyticOnNhd_of_differentiableOn_fin hO (S.differentiable.comp_differentiableOn
      (hg.comp Ψ.differentiable.differentiableOn fun y hy => hy))
  · intro y hy
    ext k
    have h1 := congrFun (hproj (Ψ y) hy) (eI.symm k)
    simp only [frameProj, b, EuclideanSpace.basisFun_inner] at h1
    show A (S (g (Ψ y))) k = y k
    rw [hA, hS, Equiv.apply_symm_apply, h1, hΨ, Equiv.apply_symm_apply]
  · ext x
    constructor
    · rintro ⟨hxZ, hxV⟩
      have hmem : T x ∈ zeroSetEuc J ∩ V := ⟨(hZ x).mp hxZ, hxV⟩
      rw [hgraph] at hmem
      obtain ⟨u, hu, hgu⟩ := hmem
      have hΨu : Ψ (fun k => u (eI.symm k)) = u := funext fun i => by simp [hΨ]
      refine ⟨fun k => u (eI.symm k), ?_, ?_⟩
      · show Ψ _ ∈ Ω
        rwa [hΨu]
      · simp only [hΨu, hgu, hST]
    · rintro ⟨y, hy, rfl⟩
      have hmem : g (Ψ y) ∈ zeroSetEuc J ∩ V := hgraph ▸ Set.mem_image_of_mem g hy
      refine ⟨(hZ _).mpr ?_, ?_⟩
      · rw [hTS]; exact hmem.1
      · show T (S (g (Ψ y))) ∈ V
        rw [hTS]; exact hmem.2

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRiemannExtensionPolynomial
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology Set

open scoped Matrix

noncomputable section

theorem RiemannExtensionPolynomial.proof : RiemannExtensionPolynomial.Statement := by
  intro k P O f hP hO hc hd
  obtain ⟨M, hM, hlines⟩ := exists_frame_lines_not_in_zeroSet hP
  set A : (Fin k → ℂ) →L[ℂ] (Fin k → ℂ) := LinearMap.toContinuousLinearMap (Matrix.toLin' M) with hAdef
  have hAapp : ∀ x, A x = M *ᵥ x := fun x => rfl
  set U := A ⁻¹' O with hUdef
  have hU : IsOpen U := hO.preimage A.continuous
  have hgc : ContinuousOn (f ∘ A) U := hc.comp A.continuous.continuousOn fun z hz => hz
  have hPc : Continuous fun y : Fin k → ℂ => eval y P := by
    refine continuous_iff_continuousAt.2 fun y => ?_
    exact (AnalyticOnNhd.eval_mvPolynomial P y (mem_univ y)).continuousAt
  have hopen : IsOpen (O ∩ {y | eval y P ≠ 0}) := hO.inter (isOpen_ne_fun hPc continuous_const)
  have hA : ∀ (z : Fin k → ℂ) (i : Fin k) (t : ℂ),
      A (Function.update z i t) = A z + (t - z i) • fun j => M j i := by
    intro z i t
    have hupd : Function.update z i t = z + (t - z i) • Pi.single i 1 := by
      ext l
      by_cases h : l = i
      · subst h
        simp
      · simp [h]
    rw [hupd, hAapp, hAapp, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_single_one]
    rfl
  have hs : ∀ z ∈ U, ∀ i, DifferentiableAt ℂ (fun t => (f ∘ A) (Function.update z i t)) (z i) := by
    intro z hz i
    set v : Fin k → ℂ := fun j => M j i with hv
    set q : ℂ → ℂ := fun t => eval (A z + (t - z i) • v) P with hqdef
    have hqa : AnalyticOnNhd ℂ q univ := fun t _ =>
      (AnalyticOnNhd.eval_mvPolynomial P _ (mem_univ _)).comp
        (analyticAt_const.add ((analyticAt_id.sub analyticAt_const).smul analyticAt_const))
    have hq : ∀ᶠ t in 𝓝[≠] (z i), q t ≠ 0 := by
      by_contra hfreq
      rw [Filter.not_eventually] at hfreq
      simp only [ne_eq, not_not] at hfreq
      have hz0 := hqa.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
        (mem_univ (z i)) hfreq
      obtain ⟨t, ht⟩ := hlines i (A z)
      apply ht
      have h1 := hz0 (mem_univ (t + z i))
      simpa [hqdef] using h1
    have hline : Continuous fun t : ℂ => Function.update z i t := continuous_const.update i continuous_id
    have hUev : (fun t : ℂ => Function.update z i t) ⁻¹' U ∈ 𝓝 (z i) :=
      hline.continuousAt.preimage_mem_nhds (by rw [Function.update_eq_self]; exact hU.mem_nhds hz)
    refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
    · filter_upwards [hq, mem_nhdsWithin_of_mem_nhds hUev] with t hqt htU
      have hmem : A (Function.update z i t) ∈ O ∩ {y | eval y P ≠ 0} := by
        refine ⟨htU, ?_⟩
        show eval (A (Function.update z i t)) P ≠ 0
        rw [hA]
        exact hqt
      have hfd : DifferentiableAt ℂ f (A (Function.update z i t)) := hd.differentiableAt (hopen.mem_nhds hmem)
      exact hfd.comp t (A.differentiableAt.comp t (hasFDerivAt_update z t).differentiableAt)
    · exact ContinuousAt.comp_of_eq (g := f ∘ A) (f := fun t : ℂ => Function.update z i t) (hgc.continuousAt (hU.mem_nhds hz)) hline.continuousAt
        (Function.update_eq_self i z)
  have hgd : DifferentiableOn ℂ (f ∘ A) U := differentiableOn_of_continuousOn_of_separately hU hgc hs
  set B : (Fin k → ℂ) →L[ℂ] (Fin k → ℂ) := LinearMap.toContinuousLinearMap (Matrix.toLin' M⁻¹) with hBdef
  have hAB : ∀ y, A (B y) = y := by
    intro y
    show M *ᵥ (M⁻¹ *ᵥ y) = y
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M (Ne.isUnit hM), Matrix.one_mulVec]
  intro y hy
  have hBy : B y ∈ U := by
    show A (B y) ∈ O
    rw [hAB]
    exact hy
  have h1 : DifferentiableAt ℂ ((f ∘ A) ∘ B) y :=
    (hgd.differentiableAt (hU.mem_nhds hBy)).comp y B.differentiableAt
  have h2 : (f ∘ A) ∘ B = f := funext fun y => by simp only [Function.comp, hAB]
  rw [h2] at h1
  exact h1.differentiableWithinAt

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetImageAreaSetFrame
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Module

noncomputable section

namespace SheetImageAreaSet

theorem exists_adapted_frame {n d : ℕ}
    (P : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin d)) (hP : Function.Surjective P) :
    ∃ (m : ℕ) (e : Fin n ≃ Fin d ⊕ Fin m)
      (Q : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))
      (L : EuclideanSpace ℂ (Fin d) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin d))
      (π : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)),
      (∀ z, ‖Q z‖ = ‖z‖) ∧
        ∀ z, Q z = WithLp.toLp 2 (fun j => Sum.elim (fun i => L (P z) i) (fun i => π z i) (e j)) := by
  classical
  set K := LinearMap.ker P with hKdef
  have h1 := K.finrank_add_finrank_orthogonal
  have h2 := LinearMap.finrank_range_add_finrank_ker P
  rw [LinearMap.range_eq_top.2 hP, finrank_top] at h2
  simp only [finrank_euclideanSpace_fin] at h1 h2
  rw [← hKdef] at h2
  have hW : finrank ℂ Kᗮ = d := by omega
  have hn : n = d + finrank ℂ K := by omega
  let bW : OrthonormalBasis (Fin d) ℂ Kᗮ := (stdOrthonormalBasis ℂ Kᗮ).reindex (finCongr hW)
  let bK := stdOrthonormalBasis ℂ K
  let e : Fin n ≃ Fin d ⊕ Fin (finrank ℂ K) := (finCongr hn).trans finSumFinEquiv.symm
  let πW : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin d) :=
    bW.repr.toLinearMap ∘ₗ (Kᗮ.orthogonalProjectionOnto : _ →L[ℂ] Kᗮ).toLinearMap
  let π : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin (finrank ℂ K)) :=
    bK.repr.toLinearMap ∘ₗ (K.orthogonalProjectionOnto : _ →L[ℂ] K).toLinearMap
  obtain ⟨R, hR⟩ := P.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hP)
  have hPR : ∀ y, P (R y) = y := fun y => LinearMap.congr_fun hR y
  have hWR : ∀ z, πW (R (P z)) = πW z := by
    intro z
    have hmem : R (P z) - z ∈ Kᗮᗮ :=
      K.le_orthogonal_orthogonal (by simp [hKdef, LinearMap.mem_ker, hPR])
    have h0 := Submodule.orthogonalProjectionOnto_eq_zero_iff.2 hmem
    have h3 : πW (R (P z) - z) = 0 := by simp [πW, h0]
    rwa [map_sub, sub_eq_zero] at h3
  have hinj : Function.Injective (πW ∘ₗ R) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h0 : Kᗮ.orthogonalProjectionOnto (R y) = 0 := by simpa [πW] using hy
    rw [Submodule.orthogonalProjectionOnto_eq_zero_iff, K.orthogonal_orthogonal] at h0
    rw [← hPR y]
    exact h0
  let L := LinearEquiv.ofInjectiveEndo _ hinj
  let Q : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
    { toFun := fun z => WithLp.toLp 2 (fun j => Sum.elim (fun i => πW z i) (fun i => π z i) (e j))
      map_add' := fun z w => by
        ext j
        obtain ⟨s, rfl⟩ := e.symm.surjective j
        rcases s with i | i <;> simp
      map_smul' := fun c z => by
        ext j
        obtain ⟨s, rfl⟩ := e.symm.surjective j
        rcases s with i | i <;> simp }
  refine ⟨finrank ℂ K, e, Q, L, π, fun z => ?_, fun z => ?_⟩
  · refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    show ‖(WithLp.toLp 2 (fun j => Sum.elim (fun i => πW z i) (fun i => π z i) (e j)) :
      EuclideanSpace ℂ (Fin n))‖ ^ 2 = _
    rw [GraphAreaHolomorphic.norm_sq_sumElim e (πW z) (π z), Submodule.norm_sq_eq_add_norm_sq_projection z K,
      add_comm]
    simp [πW, π]
  · show WithLp.toLp 2 (fun j => Sum.elim (fun i => πW z i) (fun i => π z i) (e j)) = _
    simp [L, hWR]

theorem areaJacobian_eq_normDet {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (M : E →ₗ[ℝ] F) : areaJacobian M = M.normDet := by
  have h := M.normDet_sq
  simp only [RCLike.ofReal_real_eq_id, id_eq] at h
  rw [areaJacobian, ← h, Real.sqrt_sq M.normDet_nonneg]

theorem areaJacobian_comp_of_norm {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (Q : F →ₗ[ℝ] F) (hQ : ∀ v, ‖Q v‖ = ‖v‖) (M : E →ₗ[ℝ] F) :
    areaJacobian (Q ∘ₗ M) = areaJacobian M := by
  rw [areaJacobian_eq_normDet, areaJacobian_eq_normDet, LinearMap.normDet_comp,
    show (Q.domRestrict (LinearMap.range M)).normDet = 1 from
      LinearIsometry.normDet_eq_one ⟨Q.domRestrict _, fun v => hQ v⟩, one_mul]

theorem areaJacobian_comp_endo {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (M : E →ₗ[ℝ] F) (T : E →ₗ[ℝ] E) :
    areaJacobian (M ∘ₗ T) = areaJacobian M * |LinearMap.det T| := by
  rw [areaJacobian_eq_normDet, areaJacobian_eq_normDet, LinearMap.normDet_comp_of_finrank_eq _ _ rfl,
    LinearMap.normDet_eq_abs_det]

end SheetImageAreaSet

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetPieceReachesCentre
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem SheetPieceReachesCentre.proof : SheetPieceReachesCentre.Statement := by
  intro σ _ X w B d A D δ N U V hpar hU hV hcover hdisj hne
  obtain ⟨-, hwXB, hD, hDc, hmaps, hprop, hcentre, hδ, ⟨y₁, hy₁D, hy₁⟩, -, hchart, -⟩ := hpar
  set T : Set (σ → ℂ) := {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ U with hTdef

  have key : ∀ y ∈ D, y ∈ closure (A '' T) → ∃ x ∈ closure T, x ∈ X ∩ B ∧ A x = y := by
    intro y hyD hy
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hD y hyD
    have hKD : Metric.closedBall y (ε / 2) ⊆ D :=
      (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
    have hP := hprop _ hKD (isCompact_closedBall y (ε / 2))
    have hQsub : closure (T ∩ A ⁻¹' Metric.closedBall y (ε / 2)) ⊆
        {x | x ∈ X ∩ B ∧ A x ∈ Metric.closedBall y (ε / 2)} :=
      closure_minimal (fun x hx => ⟨hx.1.1.1, hx.2⟩) hP.isClosed
    have hQ : IsCompact (closure (T ∩ A ⁻¹' Metric.closedBall y (ε / 2))) :=
      hP.of_isClosed_subset isClosed_closure hQsub
    have hAQ : IsClosed (A '' closure (T ∩ A ⁻¹' Metric.closedBall y (ε / 2))) :=
      (hQ.image A.continuous).isClosed
    have hyK : y ∈ closure (A '' (T ∩ A ⁻¹' Metric.closedBall y (ε / 2))) := by
      rw [mem_closure_iff_nhds] at hy ⊢
      intro t ht
      obtain ⟨z, ⟨hzt, hzK⟩, x, hxT, rfl⟩ :=
        hy (t ∩ Metric.closedBall y (ε / 2)) (Filter.inter_mem ht (Metric.closedBall_mem_nhds y (half_pos hε)))
      exact ⟨A x, hzt, x, ⟨hxT, hzK⟩, rfl⟩
    obtain ⟨x, hxQ, rfl⟩ := closure_minimal (Set.image_mono subset_closure) hAQ hyK
    exact ⟨x, closure_mono Set.inter_subset_left hxQ, (hQsub hxQ).1, rfl⟩

  have hopen : IsOpen (A '' T) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨x, ⟨⟨hxXB, hδx⟩, hxU⟩, rfl⟩
    obtain ⟨O, V', g, hO, hV', hxV', hg, hAg, hXBV⟩ := hchart x hxXB hδx
    obtain ⟨y₀, hy₀O, hgy₀⟩ : x ∈ g '' O := hXBV ▸ ⟨hxXB, hxV'⟩
    have hAx : A x = y₀ := by rw [← hgy₀, hAg y₀ hy₀O]
    subst hAx
    have h1 : g ⁻¹' (U ∩ V') ∈ 𝓝 (A x) :=
      (hg (A x) hy₀O).continuousAt.preimage_mem_nhds (by rw [hgy₀]; exact (hU.inter hV').mem_nhds ⟨hxU, hxV'⟩)
    have h2 : δ ⁻¹' {0}ᶜ ∈ 𝓝 (A x) :=
      (hδ (A x) (hmaps hxXB)).continuousAt.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hδx)
    filter_upwards [h1, h2, hO.mem_nhds hy₀O] with y hy1 hy2 hy3
    have hgy : g y ∈ X ∩ B ∩ V' := hXBV ▸ ⟨y, hy3, rfl⟩
    refine ⟨g y, ⟨⟨hgy.1, ?_⟩, hy1.1⟩, hAg y hy3⟩
    rw [hAg y hy3]
    exact hy2

  have hreg : ∀ y ∈ D, IsRegularPointOf D y := fun y hy =>
    ⟨hy, d, ContinuousLinearMap.id ℂ _, D, D, id, hD, hD, hy, fun _ _ => analyticAt_id, fun _ _ => rfl,
      by rw [Set.inter_self, Set.image_id]⟩
  have hE : IsPreconnected (D \ {z | δ z = 0}) :=
    ManifoldZerosComplementConnected.proof (Fin d) D δ hDc hreg hδ ⟨y₁, hy₁D, hy₁⟩
  have hEsub : D \ {z | δ z = 0} ⊆ A '' T := by
    refine hE.subset_of_closure_inter_subset hopen ?_ ?_
    · obtain ⟨x₀, hx₀S, hx₀U⟩ := hne
      exact ⟨A x₀, ⟨hmaps hx₀S.1, hx₀S.2⟩, x₀, ⟨hx₀S, hx₀U⟩, rfl⟩
    · rintro y ⟨hy, hyD, hyδ⟩
      obtain ⟨x, hxcl, hxXB, rfl⟩ := key y hyD hy
      have hxS : x ∈ {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} := ⟨hxXB, hyδ⟩
      rcases hcover hxS with hxU | hxV
      · exact ⟨x, ⟨hxS, hxU⟩, rfl⟩
      · exfalso
        obtain ⟨z, hzV, hzS, hzU⟩ := mem_closure_iff.mp hxcl V hV hxV
        have hz : z ∈ {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ (U ∩ V) := ⟨hzS, hzU, hzV⟩
        rw [hdisj] at hz
        exact hz

  have hwD : A w ∈ D := hmaps hwXB
  have hwE : A w ∈ closure (D \ {z | δ z = 0}) := by
    by_contra hw
    rw [mem_closure_iff_nhds] at hw
    push Not at hw
    obtain ⟨t, ht, hte⟩ := hw
    have hzero : δ =ᶠ[𝓝 (A w)] 0 := by
      filter_upwards [ht, hD.mem_nhds hwD] with y hyt hyD
      by_contra hy
      exact (Set.not_nonempty_iff_eq_empty.mpr hte) ⟨y, hyt, hyD, hy⟩
    exact hy₁ (hδ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hDc hwD hzero hy₁D)
  obtain ⟨x, hxcl, hxXB, hAx⟩ := key (A w) hwD (closure_mono hEsub hwE)
  rw [← hcentre x hxXB hAx]
  exact hxcl

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarietyProjectionMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix

open scoped ENNReal

noncomputable section

theorem VarietyProjectionMass.proof (hG : ComplexSets.GenericProjectionFinite.Statement)
    (hD : ComplexSets.DiscriminantCover.Statement) (hL : LocalGraphProjectionMass.Statement) :
    VarietyProjectionMass.Statement := by
  intro n d J hJ hd U hU B hB
  have hdn : d ≤ n := by
    have h1 := ringKrullDim_quotient_le J
    rw [hd, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h1
    simpa using h1
  obtain ⟨W, hW, hWfin⟩ := (hG n d J hJ hd).2.2.2 1 (fun _ => 1)
  obtain ⟨b, hb⟩ := MassFinite.exists_frame W hW
  obtain ⟨I₀, -, hI₀⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
    (by simpa using hdn)
  set A := W.submatrix (I₀.orderEmbOfFin hI₀) id
  have hAfin : ComplexSets.IsFiniteProjection J A := by
    simpa using hWfin 0 (I₀.orderEmbOfFin hI₀).toEmbedding
  obtain ⟨P, hP0, hP⟩ := hD n d J A hJ hd hAfin
  set G := zeroSetEuc J ∩ {z | eval (A *ᵥ WithLp.ofLp z) P ≠ 0}
  have hPJ : ComplexSets.pullback A P ∉ J := fun hmem => hP0 <| hAfin.injective <| by
    rw [map_zero, ComplexSets.projHom, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hmem
  have hbad : μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P})) = 0 :=
    NullSmaller.proof n d _ (MassFinite.dim_sup_lt J hJ hd _ hPJ)
  have hsub : zeroSetEuc J ∩ B ⊆
      zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P}) ∪ G ∩ B := by
    rintro z ⟨hz, hzB⟩
    by_cases hzP : eval (A *ᵥ WithLp.ofLp z) P = 0
    · left
      intro q hq
      obtain ⟨j, hj, c, hc, rfl⟩ := Submodule.mem_sup.mp hq
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hc
      have hzj : eval (fun i => z i) j = 0 := hz j hj
      have hpb : eval (fun i => z i) (ComplexSets.pullback A P) = 0 := by
        rw [MassFinite.eval_pullback]
        exact hzP
      simp [hzj, hpb]
    · exact Or.inr ⟨⟨hz, hzP⟩, hzB⟩
  have hgood := hL n d b I₀ G hI₀ (MassFinite.good_localGraph J W b hb I₀ hI₀ P
    (fun y hy x hx => (hP y hy).2.2 x hx)) U hU B hB
  have hGZ : G ∩ B ⊆ zeroSetEuc J ∩ B := Set.inter_subset_inter_left _ Set.inter_subset_left
  calc μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ B)
      ≤ μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P}) ∪ G ∩ B) :=
        measure_mono hsub
    _ ≤ μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P})) +
          μH[((2 * d : ℕ) : ℝ)] (G ∩ B) := measure_union_le _ _
    _ = μH[((2 * d : ℕ) : ℝ)] (G ∩ B) := by rw [hbad, zero_add]
    _ ≤ _ := hgood
    _ ≤ _ := by
      refine Finset.sum_le_sum fun s _ => mul_le_mul' (iSup_mono fun x => ?_)
        (measure_mono (Set.image_mono hGZ))
      exact ENat.toENNReal_le.2 (Set.encard_le_encard fun z hz => ⟨hGZ hz.1, hz.2⟩)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartMassCompare
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

open scoped ENNReal

noncomputable section

def ChartMassCompare.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) (R : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
    (∀ k, SmoothNear (zeroSet J) (φ k)) →
      ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ g : (Fin n → ℂ) → ℝ, Measurable g →
        ∫⁻ y, ‖chartAbsDens J A ((Metric.closedBall 0 R).indicator g) φ y‖ₑ ≤
          K * ∫⁻ z in zeroSetEuc J ∩ {z | WithLp.ofLp z ∈ Metric.closedBall (0 : Fin n → ℂ) R},
            ‖g (WithLp.ofLp z)‖ₑ ∂(μH[((2 * d : ℕ) : ℝ)])

end

end GroundTheory.Heights₂.Heights
end

