import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothInExponentialCoordsIffFirstSecondKind
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0314
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0288
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0309
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
section
noncomputable section

namespace GlobalTheory.Mem.DerClosed

section Abstract

open GlobalTheory.SmoothForms GlobalTheory.SmoothForms.SecondKind NormedSpace Filter Asymptotics
open scoped ContDiff Topology

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem hasFDerivAt_diag {f f' : P → ℝ → ℂ} {A : P →L[ℝ] ℂ} (l : P →L[ℝ] ℝ) (h1 : HasFDerivAt (fun p => f p 0) A 0)
    (h2 : ∀ p t, HasDerivAt (f p) (f' p t) t) (h3 : ContinuousAt (fun q : P × ℝ => f' q.1 q.2) (0, 0)) :
    HasFDerivAt (fun p => f p (l p)) (A + l.smulRight (f' 0 0)) 0 := by
  have key : HasFDerivAt (fun p => f p (l p) - f p 0) (l.smulRight (f' 0 0)) 0 := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    refine IsLittleO.trans_isBigO (g := fun p => l p) ?_ (l.isBigO_id _)
    rw [isLittleO_iff]
    intro ε hε
    obtain ⟨δ, hδ, h4⟩ := Metric.continuousAt_iff.1 h3 ε hε
    have e1 : ∀ᶠ p in 𝓝 (0 : P), ‖p‖ < δ := (continuous_norm.tendsto' 0 0 norm_zero).eventually (gt_mem_nhds hδ)
    have e2 : ∀ᶠ p in 𝓝 (0 : P), ‖l p‖ < δ :=
      (l.continuous.norm.tendsto' 0 0 (by simp)).eventually (gt_mem_nhds hδ)
    filter_upwards [e1, e2] with p q1 q2
    have := (convex_ball (0 : ℝ) δ).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun t => f p t - t • f' 0 0) (f' := fun t => f' p t - f' 0 0) (C := ε) (x := 0) (y := l p)
      (fun t _ => ((h2 p t).sub (by simpa using (hasDerivAt_id t).smul_const (f' 0 0))).hasDerivWithinAt)
      (fun t ht => by
        have := @h4 (p, t) (by
          rw [Prod.dist_eq, max_lt_iff]
          exact ⟨by simpa using q1, ht⟩)
        rw [dist_eq_norm] at this
        exact this.le)
      (Metric.mem_ball_self hδ) (by simpa using q2)
    simp only [zero_add, map_zero, sub_self, sub_zero, zero_smul, ContinuousLinearMap.smulRight_apply] at this ⊢
    rwa [sub_right_comm]
  have := h1.fun_add key
  simpa using this

variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}

omit [FiniteDimensional ℝ 𝔸] in
theorem unit_mul (H : IsLieData σ j s) {a b : 𝔸} (ha : σ a * a = 1) (hb : σ b * b = 1) : σ (a * b) * (a * b) = 1 := by
  rw [H.anti, mul_assoc, ← mul_assoc (σ a), ha, one_mul, hb]

theorem expMap_add (H : IsLieData σ j s) (X : L) (t u : ℝ) :
    expMap j s ((t + u) • X) = expMap j s (t • X) * expMap j s (u • X) := by
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  let : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  unfold expMap
  rw [← H.mul _ _ (exp_unitary H _) (exp_unitary H _), add_smul, map_add, NormedSpace.exp_add_of_commute]
  rw [map_smul, map_smul]
  exact ((Commute.refl _).smul_left _).smul_right _

theorem exists_coord (H : IsLieData σ j s) (J : L →L[ℝ] 𝔸) (hJ : ∀ X, J X = j X) {ι : Type} (l : ι → P →L[ℝ] ℝ)
    (b : ι → L) {φ : G → ℂ} {φ' : ι → G → ℂ}
    (hd : ∀ i g, HasDerivAt (fun t : ℝ => φ (g * expMap j s (t • b i))) (φ' i g) 0) (g : G)
    (hc : ∀ i, ContinuousOn (fun u => φ' i (g * s u)) {u | σ u * u = 1}) (S : Finset ι) :
    ∃ c : P → 𝔸, ContDiff ℝ ∞ c ∧ (∀ p, σ (c p) * c p = 1) ∧ c 0 = 1 ∧
      HasFDerivAt c (J ∘L ∑ i ∈ S, (l i).smulRight (b i)) 0 ∧
      HasFDerivAt (fun p => φ (g * s (c p))) (∑ i ∈ S, (l i).smulRight (φ' i g)) 0 := by
  classical
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => 1, contDiff_const, fun _ => by simp [H.one], rfl, ?_, ?_⟩
    · simpa using hasFDerivAt_const (1 : 𝔸) (0 : P)
    · simpa using hasFDerivAt_const (φ (g * s 1)) (0 : P)
  | insert i S hi ih =>
    obtain ⟨c, h1, h2, h4, h5, h6⟩ := ih
    let A : P →L[ℝ] L := (l i).smulRight (b i)
    have hA : ContDiff ℝ ∞ fun p => exp (J (A p)) := contDiff_exp.comp (J ∘L A).contDiff
    have hu : ∀ X, σ (exp (J X)) * exp (J X) = 1 := fun p => by rw [hJ]; exact exp_unitary H _
    refine ⟨fun p => c p * exp (J (A p)), h1.mul hA, fun p => unit_mul H (h2 p) (hu _), by simp [h4], ?_, ?_⟩
    · have hd : HasFDerivAt (fun p => exp (J (A p))) (J ∘L A) 0 := by
        have := HasFDerivAt.comp (g := (exp : 𝔸 → 𝔸)) (g' := 1) (0 : P)
          (by simpa using hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := 𝔸)) (J ∘L A).hasFDerivAt
        exact this
      refine (h5.mul' hd).congr_fderiv ?_
      rw [Finset.sum_insert hi]
      ext p
      simp [h4, A]
    · have e : ∀ p (t : ℝ), s (c p * exp (J (t • b i))) = s (c p) * expMap j s (t • b i) := fun p t => by
        rw [H.mul _ _ (h2 p) (hu _), hJ, expMap]
      have := hasFDerivAt_diag (f := fun p t => φ (g * s (c p * exp (J (t • b i)))))
        (f' := fun p t => φ' i (g * s (c p * exp (J (t • b i))))) (l i) (by simpa using h6) (fun p t => ?_) ?_
      · rw [Finset.sum_insert hi, add_comm]
        simpa [h4, map_one_eq H, A] using this
      · have k := hd i (g * s (c p * exp (J (t • b i))))
        have k2 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact k)
        refine k2.congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)
        beta_reduce
        rw [e, e, mul_assoc, mul_assoc, ← expMap_add H, add_sub_cancel]
      · refine ((hc i).comp_continuous (f := fun q : P × ℝ => c q.1 * exp (J (q.2 • b i))) ?_
          fun q => unit_mul H (h2 _) (hu _)).continuousAt
        exact (h1.continuous.comp continuous_fst).mul (contDiff_exp.continuous.comp (by fun_prop))

theorem hasFDerivAt_expMap (H : IsLieData σ j s) (hl : HasLog σ j) {ι : Type} [Fintype ι] (l : ι → L →L[ℝ] ℝ)
    (b : ι → L) (hb : ∑ i, (l i).smulRight (b i) = ContinuousLinearMap.id ℝ L) {φ : G → ℂ} {φ' : ι → G → ℂ}
    (hd : ∀ i g, HasDerivAt (fun t : ℝ => φ (g * expMap j s (t • b i))) (φ' i g) 0) (g : G)
    (hc : ∀ i, ContinuousOn (fun u => φ' i (g * s u)) {u | σ u * u = 1}) :
    HasFDerivAt (fun X => φ (g * expMap j s X)) (∑ i, (l i).smulRight (φ' i g)) 0 := by
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  have : FiniteDimensional ℝ L := FiniteDimensional.of_injective j H.inj
  have : CompleteSpace L := FiniteDimensional.complete ℝ L
  let J : L →L[ℝ] 𝔸 := LinearMap.toContinuousLinearMap j
  obtain ⟨c, h1, h2, h4, h5, h6⟩ := exists_coord H J (fun _ => rfl) l b hd g hc Finset.univ
  rw [hb, ContinuousLinearMap.comp_id] at h5
  obtain ⟨Λ, l1, l2, l3⟩ := hl
  have hΛ : Λ 1 = 0 := by simpa using l3.self_of_nhds
  have l4 := (l1.differentiableAt (by simp)).hasFDerivAt
  have hd : HasFDerivAt (fun X : L => exp (j X)) J 0 :=
    HasFDerivAt.comp (g := (exp : 𝔸 → 𝔸)) (g' := 1) (0 : L)
        (by simpa using hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := 𝔸)) J.hasFDerivAt
  have l5 : fderiv ℝ Λ 1 ∘L J = ContinuousLinearMap.id ℝ L := by
    have := HasFDerivAt.comp (g := Λ) (g' := fderiv ℝ Λ 1) (0 : L) (by simpa using l4) hd
    exact this.unique ((hasFDerivAt_id (0 : L)).congr_of_eventuallyEq l3)
  have hΦ : ContDiffAt ℝ ∞ (Λ ∘ c) 0 := ContDiffAt.comp 0 (by rwa [h4]) h1.contDiffAt
  have hΦ' : HasFDerivAt (Λ ∘ c) (ContinuousLinearEquiv.refl ℝ L : L →L[ℝ] L) 0 := by
    have := HasFDerivAt.comp (g := Λ) (g' := fderiv ℝ Λ 1) _ (by rwa [h4]) h5
    rwa [l5] at this
  have h0 : (Λ ∘ c) 0 = 0 := by simp [h4, hΛ]
  have hs := hΦ.hasStrictFDerivAt' hΦ' (by simp)
  have p1 := hs.to_localInverse.hasFDerivAt
  have p2 := hs.localInverse_apply_image
  have p3 := hs.eventually_right_inverse
  rw [h0] at p1 p2 p3
  set Ψ := hs.localInverse _ _ _
  have ht : Tendsto (fun X => c (Ψ X)) (𝓝 0) (𝓝 1) := by
    have := (h1.continuous.tendsto (Ψ 0)).comp p1.continuousAt
    rwa [p2, h4] at this
  refine (HasFDerivAt.comp (g := fun p => φ (g * s (c p))) (0 : L) (by rw [p2]; exact h6) p1).congr_of_eventuallyEq ?_
  filter_upwards [p3, ht.eventually l2] with X q1 q2
  have := q2 (h2 _)
  simp only [Function.comp] at q1 ⊢
  rw [q1] at this
  rw [← this, expMap]

theorem sm_of_closed (H : IsLieData σ j s) (hl : HasLog σ j) (T : Set L) (hT : Submodule.span ℝ T = ⊤)
    (𝒮 : Set (G → ℂ)) (hc : ∀ φ ∈ 𝒮, ∀ g, ContinuousOn (fun u => φ (g * s u)) {u | σ u * u = 1})
    (hd : ∀ φ ∈ 𝒮, ∀ X ∈ T, ∃ φ' ∈ 𝒮, ∀ g, HasDerivAt (fun t : ℝ => φ (g * expMap j s (t • X))) (φ' g) 0) :
    ∀ φ ∈ 𝒮, Sm (expMap j s) φ := by
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  have : FiniteDimensional ℝ L := FiniteDimensional.of_injective j H.inj
  let J : L →L[ℝ] 𝔸 := LinearMap.toContinuousLinearMap j
  let b₀ := Module.Basis.ofSpan hT.ge
  have := FiniteDimensional.fintypeBasisIndex b₀
  let b := b₀.reindex (Fintype.equivFin _)
  have hb : ∀ i, b i ∈ T := fun i => Module.Basis.ofSpan_subset hT.ge ⟨_, (b₀.reindex_apply _ i).symm⟩
  let l := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  have hl' : ∑ i, (l i).smulRight (b i) = ContinuousLinearMap.id ℝ L := ContinuousLinearMap.ext fun X => by
    rw [_root_.sum_apply]
    exact b.sum_repr X
  obtain ⟨c, hcd⟩ : ∃ c : L → 𝔸, c = fun X => exp (j X) := ⟨_, rfl⟩
  have hE : ContDiff ℝ ∞ c := hcd ▸ contDiff_exp.comp J.contDiff
  have hu : ∀ p, σ (c p) * c p = 1 := hcd ▸ exp_unitary H
  have hσ : ContDiff ℝ ∞ fun p => σ (c p) := (LinearMap.toContinuousLinearMap σ).contDiff.comp hE
  obtain ⟨Λ, h1, h2, h3⟩ := id hl
  have hΛ : Λ 1 = 0 := by simpa using h3.self_of_nhds
  have key : ∀ n : ℕ, ∀ φ ∈ 𝒮, ∀ g, ContDiff ℝ n fun p => φ (g * s (c p)) := by
    intro n
    induction n with
    | zero => exact fun φ hφ g => contDiff_zero.2 ((hc φ hφ g).comp_continuous hE.continuous hu)
    | succ n ih =>
      intro φ hφ g
      choose φ' m1 m2 using fun i => hd φ hφ _ (hb i)
      have der : ∀ p₀, HasFDerivAt (fun p => φ (g * s (c p))) ((∑ i, (l i).smulRight (φ' i (g * s (c p₀)))) ∘L
          (fderiv ℝ Λ 1 ∘L (σ (c p₀) • fderiv ℝ c p₀))) p₀ := fun p₀ => by
        have hr : c p₀ * σ (c p₀) = 1 := by
          haveI : IsArtinianRing 𝔸 := IsArtinianRing.of_finite ℝ 𝔸
          exact mul_eq_one_comm.1 (hu p₀)
        have hd : HasFDerivAt (fun p => σ (c p₀) * c p) (σ (c p₀) • fderiv ℝ c p₀) p₀ :=
          (hE.differentiable (by simp) p₀).hasFDerivAt.const_mul _
        have ht : Tendsto (fun p => σ (c p₀) * c p) (𝓝 p₀) (𝓝 1) := by
          have := hd.continuousAt.tendsto
          rwa [hu p₀] at this
        have hu' : ∀ p, σ (σ (c p₀) * c p) * (σ (c p₀) * c p) = 1 := fun p =>
          unit_mul H (by rw [H.invol, hr]) (hu p)
        have h4 := HasFDerivAt.comp (g := Λ) (g' := fderiv ℝ Λ 1) p₀
          (by rw [hu p₀]; exact (h1.differentiableAt (by simp)).hasFDerivAt) hd
        have h5 := HasFDerivAt.comp (g := fun X : L => φ (g * s (c p₀) * expMap j s X)) p₀
          (by
            rw [Function.comp, hu p₀, hΛ]
            exact hasFDerivAt_expMap H hl l b hl' m2 _ fun i => hc _ (m1 i) _) h4
        refine h5.congr_of_eventuallyEq ((ht.eventually h2).mono fun p hp => ?_)
        simp only [Function.comp, expMap]
        rw [hp (hu' p), mul_assoc, ← H.mul _ _ (hu p₀) (hu' p), ← mul_assoc, hr, one_mul]
      rw [Nat.cast_succ, contDiff_succ_iff_fderiv_apply]
      refine ⟨fun p => (der p).differentiableAt, by simp, fun y => ?_⟩
      simp only [(der _).fderiv, ContinuousLinearMap.comp_apply, _root_.sum_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.smul_apply]
      refine ContDiff.sum fun i _ => ContDiff.smul (𝕜' := ℝ) ?_ (ih _ (m1 i) g)
      have k : ContDiff ℝ ∞ fun p => fderiv ℝ c p y :=
        (hE.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
      exact contDiff_infty.1 ((l i ∘L fderiv ℝ Λ 1).contDiff.comp (hσ.mul k)) n
  intro φ hφ g
  subst hcd
  exact contDiff_infty.2 fun n => key n φ hφ g

end Abstract

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SmoothForms

theorem continuousOn_secInf {D : D7} {θ : InfF D} (hθ : IsInfFam θ) (V : HSp D) :
    ContinuousOn (secInf θ V) {u | sigInf V u * u = 1} := by
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  have h := GlobalTheory.RealLift.continuousOn_prodAt hθ V Finset.univ.toList
  refine ContinuousOn.congr (h.mono fun u hu => (unit_iff R u).1 hu) fun u hu => ?_
  refine R.2.2.1 _ (secInf_spec R hu).1 _ (GlobalTheory.RealLift.prodAt_mem θ V _ u) fun τ => ?_
  rw [(secInf_spec R hu).2, GlobalTheory.RealLift.infMat_prodAt hθ V ((unit_iff R u).1 hu) τ _ (Finset.nodup_toList _),
    if_pos (Finset.mem_toList.2 (Finset.mem_univ _))]

theorem mem_smFun_of_closed : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), ∀ 𝒮 : Set (GA D V → ℂ), (∀ φ ∈ 𝒮, Continuous φ) → (∀ φ ∈ 𝒮, ∀ τ, ∀ X ∈ lieAt V τ, ∃ φ' ∈ 𝒮, ∀ g, HasDerivAt (fun t : ℝ => φ (g * oneP θ V τ X t)) (φ' g) 0) → ∀ φ ∈ 𝒮, φ ∈ SmFun θ V := by
  intro D θ hθ V 𝒮 hc hd φ hφ
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hT : Submodule.span ℝ {Y : LieN V | ∃ τ X, Y = atPlace V τ X} = ⊤ := by
    rw [eq_top_iff]
    intro X _
    have : X = ∑ τ, (atPlace V τ (X τ) : LieN V) := (sum_atPlace X).symm
    rw [this]
    exact sum_mem fun τ _ => Submodule.subset_span ⟨τ, _, rfl⟩
  refine (smooth_iff R φ).2 (sm_of_closed (isLieData R) (hasLog R) _ hT 𝒮 (fun ψ hψ g => ?_) ?_ φ hφ)
  · exact (hc ψ hψ).comp_continuousOn (continuousOn_const.mul (continuousOn_secInf hθ V))
  · rintro ψ hψ _ ⟨τ, X, rfl⟩
    obtain ⟨ψ', h1, h2⟩ := hd ψ hψ τ X.1 X.2
    refine ⟨ψ', h1, fun g => ?_⟩
    have := h2 g
    simp only [oneP_eq R] at this
    exact this

end GlobalTheory.Mem.DerClosed

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MoveDownLevelFunctionalEqStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.move_down_level_functional_eq : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → I.IdV l u a eV → I.IdL l Z u a i hi L → ∀ (v : (I.atT l u a).vT) (β : Ch) (c : {c // chOf c = β}) (g : Module.Dual (Res v.1) (((I.atIn u a).A i).lk v c.1)), g ≠ 0 → ∀ (γ : UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi)), (γ.1 : GL (Fin (B.R.N i)) B.fields.E) = (I.stp u a i).gam c.1.1 ((I.stp u a i).mv c.1.1 (((I.atIn u a).A i).dnPt v c.1 g)) → ∀ (x : ↥(LdG (I.rec7 l Z) i hi (latCrd (I.rec7 l Z) i hi (I.latAt u a i ((I.fm l u a).dn i v c.1 g))))) (hx : γ.1.1 *ᵥ x.1 ∈ LkG (I.rec7 l Z) i hi (PvG (I.resT l u a) v) (latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))), (I.fm l u a).fv i v _ (L.pr v _ x) = g (L.prk v c.1 ⟨_, hx⟩) := by
  first | exact @GlobalTheory.Mem.Col2.TC.dn_level_functional | exact GlobalTheory.Mem.Col2.TC.dn_level_functional | (intros; apply GlobalTheory.Mem.Col2.TC.dn_level_functional <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPullback
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.ArInt

theorem cls_eq_zero_of_chart_eq_top {Z : Scheme.{0}} {L : LB Z} (hL : L.IsLB) (i₀ : L.ι)
    (h : L.U i₀ = ⊤) : cls L hL = 0 := by
  have le : ∀ j, L.U j ≤ L.U j ⊓ L.U i₀ := fun j => le_inf le_rfl (h ▸ le_top)
  have hm : ∀ y : Z, y ∈ L.U i₀ := fun y => h ▸ Opens.mem_top y
  have H : ∃ t : LB.Gen L, t.IsGen :=
    ⟨⟨fun j => res (le j) (L.g j i₀)⟩, fun i j => unit_ext fun y hy => by
      rw [map_mul, gm_res (𝟙 Z) y _ hy, gm_res (𝟙 Z) y _ hy.1, gm_res (𝟙 Z) y _ hy, gm_res (𝟙 Z) y _ hy.2]
      exact (gm_cocycle hL (𝟙 Z) y hy.1 hy.2 (hm y)).symm⟩
  exact (cls_eq_iff hL (LB.isLB_triv Z)).2 (LBIso.symm ((iso_triv_iff L).2 H))

theorem topSelf_pull_eq_zero_of_const {X Z : Scheme.{0}} (κ : Type) [Field κ] [Algebra κ Γ(Z, ⊤)]
    {M : LB X} (hM : M.IsLB) (g : Z ⟶ X) (x : X) (hg : ∀ z, g z = x) :
    topSelfIntersection κ (M.pull g) 1 = 0 := by
  obtain ⟨i, hi⟩ := exists_chart hM x
  have h := cls_eq_zero_of_chart_eq_top (pull_isLB hM g) (fun _ => i)
    (top_le_iff.1 fun z _ => mem_pull.2 ((hg z).symm ▸ hi))
  exact interNum_eq_zero_of_cls_eq_zero κ _ (fun _ => pull_isLB hM g) 0 h

theorem isProper_strHom (κ : Type) [Field κ] {Z : Scheme.{0}} [Algebra κ Γ(Z, ⊤)] (t : Z ⟶ Sp ℤ)
    [IsProper t] : IsProper (strHom κ Z) := by
  have e : strHom κ Z ≫ spMap (Int.castRingHom κ) = t := specZIsTerminal.hom_ext _ _
  have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e]; infer_instance
  exact IsProper.of_comp _ (spMap (Int.castRingHom κ))

theorem appTop_injective_of_denseRange {Z W : Scheme.{0}} [IsReduced Z] (φ : W ⟶ Z)
    (h : DenseRange φ) : Function.Injective φ.appTop.hom := by
  refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
  by_contra hne0
  have hne : Z.basicOpen a ≠ ⊥ := fun h0 => hne0 ((basicOpen_eq_bot_iff a).1 h0)
  obtain ⟨w, hw⟩ := h.exists_mem_open (Z.basicOpen a).isOpen
    (Set.nonempty_iff_ne_empty.2 fun e => hne (Opens.ext e))
  have e : φ ⁻¹ᵁ Z.basicOpen a = W.basicOpen (φ.appTop.hom a) := Scheme.preimage_basicOpen_top φ a
  have hw' : w ∈ W.basicOpen (φ.appTop.hom a) := e ▸ hw
  rw [ha, Scheme.basicOpen_zero] at hw'
  exact hw'

section

attribute [local instance low] specializationOrder

theorem one_le_dim {S : Type} [TopologicalSpace S] [QuasiSober S] [T0Space S] {a b : S} (h : a ⤳ b)
    (hne : a ≠ b) : 1 ≤ topologicalKrullDim S := by
  rw [PosBaseChange.dim_eq_krullDim]
  exact Order.one_le_krullDim_iff.2 ⟨b, a, lt_of_le_of_ne h hne.symm⟩

end

section Curve

variable {X W : Scheme.{0}} [IsIntegral W] (ℓ : ℕ) [Fact ℓ.Prime] [Algebra (ZMod ℓ) Γ(W, ⊤)]

theorem topSelf_pull_nonneg (t : X ⟶ Sp ℤ) [IsProper t] (hd : topologicalKrullDim W = 1)
    {M : LB X} (hM : M.IsLB) (g : W ⟶ X) [IsProper (g ≫ t)]
    (H : ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
      [Algebra (ZMod ℓ) Γ(Z, ⊤)], topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod ℓ) (M.pull i) 1) :
    0 ≤ topSelfIntersection (ZMod ℓ) (M.pull g) 1 := by
  have : IsProper g := .of_comp g t
  have hW : IsProper (strHom (ZMod ℓ) W) := isProper_strHom (ZMod ℓ) (g ≫ t)
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (strHom (ZMod ℓ) W)
  have := isNoetherian_of_locallyOfFiniteType_field (strHom (ZMod ℓ) W)
  by_cases hc : ∀ w, g w = g (genericPoint W)
  · exact (topSelf_pull_eq_zero_of_const (ZMod ℓ) hM g _ hc).ge
  push_neg at hc
  obtain ⟨x₀, hx₀⟩ := hc
  let φ : W ⟶ g.image := g.toImage
  have e : φ ≫ g.imageι = g := g.toImage_imageι
  have : IsProper (φ ≫ g.imageι) := by rw [e]; infer_instance
  have : IsProper φ := .of_comp φ g.imageι
  have hne : φ x₀ ≠ φ (genericPoint W) := fun h => hx₀ (by
    rw [← e, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h])
  have : LocallyQuasiFinite φ := ProperCurve.locallyQuasiFinite_of_ne hd φ hne
  have : IsFinite φ := IsFinite.of_isProper_of_locallyQuasiFinite φ
  have hdense : DenseRange φ := g.toImage.denseRange
  have hsurj : Function.Surjective φ := by
    rw [← Set.range_eq_univ, ← φ.isClosedMap.isClosed_range.closure_eq]
    exact hdense.closure_range
  have hgen : φ (genericPoint W) = genericPoint g.image := by
    have h₁ := (genericPoint_spec W).image φ.continuous
    rw [Set.image_univ, hdense.closure_range] at h₁
    exact h₁.eq (genericPoint_spec _)
  have hdZ : topologicalKrullDim g.image = 1 := by
    exact le_antisymm ((PosBaseChange.dim_le_of_isClosedMap φ.isClosedMap hsurj).trans hd.le)
      (one_le_dim (genericPoint_specializes (φ x₀)) fun h => hne (h.symm.trans hgen.symm))
  have hinj := appTop_injective_of_denseRange φ hdense
  have : CharP Γ(W, ⊤) ℓ := charP_of_injective_algebraMap (algebraMap (ZMod ℓ) Γ(W, ⊤)).injective ℓ
  have : CharP Γ(g.image, ⊤) ℓ := φ.appTop.hom.charP hinj ℓ
  letI : Algebra (ZMod ℓ) Γ(g.image, ⊤) := ZMod.algebra _ ℓ
  have hf (r : ZMod ℓ) : φ.appTop (algebraMap (ZMod ℓ) Γ(g.image, ⊤) r) = algebraMap (ZMod ℓ) Γ(W, ⊤) r :=
    RingHom.congr_fun (RingHom.ext_zmod (φ.appTop.hom.comp (algebraMap (ZMod ℓ) Γ(g.image, ⊤)))
      (algebraMap (ZMod ℓ) Γ(W, ⊤))) r
  have : IsProper (g.imageι ≫ t) := inferInstance
  have hZ : IsProper (strHom (ZMod ℓ) g.image) := isProper_strHom (ZMod ℓ) (g.imageι ≫ t)
  have hproj : IsProjOver (strHom (ZMod ℓ) g.image) := ProperCurve.isProjOver_of_isProper _ hdZ
  have hN := pull_isLB hM g.imageι
  have h₁ := GlobalTheory.ProjFin.interNumOn_eq_residueDegree_mul (ZMod ℓ) g.image W φ hproj hdZ hgen (M.pull g.imageι) hN
  have h₂ := interNumOn_eq_interNum_pull (k := ZMod ℓ) (L := ![M.pull g.imageι]) hf
    (fun i => by fin_cases i; exact hN)
  have h₃ : topSelfIntersection (ZMod ℓ) (M.pull g) 1 =
      interNum (ZMod ℓ) (structureModule W) fun i => (![M.pull g.imageι] i).pull φ := by
    refine interNum_congr_cls _ _ (fun _ => pull_isLB hM g) (fun i => by fin_cases i; exact pull_isLB hN φ) fun i => ?_
    fin_cases i
    refine (cls_pull hM g _).trans ?_
    refine Eq.trans ?_ (cls_pull hN φ _).symm
    exact (congrArg (fun f => pull f (cls M hM)) e.symm).trans (pull_comp φ g.imageι _)
  have h₄ : interNum (ZMod ℓ) (structureModule g.image) ![M.pull g.imageι] =
      topSelfIntersection (ZMod ℓ) (M.pull g.imageι) 1 := by
    refine congrArg _ (funext fun j => ?_)
    fin_cases j
    rfl
  rw [h₃, ← h₂, h₁, h₄]
  exact mul_nonneg (Int.natCast_nonneg _) (H _ g.imageι hdZ)

end Curve

theorem nefFib_pull : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X Y : Scheme.{0}) (p : X ⟶ Sp k)
    (q : Y ⟶ Sp k), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p),
    ArInt.NefFib L → ArInt.NefFib (L.pull π hπ) := by
  intro k _ _ X Y p q hp hq π hπ L hL
  refine nefFib_of_primeField k Y q _ fun W i _ _ ℓ _ _ hd => ?_
  obtain ⟨N, j, _, hj⟩ := hp
  obtain ⟨N', j', _, hj'⟩ := hq
  have := isProper_str k N
  have := isProper_str k N'
  have : IsProper p := hj ▸ inferInstance
  have : IsProper q := hj' ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have hp' : IsProper (π ≫ p) := by rw [hπ]; infer_instance
  have : IsProper π := .of_comp π p
  have hg : IsProper ((i ≫ π) ≫ p ≫ spMap (Int.castRingHom k)) := inferInstance
  have h := topSelf_pull_nonneg ℓ (p ≫ spMap (Int.castRingHom k)) hd L.isLB (i ≫ π)
    fun Z i' _ _ _ hd' => hL Z i' (ZMod ℓ) hd'
  have e : cls ((L.pull π hπ).B.pull i) (pull_isLB (L.pull π hπ).isLB i) =
      cls (L.B.pull (i ≫ π)) (pull_isLB L.isLB _) := by
    refine (cls_pull (L.pull π hπ).isLB i _).trans ?_
    refine Eq.trans ?_ (cls_pull L.isLB (i ≫ π) _).symm
    exact (pull_comp i π (cls L.B L.isLB)).symm
  rwa [topSelf_congr (ZMod ℓ) (pull_isLB (L.pull π hπ).isLB i) (pull_isLB L.isLB _)
    ((cls_eq_iff _ _).1 e)]

end GlobalTheory.ArInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Nontrivial
section
noncomputable section
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions.N Formalism.L2.Host GlobalTheory.CuspRep NumberField IsDedekindDomain

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

def trueK (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)
    (η η' : HostCGu D.host 1)
    (h1 : ∀ w, (ParLaws.locG hL D.nd.plOm η w).unr)
    (h2 : ∀ w, ¬ IsSplitPl D.host w → (ParLaws.locG hL D.nd.plOm η w).frobEig = {-1})
    (h3 : ∀ w, (ParLaws.locG hL D.nd.plOm η' w).unr ∧ (ParLaws.locG hL D.nd.plOm η' w).frobEig = (ParLaws.locG hL D.nd.plOm η w).frobEig.map (·⁻¹))
    (h4 : ∀ w w', IsSplitPl D.host w → IsConjPl D.host w w' → ∀ a b : ℂ, (ParLaws.locG hL D.nd.plOm η w).frobEig = {a} →
      (ParLaws.locG hL D.nd.plOm η w').frobEig = {b} → a * b = 1) : CGK D.naut :=
  haveI := host_isCMField D.host
  have L := ParLaws.laws hL hF D.host D.nd.Om D.nd.plOm
  have U : ∀ {a} (π : HostCGu D.host a) w, D.naut.unr ((T.e w).symm (ParLaws.locG hL D.nd.plOm π w)) ↔ (ParLaws.locG hL D.nd.plOm π w).unr :=
    fun π w => by rw [T.unr, Equiv.apply_symm_apply]
  have Fr : ∀ {a} (π : HostCGu D.host a) w, (ParLaws.locG hL D.nd.plOm π w).unr →
      D.naut.frobEig ((T.e w).symm (ParLaws.locG hL D.nd.plOm π w)) = (ParLaws.locG hL D.nd.plOm π w).frobEig :=
    fun π w h => by rw [T.frobEig _ _ ((U π w).2 h), Equiv.apply_symm_apply]
  have Dm : ∀ {a} (π : HostCGu D.host a) w, D.naut.lpDim ((T.e w).symm (ParLaws.locG hL D.nd.plOm π w)) = a :=
    fun π w => by rw [← T.dim, Equiv.apply_symm_apply]; exact L.1 π w
  { CG := fun a => {_π : HostCGu D.host a // 0 < a}
    csd := fun π => π.1.IsCsd
    ralg := fun π => π.1.IsRegAlg
    locG := fun π w => (T.e w).symm (ParLaws.locG hL D.nd.plOm π.1 w)
    locG_dim := fun π w => Dm π.1 w
    locG_unr_ae := fun π => (L.2.1 π.1).mono fun w h => (U π.1 w).2 h
    tw := fun π χ => ⟨π.1.tw χ.1, π.2⟩
    locG_tw := fun π χ w => (T.e w).injective (by
      rw [T.char _ _ _ (Dm χ.1 w), Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact L.2.2.1 π.1 χ.1 w)
    infG := fun π τ => π.1.infChar τ
    infG_card := fun π => L.2.2.2.1 π.1
    ralg_def := fun π => L.2.2.2.2.1 π.1
    infG_tw := fun π χ => L.2.2.2.2.2.1 π.1 χ.1
    csd_tw := fun π χ => L.2.2.2.2.2.2.1 π.1 χ.1
    csd_unr := fun π w w' hπ hc hu => by
      have h := L.2.2.2.2.2.2.2.1 π.1 w w' hπ hc ((U π.1 w).1 hu)
      exact ⟨(U π.1 w').2 h.1, by rw [Fr π.1 w' h.1, Fr π.1 w ((U π.1 w).1 hu)]; exact h.2⟩
    etaT := ⟨η, one_pos⟩
    etaTinv := ⟨η', one_pos⟩
    etaT_unr := fun w => (U η w).2 (h1 w)
    etaT_inert := fun w h => by rw [Fr η w (h1 w)]; exact h2 w h
    etaTinv_def := fun w => ⟨(U η' w).2 (h3 w).1, by rw [Fr η' w (h3 w).1, Fr η w (h1 w)]; exact (h3 w).2⟩
    etaT_split := fun w w' hs hc a b ha hb => by
      rw [Fr η w (h1 w)] at ha; rw [Fr η w' (h1 w')] at hb; exact h4 w w' hs hc a b ha hb }

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

def trueCG (hL hF) (D : D7) (hE : IsEmpty D.nd.Loc) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (η η' h1 h2 h3 h4) :
    CGTrue hL (setCG D hE (trueK hL hF D T η η' h1 h2 h3 h4)) (wdCG hE _ T) where
  e := fun _ => Function.Embedding.subtype _
  surj := fun _ h π => ⟨⟨π, h⟩, rfl⟩
  zero := ⟨fun π => lt_irrefl 0 π.2⟩
  loc := fun _ _ w => (T.e w).apply_symm_apply _
  tw := fun _ _ _ => rfl
  inf := fun _ _ _ => rfl
  csd := fun _ _ => Iff.rfl

theorem CGTrue.ralg {hL D T} (C : CGTrue hL D T) a (π : D.naut.CG a) : haveI := host_isCMField D.host; D.naut.ralg π ↔ (C.e a π).IsRegAlg := by
  rw [D.naut.ralg_def]; simp only [C.inf]; exact (GlobalTheory.CuspRep.CG.isRegAlg_iff _).symm

end GlobalTheory.HeightCounting
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormInfIsometryConjLeConstMulStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normInf_isometryConj_le_const_mul : ∀ (D : D7) (V V' : HSp D) (I : GlobalTheory.Mem.Isom.IsoMat V V') (θ : InfF D), IsInfFam θ → ∃ C : ℝ, 0 ≤ C ∧ ∀ g : GA D V, normInf θ V' (I.kap g) ≤ C * normInf θ V g := by
  first | exact @GlobalTheory.Mem.Isom.normInf_kap_le | exact GlobalTheory.Mem.Isom.normInf_kap_le | (intros; apply GlobalTheory.Mem.Isom.normInf_kap_le <;> assumption)
end

