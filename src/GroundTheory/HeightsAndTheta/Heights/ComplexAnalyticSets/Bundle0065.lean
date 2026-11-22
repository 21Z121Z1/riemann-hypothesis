import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0051
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0054
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0048
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0058
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0034
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0032
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0056
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0057
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0060
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0055
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0035

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHolomorphicKernelFibre
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology

theorem HolomorphicKernelFibre.proof : HolomorphicKernelFibre.Statement := by
  intro k U f b hU hf hb d hd
  set A : (Fin k → ℂ) →L[ℂ] Fin k → ℂ := fderiv ℂ f b with hA
  have hfa : AnalyticAt ℂ f b := InjectiveHolomorphicInverse.analyticAt_of_differentiableOn hU hf hb
  have hfd : HasFDerivAt f A b := (hf.differentiableAt (hU.mem_nhds hb)).hasFDerivAt
  set W := LinearMap.range (A : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) with hW
  set K := LinearMap.ker (A : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) with hK
  obtain ⟨C, hWC⟩ := W.exists_isCompl
  obtain ⟨K', hKK'⟩ := K.exists_isCompl
  have hdimC : Module.finrank ℂ C = Module.finrank ℂ (Fin d → ℂ) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (A : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ)
    have h2 := Submodule.finrank_add_eq_of_isCompl hWC
    rw [Module.finrank_fin_fun]
    rw [← hW, ← hK, hd] at h1
    omega
  have hdimK : Module.finrank ℂ K = Module.finrank ℂ (Fin d → ℂ) := by
    rw [Module.finrank_fin_fun]; exact hd
  let eC : C ≃ₗ[ℂ] (Fin d → ℂ) := LinearEquiv.ofFinrankEq _ _ hdimC
  let eK : K ≃ₗ[ℂ] (Fin d → ℂ) := LinearEquiv.ofFinrankEq _ _ hdimK
  let P : (Fin k → ℂ) →L[ℂ] Fin k → ℂ := LinearMap.toContinuousLinearMap (W.projection C hWC)
  let E : (Fin d → ℂ) →L[ℂ] Fin k → ℂ :=
    LinearMap.toContinuousLinearMap (C.subtype ∘ₗ (eC.symm : (Fin d → ℂ) →ₗ[ℂ] C))
  let lam : (Fin k → ℂ) →L[ℂ] Fin d → ℂ :=
    LinearMap.toContinuousLinearMap ((eK : K →ₗ[ℂ] Fin d → ℂ) ∘ₗ K.projectionOnto K' hKK')
  let ℓ : (Fin k → ℂ) →L[ℂ] Fin d → ℂ :=
    LinearMap.toContinuousLinearMap ((eC : C →ₗ[ℂ] Fin d → ℂ) ∘ₗ C.projectionOnto W hWC.symm)
  have hEC : ∀ t, E t ∈ C := fun t => (eC.symm t).2
  have hEinj : Function.Injective E := fun s t hst => by
    have : eC.symm s = eC.symm t := Subtype.ext hst
    exact eC.symm.injective this
  have hPE : ∀ t, P (E t) = 0 := fun t => Submodule.projection_apply_of_mem_right hWC (hEC t)
  have hPP : ∀ x, P (P x) = P x := fun x =>
    Submodule.projection_apply_of_mem_left hWC (Submodule.projection_apply_mem hWC x)
  have hPA : ∀ v, P (A v) = A v := fun v =>
    Submodule.projection_apply_of_mem_left hWC (LinearMap.mem_range_self _ v)
  have hℓA : ∀ v, ℓ (A v) = 0 := fun v => by
    have h0 : C.projectionOnto W hWC.symm (A v) = 0 :=
      Submodule.projectionOnto_apply_of_mem_right hWC.symm (LinearMap.mem_range_self _ v)
    show eC (C.projectionOnto W hWC.symm (A v)) = 0
    rw [h0, map_zero]

  let M : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ := (A : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) + (E.comp lam : _)
  have hMinj : Function.Injective M := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have hv' : A v + E (lam v) = 0 := hv
    have hAv : A v = 0 := by
      refine (Submodule.disjoint_def.mp hWC.disjoint) (A v) (LinearMap.mem_range_self _ v) ?_
      rw [eq_neg_of_add_eq_zero_left hv']
      exact C.neg_mem (hEC _)
    have hlv : lam v = 0 := by
      rw [hAv, zero_add] at hv'
      exact hEinj (hv'.trans (map_zero E).symm)
    have hvK : v ∈ K := hAv
    have : eK (K.projectionOnto K' hKK' v) = 0 := hlv
    rw [Submodule.projectionOnto_apply_of_mem_left hKK' hvK, LinearEquiv.map_eq_zero_iff] at this
    exact congrArg Subtype.val this
  let M' : (Fin k → ℂ) ≃L[ℂ] Fin k → ℂ := (LinearEquiv.ofInjectiveEndo M hMinj).toContinuousLinearEquiv
  let Φ : (Fin k → ℂ) → Fin k → ℂ := fun z => P (f z) + E (lam z)
  have hΦd : HasFDerivAt Φ (M' : (Fin k → ℂ) →L[ℂ] Fin k → ℂ) b := by
    have h := (P.hasFDerivAt.comp b hfd).add (E.comp lam).hasFDerivAt
    have hM : P.comp A + E.comp lam = (M' : (Fin k → ℂ) →L[ℂ] Fin k → ℂ) := by
      ext1 v
      show P (A v) + E (lam v) = A v + E (lam v)
      rw [hPA]
    rw [hM] at h
    exact h
  have hΦc : ContDiffAt ℂ 1 Φ b :=
    (P.contDiff.contDiffAt.comp b hfa.contDiffAt).add (E.comp lam).contDiff.contDiffAt
  let H := hΦc.toOpenPartialHomeomorph Φ hΦd one_ne_zero
  have hHΦ : ∀ z, H z = Φ z := fun z => rfl
  have hbS : b ∈ H.source := hΦc.mem_toOpenPartialHomeomorph_source hΦd one_ne_zero
  have hΦbT : Φ b ∈ H.target := hΦc.image_mem_toOpenPartialHomeomorph_target hΦd one_ne_zero
  have hinv : ContDiffAt ℂ 1 H.symm (Φ b) := hΦc.to_localInverse hΦd one_ne_zero
  have hHb : H.symm (Φ b) = b := by rw [← hHΦ]; exact H.left_inv hbS
  obtain ⟨O, hO, hOo, hbO⟩ := eventually_nhds_iff.mp (hinv.eventually (by simp))
  set c := P (f b) with hc
  let T := (H.target ∩ H.symm ⁻¹' U) ∩ O
  have hTo : IsOpen T := (H.isOpen_inter_preimage_symm hU).inter hOo
  let aff : (Fin d → ℂ) → Fin k → ℂ := fun t => c + E t
  have haff : Continuous aff := continuous_const.add E.continuous
  refine ⟨aff ⁻¹' T, lam b, fun t => H.symm (aff t), ℓ, hTo.preimage haff, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show c + E (lam b) ∈ T
    refine ⟨⟨hΦbT, ?_⟩, hbO⟩
    show H.symm (Φ b) ∈ U
    rw [hHb]; exact hb
  · intro t ht
    exact ((hO _ ht.2).differentiableAt one_ne_zero).comp t
      ((differentiableAt_const c).add E.differentiableAt) |>.differentiableWithinAt
  · intro t ht
    exact ht.1.2
  · intro s hs t ht hst
    have h1 := H.right_inv hs.1.1
    have h2 := H.right_inv ht.1.1
    have : aff s = aff t := by rw [← h1, ← h2]; exact congrArg H hst
    exact hEinj (add_left_cancel this)
  ·
    have hfib : ∀ t ∈ aff ⁻¹' T, P (f (H.symm (aff t))) = c := by
      intro t ht
      have h1 : Φ (H.symm (aff t)) = c + E t := H.right_inv ht.1.1
      have h2 := congrArg P h1
      simp only [Φ, map_add, hPE, add_zero, hPP] at h2
      rw [h2, hc, hPP]
    intro s hs t ht hst
    have hq : C.projectionOnto W hWC.symm (f (H.symm (aff s))) =
        C.projectionOnto W hWC.symm (f (H.symm (aff t))) := eC.injective hst
    rw [← Submodule.projection_add_projection_eq_self hWC (f (H.symm (aff s))),
      ← Submodule.projection_add_projection_eq_self hWC (f (H.symm (aff t)))]
    have hs' := hfib s hs
    have ht' := hfib t ht
    simp only [P, LinearMap.coe_toContinuousLinearMap'] at hs' ht'
    rw [hs', ht', Submodule.projection_apply, Submodule.projection_apply (q := W), hq]
  ·
    have hγy : H.symm (aff (lam b)) = b := hHb
    have hγd : DifferentiableAt ℂ (fun t => H.symm (aff t)) (lam b) :=
      (hinv.differentiableAt one_ne_zero).comp (lam b) ((differentiableAt_const c).add E.differentiableAt)
    have hfd' : HasFDerivAt f A (H.symm (aff (lam b))) := by rw [hγy]; exact hfd
    have h := ℓ.hasFDerivAt.comp (lam b) (hfd'.comp (lam b) hγd.hasFDerivAt)
    refine h.fderiv.trans ?_
    ext1 v
    exact hℓA _

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHolomorphicZeroSetDimH
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric Filter
open scoped ENNReal NNReal

noncomputable section

namespace HolomorphicZeroSetDimH

def partialDeriv {k : ℕ} (h : (Fin k → ℂ) → ℂ) (n : ℕ) (m : Fin n → Fin k) (v : Fin k → ℂ) : ℂ :=
  iteratedFDeriv ℂ n h v (fun j => Pi.basisFun ℂ (Fin k) (m j))

theorem dimH_le_of_local {X : Type*} [EMetricSpace X] [SecondCountableTopology X] {S : Set X}
    {c : ℝ≥0∞} (hS : ∀ x ∈ S, ∃ N ∈ 𝓝 x, dimH (S ∩ N) ≤ c) : dimH S ≤ c := by
  by_contra hlt
  obtain ⟨x, hx, hall⟩ := exists_mem_nhdsWithin_lt_dimH_of_lt_dimH (not_le.1 hlt)
  obtain ⟨N, hN, hc⟩ := hS x hx
  exact (not_le.2 (hall _ (inter_mem_nhdsWithin S hN))) hc

theorem dimH_image_le_of_analyticOnNhd {d : ℕ} {σ : Type*} [Fintype σ] {O : Set (Fin d → ℂ)}
    {g : (Fin d → ℂ) → σ → ℂ} (hg : AnalyticOnNhd ℂ g O) : dimH (g '' O) ≤ 2 * (d : ℝ≥0∞) := by
  refine (dimH_image_le_of_locally_lipschitzOn fun y hy => ?_).trans ?_
  · obtain ⟨K, t, ht, hK⟩ := ((hg y hy).contDiffAt (n := 1)).exists_lipschitzOnWith
    exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩
  · have hfin : Module.finrank ℝ (Fin d → ℂ) = 2 * d := by
      rw [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]
    calc dimH O ≤ dimH (Set.univ : Set (Fin d → ℂ)) := dimH_mono (Set.subset_univ _)
      _ = Module.finrank ℝ (Fin d → ℂ) := Real.dimH_univ_eq_finrank _
      _ = 2 * (d : ℝ≥0∞) := by rw [hfin]; push_cast; ring

theorem dimH_regular_zeros_le {k : ℕ} {U : Set (Fin k → ℂ)} {g : (Fin k → ℂ) → ℂ}
    (hg : AnalyticOnNhd ℂ g U) :
    dimH {v | v ∈ U ∧ g v = 0 ∧ fderiv ℂ g v ≠ 0} ≤ 2 * ((k - 1 : ℕ) : ℝ≥0∞) := by
  refine dimH_le_of_local fun p hp => ?_
  obtain ⟨d, A, O, V, φ, hd, hO, hV, hpV, -, hφ, -, hZ⟩ :=
    AnalyticImplicitChart.proof (Fin k) (Fin 1) (fun _ => g) p Set.univ (fun _ => hg p hp.1)
      (fun _ => hp.2.1) (linearIndependent_unique_iff.2 hp.2.2) univ_mem
  refine ⟨V, hV.mem_nhds hpV, ?_⟩
  have hk : k - 1 = d := by simp only [Fintype.card_fin] at hd; omega
  rw [hk]
  refine (dimH_mono ?_).trans (dimH_image_le_of_analyticOnNhd hφ)
  rw [← hZ]
  rintro z ⟨hz, hzV⟩
  exact ⟨hzV, fun _ => hz.2.1⟩

theorem exists_partialDeriv {k : ℕ} {U : Set (Fin k → ℂ)} {h : (Fin k → ℂ) → ℂ} (hU : IsOpen U)
    (hh : AnalyticOnNhd ℂ h U) (hW : ∀ W ⊆ U, IsOpen W → W.Nonempty → ∃ w ∈ W, h w ≠ 0)
    {v : Fin k → ℂ} (hv : v ∈ U) (h0 : h v = 0) :
    ∃ n m, partialDeriv h n m v = 0 ∧ fderiv ℂ (partialDeriv h n m) v ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hdiff : ∀ n, DifferentiableAt ℂ (iteratedFDeriv ℂ n h) v := fun n =>
    ((hh.iteratedFDeriv n) v hv).differentiableAt
  have hall : ∀ n m, partialDeriv h n m v = 0 := by
    intro n
    induction n with
    | zero => intro m; simp [partialDeriv, iteratedFDeriv_zero_apply, h0]
    | succ n ih =>
      intro m
      have h1 := hcon n (Fin.tail m) (ih _)
      have h2 := congrArg (fun L => L (Pi.basisFun ℂ (Fin k) (m 0))) h1
      simp only [zero_apply] at h2
      unfold partialDeriv at h2 ⊢
      rw [fderiv_continuousMultilinear_apply_const_apply (hdiff n)] at h2
      rw [iteratedFDeriv_succ_apply_left]
      exact h2
  have hzero : ∀ n, iteratedFDeriv ℂ n h v = 0 := fun n =>
    ContinuousMultilinearMap.toMultilinearMap_injective
      (Module.Basis.ext_multilinear (fun _ => Pi.basisFun ℂ (Fin k)) fun m => by
        simpa [partialDeriv] using hall n m)
  obtain ⟨p, r, hp⟩ := hh v hv
  have hev : ∀ᶠ x in 𝓝 v, h x = 0 := by
    have h1 : Tendsto (fun x => x - v) (𝓝 v) (𝓝 0) := by
      simpa using (continuous_sub_right v).tendsto v
    filter_upwards [h1.eventually (Metric.eball_mem_nhds 0 hp.r_pos)] with x hx
    have hs := hp.hasSum_iteratedFDeriv hx
    simp only [hzero, zero_apply, smul_zero, add_sub_cancel] at hs
    exact hs.unique hasSum_zero
  obtain ⟨W, hWsub, hWo, hvW⟩ := _root_.mem_nhds_iff.1 (hev.and (hU.mem_nhds hv))
  obtain ⟨w, hw, hw0⟩ := hW W (fun x hx => (hWsub hx).2) hWo ⟨v, hvW⟩
  exact hw0 (hWsub hw).1

theorem proof : HolomorphicZeroSetDimH.Statement := by
  intro k U h hU hh hW
  have ha : AnalyticOnNhd ℂ h U :=
    analyticOnNhd_pi_iff.1 (ProperHolomorphicSurjective.analyticOnNhd_of_differentiableOn (m := 1)
      (f := fun v _ => h v) hU (differentiableOn_pi.2 fun _ => hh)) 0
  have hpd : ∀ n m, AnalyticOnNhd ℂ (partialDeriv h n m) U := fun n m x hx =>
    ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => Fin k → ℂ) ℂ
      (fun j => Pi.basisFun ℂ (Fin k) (m j))).analyticAt _).comp (ha.iteratedFDeriv n x hx)
  calc dimH {v | v ∈ U ∧ h v = 0}
      ≤ dimH (⋃ nm : (Σ n, Fin n → Fin k),
          {v | v ∈ U ∧ partialDeriv h nm.1 nm.2 v = 0 ∧ fderiv ℂ (partialDeriv h nm.1 nm.2) v ≠ 0}) := by
        refine dimH_mono fun v hv => ?_
        obtain ⟨n, m, h1, h2⟩ := exists_partialDeriv hU ha hW hv.1 hv.2
        exact Set.mem_iUnion.2 ⟨⟨n, m⟩, hv.1, h1, h2⟩
    _ ≤ 2 * ((k - 1 : ℕ) : ℝ≥0∞) := by
        rw [dimH_iUnion]
        exact iSup_le fun nm => dimH_regular_zeros_le (hpd nm.1 nm.2)

end HolomorphicZeroSetDimH

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIrreducibleGermPointsOffDiscriminant
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric Filter Set

theorem isRegularPointOf_ball {d : ℕ} (c : Fin d → ℂ) (ε : ℝ) :
    ∀ y ∈ ball c ε, IsRegularPointOf (ball c ε) y := fun y hy =>
  ⟨hy, d, ContinuousLinearMap.id ℂ _, ball c ε, ball c ε, id, isOpen_ball, isOpen_ball, hy,
    analyticOnNhd_id, fun _ _ => rfl, by simp⟩

theorem IrreducibleGermPointsOffDiscriminant.proof (hPF : IrreducibleGermPrimitiveForm.Statement)
    (hSh : PrimitiveFormSheetedOffDiscriminant.Statement) (hNear : PrimitiveFormSheetedPointsNear.Statement)
    (hConn : ManifoldZerosComplementConnected.Statement) :
    IrreducibleGermPointsOffDiscriminant.Statement := by
  intro σ _ X x d A hX hirr hiso hinj
  obtain ⟨ℓ, N, a, δ, q, ha, hδ, hq, hδ0, hp, hsep, hqz⟩ := hPF σ X x d A hX hirr hiso hinj
  obtain ⟨M, hM, hMsh⟩ := hSh σ X x d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδ0 hp hsep hqz
  have hnear := hNear σ X x d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδ0 hp hsep hqz
  refine ⟨δ, hδ, hδ0, fun W hW => ?_⟩
  obtain ⟨W₀, hW₀, hiso'⟩ := hiso
  obtain ⟨Nn, k, f, hNo, hxN, hf, hXN⟩ := hX
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (inter_mem hW hM) (inter_mem hW₀ (hNo.mem_nhds hxN)))
  have hr2 : 0 < r / 2 := half_pos hr
  have hcb : closedBall x (r / 2) ⊆ (W ∩ M) ∩ (W₀ ∩ Nn) := (closedBall_subset_ball (half_lt_self hr)).trans hrsub

  set K : Set (σ → ℂ) := closedBall x (r / 2) ∩ ⋂ i, (closedBall x (r / 2) ∩ f i ⁻¹' {0}) with hK
  have hKc : IsCompact K := by
    refine (isCompact_closedBall x (r / 2)).of_isClosed_subset ?_ inter_subset_left
    refine isClosed_closedBall.inter (isClosed_iInter fun i => ?_)
    exact ((hf i).continuousOn.mono fun z hz => (hcb hz).2.2).preimage_isClosed_of_isClosed
      isClosed_closedBall isClosed_singleton
  have hKmem : ∀ z, z ∈ K ↔ z ∈ closedBall x (r / 2) ∧ z ∈ X := by
    intro z
    simp only [hK, mem_inter_iff, mem_iInter, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨hz, h0⟩
      have : z ∈ {z | z ∈ Nn ∧ ∀ i, f i z = 0} := ⟨(hcb hz).2.2, fun i => (h0 i).2⟩
      rw [← hXN] at this
      exact ⟨hz, this.1⟩
    · rintro ⟨hz, hzX⟩
      have : z ∈ X ∩ Nn := ⟨hzX, (hcb hz).2.2⟩
      rw [hXN] at this
      exact ⟨hz, fun i => ⟨hz, this.2 i⟩⟩
  have hSc : IsCompact (K ∩ sphere x (r / 2)) := hKc.inter_right isClosed_sphere
  have hAS : A x ∉ A '' (K ∩ sphere x (r / 2)) := by
    rintro ⟨z, ⟨hzK, hzs⟩, hAz⟩
    have hzx : z = x := hiso' z ⟨((hKmem z).mp hzK).2, (hcb ((hKmem z).mp hzK).1).2.1⟩ hAz
    rw [hzx, mem_sphere, dist_self] at hzs
    exact hr2.ne hzs
  obtain ⟨ε₁, hε₁, hε₁S⟩ := Metric.isOpen_iff.mp (hSc.image A.continuous).isClosed.isOpen_compl (A x) hAS
  obtain ⟨ε₂, hε₂, hε₂a⟩ := hδ.exists_ball_analyticOnNhd
  set D := ball (A x) (min ε₁ ε₂) with hD
  have hε : 0 < min ε₁ ε₂ := lt_min hε₁ hε₂
  have hDa : AnalyticOnNhd ℂ δ D := hε₂a.mono (ball_subset_ball (min_le_right _ _))

  set T := D \ {y | δ y = 0} with hT
  have hTo : IsOpen T := hDa.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton
  have hTc : IsPreconnected T := by
    refine hConn (Fin d) D δ (convex_ball _ _).isPreconnected (isRegularPointOf_ball _ _) hDa ?_
    obtain ⟨y, hy0, hyD⟩ := ((Filter.not_eventually.mp hδ0).and_eventually (ball_mem_nhds _ hε)).exists
    exact ⟨y, hyD, hy0⟩

  set u : Set (Fin d → ℂ) := T ∩ A '' (X ∩ ball x (r / 2)) with hu
  have huo : IsOpen u := by
    refine isOpen_iff_mem_nhds.mpr ?_
    rintro y ⟨hyT, z, ⟨hzX, hzb⟩, rfl⟩
    obtain ⟨O, V, g, hO, hV, hzV, hg, hAg, hXV⟩ := hMsh z ⟨hzX, (hcb (ball_subset_closedBall hzb)).1.2⟩ hyT.2
    obtain ⟨t₀, ht₀, hgt₀⟩ : z ∈ g '' O := hXV ▸ ⟨hzX, hzV⟩
    have hAz : A z = t₀ := by rw [← hgt₀]; exact hAg t₀ ht₀
    rw [hAz] at hyT ⊢
    have hpre : g ⁻¹' (V ∩ ball x (r / 2)) ∈ 𝓝 t₀ :=
      (hg t₀ ht₀).continuousAt.preimage_mem_nhds ((hV.inter isOpen_ball).mem_nhds (hgt₀ ▸ ⟨hzV, hzb⟩))
    filter_upwards [hTo.mem_nhds hyT, hO.mem_nhds ht₀, hpre] with t ht htO htg
    have hgX : g t ∈ X ∩ V := hXV ▸ ⟨t, htO, rfl⟩
    exact ⟨ht, g t, ⟨hgX.1, htg.2⟩, hAg t htO⟩
  have hune : (T ∩ u).Nonempty := by
    have hU : ball x (r / 2) ∩ A ⁻¹' D ∈ 𝓝 x :=
      inter_mem (ball_mem_nhds x hr2) (A.continuous.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hε))
    obtain ⟨z, ⟨hzX, hzb, hzD⟩, hδz, -⟩ := hnear _ hU
    exact ⟨A z, ⟨hzD, hδz⟩, ⟨hzD, hδz⟩, z, ⟨hzX, hzb⟩, rfl⟩
  have hucl : closure u ∩ T ⊆ u := by
    rintro y ⟨hycl, hyT⟩
    have hsubK : u ⊆ A '' K := by
      rintro _ ⟨-, z, ⟨hzX, hzb⟩, rfl⟩
      exact ⟨z, (hKmem z).mpr ⟨ball_subset_closedBall hzb, hzX⟩, rfl⟩
    obtain ⟨z, hzK, rfl⟩ := (hKc.image A.continuous).isClosed.closure_subset_iff.mpr hsubK hycl
    obtain ⟨hzcb, hzX⟩ := (hKmem z).mp hzK
    have hzb : z ∈ ball x (r / 2) := by
      refine mem_ball.mpr (lt_of_le_of_ne (mem_closedBall.mp hzcb) fun hzs => ?_)
      exact hε₁S (ball_subset_ball (min_le_left _ _) hyT.1) ⟨z, ⟨hzK, mem_sphere.mpr hzs⟩, rfl⟩
    exact ⟨hyT, z, ⟨hzX, hzb⟩, rfl⟩
  have hTu : T ⊆ u := hTc.subset_of_closure_inter_subset huo hune hucl
  filter_upwards [ball_mem_nhds (A x) hε] with y hy hδy
  obtain ⟨-, z, ⟨hzX, hzb⟩, hzy⟩ := hTu ⟨hy, hδy⟩
  exact ⟨z, ⟨hzX, (hcb (ball_subset_closedBall hzb)).1.1⟩, hzy⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PJacobianPrimeDerivations
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

theorem JacobianPrimeDerivations.proof (hDetect : PolyDerivationsDetectSquare.Statement)
    (hBasis : CotangentBasisInPrime.Statement) (hMinor : DerivationMinorOfDetection.Statement)
    (hClear : LocalGeneratorsClearDenominators.Statement) : JacobianPrimeDerivations.Statement := by
  intro k _ n p hp
  obtain ⟨h, f, hfp, hspan, hind⟩ := hBasis (MvPolynomial (Fin n) k) p
  obtain ⟨D, hD⟩ := hMinor (MvPolynomial (Fin n) k) p h f hfp hind
    (fun g hg hDg => hDetect k n p g hg hDg)
  obtain ⟨s, hs, hsp⟩ := hClear (MvPolynomial (Fin n) k) p h f hfp hspan
  exact ⟨h, f, D, s, hfp, hs, hsp, hD⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLogIntegrable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Set Filter ComplexSets

open scoped ENNReal

noncomputable section

namespace LogIntegrableProof

variable {n : ℕ}

theorem lintegral_lt_top (hS : VarSlabMeasure.Statement) (hF : MassFinite.Statement) {d : ℕ}
    {J : Ideal (MvPolynomial (Fin n) ℂ)} (u : Fin n → ℂ) (R : ℝ) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) (hu : linForm u ∉ J) :
    ∫⁻ z in zeroSetEuc J ∩ {z | ‖z‖ ≤ R}, ‖Real.log ‖∑ j, u j * z j‖‖ₑ
      ∂(μH[((2 * d : ℕ) : ℝ)]) < ⊤ := by
  obtain ⟨C, α, hα, hC⟩ := hS n d J u R hJ hdim hu
  set S := zeroSetEuc J ∩ {z : EuclideanSpace ℂ (Fin n) | ‖z‖ ≤ R} with hSdef
  set μ := (μH[((2 * d : ℕ) : ℝ)]).restrict S
  have hsub : S ⊆ zeroSetEuc J ∩ Metric.ball 0 (R + 1) := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    rw [mem_ball_zero_iff]
    linarith [(show ‖z‖ ≤ R from hz.2)]
  have hSfin : μH[((2 * d : ℕ) : ℝ)] S < ⊤ :=
    (measure_mono hsub).trans_lt (hF n d J hJ hdim (R + 1))
  have hcont : Continuous fun z : EuclideanSpace ℂ (Fin n) => ∑ j, u j * z j := by fun_prop
  set F : EuclideanSpace ℂ (Fin n) → ℝ := fun z => Real.log ‖∑ j, u j * z j‖
  have hFm : Measurable F := Real.measurable_log.comp hcont.norm.measurable
  set G : EuclideanSpace ℂ (Fin n) → ℝ := fun z => max (-F z) 0
  have hGm : Measurable G := hFm.neg.max measurable_const
  set M : ℝ := max (∑ j, ‖u j‖ * R) 0

  have hFle : ∀ z ∈ S, F z ≤ M := by
    intro z hz
    refine (Real.log_le_self (norm_nonneg _)).trans ((norm_sum_le _ _).trans ?_)
    refine le_trans ?_ (le_max_left _ _)
    refine Finset.sum_le_sum fun j _ => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((PiLp.norm_apply_le z j).trans hz.2) (norm_nonneg _)

  have hG : ∫⁻ z, ENNReal.ofReal (G z) ∂μ < ⊤ := by
    rw [lintegral_eq_lintegral_meas_le (f := G) μ (Eventually.of_forall fun z => le_max_right _ _)
      hGm.aemeasurable]
    have hint : IntegrableOn (fun t => C * Real.exp (-α * t)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 hα).const_mul C
    refine lt_of_le_of_lt (lintegral_mono_ae ?_) hint.lintegral_lt_top
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t (ht : 0 < t) => ?_)
    rw [Measure.restrict_apply (measurableSet_le measurable_const hGm)]
    refine (measure_mono ?_).trans ((hC (Real.exp (-t)) (Real.exp_pos _)
      (Real.exp_le_one_iff.mpr (by linarith))).trans_eq ?_)
    · rintro z ⟨hz, hzS⟩
      refine ⟨hzS, ?_⟩
      have htF : F z ≤ -t := by
        rcases le_max_iff.mp (show t ≤ G z from hz) with h1 | h1
        · linarith
        · linarith
      change ‖∑ j, u j * z j‖ ≤ Real.exp (-t)
      rcases (norm_nonneg (∑ j, u j * z j)).eq_or_lt with h0 | h0
      · rw [← h0]; positivity
      · exact (Real.log_le_iff_le_exp h0).mp htF
    · rw [← Real.exp_mul]; ring_nf
  have hle : ∀ z ∈ S, ‖F z‖ₑ ≤ ENNReal.ofReal M + ENNReal.ofReal (G z) := by
    intro z hz
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := hFle z hz
    rcases le_or_gt 0 (F z) with h2 | h2
    · rw [abs_of_nonneg h2]; have := le_max_right (-F z) 0; linarith
    · rw [abs_of_neg h2]; have := le_max_left (-F z) 0; have := le_max_right (∑ j, ‖u j‖ * R) 0
      linarith
  refine lt_of_le_of_lt (setLIntegral_mono (g := fun z => ENNReal.ofReal M + ENNReal.ofReal (G z))
    (measurable_const.add hGm.ennreal_ofReal) hle) ?_
  rw [lintegral_add_left measurable_const, lintegral_const, Measure.restrict_apply_univ]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hSfin, hG⟩

end LogIntegrableProof

open LogIntegrableProof in

theorem LogIntegrable.proof (hM : SheetSumMeasurable.Statement) (hD : ChartMassCompare.Statement)
    (hS : VarSlabMeasure.Statement) (hF : MassFinite.Statement) : LogIntegrable.Statement := by
  intro n d J A u φ R hJ hdim hA hu hφ
  have hcont : Continuous fun x : Fin n → ℂ => linEval u x := by unfold linEval; fun_prop
  have hwm : Measurable fun x : Fin n → ℂ => Real.log ‖linEval u x‖ :=
    Real.measurable_log.comp (continuous_norm.comp hcont).measurable
  refine ⟨(hM n d J A _ φ hJ hdim hA (hwm.indicator measurableSet_closedBall) hφ).2.aestronglyMeasurable,
    ?_⟩
  obtain ⟨K, hK, hDK⟩ := hD n d J A φ R hJ hdim hA hφ

  obtain ⟨L, hL0, hL⟩ : ∃ L : ℝ, 0 ≤ L ∧
      ∀ z : EuclideanSpace ℂ (Fin n), ‖z‖ ≤ L * ‖WithLp.ofLp z‖ :=
    ⟨(n : ℝ) ^ (2⁻¹ : ℝ), by positivity, fun z => by
      simpa [dist_zero_right] using
        (PiLp.lipschitzWith_toLp 2 (fun _ : Fin n => ℂ)).dist_le_mul (WithLp.ofLp z) 0⟩
  unfold HasFiniteIntegral
  refine (hDK _ hwm).trans_lt (ENNReal.mul_lt_top hK ?_)
  refine lt_of_le_of_lt (lintegral_mono_set ?_) (lintegral_lt_top hS hF u (L * R) hJ hdim hu)
  rintro z ⟨hz, hzB⟩
  refine ⟨hz, ?_⟩
  have : ‖WithLp.ofLp z‖ ≤ R := mem_closedBall_zero_iff.mp hzB
  exact (hL z).trans (mul_le_mul_of_nonneg_left this hL0)

end

end GroundTheory.Heights₂.Heights
end

