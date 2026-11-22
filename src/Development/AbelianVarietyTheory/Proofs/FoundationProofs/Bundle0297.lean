import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0082
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0289
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0092
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0088
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SinhcAdjointApplyMatrixUpperRightBlockElementP
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0086
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0093
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0085
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0254
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0280
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardPairLatticeLocallyOrthonormalBasis
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHCModuleOfGradedDenseGK
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.GradedKFin

variable {p q : ℕ}

theorem kset_one (T : GrpData p q) : (1 : T.G) ∈ T.Kset := by
  intro a b hab
  have : a ≠ b := by
    rintro rfl
    cases a <;> simp [sameBlock] at hab
  simp [Matrix.one_apply, this]

theorem kset_mul (T : GrpData p q) {g h : T.G} (hg : g ∈ T.Kset) (hh : h ∈ T.Kset) :
    g * h ∈ T.Kset := by
  intro a b hab
  rw [map_mul, Units.val_mul, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hac : sameBlock a c
  · have hcb : ¬ sameBlock c b := by
      cases a <;> cases b <;> cases c <;> simp_all [sameBlock]
    rw [hh c b hcb, mul_zero]
  · rw [hg a c hac, zero_mul]

theorem map_stable (hpq : 1 ≤ p + q) (T : GrpData p q) (σ : URep T) (M : GKMod p q)
    (j : M.V →ₗ[ℂ] σ.H)
    (hder : ∀ Y ∈ upq p q, ∀ x,
      HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (M.act Y x)) 0)
    (W : Submodule ℂ M.V) [FiniteDimensional ℂ W] (hW : KStable M.act W)
    {g : T.G} (hg : g ∈ T.Kset) : ∀ x ∈ W.map j, σ.π g x ∈ W.map j := by
  have hcl := GlobalTheory.CoverKGen.kset_gen p q hpq T g hg
  suffices h : (∀ x ∈ W.map j, σ.π g x ∈ W.map j) ∧ (∀ x ∈ W.map j, σ.π g⁻¹ x ∈ W.map j) from h.1
  clear hg
  induction hcl using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨Y, ⟨hY, hKC⟩, rfl⟩ := hg
    have hf := GlobalTheory.RealPar.flow_mem_map j (M.act Y) W (hW Y hKC) (fun t => σ.π (T.expt (t • Y)))
      (by simp [T.expt_zero]) (fun s t => by simp only [T.expt_add Y hY, map_mul]) (hder Y hY)
    have hinv : (T.expt Y)⁻¹ = T.expt ((-1 : ℝ) • Y) := by
      have := T.expt_add Y hY 1 (-1)
      rw [add_neg_cancel, zero_smul, T.expt_zero, one_smul] at this
      exact (eq_inv_of_mul_eq_one_right this.symm).symm
    refine ⟨?_, ?_⟩
    · have := hf 1
      simpa only [one_smul] using this
    · rw [hinv]; exact hf (-1)
  | one => simp
  | mul a b _ _ ha hb =>
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [map_mul]; exact ha.1 _ (hb.1 x hx)
    · rw [mul_inv_rev, map_mul]; exact hb.2 _ (ha.2 x hx)
  | inv a _ ha => exact ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

theorem isHCMod_of_graded : ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (σ : URep T) (M : GKMod p q) (j : M.V →ₗ[ℂ] σ.H), Function.Injective j → Dense (Set.range j) → (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (M.act Y x)) 0) → ∀ (N : ℕ → Submodule ℂ M.V) (k : T.G) (lam : ℕ → ℂ), (∀ m, FiniteDimensional ℂ (N m)) → (⨆ m, N m) = ⊤ → k ∈ T.Kset → Function.Injective lam → (∀ m, ∀ x ∈ N m, σ.π k (j x) = lam m • j x) → IsHCMod σ M j := by
  intro p q hpq T σ M j hj hd hder N k lam hfin htop hk hlam heig
  refine ⟨hj, fun x => ⟨?_, fun hx => ?_⟩, hder⟩
  · rintro ⟨v, rfl⟩
    obtain ⟨W, hWf, hv, hW⟩ := M.kfin v
    have hle : Submodule.span ℂ (Set.range fun g : T.Kset => σ.π g (j v)) ≤ W.map j := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact map_stable hpq T σ M j hder W hW g.2 _ ⟨v, hv, rfl⟩
    exact Submodule.finiteDimensional_of_le hle
  · have hsup : (⨆ m, (N m).map j) = LinearMap.range j := by
      rw [← Submodule.map_iSup, htop, Submodule.map_top]
    have hle := GlobalTheory.HolDS.finiteDimensional_stable_le_iSup_eigen σ.H (σ.π k) (σ.isom k)
      (fun m => (N m).map j) lam hlam (fun m => inferInstance)
      (by rintro m _ ⟨y, hy, rfl⟩; exact heig m y hy)
      (by rw [hsup]; exact hd)
      (Submodule.span ℂ (Set.range fun g : T.Kset => σ.π g x)) hx (by
        intro w hw
        induction hw using Submodule.span_induction with
        | mem w hw =>
          obtain ⟨g, rfl⟩ := hw
          refine Submodule.subset_span ⟨⟨k * g, kset_mul T hk g.2⟩, ?_⟩
          simp only [map_mul]
          rfl
        | zero => simp
        | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
        | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha)
    rw [hsup] at hle
    exact hle (Submodule.subset_span ⟨⟨1, kset_one T⟩, by simp⟩)

end GlobalTheory.GradedKFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsInvInvariantOfRight
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower Matrix MeasureTheory

noncomputable section
namespace GlobalTheory.CartanInt

variable {p q : ℕ}

theorem isInvInvariant_of_right {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : μ.IsInvInvariant := by
  constructor
  let c : ENNReal := Measure.haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  have h1 : Measure.map Inv.inv (Measure.map Inv.inv μ) = c ^ 2 • μ := by
    rw [← Measure.inv_def μ, hc, Measure.map_smul, ← Measure.inv_def μ, hc, smul_smul, pow_two]
  have μeq : μ = c ^ 2 • μ := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at h1
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id] using h1
  have K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have h2 : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [μeq]
    simp
  have h3 : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
          K.isCompact.measure_lt_top.ne).1 h2
  have h4 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective h3
  rw [hc, h4, one_smul]

theorem isUnit_mat (g : UpqT p q) : IsUnit (UpqT.mat g) := Units.isUnit _

theorem isCompact_Kc : IsCompact (Kc p q) := by
  have h : Kc p q = ⋂ a, ⋂ b, ⋂ (_ : ¬ sameBlock a b), {x : UpqT p q | UpqT.mat x a b = 0} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact Iff.rfl
  have hcl : IsClosed (Kc p q) := by
    rw [h]
    refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ => ?_
    exact isClosed_eq (GlobalTheory.UpqTopology.continuous_mat.matrix_elem a b) continuous_const
  have hc : IsCompact (Set.univ.pi fun _ : Ix p q => Set.univ.pi fun _ : Ix p q => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine (GlobalTheory.UpqTopology.isClosedEmbedding_mat.isCompact_preimage (K := _) hc).of_isClosed_subset hcl ?_
  intro x hx a _ b _
  simpa using entry_norm_bound_of_unitary (Matrix.mem_unitaryGroup_iff'.2 (star_mul_of_mem_Kc hx)) a b

theorem exists_action (L : Mat p q → (Fin p → Fin q → ℂ)) (hL : ContinuousOn L {g | IsUnit g})
    (hLk : ∀ (k : Mat p q) (B : Fin p → Fin q → ℂ), kᴴ * k = 1 → L (k * NormedSpace.exp (pY B)) = B)
    (g : UpqT p q) : ∃ ψ : (Fin p → Fin q → ℂ) → (Fin p → Fin q → ℂ), Continuous ψ ∧ Function.Bijective ψ ∧
      ∀ B, ∃ κ ∈ Kc p q, eP B * g = κ * eP (ψ B) := by
  obtain ⟨i1, -⟩ := GlobalTheory.UpqTopology.upq_lcsc p q
  let ψ : UpqT p q → (Fin p → Fin q → ℂ) → (Fin p → Fin q → ℂ) := fun g B => L (UpqT.mat (eP B * g))
  have key : ∀ (x κ : UpqT p q) (B' : Fin p → Fin q → ℂ), κ ∈ Kc p q → x = κ * eP B' →
      L (UpqT.mat x) = B' := by
    intro x κ B' hκ hx
    rw [hx, mat_mul, mat_eP]
    exact hLk _ _ (star_mul_of_mem_Kc hκ)
  have dec : ∀ g B, ∃ κ ∈ Kc p q, eP B * g = κ * eP (ψ g B) := by
    intro g B
    obtain ⟨κ, hκ, B', h⟩ := exists_cartan (eP B * g)
    have : ψ g B = B' := key _ κ B' hκ h
    exact ⟨κ, hκ, by rw [this]; exact h⟩
  have inv : ∀ g B, ψ g⁻¹ (ψ g B) = B := by
    intro g B
    obtain ⟨κ, hκ, h⟩ := dec g B
    refine key _ κ⁻¹ B ((Ksg p q).inv_mem hκ) ?_
    rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← h, mul_inv_cancel_right]
  refine ⟨ψ g, ?_, ?_, dec g⟩
  · exact hL.comp_continuous
      (GlobalTheory.UpqTopology.continuous_mat.comp (continuous_eP.mul continuous_const)) fun B => isUnit_mat _
  · refine Function.bijective_iff_has_inverse.2 ⟨ψ g⁻¹, inv g, fun B => ?_⟩
    have := inv g⁻¹ B
    rwa [inv_inv] at this

theorem haar_polar : ∀ (p q : ℕ) (m : Measure (UpqT p q)), m.IsHaarMeasure → ∃ (c : ℝ) (mK : Measure (UpqT p q)), 0 < c ∧ IsProbabilityMeasure mK ∧ mK (Kc p q)ᶜ = 0 ∧ (∀ k ∈ Kc p q, Measure.map (fun x => k * x) mK = mK) ∧ ∀ f : UpqT p q → ENNReal, Measurable f → ∫⁻ g, f g ∂m = ENNReal.ofReal c * ∫⁻ B : Fin p → Fin q → ℂ, (∫⁻ k, f (k * eP B) ∂mK) * ENNReal.ofReal (polJ (pY B)) := by
  intro p q m hm
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc p q
  haveI := GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure p q m hm
  haveI := isInvInvariant_of_right m
  obtain ⟨mK, hprob, hK0, hleft, hright⟩ :=
    GlobalTheory.exists_biinvariant_probability_on_compact_subgroup (UpqT p q) (Ksg p q) isCompact_Kc
  obtain ⟨L, hLc, hL⟩ := GlobalTheory.PolarLogCont.exists_continuousOn_polar_log p q
  have hpos : ∀ B : Fin p → Fin q → ℂ, 0 < polJ (pY B) := fun B => one_pos.trans_le (one_le_polJ _)
  have hJc : Continuous fun B : Fin p → Fin q → ℂ => polJ (pY B) := (continuous_polJ p q).comp continuous_pY
  have hJm : Measurable fun B : Fin p → Fin q → ℂ => ENNReal.ofReal (polJ (pY B)) :=
    ENNReal.measurable_ofReal.comp hJc.measurable
  have hdet : ∀ B : Fin p → Fin q → ℂ, LinearMap.det (sP (pY B)) = polJ (pY B) :=
    fun B => det_sinhc_eq_polarJacobian p q _ (SinhcPres.sAd_pY p q B)
  have hem : Measurable (eP : (Fin p → Fin q → ℂ) → UpqT p q) := continuous_eP.measurable
  haveI : IsLocallyFiniteMeasure
      ((volume : Measure (Fin p → Fin q → ℂ)).withDensity fun B => ENNReal.ofReal (polJ (pY B))) :=
    IsLocallyFiniteMeasure.withDensity_ofReal hJc
  obtain ⟨c, hc, hf⟩ := GlobalTheory.Twist.lintegral_haar_eq_transversal (UpqT p q) (Fin p → Fin q → ℂ) m mK
    (volume.withDensity fun B => ENNReal.ofReal (polJ (pY B))) (Kc p q) eP hem hK0 hright
    (by
      intro h0
      rw [withDensity_eq_zero_iff hJm.aemeasurable] at h0
      haveI : (volume : Measure (Fin q → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
      haveI : (volume : Measure (Fin p → Fin q → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
      haveI : (ae (volume : Measure (Fin p → Fin q → ℂ))).NeBot :=
        ae_neBot.2 fun h => (isOpen_univ.measure_ne_zero (volume : Measure (Fin p → Fin q → ℂ))
          Set.univ_nonempty) (by rw [h]; rfl)
      obtain ⟨B, hB⟩ := h0.exists
      exact absurd hB (by simpa using hpos B))
    (by
      intro C hC
      have hcomp : IsCompact (L '' (UpqT.mat '' C)) :=
        (hC.image GlobalTheory.UpqTopology.continuous_mat).image_of_continuousOn (hLc.mono (by
          rintro _ ⟨x, -, rfl⟩; exact isUnit_mat x))
      refine lt_of_le_of_lt (measure_mono ?_) hcomp.measure_lt_top
      rintro B ⟨k, hk, hB⟩
      refine ⟨_, ⟨_, hB, rfl⟩, ?_⟩
      rw [mat_mul, mat_eP]
      exact hL _ B (star_mul_of_mem_Kc hk))
    (by
      intro g
      obtain ⟨ψ, hψc, hψb, hψ⟩ := exists_action L hLc hL g
      refine ⟨ψ, hψc.measurable, GlobalTheory.map_withDensity_of_jacobian p q _ ψ hJc hψc hψb ?_, hψ⟩
      have := jacobian_action_p p q (UpqT.mat g) ψ hψc (fun B => by
          obtain ⟨κ, hκ, h⟩ := hψ B
          obtain ⟨U, hU, V, hV, hm⟩ := (mem_Kc_iff κ).1 hκ
          refine ⟨U, hU, V, hV, ?_⟩
          have := congrArg UpqT.mat h
          rwa [mat_mul, mat_mul, mat_eP, mat_eP, hm] at this)
        (fun B => by rw [hdet]; exact hpos B) (SinhcPres.sAd_pY p q)
        (fun B => hasStrictFDerivAt_exp_two_pY p q B (hasDerivAt_exp_two_add_smul p q (pY B)))
      simpa only [hdet] using this)
  refine ⟨c, mK, hc, hprob, hK0, hleft, fun f hfm => ?_⟩
  rw [hf f hfm, lintegral_withDensity_eq_lintegral_mul _ hJm]
  · congr 1
    refine lintegral_congr fun B => ?_
    simp only [Pi.mul_apply, mul_comm]
  · exact Measurable.lintegral_prod_right' (f := fun z : (Fin p → Fin q → ℂ) × UpqT p q => f (z.2 * eP z.1))
      (hfm.comp (measurable_snd.mul (hem.comp measurable_fst)))

end GlobalTheory.CartanInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelLatticesFormSelfDualTriples
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaTriple

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem theta_cocycle_eq_exp_hermitian (T : Tor D) (x y : VC D N N') :
    bc D T x y = Complex.exp (-(2 * Real.pi * Complex.I) * ((Hf D T (w0 D • x) y).im : ℂ)) := by
  have h : Hf D T (w0 D • x) y = w0 D * Hf D T x y := by
    rw [GlobalTheory.ThetaLine.Hf_eq, GlobalTheory.ThetaLine.sq_smul_left, GlobalTheory.ThetaLine.Hf_eq, mul_div_assoc]
  have h1 : (w0 D).re = 1 / 2 := by simp [w0]
  have h2 : (w0 D).im = Real.sqrt D.host.d / 2 := by simp [w0]
  rw [bc, h, Complex.mul_im, h1, h2]
  congr 1
  push_cast
  ring

theorem nice_of_klat (hc : Crv D cc δ) {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A) :
    Nice D (tor0 D cc δ) A := by
  obtain ⟨-, h0, h1, h2, -, -, -⟩ :=
    GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hc N N' A hA
  refine ⟨h0, fun x hx y hy => ?_, fun x hx => h2 x fun y hy => ?_⟩
  · obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
    have hw := GlobalTheory.ThetaInter.klat_smul_mem hA a hx
    rw [ha] at hw
    obtain ⟨m, hm⟩ := h1 _ hw y hy
    rw [theta_cocycle_eq_exp_hermitian, hm, Complex.exp_eq_one_iff]
    exact ⟨-m, by push_cast; ring⟩
  · have h := hx y hy
    rw [bc_comm, mul_eq_right₀ (bc_ne_zero _ _ _ _), Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    refine ⟨-n, ?_⟩
    have h3 : (2 * (Real.pi : ℂ) * Complex.I) * ((Hf D (tor0 D cc δ) x y).im : ℂ) =
        (2 * (Real.pi : ℂ) * Complex.I) * ((-n : ℤ) : ℂ) := by
      push_cast
      linear_combination -hn
    exact_mod_cast mul_left_cancel₀ Complex.two_pi_I_ne_zero h3

theorem index_ne_zero (hc : Crv D cc δ) {A₁ A₂ : AddSubgroup (VC D N N')} (h₁ : KLat D (tor0 D cc δ) A₁)
    (h₂ : KLat D (tor0 D cc δ) A₂) : (A₁.addSubgroupOf A₂).index ≠ 0 := by
  haveI := GlobalTheory.ThetaInter.klat_finite (GlobalTheory.InducedType.induced_type D).1.1 hc.1.1 h₁ h₂
    (GlobalTheory.ThetaInter.klat_facts hc h₂).1
  exact AddSubgroup.index_ne_zero_of_finite

theorem iop_self {T : Tor D} {A : AddSubgroup (VC D N N')} (hA : Nice D T A) {e : VC D N N' → ℂ}
    (he : e ∈ ThSp D T A) : Iop D T A A e = e := by
  rw [hA.Iop_eq]
  funext z
  have hi : (A.addSubgroupOf A).index = 1 := by simp
  have hc : Nat.card (A ⧸ A.addSubgroupOf A) = 1 := hi
  obtain ⟨hs, ⟨q₀⟩⟩ := Nat.card_eq_one_iff_unique.1 hc
  rw [finsum_eq_single _ q₀ (fun q hq => absurd (Subsingleton.elim q q₀) hq), hi,
    ((hA.mem_ThSp e).1 he).2 _ (Quotient.out q₀ : A).2]
  simp

theorem klat_triples : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), (∀ A : AddSubgroup (VC D N N'), KLat D (tor0 D cc δ) A → Nice D (tor0 D cc δ) A) ∧ (∀ A₁ A₂ : AddSubgroup (VC D N N'), KLat D (tor0 D cc δ) A₁ → KLat D (tor0 D cc δ) A₂ → ∀ e ∈ ThSp D (tor0 D cc δ) A₁, e ≠ 0 → (A₁.addSubgroupOf A₂).index ≠ 0) ∧ (∀ A : AddSubgroup (VC D N N'), KLat D (tor0 D cc δ) A → ∀ e ∈ ThSp D (tor0 D cc δ) A, Iop D (tor0 D cc δ) A A e = e) ∧ ∀ A₁ A₂ A₃ : AddSubgroup (VC D N N'), KLat D (tor0 D cc δ) A₁ → KLat D (tor0 D cc δ) A₂ → KLat D (tor0 D cc δ) A₃ → ∀ e ∈ ThSp D (tor0 D cc δ) A₁, e ≠ 0 → ∃ μ, Trip D (tor0 D cc δ) A₁ A₂ A₃ e μ := by
  intro D cc δ hc N N'
  refine ⟨fun A hA => nice_of_klat hc hA, fun A₁ A₂ h₁ h₂ _ _ _ => index_ne_zero hc h₁ h₂,
    fun A hA e he => iop_self (nice_of_klat hc hA) he, fun A₁ A₂ A₃ h₁ h₂ h₃ e he h0 => ?_⟩
  obtain ⟨μ, hμ, h⟩ := GlobalTheory.TripleIntertwiner.triple_constant D cc δ hc N N' A₁ A₂ A₃ h₁ h₂ h₃ e he
  exact ⟨μ, nice_of_klat hc h₁, nice_of_klat hc h₂, nice_of_klat hc h₃, index_ne_zero hc h₁ h₂,
    index_ne_zero hc h₂ h₃, index_ne_zero hc h₁ h₃, he, h0, hμ, h⟩

end GlobalTheory.ThetaTriple
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LamBallULe
section
noncomputable section
namespace GlobalTheory.CartanInt.LamBall
open Formalism.BasicNotions Matrix MeasureTheory

theorem pow_self_le_factorial_sq (n : ℕ) : n ^ n ≤ n.factorial ^ 2 := by
  have h1 : ∏ k ∈ Finset.range n, (k + 1) = n.factorial := Finset.prod_range_add_one_eq_factorial n
  have h2 : ∏ k ∈ Finset.range n, (n - k) = n.factorial := by
    calc ∏ k ∈ Finset.range n, (n - k) = ∏ k ∈ Finset.range n, ((n - 1 - k) + 1) :=
          Finset.prod_congr rfl fun k hk => by have := Finset.mem_range.1 hk; omega
      _ = ∏ k ∈ Finset.range n, (k + 1) := Finset.prod_range_reflect (fun k => k + 1) n
      _ = n.factorial := h1
  calc n ^ n = ∏ _k ∈ Finset.range n, n := by rw [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ k ∈ Finset.range n, ((k + 1) * (n - k)) := by
        apply Finset.prod_le_prod'
        intro k hk
        have hk := Finset.mem_range.1 hk
        obtain ⟨m, hm⟩ : ∃ m, n - k = m + 1 := ⟨n - k - 1, by omega⟩
        have hn : n = k + m + 1 := by omega
        rw [hm, hn]
        nlinarith
    _ = n.factorial ^ 2 := by rw [Finset.prod_mul_distrib, h1, h2, sq]

theorem two_mul_pow_le_factorial (N : ℕ) : (2 * N) ^ N ≤ (2 * N).factorial := by
  have h := pow_self_le_factorial_sq (2 * N)
  rw [pow_mul'] at h
  exact (Nat.pow_le_pow_iff_left two_ne_zero).1 h

theorem volume_l1_ball_le {ι : Type} [Fintype ι] (a : ℕ) (ha : Fintype.card ι = a ^ 2) (r : ℝ)
    (hr : 0 < r) : (volume : Measure (ι → ℂ)) {z | ∑ i, ‖z i‖ < 2 * r} ≤
      ENNReal.ofReal ((18 / 5 * r / (a : ℝ)) ^ (a ^ 2)) ^ 2 := by
  classical
  rcases Nat.eq_zero_or_pos a with rfl | ha0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.1 (by simpa using ha)
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, pow_zero,
      ENNReal.ofReal_one, one_pow]
    rw [MeasureTheory.volume_pi, Measure.pi_of_empty]
    exact prob_le_one
  · have hnpos : (0 : ℝ) < Fintype.card ι := by rw [ha]; push_cast; positivity
    have : Nonempty ι := Fintype.card_pos_iff.1 (by rw [ha]; positivity)
    have hset : {z : ι → ℂ | ∑ i, ‖z i‖ < 2 * r} =
        {z | (∑ i, ‖z i‖ ^ (1 : ℝ)) ^ (1 / (1 : ℝ)) < 2 * r} := by
      simp only [Real.rpow_one, div_one]
    have hG3 : Real.Gamma (2 / 1 + 1) = 2 := by
      have := Real.Gamma_nat_eq_factorial 2
      norm_num at this ⊢
    have hGn : Real.Gamma (2 * (Fintype.card ι : ℝ) / 1 + 1) = ((2 * Fintype.card ι).factorial : ℝ) := by
      rw [div_one, ← Real.Gamma_nat_eq_factorial]
      push_cast
      ring_nf
    rw [hset, Complex.volume_sum_rpow_lt ι le_rfl, hG3, hGn, ← ha,
      ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_pow (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    set n := Fintype.card ι with hn
    have hfac : ((2 : ℝ) * n) ^ n ≤ ((2 * n).factorial : ℝ) := by
      exact_mod_cast two_mul_pow_le_factorial n
    have han : (a : ℝ) ^ 2 = n := by exact_mod_cast ha.symm
    calc (2 * r) ^ (2 * n) * ((Real.pi * 2) ^ n / ((2 * n).factorial : ℝ))
        = (8 * Real.pi * r ^ 2) ^ n / ((2 * n).factorial : ℝ) := by
          rw [pow_mul, ← mul_div_assoc, ← mul_pow]
          congr 2
          ring
      _ ≤ (8 * Real.pi * r ^ 2) ^ n / ((2 : ℝ) * n) ^ n :=
          div_le_div_of_nonneg_left (by positivity) (pow_pos (by positivity) n) hfac
      _ = (4 * Real.pi * r ^ 2 / n) ^ n := by
          rw [← div_pow]
          congr 1
          field_simp
          ring
      _ ≤ (324 / 25 * r ^ 2 / n) ^ n := by
          apply pow_le_pow_left₀ (by positivity)
          gcongr
          linarith [Real.pi_lt_d2]
      _ = ((18 / 5 * r / a) ^ 2) ^ n := by
          congr 1
          rw [div_pow, han]
          ring
      _ = ((18 / 5 * r / a) ^ n) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]

theorem lam_ballU_le (p q : ℕ) (lam : Measure (lieU p q)) (h : IsOmegaLeb lam) (r : ℝ) (hr : 0 < r) :
    lam (ballU p q r) ≤ ENNReal.ofReal ((18 / 5 * r / ((p + q : ℕ) : ℝ)) ^ ((p + q) ^ 2)) := by
  classical
  obtain ⟨hHaar, hmap⟩ := h
  have : BorelSpace (lieU p q) := ⟨rfl⟩
  have hcont : Continuous fun X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ =>
      Xᴴ * Formalism.UG.Jpq p q + Formalism.UG.Jpq p q * X :=
    (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).add
      (continuous_const.matrix_mul continuous_id)
  have hcl : IsClosed (lieU p q : Set (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) :=
    isClosed_eq hcont continuous_const
  have : LocallyCompactSpace (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin p ⊕ Fin q → Fin p ⊕ Fin q → ℂ))
  have : SecondCountableTopology (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin p ⊕ Fin q → Fin p ⊕ Fin q → ℂ))
  have : LocallyCompactSpace (lieU p q) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (lieU p q) :=
    hcl.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  have : OpensMeasurableSpace (lieU p q × lieU p q) := inferInstance
  have : IsLocallyFiniteMeasure lam := inferInstance
  have : SigmaFinite lam := inferInstance
  have hc : Continuous fun ab : lieU p q × lieU p q =>
      (ab.1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) +
        Complex.I • (ab.2 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :=
    have h1 : Continuous fun ab : lieU p q × lieU p q =>
        (ab.1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) := continuous_subtype_val.comp continuous_fst
    have h2 : Continuous fun ab : lieU p q × lieU p q =>
        (ab.2 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) := continuous_subtype_val.comp continuous_snd
    h1.add (h2.const_smul Complex.I)
  have hΦ : Measurable fun ab : lieU p q × lieU p q =>
      entries ((ab.1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) +
        Complex.I • (ab.2 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) :=
    (continuous_pi fun ij : (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q) => hc.matrix_elem ij.1 ij.2).measurable
  have hS : MeasurableSet {z : (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q) → ℂ | ∑ i, ‖z i‖ < 2 * r} :=
    (isOpen_lt (continuous_finsetSum _ fun i _ => (continuous_apply i).norm)
      continuous_const).measurableSet
  have hsub : ballU p q r ×ˢ ballU p q r ⊆ (fun ab : lieU p q × lieU p q =>
      entries ((ab.1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) +
        Complex.I • (ab.2 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ))) ⁻¹'
      {z | ∑ i, ‖z i‖ < 2 * r} := by
    rintro ⟨X, Y⟩ ⟨hX, hY⟩
    simp only [ballU, Set.mem_ofPred_eq] at hX hY
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, entries, Fintype.sum_prod_type]
    calc ∑ i, ∑ j, ‖((X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) +
          Complex.I • (Y : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) i j‖
        ≤ ∑ i, ∑ j, (‖(X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖ +
          ‖(Y : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
          calc _ ≤ _ := norm_add_le _ _
            _ = _ := by rw [norm_mul, Complex.norm_I, one_mul]
      _ = (∑ i, ∑ j, ‖(X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖) +
          ∑ i, ∑ j, ‖(Y : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖ := by
          simp only [Finset.sum_add_distrib]
      _ < r + r := add_lt_add hX hY
      _ = 2 * r := by ring
  have hvol := volume_l1_ball_le (ι := (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q)) (p + q)
    (by simp [Fintype.card_prod, Fintype.card_sum, sq]) r hr
  have key : lam (ballU p q r) ^ 2 ≤
      ENNReal.ofReal ((18 / 5 * r / ((p + q : ℕ) : ℝ)) ^ ((p + q) ^ 2)) ^ 2 := by
    calc lam (ballU p q r) ^ 2 = (lam.prod lam) (ballU p q r ×ˢ ballU p q r) := by
          rw [Measure.prod_prod, sq]
      _ ≤ (lam.prod lam) ((fun ab : lieU p q × lieU p q =>
            entries ((ab.1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) +
              Complex.I • (ab.2 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ))) ⁻¹'
            {z | ∑ i, ‖z i‖ < 2 * r}) := measure_mono hsub
      _ = ((lam.prod lam).map (fun ab : lieU p q × lieU p q =>
            entries ((ab.1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) +
              Complex.I • (ab.2 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ))))
            {z | ∑ i, ‖z i‖ < 2 * r} := (Measure.map_apply hΦ hS).symm
      _ = volume {z : (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q) → ℂ | ∑ i, ‖z i‖ < 2 * r} := by
          rw [hmap]
      _ ≤ _ := hvol
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 key

end GlobalTheory.CartanInt.LamBall
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardPairLatticeLocallyOrthonormalBasisStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardPairLattice_locally_orthonormal_basis : ∀ D : D7, odd1 D := by
  first | exact @GlobalTheory.OddGenus.odd_one | exact GlobalTheory.OddGenus.odd_one | (intros; apply GlobalTheory.OddGenus.odd_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTripleConstantEqNegOnePowStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTripleConstant_eq_neg_one_pow : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A₁ A₂ A₃ : AddSubgroup (VC D N N')) (e : VC D N N' → ℂ) (μ : ℂ), Trip D T A₁ A₂ A₃ e μ → ∀ (P : Ideal (𝓞 D.host.E)) (r : ℕ), P.IsMaximal → (∀ a ∈ P, sgO D a ∈ P) → (∃ a, a - sgO D a ∉ P) → TriDat D T A₁ A₂ A₃ P r → μ = (-1) ^ r := by
  first | exact @GlobalTheory.TriangleSign.mu_eq_sign | exact GlobalTheory.TriangleSign.mu_eq_sign | (intros; apply GlobalTheory.TriangleSign.mu_eq_sign <;> assumption)
end

