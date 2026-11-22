import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0199
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqOrConjOfPlaceOf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0024
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0227
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiGroupSplitRealFinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.JacSplit

open GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
  {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']

theorem tensNU_map (φ : R' →ₐ[F] R) (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b) (h : ∀ a, j (φ a) = j 1 * a)
    (z : R' ⊗[F] E) : tensNU j hj (Algebra.TensorProduct.map φ (AlgHom.id F E) z) = tensNU (E := E) j hj 1 * z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [Algebra.TensorProduct.one_def, h]
  | add x y hx hy => rw [map_add, map_add, hx, hy, mul_add]

theorem mat_extH_mapH (φ : R' →ₐ[F] R) (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b) (h : ∀ a, j (φ a) = j 1 * a)
    (g : HA R' σ J) : ∃ c : R' ⊗[F] E, (HA.mat R' σ J (extH σ J j hj (mapH σ J φ g))).1 =
      (1 - c) • (1 : Matrix (Fin M) (Fin M) (R' ⊗[F] E)) + c • (HA.mat R' σ J g).1 := by
  refine ⟨tensNU (E := E) j hj 1, ?_⟩
  ext r s
  rw [GlobalTheory.AutFunCompare.mat_extH, GlobalTheory.AutFunCompare.mat_mapH, tensNU_map φ j hj h]
  rfl

omit [Algebra F R] in
theorem conj_mix {k n m : ℕ} (c : R) (P : Matrix (Fin k) (Fin n) R) (G : Matrix (Fin n) (Fin n) R)
    (Q : Matrix (Fin n) (Fin m) R) :
    P * (((1 - c) • (1 : Matrix (Fin n) (Fin n) R) + c • G) * Q) = (1 - c) • (P * Q) + c • (P * (G * Q)) := by
  rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]

omit [Algebra F R] in
theorem mix_zero {k m : ℕ} (c : R) {A B : Matrix (Fin k) (Fin m) R} (hA : A = 0) (hB : B = 0) :
    (1 - c) • A + c • B = 0 := by rw [hA, hB, smul_zero, smul_zero, add_zero]

omit [Algebra F R] in
theorem mix_uni {k : ℕ} (c : R) {A B : Matrix (Fin k) (Fin k) R} (hA : A = 1)
    (hB : ∀ i j : Fin k, (j < i → B i j = 0) ∧ B i i = 1) (i j : Fin k) :
    (j < i → ((1 - c) • A + c • B) i j = 0) ∧ ((1 - c) • A + c • B) i i = 1 := by
  subst hA
  refine ⟨fun hji => ?_, ?_⟩
  · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, (hB i j).1 hji, Matrix.one_apply_ne hji.ne',
      mul_zero, add_zero]
  · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, (hB i i).2, Matrix.one_apply_eq, mul_one,
      sub_add_cancel]

end Gen

variable {D : D7}

theorem mt_ofInf_projInf (V : HSp D) (g : GA D V) : ∃ c : AE D,
    mt V (ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram g)) = (1 - c) • (1 : Mx D V.rank V.rank) + c • mt V g :=
  mat_extH_mapH (R' := AF D.host.F) D.sp.cm.sig V.gram (fstA D.host.F) _ _
    (fun a => Prod.ext (one_mul a.1).symm (zero_mul a.2).symm) g

theorem mt_ofFin_projFin (V : HSp D) (g : GA D V) : ∃ c : AE D,
    mt V (ofFin D.sp.cm.sig V.gram (projFin D.sp.cm.sig V.gram g)) = (1 - c) • (1 : Mx D V.rank V.rank) + c • mt V g :=
  mat_extH_mapH (R' := AF D.host.F) D.sp.cm.sig V.gram (sndA D.host.F) _ _
    (fun a => Prod.ext (zero_mul a.1).symm (one_mul a.2).symm) g

theorem mem_jacGrp_of_mat {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (c : AE D) {g h : GA D S} (hg : g ∈ jacGrp d)
    (hh : mt S h = (1 - c) • (1 : Mx D S.rank S.rank) + c • mt S g) : h ∈ jacGrp d := by
  obtain ⟨h0, hY, hX⟩ := (GlobalTheory.BesClosed.mem_jacGrp_iff_mat d g).1 hg
  have e : ∀ {k : ℕ} (P : Mx D k S.rank),
      P ⬝ (mt S h ⬝ d.jX) = (1 - c) • (P ⬝ d.jX) + c • (P ⬝ (mt S g ⬝ d.jX)) := fun P =>
    (congrArg (fun N : Mx D S.rank S.rank => P ⬝ (N ⬝ d.jX)) hh).trans (conj_mix c P (mt S g) d.jX)
  refine (GlobalTheory.BesClosed.mem_jacGrp_iff_mat d h).2
    ⟨(e _).trans (mix_zero c d.p0_jX h0), (e _).trans (mix_zero c d.pY_jX hY), ?_⟩
  rw [e]
  exact mix_uni c d.pX_jX hX

end GlobalTheory.JacSplit

namespace GlobalTheory

open GlobalTheory.AdelicU

theorem jacGrp_split_inf_fin : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ), ∀ a ∈ GinfC V, ∀ b ∈ GfC V,
    a * b ∈ jacGrp d → a ∈ jacGrp d ∧ b ∈ jacGrp d := by
  intro D V V₀ ρ d a ha b hb hab
  rw [GinfC_eq, mem_infPts] at ha
  rw [GfC_eq, mem_finPts] at hb
  have hA : ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram (a * b)) = a := by
    rw [map_mul, hb, mul_one]
    conv_rhs => rw [← ofInf_projInf_mul_ofFin_projFin D.sp.cm.sig V.gram a]
    rw [ha, map_one, mul_one]
  have hB : ofFin D.sp.cm.sig V.gram (projFin D.sp.cm.sig V.gram (a * b)) = b := by
    rw [map_mul, ha, one_mul]
    conv_rhs => rw [← ofInf_projInf_mul_ofFin_projFin D.sp.cm.sig V.gram b]
    rw [hb, map_one, one_mul]
  obtain ⟨c, hc⟩ := GlobalTheory.JacSplit.mt_ofInf_projInf V (a * b)
  obtain ⟨c', hc'⟩ := GlobalTheory.JacSplit.mt_ofFin_projFin V (a * b)
  rw [hA] at hc
  rw [hB] at hc'
  exact ⟨GlobalTheory.JacSplit.mem_jacGrp_of_mat d c hab hc, GlobalTheory.JacSplit.mem_jacGrp_of_mat d c' hab hc'⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfAvgLinear
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped GlobalTheory.HalfAverage

noncomputable section

namespace GlobalTheory.HalfLinForm

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in

theorem halfAvg_linear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ e, IsSplitIdem D e → ∀ ℓ₀ : (WO S₀ T → ℂ) →ₗ[ℂ] ℂ, ∀ H : AddSubgroup (Mx D T.rank ρ), (∀ x, x ∈ H ↔ ∀ i j, cA D e * x i j = x i j) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsAddHaarMeasure], ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, ∀ f, IsThetaFunO ψ S T f → ℓ f = ∫ x : H, ℓ₀ (d.mixS T ψ μ 𝓕 f x.1) ∂ν := by
  intro D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he ℓ₀ H hH _ _ ν _
  haveI : IsTopologicalAddGroup (Mx D T.rank ρ) := GlobalTheory.HalfAverage.tagMx _ _
  haveI : T2Space (Mx D T.rank ρ) := GlobalTheory.HalfAverage.t2Mx _ _
  haveI : T2Space H := inferInstance
  haveI : R1Space H := T2Space.r1Space
  haveI : ContinuousSub (Mx D T.rank ρ) := by first | exact IsTopologicalAddGroup.to_continuousSub | exact inferInstance
  have hHc : IsClosed (H : Set (Mx D T.rank ρ)) := by
    have : (H : Set (Mx D T.rank ρ)) = ⋂ i, ⋂ j, {t : Mx D T.rank ρ | cA D e * t i j = t i j} := by
      ext t; simp only [SetLike.mem_coe, hH, Set.mem_iInter, Set.mem_setOf_eq]
    rw [this]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (continuous_const.mul ((continuous_apply j).comp (continuous_apply i)))
        ((continuous_apply j).comp (continuous_apply i))

  have hint : ∀ f, IsThetaFunO ψ S T f → Integrable (fun x : H => ℓ₀ (d.mixS T ψ μ 𝓕 f x.1)) ν := by
    intro f hf
    obtain ⟨⟨U, hUo, hU⟩, K, hK, hKs⟩ := GlobalTheory.MixHalf.mixS_half D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he f hf
    have hKc : IsCompact ((Subtype.val : H → Mx D T.rank ρ) ⁻¹' K) :=
      hHc.isClosedEmbedding_subtypeVal.isCompact_preimage hK
    refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.intro hKc fun t ht => ?_)
    · refine IsLocallyConstant.continuous ?_
      rw [IsLocallyConstant.iff_eventually_eq]
      intro t
      have hn : {s : H | (s : Mx D T.rank ρ) - t ∈ U} ∈ nhds t := by
        refine IsOpen.mem_nhds (hUo.preimage (continuous_subtype_val.sub continuous_const)) ?_
        show (t : Mx D T.rank ρ) - t ∈ U
        rw [sub_self]; exact U.zero_mem
      filter_upwards [hn] with s hs
      have hsH : ∀ i j, cA D e * ((s : Mx D T.rank ρ) - t) i j = ((s : Mx D T.rank ρ) - t) i j :=
        (hH _).1 (H.sub_mem s.2 t.2)
      have h1 := hU _ hs hsH t
      rw [show (t : Mx D T.rank ρ) + ((s : Mx D T.rank ρ) - t) = s by abel] at h1
      rw [h1]
    · by_contra hne
      exact ht (hKs _ ((hH _).1 t.2) fun h0 => hne (by rw [h0, map_zero]))

  have madd : ∀ f g : WO S T → ℂ,
      (∀ x w, IntegrableOn (fun a => heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) f)) 0) 𝓕 μ) →
      (∀ x w, IntegrableOn (fun a => heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) g)) 0) 𝓕 μ) →
      ∀ x, d.mixS T ψ μ 𝓕 (f + g) x = d.mixS T ψ μ 𝓕 f x + d.mixS T ψ μ 𝓕 g x := by
    intro f g hf hg x
    funext w
    have h1 := hf x w
    have h2 := hg x w
    simp only [HypDec.mixS, HypDec.integrandS_eq, Pi.add_apply, mul_add] at h1 h2 ⊢
    exact integral_add h1 h2
  have msmul : ∀ (c : ℂ) (f : WO S T → ℂ) x, d.mixS T ψ μ 𝓕 (c • f) x = c • d.mixS T ψ μ 𝓕 f x := by
    intro c f x
    funext w
    simp only [HypDec.mixS, HypDec.integrandS_eq, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, integral_const_mul]
  let P : Submodule ℂ (WO S T → ℂ) :=
    { carrier := {f | (∀ x w, IntegrableOn
          (fun a => heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) f)) 0) 𝓕 μ) ∧
        Integrable (fun x : H => ℓ₀ (d.mixS T ψ μ 𝓕 f x.1)) ν}
      add_mem' := by
        rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
        refine ⟨fun x w => ?_, ?_⟩
        · have h1 := hf1 x w
          have h2 := hg1 x w
          simp only [HypDec.integrandS_eq, Pi.add_apply, mul_add] at h1 h2 ⊢
          exact h1.add h2
        · refine (hf2.add hg2).congr (Filter.Eventually.of_forall fun x => ?_)
          simp only [Pi.add_apply, madd f g hf1 hg1, map_add]
      zero_mem' := by
        have h0 : ∀ x, d.mixS T ψ μ 𝓕 (0 : WO S T → ℂ) x = 0 := fun x => by
          simpa using msmul 0 0 x
        refine ⟨fun x w => ?_, ?_⟩
        · simp only [HypDec.integrandS_eq, Pi.zero_apply, mul_zero]; exact integrableOn_zero
        · simp only [h0, map_zero]; exact integrable_zero _ _ _
      smul_mem' := by
        rintro c f ⟨hf1, hf2⟩
        refine ⟨fun x w => ?_, ?_⟩
        · have h1 := hf1 x w
          simp only [HypDec.integrandS_eq, Pi.smul_apply, smul_eq_mul] at h1 ⊢
          simp only [mul_left_comm _ c]
          exact h1.const_mul c
        · refine (hf2.const_mul c).congr (Filter.Eventually.of_forall fun x => ?_)
          simp only [msmul, map_smul, smul_eq_mul] }
  have hP : ∀ f, IsThetaFunO ψ S T f → f ∈ P := fun f hf =>
    ⟨fun x w => d.integrableOn_mixS hψ.1.1 hμ hf x w, hint f hf⟩
  let L : P →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ x : H, ℓ₀ (d.mixS T ψ μ 𝓕 f.1 x.1) ∂ν
      map_add' := by
        rintro ⟨f, hf1, hf2⟩ ⟨g, hg1, hg2⟩
        show ∫ x : H, ℓ₀ (d.mixS T ψ μ 𝓕 (f + g) x.1) ∂ν =
          ∫ x : H, ℓ₀ (d.mixS T ψ μ 𝓕 f x.1) ∂ν + ∫ x : H, ℓ₀ (d.mixS T ψ μ 𝓕 g x.1) ∂ν
        rw [← integral_add hf2 hg2]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [madd f g hf1 hg1, map_add]
      map_smul' := by
        rintro c ⟨f, hf1, hf2⟩
        show ∫ x : H, ℓ₀ (d.mixS T ψ μ 𝓕 (c • f) x.1) ∂ν = c • ∫ x : H, ℓ₀ (d.mixS T ψ μ 𝓕 f x.1) ∂ν
        rw [smul_eq_mul, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [msmul, map_smul, smul_eq_mul] }
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend L
  exact ⟨ℓ, fun f hf => LinearMap.congr_fun hℓ ⟨f, hP f hf⟩⟩

end GlobalTheory.HalfLinForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeisComb

variable {D : D7}

theorem heisO_finset_sum (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (x : WO S T) {ι : Type} (s : Finset ι)
    (a : ι → ℂ) (g : ι → WO S T → ℂ) :
    heisO ψ S T x (∑ i ∈ s, a i • g i) = ∑ i ∈ s, a i • heisO ψ S T x (g i) := by
  funext w
  simp only [heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem comb_eq_sum (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T c f = c.sum fun u a => a • heisO ψ S T u f := rfl

theorem comb_comb (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c c' : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T c (comb ψ S T c' f) =
      ∑ x ∈ c.support, ∑ y ∈ c'.support, (c x * c' y) • heisO ψ S T x (heisO ψ S T y f) := by
  unfold comb
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [heisO_finset_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_smul]

theorem symplO_half (S T : HSp D) (e e' : AE D) (x y : WO S T) (he : cA D e = e) (hee : e * e' = 0)
    (hx : IsHalf e x) (hy : IsHalf e' y) : symplO S T x y = 0 := by
  have h0 : e * cA D e' = 0 := by
    conv_lhs => rw [← he]
    rw [← map_mul, hee, map_zero]
  have hh : hO S T x y = 0 := by
    unfold hO
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
      Finset.sum_eq_zero fun d _ => ?_
    rw [← hy c b, ← hx d a, map_mul]
    calc incA D (S.gram⁻¹ a b) * (cA D e' * cA D (y c b)) * incA D (T.gram c d) * (e * x d a)
        = (e * cA D e') * (incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a) := by ring
      _ = 0 := by rw [h0, zero_mul]
  unfold symplO
  rw [hh, mul_zero, map_zero]

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), (∀ c c' : WO S T →₀ ℂ, ∃ c'' : WO S T →₀ ℂ, (∀ w ∈ c''.support, ∃ x ∈ c.support, ∃ y ∈ c'.support, w = x + y) ∧ ∀ f, comb ψ S T c'' f = comb ψ S T c (comb ψ S T c' f)) ∧ (∀ c c' : WO S T →₀ ℂ, (∀ x ∈ c.support, ∀ y ∈ c'.support, symplO S T x y = 0) → ∀ f, comb ψ S T c (comb ψ S T c' f) = comb ψ S T c' (comb ψ S T c f)) ∧ (∀ (c : WO S T →₀ ℂ) f, IsThetaFunO ψ S T f → IsFinComb c → IsStdChar D ψ (-1) → IsThetaFunO ψ S T (comb ψ S T c f)) ∧ ∀ (e e' : AE D) (x y : WO S T), cA D e = e → e * e' = 0 → IsHalf e x → IsHalf e' y → symplO S T x y = 0 := by
  intro D ψ S T
  refine ⟨fun c c' => ?_, fun c c' h f => ?_, fun c f hf hc hψ => ?_,
    fun e e' x y he hee hx hy => symplO_half S T e e' x y he hee hx hy⟩
  · classical
    refine ⟨∑ x ∈ c.support, ∑ y ∈ c'.support, Finsupp.single (x + y) (c x * c' y * ψ (symplOH S T x y)), ?_,
      fun f => ?_⟩
    · intro w hw
      have h1 := Finsupp.support_finset_sum hw
      rw [Finset.mem_biUnion] at h1
      obtain ⟨x, hx, hw2⟩ := h1
      have h2 := Finsupp.support_finset_sum hw2
      rw [Finset.mem_biUnion] at h2
      obtain ⟨y, hy, hw3⟩ := h2
      have h3 := Finsupp.support_single_subset hw3
      rw [Finset.mem_singleton] at h3
      exact ⟨x, hx, y, hy, h3⟩
    · rw [comb_comb, comb_eq_sum]
      rw [← Finsupp.sum_finset_sum_index (fun u => zero_smul ℂ (heisO ψ S T u f)) (fun u a b => add_smul a b (heisO ψ S T u f))]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finsupp.sum_finset_sum_index (fun u => zero_smul ℂ (heisO ψ S T u f)) (fun u a b => add_smul a b (heisO ψ S T u f))]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finsupp.sum_single_index (zero_smul ℂ (heisO ψ S T (x + y) f)), GlobalTheory.WeilVacMove.heisO_heisO, smul_smul]
  · rw [comb_comb, comb_comb, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun x hx => ?_
    have h0 : symplOH S T x y = 0 := by
      unfold symplOH
      rw [h x hx y hy, mul_zero]
    have h1 : symplOH S T y x = 0 := by
      rw [GlobalTheory.MixModel.symplOH_skew, h0, neg_zero]
    rw [GlobalTheory.WeilVacMove.heisO_heisO, GlobalTheory.WeilVacMove.heisO_heisO, h0, h1, add_comm x y, mul_comm (c x)]
  · exact GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hψ.1 f hf (WO S T) c.support id (fun u => c u) hc

end GlobalTheory.HeisComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergBasisDerivEqOfUniformLimits
section
noncomputable section

open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

namespace GlobalTheory.ThetaLimDeriv

theorem tendstoUniformly_heisO {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {G : ℕ → WO S T → ℂ} {F : WO S T → ℂ} (h : TendstoUniformly G F Filter.atTop) (x : ℝ → WO S T) (w : WO S T) :
    TendstoUniformly (fun j t => heisO ψ S T (x t) (G j) w) (fun t => heisO ψ S T (x t) F w) Filter.atTop := by
  rw [Metric.tendstoUniformly_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with j hj t
  have := hj (w + x t)
  rw [dist_eq_norm] at this ⊢
  simp only [heisO]
  rw [← mul_sub, norm_mul, hψ.1.2.1, one_mul]
  exact this

theorem heisDer_of_tendstoUniformly : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (G : ℕ → WO S T → ℂ) (F F' : WO S T → ℂ), (∀ j, IsThetaFunO ψ S T (G j)) → TendstoUniformly G F Filter.atTop → ∀ a : (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), TendstoUniformly (fun j => GlobalTheory.Size.heisDer ψ θ a (G j)) F' Filter.atTop → GlobalTheory.Size.heisDer ψ θ a F = F' := by
  intro D ψ hψ θ hθ S T G F F' hG hF a hF'
  have hL := GlobalTheory.OrientedHeis.isRealDir_lineAt (S := S) (T := T) hθ a.1
    (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1))
  have e : ∀ f, GlobalTheory.Size.heisDer ψ θ a f = GlobalTheory.OrientedHeis.dLine ψ S T
      (lineAt θ a.1 (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1))) f := fun _ => rfl
  simp only [e] at hF' ⊢
  generalize lineAt θ a.1 (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)) = L at hL hF' ⊢
  funext w
  have h1 := tendstoUniformly_heisO hψ hF L w
  have h2 := tendstoUniformly_heisO hψ hF' L w
  have h3 := hasDerivAt_of_tendstoUniformly h2
    (Filter.Eventually.of_forall fun j s => GlobalTheory.OrientedHeis.hasDerivAt_heisO hθ hψ hL (hG j) w s)
    (fun s => h1.tendsto_at s) 0
  have h4 := h3.deriv
  rw [map_zero, GlobalTheory.OrientedHeis.heisO_zero] at h4
  exact h4

end GlobalTheory.ThetaLimDeriv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergDerivWeilTranslateContinuousCombinatio
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeisLineComb

open GlobalTheory.WeilVacMove GlobalTheory.FockCompare

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem actO_actO_inv (g : GA D S) (h : GA D T) (x : WO S T) : actO S T g h (actO S T g⁻¹ h⁻¹ x) = x := by
  unfold actO
  rw [inv_inv]
  calc HMul.hMul (HMul.hMul (mt T h) (HMul.hMul (HMul.hMul (mt T h⁻¹) x) (mt S g))) (mt S g⁻¹)
      = HMul.hMul (HMul.hMul (HMul.hMul (mt T h) (mt T h⁻¹)) x) (HMul.hMul (mt S g) (mt S g⁻¹)) := by
        simp only [Matrix.mul_assoc]
    _ = x := by rw [← GlobalTheory.WeilVacMove.mt_mul, ← GlobalTheory.WeilVacMove.mt_mul, mul_inv_cancel, mul_inv_cancel, GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.mt_one, Matrix.one_mul, Matrix.mul_one]

theorem dLine_apply {θ : GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition.InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : Chart θ σ)
    {lam : AF D.host.F →+ ℂ} (hl : Continuous lam) (hlam : ∀ a, sndA D.host.F a = 0 → ψ a = Complex.exp (lam a))
    {L : ℝ →+ WO S T} (hL : Continuous L) (hL0 : ∀ t, (L t).map (finPart D) = 0) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (w : WO S T) :
    dLine ψ S T L f w = phase lam S T (L 1) w * f w +
      fderiv ℝ (fun x => f (w + iotaW σ T S x)) 0 (piW θ T S (L 1)) := by
  have hline := (smooth_iff_sm_and_real_lines D θ σ h T S).2.1 L ⟨hL, hL0⟩
  have hfs := ((smooth_iff_sm_and_real_lines D θ σ h T S).1 f).1 hf.smooth
  have e : (fun t : ℝ => heisO ψ S T (L t) f w) = fun t : ℝ => Complex.exp (t * phase lam S T (L 1) w) *
      f (w + iotaW σ T S (t • piW θ T S (L 1))) := by
    funext t
    rw [heisO, psi_sympl_line hl hlam hL hL0, ← hline t]
  unfold dLine
  rw [e]
  exact (hasDerivAt_exp_mul _ _ f hfs _ w).deriv

theorem dLine_eq_sum (hψ : IsStdChar D ψ (-1)) {θ : GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition.InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D}
    (h : Chart θ σ) {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ (RW T S)) {L : ℝ →+ WO S T} (hL : Continuous L)
    (hL0 : ∀ t, (L t).map (finPart D) = 0) (N : ι → ℝ →+ WO S T) (hN : ∀ i, Continuous (N i))
    (hN0 : ∀ i t, (N i t).map (finPart D) = 0) (hN1 : ∀ i, piW θ T S (N i 1) = b i) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) :
    dLine ψ S T L f = ∑ i, ((b.coord i (piW θ T S (L 1)) : ℝ) : ℂ) • dLine ψ S T (N i) f := by
  obtain ⟨lam, hl, hlam⟩ := exists_log hψ
  funext w
  let A : RW T S →+ ℂ := AddMonoidHom.mk' (fun v => lam (symplOH S T w (iotaW σ T S v))) fun u v => by
    rw [map_add, symplOH_add_right, map_add]
  have hA : Continuous A := hl.comp (continuous_symplOH S T continuous_const (h.continuous_iota T S))
  let A' : RW T S →L[ℝ] ℂ := A.toRealLinearMap hA
  let B : RW T S →L[ℝ] ℂ := fderiv ℝ (fun x => f (w + iotaW σ T S x)) 0
  let Φ : RW T S →ₗ[ℝ] ℂ := (LinearMap.mulRight ℝ (f w)).comp A'.toLinearMap + B.toLinearMap
  have key : ∀ (K : ℝ →+ WO S T), Continuous K → (∀ t, (K t).map (finPart D) = 0) →
      dLine ψ S T K f w = Φ (piW θ T S (K 1)) := by
    intro K hK hK0
    rw [dLine_apply h hl hlam hK hK0 hf]
    have e1 : K 1 = iotaW σ T S (piW θ T S (K 1)) := by
      have := (smooth_iff_sm_and_real_lines D θ σ h T S).2.1 K ⟨hK, hK0⟩ 1
      rwa [one_smul] at this
    have e2 : lam (symplOH S T w (K 1)) = A (piW θ T S (K 1)) := by
      show _ = lam (symplOH S T w (iotaW σ T S (piW θ T S (K 1))))
      rw [← e1]
    show lam (symplOH S T w (K 1)) * f w + _ = _
    rw [e2]
    rfl
  rw [Finset.sum_apply, key L hL hL0]
  simp only [Pi.smul_apply, smul_eq_mul]
  simp only [fun i => key (N i) (hN i) (hN0 i), hN1]
  conv_lhs => rw [← b.sum_repr (piW θ T S (L 1))]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Complex.real_smul, Module.Basis.coord_apply]

theorem dLine_om_comb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ M : ℝ →+ WO S T, Continuous M → (∀ s, (M s).map (finPart D) = 0) → ∃ (m : ℕ) (N : Fin m → ℝ →+ WO S T) (c : Fin m → GA D S × GA D T → ℂ), (∀ i, Continuous (N i)) ∧ (∀ i s, (N i s).map (finPart D) = 0) ∧ (∀ i, Continuous (c i)) ∧ ∀ p f, IsThetaFunO ψ S T f → GlobalTheory.WeilVacMove.dLine ψ S T M (om p f) = ∑ i, c i p • om p (GlobalTheory.WeilVacMove.dLine ψ S T (N i) f) := by
  intro D ψ S T χS χT om hW M hM hM0
  have hψ := hW.std
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  let b := Module.finBasis ℝ (RW T S)
  let N : Fin (Module.finrank ℝ (RW T S)) → ℝ →+ WO S T := fun i =>
    (iotaW σ T S).comp (ContinuousLinearMap.toSpanSingleton ℝ (b i)).toLinearMap.toAddMonoidHom
  have hN : ∀ i, Continuous (N i) := fun i =>
    (h.continuous_iota T S).comp (ContinuousLinearMap.toSpanSingleton ℝ (b i)).continuous
  have hN0 : ∀ i t, (N i t).map (finPart D) = 0 := fun i t => h.real_iota T S _
  have hN1 : ∀ i, piW θ T S (N i 1) = b i := fun i => by
    show piW θ T S (iotaW σ T S ((1 : ℝ) • b i)) = b i
    rw [h.pi_iota, one_smul]
  let Mp : GA D S × GA D T → ℝ →+ WO S T := fun p =>
    AddMonoidHom.mk' (fun s => actO S T p.1⁻¹ p.2⁻¹ (M s)) fun s t => by rw [map_add, actO_add]
  have hMp : ∀ p, Continuous (Mp p) := fun p =>
    (continuous_const.matrix_mul hM).matrix_mul continuous_const
  have hMp0 : ∀ p t, (Mp p t).map (finPart D) = 0 := fun p t => by
    show (actO S T p.1⁻¹ p.2⁻¹ (M t)).map (finPart D) = 0
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, hM0 t, Matrix.mul_zero, Matrix.zero_mul]
  refine ⟨_, N, fun i p => ((b.coord i (piW θ T S (Mp p 1)) : ℝ) : ℂ), hN, hN0, fun i => ?_, fun p f hf => ?_⟩
  · have hc : Continuous fun p : GA D S × GA D T => actO S T p.1⁻¹ p.2⁻¹ (M 1) := by
      unfold actO
      exact (((GlobalTheory.MixModel.continuous_mt T).comp (continuous_snd.inv)).matrix_mul continuous_const).matrix_mul
        ((GlobalTheory.MixModel.continuous_mt S).comp continuous_fst.inv.inv)
    exact Complex.continuous_ofReal.comp ((LinearMap.continuous_of_finiteDimensional (b.coord i)).comp
      ((continuous_pi' hθ T S).comp hc))
  · obtain ⟨g, k⟩ := p
    have e := om_dLine hW g k (hMp (g, k)) (hMp0 (g, k)) hM hM0 (fun t => (actO_actO_inv g k (M t)).symm) hf
    rw [← e, dLine_eq_sum hψ h b (hMp (g, k)) (hMp0 (g, k)) N hN hN0 hN1 hf, map_sum]
    simp only [map_smul]

end GlobalTheory.HeisLineComb

end
end

