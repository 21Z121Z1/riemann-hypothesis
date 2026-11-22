import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0267
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0106
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0172
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0215
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0254
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0179
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0203
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0229
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0213
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0918
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0181
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaContractionIsBiSmooth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw
open scoped ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ContrSmooth

section Gen

variable {X E : Type} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

def LocSm (K : X → E → ℂ) : Prop :=
  ∀ x₀, ∃ (G : Type) (_ : NormedAddCommGroup G) (_ : NormedSpace ℝ G) (ρ : X → G) (c : X → ℂ) (F : G → E → ℂ),
    ContinuousAt ρ x₀ ∧ ContinuousAt c x₀ ∧ ContDiff ℝ ∞ (Function.uncurry F) ∧ ∀ᶠ x in 𝓝 x₀, ∀ t, K x t = c x * F (ρ x) t

theorem LocSm.continuous {K : X → E → ℂ} (h : LocSm K) : Continuous (Function.uncurry K) := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  obtain ⟨G, _, _, ρ, c, F, hρ, hc, hF, he⟩ := h p.1
  have h1 : ContinuousAt (fun q : X × E => c q.1 * Function.uncurry F (ρ q.1, q.2)) p :=
    (hc.comp continuousAt_fst).mul
      (hF.continuous.continuousAt.comp ((hρ.comp continuousAt_fst).prodMk continuousAt_snd))
  refine h1.congr ?_
  filter_upwards [continuousAt_fst.eventually he] with q hq
  exact (hq q.2).symm

theorem LocSm.differentiable {K : X → E → ℂ} (h : LocSm K) (x : X) : Differentiable ℝ (K x) := by
  obtain ⟨G, _, _, ρ, c, F, -, -, hF, he⟩ := h x
  rw [funext he.self_of_nhds]
  exact ((hF.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)).const_mul _

theorem LocSm.fderiv {K : X → E → ℂ} (h : LocSm K) (y : E) : LocSm fun x t => fderiv ℝ (K x) t y := by
  intro x₀
  obtain ⟨G, _, _, ρ, c, F, hρ, hc, hF, he⟩ := h x₀
  refine ⟨G, inferInstance, inferInstance, ρ, c, fun g t => _root_.fderiv ℝ (F g) t y, hρ, hc, ?_, ?_⟩
  · have h1 : ContDiff ℝ ∞ (Function.uncurry fun (p : G × E) (t : E) => F p.1 t) :=
      hF.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
    exact (ContDiff.fderiv (m := ∞) h1 contDiff_snd (by simp)).clm_apply contDiff_const
  · filter_upwards [he] with x hx t
    have hd : DifferentiableAt ℝ (F (ρ x)) t :=
      (hF.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) t
    rw [funext hx, fderiv_const_mul hd]
    rfl

theorem LocSm.mul {K K' : X → E → ℂ} (h : LocSm K) (h' : LocSm K') : LocSm fun x t => K x t * K' x t := by
  intro x₀
  obtain ⟨G, _, _, ρ, c, F, hρ, hc, hF, he⟩ := h x₀
  obtain ⟨G', _, _, ρ', c', F', hρ', hc', hF', he'⟩ := h' x₀
  refine ⟨G × G', inferInstance, inferInstance, fun x => (ρ x, ρ' x), fun x => c x * c' x,
    fun g t => F g.1 t * F' g.2 t, hρ.prodMk hρ', hc.mul hc', ?_, ?_⟩
  · exact (hF.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)).mul
      (hF'.comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd))
  · filter_upwards [he, he'] with x hx hx' t
    rw [hx, hx']
    ring

theorem LocSm.comp {Y : Type} [TopologicalSpace Y] {K : X → E → ℂ} (h : LocSm K) {φ : Y → X} (hφ : Continuous φ) :
    LocSm fun y => K (φ y) := by
  intro y₀
  obtain ⟨G, _, _, ρ, c, F, hρ, hc, hF, he⟩ := h (φ y₀)
  exact ⟨G, inferInstance, inferInstance, ρ ∘ φ, c ∘ φ, F, hρ.comp hφ.continuousAt, hc.comp hφ.continuousAt, hF,
    hφ.continuousAt.eventually he⟩

theorem LocSm.continuous_fderiv [FiniteDimensional ℝ E] {K : X → E → ℂ} (h : LocSm K) :
    Continuous fun p : X × E => _root_.fderiv ℝ (K p.1) p.2 :=
  continuous_clm_apply.2 fun y => (h.fderiv y).continuous

end Gen

variable {D : D7}

section Int

variable {m n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem hasFDerivAt_integral (v : VolM D m n) {K : Mx D m n → E → ℂ} (h : LocSm K)
    (hp : ∀ γ ∈ ratMx D m n, ∀ x t, K (γ + x) t = K x t) (t₀ : E) :
    Integrable (fun x => fderiv ℝ (K x) t₀) (v.μ.restrict v.𝓕) ∧
      HasFDerivAt (fun t => ∫ x in v.𝓕, K x t ∂v.μ) (∫ x in v.𝓕, fderiv ℝ (K x) t₀ ∂v.μ) t₀ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D m n
  have : BorelSpace (Mx D m n) := ⟨rfl⟩
  have hi := (ParCont.parCont D m n v E K h.continuous hp).1
  have hc : Continuous (Function.uncurry fun x t => ((‖fderiv ℝ (K x) t‖ : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp h.continuous_fderiv.norm
  obtain ⟨C, hC⟩ := (ParCont.parCont D m n v E _ hc fun γ hγ x t => by rw [funext (hp γ hγ x)]).2.2.1 t₀
  have : IsFiniteMeasure (v.μ.restrict v.𝓕) := ⟨by
    rw [Measure.restrict_apply_univ, v.covol.2.2]; exact ENNReal.one_lt_top⟩
  have hm : AEStronglyMeasurable (fun x => fderiv ℝ (K x) t₀) (v.μ.restrict v.𝓕) :=
    (h.continuous_fderiv.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  have hC' : ∀ᶠ t in 𝓝 t₀, ∀ x, ‖fderiv ℝ (K x) t‖ ≤ C := hC.mono fun t ht x => by simpa using ht x
  refine ⟨Integrable.of_bound hm C (Filter.Eventually.of_forall hC'.self_of_nhds), ?_⟩
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun t x => K x t) (F' := fun t x => fderiv ℝ (K x) t)
    (bound := fun _ => C) hC' (Filter.Eventually.of_forall fun t => (hi t).aestronglyMeasurable) (hi t₀) hm
    (Filter.Eventually.of_forall fun x t ht => ht x) (integrable_const C)
    (Filter.Eventually.of_forall fun x t _ => (h.differentiable x t).hasFDerivAt)

theorem contDiff_integral (v : VolM D m n) {K : Mx D m n → E → ℂ} (h : LocSm K)
    (hp : ∀ γ ∈ ratMx D m n, ∀ x t, K (γ + x) t = K x t) : ContDiff ℝ ∞ fun t => ∫ x in v.𝓕, K x t ∂v.μ := by
  rw [contDiff_infty]
  intro k
  induction k generalizing K with
  | zero => exact contDiff_zero.2 (ParCont.parCont D m n v E K h.continuous hp).2.1
  | succ k ih =>
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv_apply]
    refine ⟨fun t => (hasFDerivAt_integral v h hp t).2.differentiableAt, by simp, fun y => ?_⟩
    have e : (fun t => fderiv ℝ (fun t => ∫ x in v.𝓕, K x t ∂v.μ) t y) = fun t => ∫ x in v.𝓕, fderiv ℝ (K x) t y ∂v.μ := by
      funext t
      rw [(hasFDerivAt_integral v h hp t).2.fderiv, ContinuousLinearMap.integral_apply (hasFDerivAt_integral v h hp t).1]
    rw [e]
    exact ih (h.fderiv y) fun γ hγ x t => by rw [funext (hp γ hγ x)]

end Int

open GlobalTheory.DualPairCompare in

theorem locSm_theta {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (M : E →+ WO S T) (hM : Continuous M)
    (h0 : ∀ t, (M t).map (finPart D) = 0) : LocSm fun x t => f (x + M t) := by
  intro x₀
  have : IsTopologicalAddGroup (AE D) := inferInstance
  have : IsTopologicalAddGroup (WO S T) := Pi.topologicalAddGroup
  have : ContinuousSub (WO S T) := IsTopologicalAddGroup.to_continuousSub
  obtain ⟨co, c1, c2, c3⟩ := exists_coMat D T.rank S.rank
  obtain ⟨U, hU, hl⟩ := hf.level
  have hs : ContDiff ℝ ∞ fun p => f (x₀ + realMat D T.rank S.rank p) := (smoothAlong_iff f).1 hf.smooth x₀
  let N := (co.comp M).toRealLinearMap (c1.comp hM)
  have hN : ∀ t, realMat D T.rank S.rank (N t) = M t := fun t => c3 _ (h0 t)
  have hd : Continuous fun x : WO S T => x - x₀ := continuous_id.sub continuous_const
  let a : WO S T → WO S T := fun x => (x - x₀) - realMat D T.rank S.rank (co (x - x₀))
  have ha : Continuous a := hd.sub ((continuous_realMat D _ _).comp (c1.comp hd))
  have hev : ∀ᶠ x in 𝓝 x₀, a x ∈ U := (hU.preimage ha).mem_nhds (show a x₀ ∈ U by simp [a])
  have key : ∀ x, a x ∈ U → ∀ p, f (x₀ + realMat D T.rank S.rank p + a x) =
      ψ (-symplOH S T x₀ (a x)) * f (x₀ + realMat D T.rank S.rank p) := by
    intro x hx p
    have h1 := congrFun (hl _ hx (c2 _)) (x₀ + realMat D T.rank S.rank p)
    have h2 : symplOH S T (realMat D T.rank S.rank p) (a x) = 0 :=
      GlobalTheory.FinTranslate.symplOH_real_fin (c2 _) (Matrix.ext fun i j => finPart_realPt D (p i j))
    rw [heisO, GlobalTheory.FinTranslate.symplOH_add_left, h2, add_zero] at h1
    rw [← h1, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
  have dec : ∀ x t, x + M t = x₀ + realMat D T.rank S.rank (co (x - x₀) + N t) + a x := by
    intro x t
    rw [map_add, hN]
    simp only [a]
    abel
  have hF : ContDiff ℝ ∞ (Function.uncurry fun p t => f (x₀ + realMat D T.rank S.rank (p + N t))) :=
    hs.comp (contDiff_fst.add (N.contDiff.comp contDiff_snd))
  by_cases hz : ∀ p, f (x₀ + realMat D T.rank S.rank p) = 0
  · refine ⟨_, inferInstance, inferInstance, fun x => co (x - x₀), fun _ => 0, _, (c1.comp hd).continuousAt,
      continuousAt_const, hF, ?_⟩
    filter_upwards [hev] with x hx t
    rw [dec, key x hx, hz, mul_zero, mul_zero]
  · obtain ⟨p, hp⟩ := not_forall.1 hz
    refine ⟨_, inferInstance, inferInstance, fun x => co (x - x₀),
      fun x => f (x₀ + realMat D T.rank S.rank p + a x) / f (x₀ + realMat D T.rank S.rank p), _, (c1.comp hd).continuousAt,
      ((hf.cont.comp (continuous_const.add ha)).div_const _).continuousAt, hF, ?_⟩
    filter_upwards [hev] with x hx t
    rw [dec, key x hx, key x hx, mul_div_cancel_right₀ _ hp]

theorem extL_fin {V₀ A L S : HSp D} (o : OrthDec V₀ A L) (u : WO A S) (h : u.map (finPart D) = 0) :
    (ContrComb.extL (S := S) o u).map (finPart D) = 0 := by
  rw [ContrComb.extL_apply, OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero]
  rw [Matrix.map_mul, h, Matrix.zero_mul]

theorem extR_fin {V₀ A L S : HSp D} (o : OrthDec V₀ A L) (u : WO S A) (h : u.map (finPart D) = 0) :
    (ContrComb.extR (S := S) o u).map (finPart D) = 0 := by
  rw [ContrComb.extR_apply, OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero]
  rw [Matrix.map_mul, h, Matrix.mul_zero]

theorem integrand_periodic {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) (S : HSp D)
    {ψ : AddChar (AF D.host.F) ℂ} {f₁ : WO B.V₀ S → ℂ} {f₂ : WO S B'.V₀ → ℂ} (h₁ : IsThetaFunO ψ B.V₀ S f₁)
    (h₂ : IsThetaFunO ψ S B'.V₀ f₂) (u : WO B.A S) (v : WO S B'.A) (γ : WO S B'.L) (hγ : γ ∈ ratMx D B'.L.rank S.rank)
    (a : WO S B'.L) :
    f₂ ((B'.o.resT S).symm (v, γ + a)) * f₁ ((B.o.resS S).symm (u, l.κ S (γ + a))) =
      f₂ ((B'.o.resT S).symm (v, a)) * f₁ ((B.o.resS S).symm (u, l.κ S a)) := by
  have hτ := (GlobalTheory.Unf.LinkGram.link_gram D ρ B B'.L B'.ζ B'.line l).1
  obtain ⟨hadd, -, hrat, -, hsym, -⟩ := GlobalTheory.LinkKappa.kappa_props D B.L B'.L S l.τ 1 hτ (l.κ S) (fun _ => rfl)
  have hκ : symplOH B.L S (l.κ S γ) (l.κ S a) = -symplOH S B'.L γ a := by
    rw [symplOH, symplOH, hsym, Int.cast_one, one_mul, mul_neg]
  have r2 : (B'.o.resT S).symm (0, γ) ∈ ratMx D B'.V₀.rank S.rank := by
    refine (B'.o.mem_ratL_resT S _).2 ?_
    rw [AddEquiv.apply_symm_apply]
    exact ⟨zero_mem _, hγ⟩
  have r1 : (B.o.resS S).symm (0, l.κ S γ) ∈ ratMx D S.rank B.V₀.rank := by
    refine (B.o.mem_ratL_resS S _).2 ?_
    rw [AddEquiv.apply_symm_apply]
    exact ⟨zero_mem _, hrat γ hγ⟩
  obtain ⟨γ₂, hγ₂⟩ := r2
  obtain ⟨γ₁, hγ₁⟩ := r1
  have q2 := h₂.quasi γ₂ ((B'.o.resT S).symm (v, a))
  have q1 := h₁.quasi γ₁ ((B.o.resS S).symm (u, l.κ S a))
  have e2 : ratW B'.V₀ S γ₂ = (B'.o.resT S).symm (0, γ) := hγ₂
  have e1 : ratW S B.V₀ γ₁ = (B.o.resS S).symm (0, l.κ S γ) := hγ₁
  rw [e2, ← map_add, Prod.mk_add_mk, zero_add, B'.o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
    ContrComb.symplOH_zero_left, zero_add] at q2
  rw [e1, ← map_add, Prod.mk_add_mk, zero_add, B.o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
    ContrComb.symplOH_zero_left, zero_add, hκ, neg_neg] at q1
  rw [hadd, q2, q1]
  have e : ψ (-symplOH S B'.L γ a) * ψ (symplOH S B'.L γ a) = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  linear_combination (f₂ ((B'.o.resT S).symm (v, a)) * f₁ ((B.o.resS S).symm (u, l.κ S a))) * e

theorem contr_isBiSmooth : ∀ (D : D7) (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (ψ : AddChar (AF D.host.F) ℂ) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ S f₁ → IsThetaFunO ψ S B'.V₀ f₂ → IsBiSmooth (contr l S vL f₁ f₂) := by
  intro D ρ σ B B' l S vL ψ f₁ f₂ h₁ h₂ n L L' hL hL' h0 h0' u v
  have hτ := (GlobalTheory.Unf.LinkGram.link_gram D ρ B B'.L B'.ζ B'.line l).1
  have hκ : Continuous (l.κ S) := (GlobalTheory.LinkKappa.kappa_props D B.L B'.L S l.τ 1 hτ (l.κ S) (fun _ => rfl)).2.1
  have k₁ := (locSm_theta h₁ ((ContrComb.extL B.o).comp L) ((ContrComb.continuous_extL B.o).comp hL)
    fun t => extL_fin B.o _ (h0 t)).comp (φ := fun w : WO S B'.L => (B.o.resS S).symm (u, l.κ S w))
    ((B.o.continuous_resS_symm S).comp (continuous_const.prodMk hκ))
  have k₂ := (locSm_theta h₂ ((ContrComb.extR B'.o).comp L') ((ContrComb.continuous_extR B'.o).comp hL')
    fun t => extR_fin B'.o _ (h0' t)).comp (φ := fun w : WO S B'.L => (B'.o.resT S).symm (v, w))
    ((B'.o.continuous_resT_symm S).comp (continuous_const.prodMk continuous_id))
  have k : LocSm fun (w : WO S B'.L) (t : Fin n → ℝ) =>
      f₂ ((B'.o.resT S).symm (v + L' t, w)) * f₁ ((B.o.resS S).symm (u + L t, l.κ S w)) := by
    convert k₂.mul k₁ using 5 with w t w t
    · rw [AddMonoidHom.comp_apply, ContrComb.extR_apply, ← map_add, Prod.mk_add_mk, add_zero]
    · rw [AddMonoidHom.comp_apply, ContrComb.extL_apply, ← map_add, Prod.mk_add_mk, add_zero]
  exact contDiff_integral vL k fun γ hγ w t => integrand_periodic l S h₁ h₂ _ _ γ hγ w

end GlobalTheory.ContrSmooth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainChartParahoricEqLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section

namespace GlobalTheory.ChartLevel

variable {D : D7}

open ValuativeRel in
theorem val_lt_one_iff {v : HeightOneSpectrum (𝓞 D.host.F)} (x : Fv D.host.F v) :
    valuation (Fv D.host.F v) x < 1 ↔ Valued.v x < 1 := by
  have h : valuation (Fv D.host.F v) 1 ≤ valuation (Fv D.host.F v) x ↔ Valued.v (1 : Fv D.host.F v) ≤ Valued.v x := by
    haveI : (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    rw [← Valuation.Compatible.vle_iff_le (v := valuation (Fv D.host.F v)),
      Valuation.Compatible.vle_iff_le (v := (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ))))]
  rw [map_one, map_one] at h
  rw [← not_le, ← not_le, h]

set_option maxHeartbeats 1000000 in

theorem redFn_entry_eq_zero_iff {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {g : GA D V}
    (hS : Lev.finE V g ∈ St β) {v : HeightOneSpectrum (𝓞 D.host.F)} {φ : SplitProj D v} {PP : Pl D.host.E}
    (hφ : IsProjAt φ PP) (a b : Fin V.rank) :
    (redFn β PP (Lev.finE V g)).val a b = 0 ↔ Valued.v ((grpCo φ V (frCo φ β) g).val a b) < 1 := by
  obtain ⟨⟨r, -, hr0, -, hN⟩, -⟩ := GlobalTheory.PlaceRed.red_dict D v φ PP hφ
  obtain ⟨y, hy⟩ := hS
  rw [← hy, redFn_frGL]
  obtain ⟨h, hrd⟩ := hN _ (y.val a b).2
  have e1 : (Formalism.UG.bc (resS D.host.F PP) y).val a b = resS D.host.F PP (y.val a b) := rfl
  rw [e1, ← hrd, hr0]
  have hi : intGL D.host.F D.host.E _ y = β⁻¹ * Lev.finE V g * β := by
    rw [← hy]
    simp [frGL, MulAut.conj_apply]
    group
  have hx : Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ) (Lev.finE V g) =
      Matrix.GeneralLinearGroup.map (rdA φ) (Formalism.L2.Theta.matHom V g) := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    show GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ ((Lev.finE V g).val i j) = rdA φ ((Formalism.L2.Theta.matHom V g).val i j)
    exact GlobalTheory.SplitProjChart.rdE_toEAf φ _
  have hm : Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ) (β⁻¹ * Lev.finE V g * β) = grpCo φ V (frCo φ β) g := by
    rw [MonoidHom.map_mul, MonoidHom.map_mul, MonoidHom.map_inv, hx]
    rfl
  have key : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ ((y.val a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) =
      (grpCo φ V (frCo φ β) g).val a b := by
    rw [← hm, ← hi]
    rfl
  change Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ ((y.val a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D)) < 1 ↔ _
  rw [key]

end GlobalTheory.ChartLevel

namespace GlobalTheory.ChartLevel

variable {D : D7}

theorem eps_inr_ge {r n : ℕ} {B : Type} (ε : Fin r ⊕ B ≃ Fin n) (hε : ∀ i, (ε (.inl i) : ℕ) = i) (i : B) :
    r ≤ (ε (.inr i) : ℕ) := by
  by_contra h
  rw [not_le] at h
  have e : ε (.inl ⟨_, h⟩) = ε (.inr i) := Fin.ext (hε _)
  exact Sum.inl_ne_inr (ε.injective e)

theorem twoBlockIndex_lt_iff_lowerLeft {r n : ℕ} (a b : Fin n) : blk2 r b < blk2 r a ↔ (b : ℕ) < r ∧ r ≤ (a : ℕ) := by
  unfold blk2
  by_cases ha : (a : ℕ) < r <;> by_cases hb : (b : ℕ) < r <;> simp [ha, hb] <;> omega

theorem lower_iff {r n : ℕ} {B K : Type} (ε : Fin r ⊕ B ≃ Fin n) (hε : ∀ i, (ε (.inl i) : ℕ) = i) (M : Fin n → Fin n → K)
    (P : K → Prop) : (∀ a b : Fin n, blk2 r b < blk2 r a → P (M a b)) ↔ ∀ i j, P (M (ε (.inr i)) (ε (.inl j))) := by
  constructor
  · intro h i j
    refine h _ _ ((twoBlockIndex_lt_iff_lowerLeft _ _).2 ⟨?_, eps_inr_ge ε hε i⟩)
    rw [hε]; exact j.2
  · intro h a b hab
    rw [twoBlockIndex_lt_iff_lowerLeft] at hab
    obtain ⟨p, rfl⟩ := ε.surjective a
    obtain ⟨q, rfl⟩ := ε.surjective b
    rcases p with p | p
    · exfalso; rw [hε] at hab; have := p.2; omega
    rcases q with q | q
    · exact h p q
    · exfalso; have := eps_inr_ge ε hε q; omega

end GlobalTheory.ChartLevel

open GlobalTheory.ChartLevel in

theorem GlobalTheory.chart_level_iff : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ j ≤ D.R.m, ∀ s : PiLocalization₂ D, IsStage c w j s → ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ ι, IsChart s j φ ι → ∀ y, ι y ∈ Lev.levG s.V s.β s.L ↔ y ∈ parahoric (Fv D.host.F v) (Fin D.R.r) (Blocks j D.R.t) := by
  intro D c w hw j hj s hs PP hPP v φ hφ ι hι y
  obtain ⟨hr, hL, hfl⟩ := hs
  have hsd : IsSelfDualC s.V s.Λ := hfl.selfDual
  have hfr : IsFrame s.β s.Λ := hfl.frame
  obtain ⟨e, he⟩ := GlobalTheory.ChartSplitIso.exists_equiv_emb D s j v φ ι hsd hfr hι
  have hstab := GlobalTheory.T.parahoric_chart_integral_GL_eq_lattice_stabilizer D s j v φ ι hsd hfr hι e he y
  have hv : v = PP.under (𝓞 D.host.F) := (GlobalTheory.PlaceProjAt.under_resCard D v φ PP hφ).1
  obtain ⟨ε, hε, hch⟩ := hι
  have hSt : Lev.finE s.V (ι y) ∈ St s.β ↔ y ∈ GlobalTheory.SplitWeil.KO (Fv D.host.F v) _ := by
    rw [GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D s.V s.β s.Λ hfr, he y, ← hstab]
    constructor
    · intro h
      have := h v
      rwa [GlobalTheory.AdelicU.proj_emb_self] at this
    · intro h u
      by_cases hu : u = v
      · subst hu
        rw [GlobalTheory.AdelicU.proj_emb_self]
        exact h
      · rw [GlobalTheory.AdelicU.proj_emb_ne _ _ hu]
        exact one_mem _
  have hPc : PP ∈ c.Pg := by
    classical
    rw [hw.union]; exact Finset.mem_union_right _ hPP
  have hone : ∀ PP', PP' ∈ c.Pg → PP' ≠ PP → Lev.finE s.V (ι y) ∈ St s.β →
      redFn s.β PP' (Lev.finE s.V (ι y)) = 1 := by
    intro PP' hP' hne hS
    refine GlobalTheory.ChainOnto.RedOne.redFn_eq_one D s.V s.β _ PP' hS ?_
    have hu : PP'.under (𝓞 D.host.F) ≠ v := by
      intro h
      exact hne (GlobalTheory.LevelPlaces.injOn_under D c hw.com hP' hPc (h.trans hv))
    rw [he y]
    exact GlobalTheory.AdelicU.proj_emb_ne _ _ hu _
  have hred : Lev.finE s.V (ι y) ∈ St s.β → (redFn s.β PP (Lev.finE s.V (ι y)) ∈ blockTri (blk2 D.R.r) ↔
      ∀ i j', ValuativeRel.valuation (Fv D.host.F v) (y.1 (.inr i) (.inl j')) < 1) := by
    intro hS
    rw [mem_blockTri]
    have h1 : ∀ a b, (redFn s.β PP (Lev.finE s.V (ι y))).val a b = 0 ↔
        Valued.v ((grpCo φ s.V (frCo φ s.β) (ι y)).val a b) < 1 := redFn_entry_eq_zero_iff hS hφ
    simp only [h1]
    rw [lower_iff ε hε (fun a b => (grpCo φ s.V (frCo φ s.β) (ι y)).val a b) (fun x => Valued.v x < 1)]
    have hy : ∀ p q, (grpCo φ s.V (frCo φ s.β) (ι y)).val (ε p) (ε q) = y.1 p q := fun p q => by
      have := congrFun (congrFun (hch y).2 p) q
      simpa using this
    simp only [hy, val_lt_one_iff]
  have hG : ι y ∈ GfC s.V := by
    rw [he y]; exact GlobalTheory.ChainOnto.LevelFacts.emb_mem_GfC _ _ _
  have hsub : ∀ PP', PP' ∈ w.Pg ∨ PP' ∈ w.Q → PP' ∈ c.Pg := by
    classical
    intro PP' h
    rw [hw.union]
    exact Finset.mem_union.2 h
  rw [GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.mem_parahoric, ← hSt, hL, Lev.levG, Lev.mem_levA, mem_lev, mem_parLev]
  constructor
  · rintro ⟨-, ⟨-, hS, -, hQ⟩, -⟩
    exact ⟨hS, (hred hS).1 (hQ PP hPP)⟩
  · rintro ⟨hS, hlow⟩
    have hPg : ∀ PP' ∈ w.Pg, redFn s.β PP' (Lev.finE s.V (ι y)) = 1 := by
      intro PP' hP'
      refine hone PP' (hsub _ (Or.inl hP')) ?_ hS
      rintro rfl
      exact Finset.disjoint_left.1 hw.disj hP' hPP
    refine ⟨hG, ⟨GlobalTheory.LevSplit.finE_mem_UA s.V _, hS, ?_, ?_⟩, ?_⟩
    · intro PP' hP'
      rw [hPg PP' hP']
      exact one_mem _
    · intro PP' hP'
      by_cases e : PP' = PP
      · subst e
        exact (hred hS).2 hlow
      · rw [hone PP' (hsub _ (Or.inr hP')) e hS]
        exact one_mem _
    · have h1 : rTup s.β (Lev.datY s.V.rank D.R.r D.R.t j hr w.Pg w.Q (LevelP.triv w.Pg D.R.r ℂ) w.chi w.ξ Lev.Frm.B)
          (Lev.finE s.V (ι y)) = 1 := by
        funext PP'
        show upperLeftBlock hr (redFn s.β PP'.1 (Lev.finE s.V (ι y))) = 1
        rw [hPg PP'.1 PP'.2]
        exact blockDiagonalExtendByOnePrimeField_one _ _
      rw [h1]
      exact one_mem _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumRealEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealEqWeil

theorem weilDatum_realEq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT χS' χT' : (AE D)ˣ →* Circle) (om om' : Om S T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T χS' χT' om' → (∀ τ, ∃ e : ℚ, HasInfExp D χS τ e ∧ HasInfExp D χS' τ e) → (∀ τ, ∃ e : ℚ, HasInfExp D χT τ e ∧ HasInfExp D χT' τ e) → ∀ a ∈ GinfC S, ∀ b ∈ GinfC T, ∀ f, IsThetaFunO ψ S T f → om (a, b) f = om' (a, b) f := by
  intro D ψ S T χS χT χS' χT' om om' hW hW' hS hT a ha b hb f hf
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D

  have eS : ∀ τ, HasInfExp D (χS' * χS⁻¹) τ ((0 : ℤ) : ℚ) := fun τ => by
    obtain ⟨e, h1, h2⟩ := hS τ
    simpa using GlobalTheory.Chain.hasInfExp_div h2 h1
  have eT : ∀ τ, HasInfExp D (χT' * χT⁻¹) τ ((0 : ℤ) : ℚ) := fun τ => by
    obtain ⟨e, h1, h2⟩ := hT τ
    simpa using GlobalTheory.Chain.hasInfExp_div h2 h1
  obtain ⟨om'', hW'', hmv⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D ψ hW.std S T χS χT (χS' * χS⁻¹) (χT' * χT⁻¹) om hW
    (GlobalTheory.WeilVacChar.hecke_mul_inv hW'.hecS hW.hecS) (GlobalTheory.WeilVacChar.hecke_mul_inv hW'.hecT hW.hecT)
    (GlobalTheory.WeilVacChar.resEta_mul_inv hW'.resS hW.resS) (GlobalTheory.WeilVacChar.resEta_mul_inv hW'.resT hW.resT)
  rw [GlobalTheory.WeilVacChar.mul_mul_inv_cancel, GlobalTheory.WeilVacChar.mul_mul_inv_cancel] at hW''
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.OneMapRef.RealMove.exists_root hθ S (GlobalTheory.RealPairBound.gramAt_det_ne D S) a ha
  obtain ⟨y, hy, hyv⟩ := GlobalTheory.OneMapRef.RealMove.exists_root hθ T (GlobalTheory.RealPairBound.gramAt_det_ne D T) b hb
  have x1 : (χT' * χT⁻¹) x = 1 := by
    apply Circle.coe_injective
    rw [hxv _ (fun _ => 0) eT]
    simp
  have y1 : (χS' * χS⁻¹) y = 1 := by
    apply Circle.coe_injective
    rw [hyv _ (fun _ => 0) eS]
    simp
  have h1 := hmv a b x y hx hy
  rw [x1, y1, inv_one, one_mul, Circle.coe_one, one_smul] at h1
  rw [← h1]
  exact GlobalTheory.WeilUniq.weilDatum_unique D ψ hW.std S T χS' χT' om'' om' hW'' hW' (a, b) f hf

end GlobalTheory.RealEqWeil
end

