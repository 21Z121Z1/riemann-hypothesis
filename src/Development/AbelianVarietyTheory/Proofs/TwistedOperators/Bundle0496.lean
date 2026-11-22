import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1646
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0079
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0481
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0486
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0487
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0453
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0200
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0422
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0409
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0423
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0448
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0105
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0343
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0186
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionOpenStabilizer
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilLevel

theorem stab : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ (N : AddSubgroup (WO S T)) (K : Subgroup (GA D T)), N ≤ U ∧ IsOpen (K : Set (GA D T)) ∧ (∀ x : WO S T, ∃ γ ∈ ratL T S, ∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T (x - γ) l) = 1) ∧ (∀ k ∈ K, k ∈ GfC T → ∀ u ∈ N, u.map (infPart D) = 0 → actO S T 1 k u ∈ N ∧ (actO S T 1 k u).map (infPart D) = 0) ∧ (∀ k ∈ K, k ∈ GfC T → ∀ w : WO S T, (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) → actO S T 1 k w - w ∈ N ∧ (actO S T 1 k w - w).map (infPart D) = 0 ∧ ψ (symplOH S T w (actO S T 1 k w - w)) = 1) := GlobalTheory.T.exists_lattice_level_open_stabilizer_unitary
theorem prodId : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (N : AddSubgroup (WO S T)) (M : Module.End ℂ (WO S T → ℂ)), (∀ f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → IsThetaFunO ψ S T (M f) ∧ ∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u (M f) = M f) → (∀ w f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) → M (heisO ψ S T w f) = heisO ψ S T w (M f)) → (∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) → ∀ f g, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) → ∀ x, M f x * star (M g x) = f x * star (g x) := GlobalTheory.T.thetaFunction_prod_conj_eq_of_heisenbergFixed
theorem openKer : ∀ {D : D7} (T : HSp D) (K : Subgroup (GA D T)), IsOpen (K : Set (GA D T)) → ∀ F : GA D T → ℂ, Continuous F → F 1 = 1 → (∀ a ∈ K, a ∈ GfC T → ∀ b ∈ K, b ∈ GfC T → F (a * b) = F a * F b) → ∃ U : Subgroup (GA D T), IsOpen (U : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC T → F k = 1 := GlobalTheory.T.exists_open_eq_one_of_continuous_mul_finitePoints

theorem scalar_of_prod {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (hψ : IsStdChar D ψ (-1))
    (N : AddSubgroup (WO S T)) (M : Module.End ℂ (WO S T → ℂ))
    (hAR : ∀ x : WO S T, ∃ γ ∈ ratL T S, ∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T (x - γ) l) = 1)
    (hM : ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → IsThetaFunO ψ S T (M f))
    (hc : ∀ w f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) →
      M (heisO ψ S T w f) = heisO ψ S T w (M f))
    (hp : ∀ f g, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) →
      ∀ x, M f x * star (M g x) = f x * star (g x)) :
    ∃ c : ℂ, ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → M f = c • f := by
  obtain ⟨hth, hcomp, -⟩ := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  obtain ⟨l1, l2, l3, l4, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  have hunit : ∀ a, ψ a * star (ψ a) = 1 := fun a => by
    have h : ‖ψ a‖ = 1 := hψ.1.2.1 a
    rw [Complex.star_def, Complex.mul_conj', h]; simp
  have skew : ∀ x y : WO S T, symplOH S T y x = -symplOH S T x y := fun x y => by
    have := l3 (x + y)
    rw [l1, l2, l2, l3, l3] at this
    linear_combination this

  have hfix : ∀ w g, (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) → (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) →
      (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u (heisO ψ S T w g) = (heisO ψ S T w g)) := by
    intro w g hg hw u hu hu0
    have e1 := hcomp u w g
    have e2 := hcomp w u g
    rw [hg u hu hu0] at e2
    rw [e1, add_comm u w]
    have hs : ψ (symplOH S T u w) = ψ (symplOH S T w u) := by
      have h1 := hw u hu hu0
      rw [← l4] at h1
      have h2 : ψ (symplOH S T w u) * ψ (symplOH S T w u) = 1 := by
        rw [← AddChar.map_add_eq_mul]; exact h1
      rw [skew w u, AddChar.map_neg_eq_inv]
      exact inv_eq_of_mul_eq_one_right h2
    rw [hs, e2]
  by_cases h0 : ∃ f₀ x₀, IsThetaFunO ψ S T f₀ ∧ (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f₀ = f₀) ∧ f₀ x₀ ≠ 0
  · obtain ⟨f₀, x₀, hf₀, hf₀N, hx₀⟩ := h0
    have h1 := hp f₀ f₀ hf₀ hf₀N hf₀ hf₀N x₀
    have hn1 : ‖M f₀ x₀‖ = ‖f₀ x₀‖ := by
      have := congrArg norm h1
      rw [norm_mul, norm_mul, norm_star, norm_star] at this
      exact (mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).1 this
    have hy' : M f₀ x₀ ≠ 0 := by
      rw [← norm_ne_zero_iff, hn1]; exact norm_ne_zero_iff.2 hx₀
    have hs : star (M f₀ x₀) ≠ 0 := star_ne_zero.2 hy'
    refine ⟨star (f₀ x₀) / star (M f₀ x₀), fun f hf hfN => funext fun x => ?_⟩
    obtain ⟨γ, hγ, hA⟩ := hAR (x₀ - x)
    set w := x₀ - x - γ with hw
    have hg := hth w f₀ hf₀
    have hgN := hfix w f₀ hf₀N hA
    have h2 := hp f (heisO ψ S T w f₀) hf hfN hg hgN x
    rw [hc w f₀ hf₀ hf₀N hA] at h2
    obtain ⟨δ, hδ⟩ := (ratL T S).neg_mem hγ
    have hxw : x + w = ratW T S δ + x₀ := by
      have hδ' : ratW T S δ = -γ := hδ
      rw [hδ', hw]; abel
    simp only [heisO, hxw] at h2
    rw [hf₀.quasi δ x₀, (hM f₀ hf₀ hf₀N).quasi δ x₀] at h2
    rw [star_mul', star_mul', star_mul', star_mul'] at h2
    have h3 : M f x * star (M f₀ x₀) = f x * star (f₀ x₀) := by
      linear_combination (ψ (symplOH S T x w) * ψ (-symplOH S T (ratW T S δ) x₀)) * h2
        - (M f x * star (M f₀ x₀) - f x * star (f₀ x₀)) * hunit (symplOH S T x w)
        - (M f x * star (M f₀ x₀) - f x * star (f₀ x₀)) * ψ (symplOH S T x w) * star (ψ (symplOH S T x w))
          * hunit (-symplOH S T (ratW T S δ) x₀)
    rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hs, h3, mul_comm]
  · refine ⟨0, fun f hf hfN => ?_⟩
    have : f = 0 := funext fun y => by
      by_contra hy
      exact h0 ⟨f, y, hf, hfN, hy⟩
    rw [this, map_zero, smul_zero]

theorem weil_level : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (f : WO S T → ℂ), GlobalTheory.FunPr.Hypotheses₂ → IsWeilDatumO ψ S T χS χT om → IsThetaFunO ψ S T f → ∃ U : Subgroup (GA D T), IsOpen (U : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC T → om (1, k) f = f := by
  intro D ψ S T χS χT om f _ hW hf
  have hψ := hW.std
  obtain ⟨U, hUo, hU⟩ := hf.level
  obtain ⟨N, K, hNU, hKo, hAR, hKN, hKA⟩ := stab ψ S T hψ U hUo
  have hfN : ∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f := fun u hu h0 => hU u (hNU hu) h0
  obtain ⟨-, hcomp, -⟩ := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  have hMV : ∀ k ∈ K, k ∈ GfC T → ∀ g, IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) →
      IsThetaFunO ψ S T (om (1, k) g) ∧ ∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u (om (1, k) g) = om (1, k) g := by
    intro k hk hkf g hg hgN
    refine ⟨hW.om_pres _ g hg, fun u hu hu0 => ?_⟩
    obtain ⟨h1, h2⟩ := hKN k⁻¹ (K.inv_mem hk) ((GfC T).inv_mem hkf) u hu hu0
    have e := hW.om_heis 1 k (actO S T 1 k⁻¹ u) g hg
    have e2 := GlobalTheory.AdelicLatMove.actO_actO_inv S T 1 k u
    rw [inv_one] at e2
    rw [e2, hgN _ h1 h2] at e
    exact e.symm
  have hMC : ∀ k ∈ K, k ∈ GfC T → ∀ w g, IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) →
      (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) →
      om (1, k) (heisO ψ S T w g) = heisO ψ S T w (om (1, k) g) := by
    intro k hk hkf w g hg hgN hw
    obtain ⟨d1, d2, d3⟩ := hKA k hk hkf w hw
    have e := hcomp w (actO S T 1 k w - w) (om (1, k) g)
    rw [(hMV k hk hkf g hg hgN).2 _ d1 d2, d3, one_smul, add_sub_cancel] at e
    rw [hW.om_heis 1 k w g hg, e]
  have hsc : ∀ k ∈ K, k ∈ GfC T → ∃ c : ℂ, ∀ g, IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) → om (1, k) g = c • g := by
    intro k hk hkf
    exact scalar_of_prod hψ N (om (1, k)) hAR (fun g hg hgN => (hMV k hk hkf g hg hgN).1) (hMC k hk hkf)
      (prodId ψ S T hψ N (om (1, k)) (hMV k hk hkf) (hMC k hk hkf)
        (fun μ 𝓕 hμ h𝓕 g hg _ => hW.om_unit μ 𝓕 hμ h𝓕 (1, k) g hg))
  by_cases hf0 : ∃ x₀, f x₀ ≠ 0
  · obtain ⟨x₀, hx₀⟩ := hf0
    let F : GA D T → ℂ := fun k => om (1, k) f x₀ / f x₀
    have hFc : Continuous F :=
      ((hW.om_cont f hf x₀).comp (continuous_const.prodMk continuous_id)).div_const _
    have hF1 : F 1 = 1 := by
      show om (1, 1) f x₀ / f x₀ = 1
      rw [show ((1, 1) : GA D S × GA D T) = 1 from rfl, map_one, Module.End.one_apply, div_self hx₀]
    have hFc' : ∀ k ∈ K, k ∈ GfC T → ∀ c : ℂ, (∀ g, IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) → om (1, k) g = c • g) →
        F k = c := by
      intro k hk hkf c hc
      show om (1, k) f x₀ / f x₀ = c
      rw [hc f hf hfN, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hx₀, mul_one]
    have hFm : ∀ a ∈ K, a ∈ GfC T → ∀ b ∈ K, b ∈ GfC T → F (a * b) = F a * F b := by
      intro a ha haf b hb hbf
      obtain ⟨ca, hca⟩ := hsc a ha haf
      obtain ⟨cb, hcb⟩ := hsc b hb hbf
      rw [hFc' a ha haf ca hca, hFc' b hb hbf cb hcb]
      show om (1, a * b) f x₀ / f x₀ = ca * cb
      rw [show ((1, a * b) : GA D S × GA D T) = (1, a) * (1, b) by simp, map_mul, Module.End.mul_apply,
        hcb f hf hfN, map_smul, hca f hf hfN, smul_smul, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hx₀,
        mul_one, mul_comm]
    obtain ⟨V, hVo, hV⟩ := openKer T K hKo F hFc hF1 hFm
    refine ⟨V ⊓ K, hVo.inter hKo, fun k hk hkf => ?_⟩
    obtain ⟨c, hc⟩ := hsc k hk.2 hkf
    have h1 : c = 1 := by rw [← hFc' k hk.2 hkf c hc]; exact hV k hk.1 hkf
    rw [hc f hf hfN, h1, one_smul]
  · push_neg at hf0
    have : f = 0 := funext hf0
    refine ⟨⊤, isOpen_univ, fun k _ _ => ?_⟩
    rw [this, map_zero]

end GlobalTheory.WeilLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftLowerTowerVanishing
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.ChainFr GlobalTheory.Size GlobalTheory.Grow GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift
open scoped ENNReal NNReal

namespace GlobalTheory.LowVanishObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Kernel

variable {V W : HSp D} (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (g : GA D V) (h : GA D W)

theorem thetaKO_zero : thetaKO ω g h 0 = 0 := by
  simp [thetaKO]

theorem thetaKO_add (f f' : WO V W → ℂ) : thetaKO ω g h (f + f') = thetaKO ω g h f + thetaKO ω g h f' := by
  simp [thetaKO]

theorem thetaKO_sub (f f' : WO V W → ℂ) : thetaKO ω g h (f - f') = thetaKO ω g h f - thetaKO ω g h f' := by
  simp [thetaKO]

theorem thetaKO_smul (c : ℂ) (f : WO V W → ℂ) : thetaKO ω g h (c • f) = c * thetaKO ω g h f := by
  simp [thetaKO]

end Kernel

theorem multT_apply_cusp {W : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel W S) (J : Set (GA D W))
    (χ : GA D W → ℂ) (F : SmT M →ₗ[ℂ] (GA D W → ℂ)) (hF : F ∈ MultT θ M J χ) (v : SmT M) :
    IsAutFunSm θ W (F v) ∧ IsCuspFun W (F v) := by
  have hT : IsMultMap θ M J χ (PiTensorProduct.lift.symm F) :=
    (GlobalTheory.MultMem.mem_mult_iff D θ W S M J χ _).1 ((mem_multT θ M J χ F).1 hF)
  have hFv : ∀ x, F x = PiTensorProduct.lift (PiTensorProduct.lift.symm F) x := fun x => by
    rw [LinearEquiv.apply_symm_apply]
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [hFv, LinearMap.map_smul, PiTensorProduct.lift.tprod]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_smul r (hT.aut x), GlobalTheory.MultMem.isCuspFun_smul r (hT.cusp x)⟩
  | add a b ha hb =>
    rw [map_add]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_add ha.1 hb.1,
      GlobalTheory.MultMem.isCuspFun_add ha.1.toIsAutFun hb.1.toIsAutFun ha.2 hb.2⟩

theorem liftInt_span_eq_zero {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} {Φ : GA D W → ℂ}
    (hI : ∀ f, IsThetaFunO ψ V W f → ∀ x, IntegrableOn (fun h => thetaKO ω x h f * Φ h) 𝓕 ν)
    {s : Set (WO V W → ℂ)} (hs : ∀ g ∈ s, IsThetaFunO ψ V W g ∧ Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0) :
    ∀ g ∈ Submodule.span ℂ s, IsThetaFunO ψ V W g ∧ Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0 := by
  intro g hg
  induction hg using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero =>
    refine ⟨GlobalTheory.OrientedHeis.theta_zero, ?_⟩
    funext x
    simp [Lift.liftInt, thetaKO_zero]
  | add a b _ _ ha hb =>
    refine ⟨GlobalTheory.OrientedHeis.theta_add ha.1 hb.1, ?_⟩
    funext x
    have h1 := congrFun ha.2 x
    have h2 := congrFun hb.2 x
    simp only [Lift.liftInt, Pi.zero_apply] at h1 h2 ⊢
    simp only [thetaKO_add, add_mul]
    rw [integral_add (hI a ha.1 x) (hI b hb.1 x), h1, h2, add_zero]
  | smul c a _ ha =>
    refine ⟨GlobalTheory.OrientedHeis.theta_smul c ha.1, ?_⟩
    funext x
    have h1 := congrFun ha.2 x
    simp only [Lift.liftInt, Pi.zero_apply] at h1 ⊢
    simp only [thetaKO_smul, mul_assoc]
    rw [integral_const_mul, h1, mul_zero]

theorem eq_zero_of_le_mul_pos {a K : ℝ≥0∞} (hK : K ≠ ∞) (h : ∀ δ : ℝ≥0∞, 0 < δ → a ≤ K * δ) : a = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
  rw [zero_add]
  rcases eq_or_ne K 0 with rfl | hK0
  · exact (h 1 one_pos).trans (by simp)
  · have hε' : (ε : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hε.ne'
    have := h (ε / K) (ENNReal.div_pos hε' hK)
    rwa [ENNReal.mul_div_cancel hK0 hK] at this

theorem liftInt_eq_zero_of_approx {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)}
    {cls : (GA D W → ℂ) → Prop} (hL : LiftLaws θ ψ ω ν 𝓕 cls) {Φ : GA D W → ℂ} (hΦ : cls Φ)
    {μ : Measure (WO V W)} {𝓓 : Set (WO V W)} (hμ : μ.IsAddHaarMeasure)
    (h𝓓 : IsAddFundamentalDomain (ratL W V) 𝓓 μ) {U : AddSubgroup (WO V W)} (hU : IsOpen (U : Set (WO V W)))
    {f : WO V W → ℂ} (hf : f ∈ GlobalTheory.Size.thetaLevel ψ V W U)
    (happ : ∀ (d : ℕ) (δ : ℝ≥0∞), 0 < δ → ∃ g ∈ GlobalTheory.Size.thetaLevel ψ V W U,
      Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0 ∧ sobO ψ θ μ 𝓓 d (f - g) < δ) :
    Lift.liftInt ν 𝓕 (thetaKO ω) f Φ = 0 := by
  obtain ⟨A, hA⟩ := hL.bound
  obtain ⟨d, hd⟩ := hA 0
  obtain ⟨C, hC⟩ := hd μ 𝓓 hμ h𝓓 U hU
  have hint : ∀ f', IsThetaFunO ψ V W f' → ∀ x,
      IntegrableOn (fun h => thetaKO ω x h f' * Φ h) 𝓕 ν := fun f' hf' x => by
    simpa [rTr] using hL.integ f' Φ hf' hΦ x 1
  have key : ∀ g ∈ GlobalTheory.Size.thetaLevel ψ V W U, Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0 →
      growthSob θ V 0 A (lift ω ν 𝓕 f Φ) ≤ C * sobO ψ θ μ 𝓓 d (f - g) * decayInt ν 𝓕 A Φ := by
    intro g hg hg0
    have hb := hC (f - g) (sub_mem hf hg) Φ hΦ
    have heq : lift ω ν 𝓕 (f - g) Φ = lift ω ν 𝓕 f Φ := by
      funext x
      have h0 := congrFun hg0 x
      simp only [lift, Lift.liftInt, Pi.zero_apply] at h0 ⊢
      simp only [thetaKO_sub, sub_mul]
      rw [integral_sub (hint f hf.1 x) (hint g hg.1 x), h0, sub_zero]
    rwa [heq] at hb
  have hdec := hL.decay_ne_top Φ hΦ A
  have hz : growthSob θ V 0 A (lift ω ν 𝓕 f Φ) = 0 := by
    refine eq_zero_of_le_mul_pos (K := C * decayInt ν 𝓕 A Φ) (ENNReal.mul_ne_top ENNReal.coe_ne_top hdec) ?_
    intro δ hδ
    obtain ⟨g, hg, hg0, hsm⟩ := happ d δ hδ
    calc growthSob θ V 0 A (lift ω ν 𝓕 f Φ)
        ≤ C * sobO ψ θ μ 𝓓 d (f - g) * decayInt ν 𝓕 A Φ := key g hg hg0
      _ ≤ C * δ * decayInt ν 𝓕 A Φ := by gcongr
      _ = C * decayInt ν 𝓕 A Φ * δ := by ring
  have hz' : growthSize V A (lift ω ν 𝓕 f Φ) = 0 := by simpa [growthSob] using hz
  unfold growthSize at hz'
  funext x
  have hx := ENNReal.ofReal_eq_zero.1 ((ENNReal.iSup_eq_zero.1 hz') x)
  have hpos : 0 < height V x ^ A := pow_pos (lt_of_lt_of_le one_pos ((height_laws V).1 x)) A
  rw [div_le_iff₀ hpos, zero_mul] at hx
  exact norm_le_zero_iff.1 hx

theorem lowVanish_obj : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.LowVanish D := by
  intro h1 h2 h3 D k i V' W M' θ ψ hθ hk hi hsig ω' hω' ν 𝓕 hν h𝓕 J χ F hF v f' hf'
  obtain ⟨χS, χT, hW, hexp⟩ := hω'
  have hLaws := GlobalTheory.Chain.LiftReg.liftProps_obj h3 D V' W θ ψ χS χT ω' hθ hW ν 𝓕 hν h𝓕
  have hcv := multT_apply_cusp θ M' J χ F hF v
  obtain ⟨A⟩ := (GlobalTheory.FrameExists.frame_exists_signCompat D V').1
  obtain ⟨μ, 𝓓, hcov⟩ := GlobalTheory.Size.exists_isCovolOne V' W
  have hstd : IsStdChar D ψ (-1) := hW.std
  obtain ⟨U, hU, hfU, happ⟩ :=
    GlobalTheory.FockDensity.fockDense D V' W A (Fr.ofModel M') θ ψ hstd hθ μ 𝓓 hcov f' hf'
  have hint : ∀ f, IsThetaFunO ψ V' W f → ∀ x, IntegrableOn (fun h => thetaKO ω' x h f * F v h) 𝓕 ν :=
    fun f hf x => by simpa [rTr] using hLaws.integ f (F v) hf hcv x 1
  refine liftInt_eq_zero_of_approx hLaws hcv (μ := μ) (𝓓 := 𝓓) hcov.1 hcov.2.1 hU hfU ?_
  intro d δ hδ
  obtain ⟨g, hg, hgU, hsm⟩ := happ d δ hδ
  refine ⟨g, hgU, ?_, hsm⟩
  refine (liftInt_span_eq_zero hint ?_ g hg).2
  rintro _ ⟨f₀, P, hvac, -, rfl⟩
  refine ⟨?_, ?_⟩
  · exact GlobalTheory.Chain.InnerSteps.theta_pureTensorO hstd hθ A.cart A.onb (Fr.ofModel M').cart
      (Fr.ofModel M').onb hvac.1 P
  · exact GlobalTheory.LowerMembers.lowVanishFock h1 h2 h3 D k i V' W M' θ ψ hθ hk hi hsig ω' ⟨χS, χT, hW, hexp⟩
      ν 𝓕 hν h𝓕 J χ F hF v A f₀ hvac P

end GlobalTheory.LowVanishObj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftPeriodsIsTameThetaFunctional
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.LiftTame

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem tame_congr (hψ : IsStdChar D ψ (-1)) {ℓ ℓ' : (WO S T → ℂ) → ℂ} (h : Tame ψ S T ℓ)
    (e : ∀ f, IsThetaFunO ψ S T f → ℓ' f = ℓ f) : Tame ψ S T ℓ' := by
  have hh : ∀ f, IsThetaFunO ψ S T f → ∀ w, ℓ' (heisO ψ S T w f) = ℓ (heisO ψ S T w f) := fun f hf w =>
    e _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w)
  refine ⟨fun f f' hf hf' => ?_, fun c f hf => ?_, fun f hf => ?_, fun f hf => ?_, fun f hf m _ α hα hI => ?_⟩
  · rw [e _ (GlobalTheory.WeilVacMove.isTheta_add hf hf'), e _ hf, e _ hf', h.add f f' hf hf']
  · rw [e _ (GlobalTheory.WeilVacMove.isTheta_smul c hf), e _ hf, h.smul c f hf]
  · simpa only [hh f hf] using h.cont f hf
  · simpa only [hh f hf] using h.bdd f hf
  · rw [e _ hI, h.sup f hf m α hα hI]
    simp only [hh f hf]

theorem finite_vol {V : HSp D} (v : GlobalTheory.Unf.Vol V) : IsFiniteMeasure (v.μ.restrict v.𝓕) := by
  have h : IntegrableOn (fun _ => (1 : ℝ)) v.𝓕 v.μ := by
    simpa using GlobalTheory.Size.integrableOn_inv_quotHeight_pow (V := V) 0 v.haar v.fund
  rcases (integrableOn_const_iff (by simp)).1 h with h | h
  · simp at h
  · exact isFiniteMeasure_restrict.2 h.ne

theorem tame_double {χS χT : (AE D)ˣ →* Circle} {om : Om S T} (hom : IsWeilDatumO ψ S T χS χT om) (vT : GlobalTheory.Unf.Vol T)
    {G : GA D T → ℂ} (hG : RapidDec T G) {A : HSp D} (vA : GlobalTheory.Unf.Vol A) {φ : GA D A → ℂ} (hφ : RapidDec A φ)
    {N : Type} [TopologicalSpace N] [SecondCountableTopology N] [MeasurableSpace N] [BorelSpace N] (ν : Measure N)
    [IsFiniteMeasure ν] (K : GA D A → N → ℂ) (g : GA D A → N → GA D S)
    (hK : Continuous fun p : GA D A × N => K p.1 p.2) (hg : Continuous fun p : GA D A × N => g p.1 p.2)
    {C C' : ℝ} {a a' : ℕ} (hKb : ∀ h n, ‖K h n‖ ≤ C * (‖φ h‖ * quotHeight A h ^ a))
    (hgb : ∀ h n, quotHeight S (g h n) ≤ C' * quotHeight A h ^ a') :
    Tame ψ S T fun Φ => ∫ h in vA.𝓕, ∫ n, K h n * liftS om vT.μ vT.𝓕 G Φ (g h n) ∂ν ∂vA.μ := by
  obtain ⟨-, h2A, -, hbA, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  obtain ⟨-, h2T, -, hbT, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D T
  haveI := finite_vol vA
  haveI := finite_vol vT
  have hc : Continuous fun y : (GA D A × N) × GA D T => K y.1.1 y.1.2 * G y.2 :=
    (hK.comp continuous_fst).mul (hG.continuous.comp continuous_snd)
  have hg' : Continuous fun y : (GA D A × N) × GA D T => g y.1.1 y.1.2 := hg.comp continuous_fst
  obtain ⟨hI, hT⟩ := GlobalTheory.T.weilKernelFunctional_superposition_isTame D ψ S T χS χT om hom ((GA D A × N) × GA D T)
    (((vA.μ.restrict vA.𝓕).prod ν).prod (vT.μ.restrict vT.𝓕)) (fun y => K y.1.1 y.1.2 * G y.2) (fun y => g y.1.1 y.1.2)
    (fun y => y.2) (fun _ => 0) hc.measurable hg' continuous_snd continuous_const (fun k => by
      obtain ⟨M, hM⟩ := hφ.decay (a + a' * k)
      obtain ⟨M', hM'⟩ := hG.decay k
      refine Integrable.of_bound (hc.norm.mul ((((continuous_quotHeight S).comp hg').mul
        ((continuous_quotHeight T).comp continuous_snd)).pow k)).aestronglyMeasurable (|C| * |C'| ^ k * M * M')
        (Filter.Eventually.of_forall fun y => ?_)
      obtain ⟨⟨h, n⟩, t⟩ := y
      have p1 := (quotHeight_pos A h).le
      have p2 := (quotHeight_pos T t).le
      have p3 := (quotHeight_pos S (g h n)).le
      have b1 : ‖K h n‖ ≤ |C| * (‖φ h‖ * quotHeight A h ^ a) :=
        (hKb h n).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
      have b2 : quotHeight S (g h n) ≤ |C'| * quotHeight A h ^ a' :=
        (hgb h n).trans (mul_le_mul_of_nonneg_right (le_abs_self C') (by positivity))
      have hM0 : 0 ≤ M := le_trans (by positivity) (hM h)
      show ‖‖K h n * G t‖ * (quotHeight S (g h n) * quotHeight T t) ^ k‖ ≤ _
      rw [Real.norm_of_nonneg (by positivity), norm_mul]
      calc ‖K h n‖ * ‖G t‖ * (quotHeight S (g h n) * quotHeight T t) ^ k
          ≤ |C| * (‖φ h‖ * quotHeight A h ^ a) * ‖G t‖ * (|C'| * quotHeight A h ^ a' * quotHeight T t) ^ k := by gcongr
        _ = |C| * |C'| ^ k * (‖φ h‖ * quotHeight A h ^ (a + a' * k)) * (‖G t‖ * quotHeight T t ^ k) := by ring
        _ ≤ _ := by gcongr; exacts [hM h, hM' t])
  refine tame_congr hom.std hT fun f hf => ?_
  have h1 := hI f hf
  rw [integral_prod _ h1, integral_prod _ h1.integral_prod_left]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
  simp only [liftS_apply]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  ring

theorem lift_periods_tame : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (W : HSp D) (vW : GlobalTheory.Unf.Vol W) (G : GA D W → ℂ), RapidDec W G → (∀ (ρ : ℕ) (B : BesL D ρ) (χ χ' : (AE D)ˣ →* Circle) (om : Om B.V W), IsWeilDatumO ψ B.V W χ χ' om → ∀ φ, RapidDec B.A φ → Tame ψ B.V W fun Φ => B.per ψ φ (liftS om vW.μ vW.𝓕 G Φ)) ∧ ∀ (ρ : ℕ) (J : JacL D ρ) (χ χ' : (AE D)ˣ →* Circle) (om : Om J.W W), IsWeilDatumO ψ J.W W χ χ' om → ∀ (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (χ₁ χ₂ : (AE D)ˣ →* Circle) (omz : Om J.W₀ L'), IsWeilDatumO ψ J.W₀ L' χ₁ χ₂ omz → ∀ φ Φ₀, RapidDec J.W₀ φ → IsThetaFunO ψ J.W₀ L' Φ₀ → Tame ψ J.W W fun Φ => J.per ψ ζ' omz φ (liftS om vW.μ vW.𝓕 G Φ) Φ₀ := by
  intro D ψ W vW G hG
  refine ⟨fun ρ B χ χ' om hom φ hφ => ?_, fun ρ J χ χ' om hom L' ζ' χ₁ χ₂ omz homz φ Φ₀ hφ hΦ₀ => ?_⟩
  · obtain ⟨-, h2, -, hb, ht, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.V
    haveI : SecondCountableTopology (flagN B.d) := TopologicalSpace.Subtype.secondCountableTopology (flagN B.d : Set (GA D B.V))
    haveI : IsFiniteMeasure (B.vN.ν.restrict B.vN.𝓝) :=
      isFiniteMeasure_restrict.2 (by rw [B.vN.unit.2.2]; exact ENNReal.one_ne_top)
    obtain ⟨C₁, a₁, h₁⟩ := GlobalTheory.T.unitaryQuotientHeight_comparable_wittDecomposition D B.V B.V₀ ρ B.d
    obtain ⟨C₂, a₂, h₂⟩ := GlobalTheory.T.unitaryQuotientHeight_orthogonalSum_comparable D B.V₀ B.A B.L B.o
    have hn : Continuous fun p : GA D B.A × flagN B.d => p.2.1 := continuous_subtype_val.comp continuous_snd
    have := tame_double hom vW hG B.vA hφ (B.vN.ν.restrict B.vN.𝓝)
      (fun h (n : flagN B.d) => φ h * star (psiBes ψ B.d 1 (vecB B.o B.ζ) n.1)) (fun h n => n.1 * embA B.d B.o h)
      ((hφ.continuous.comp continuous_fst).mul
        ((GlobalTheory.CharLaws.continuous_psiBes ψ B.d hom.std.1.1 1 (vecB B.o B.ζ)).comp hn).star)
      (hn.mul ((B.d.continuous_embed.comp (B.o.continuous_emb.comp (continuous_id.prodMk continuous_const))).comp
        continuous_fst))
      (C := 1) (a := 0) (C' := |C₁| * |C₂| ^ a₁) (a' := a₂ * a₁) (fun h n => by
        have e : ‖psiBes ψ B.d 1 (vecB B.o B.ζ) n.1‖ = 1 := hom.std.1.2.1 _
        simp [e]) (fun h n => by
        have p1 := (quotHeight_pos B.A h).le
        have p2 := (quotHeight_pos B.V₀ (B.o.emb (h, 1))).le
        have b : quotHeight B.V₀ (B.o.emb (h, 1)) ≤ |C₂| * quotHeight B.A h ^ a₂ :=
          (h₂ h).2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
        calc _ ≤ C₁ * quotHeight B.V₀ (B.o.emb (h, 1)) ^ a₁ := (h₁ n.1 n.2 _).2
          _ ≤ |C₁| * (|C₂| * quotHeight B.A h ^ a₂) ^ a₁ := by gcongr; exact le_abs_self _
          _ = _ := by ring)
    convert this using 2 with Φ
    unfold BesL.per besPer besFun
    congr 1; funext h; congr 1; funext n; ring
  · obtain ⟨-, h2, -, hb, ht, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W
    haveI : SecondCountableTopology (flagN J.d) := TopologicalSpace.Subtype.secondCountableTopology (flagN J.d : Set (GA D J.W))
    haveI : IsFiniteMeasure (J.vN.ν.restrict J.vN.𝓝) :=
      isFiniteMeasure_restrict.2 (by rw [J.vN.unit.2.2]; exact ENNReal.one_ne_top)
    obtain ⟨C₁, a₁, h₁⟩ := GlobalTheory.T.unitaryQuotientHeight_comparable_wittDecomposition D J.W J.W₀ ρ J.d
    obtain ⟨C₂, a₂, h₂⟩ := GlobalTheory.SupThetaGrowth.om_sup_quotHeight D ψ J.W₀ L' χ₁ χ₂ omz homz Φ₀ hΦ₀
    have hn : Continuous fun p : GA D J.W₀ × flagN J.d => p.2.1 := continuous_subtype_val.comp continuous_snd
    have hth : ∀ n h, thetaJS ψ J.d ζ' omz Φ₀ n h =
        ψ (cenS J.d L' (zEll L' ρ ζ') n) * omz (h, 1) Φ₀ (ptS J.d L' (zEll L' ρ ζ') n) := fun n h => by
      rw [thetaJS, GlobalTheory.Unf.FB.ThLaws.jacS_zero_apply]
    have hJ : Continuous fun p : (GA D J.W₀ × GA D L') × WO J.W₀ L' => omz p.1 Φ₀ p.2 :=
      (@GlobalTheory.Unf.jointCont_all D) ψ J.W₀ L' χ₁ χ₂ omz homz Φ₀ hΦ₀
    have hthc : Continuous fun p : GA D J.W₀ × flagN J.d => thetaJS ψ J.d ζ' omz Φ₀ p.2.1 p.1 := by
      simp only [hth]
      exact (hom.std.1.1.comp ((GlobalTheory.Unf.FB.ThLaws.continuous_cenS _ _ _).comp hn)).mul
        (hJ.comp ((continuous_fst.prodMk continuous_const).prodMk ((GlobalTheory.Unf.FB.ThLaws.continuous_ptS _ _ _).comp hn)))
    have := tame_double hom vW hG J.v0 hφ (J.vN.ν.restrict J.vN.𝓝)
      (fun h (n : flagN J.d) => φ h * star (thetaJS ψ J.d ζ' omz Φ₀ n.1 h) * star (psiFlag ψ J.d n.1))
      (fun h n => n.1 * J.d.emb0 h)
      (((hφ.continuous.comp continuous_fst).mul hthc.star).mul
        ((GlobalTheory.Unf.FB.ThLaws.continuous_psiFlag hom.std.1.1 _).comp hn).star)
      (hn.mul (J.d.continuous_embed.comp continuous_fst))
      (C := C₂ * quotHeight L' 1 ^ a₂) (a := a₂) (C' := C₁) (a' := a₁) (fun h n => by
        have e : ‖psiFlag ψ J.d n.1‖ = 1 := hom.std.1.2.1 _
        rw [norm_mul, norm_mul, norm_star, norm_star, e, hth, norm_mul, hom.std.1.2.1, one_mul, mul_one]
        refine (mul_le_mul_of_nonneg_left (h₂ h 1 _) (norm_nonneg _)).trans (le_of_eq ?_)
        ring) (fun h n => (h₁ n.1 n.2 _).2)
    convert this using 2 with Φ
    unfold JacL.per fjSrc fjSrcFun
    congr 1; funext h; congr 1; funext n; ring

end GlobalTheory.LiftTame

end
end

