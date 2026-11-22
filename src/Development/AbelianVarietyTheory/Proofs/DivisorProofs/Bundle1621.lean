import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1587
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1609
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1378
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0997
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalInnerProductLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionSurjectiveLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1602
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1604
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1588
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0096
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1589
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1607
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanStandardCharEqExpRealLinearStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanStandardChar_eq_exp_realLinear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∃ Λ : mixedEmbedding.mixedSpace D.host.F →L[ℝ] ℂ, ∀ x : InfiniteAdeleRing D.host.F, psiInf D.host.F ψ x = Complex.exp (Λ (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F x)) := by
  first | exact @GlobalTheory.PsiInfLinear.psiInf_eq_exp_linear | exact GlobalTheory.PsiInfLinear.psiInf_eq_exp_linear | (intros; apply GlobalTheory.PsiInfLinear.psiInf_eq_exp_linear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormDerivativeModerateGrowth
section
open NumberField GlobalTheory.CuspRep

theorem GlobalTheory.CuspStab.lie_growth : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (X : GlobalTheory.CuspRep.Lie E a) (φ : GlobalTheory.CuspRep.Sm E a), GlobalTheory.CuspRep.IsAutForm φ → ∀ g : GlobalTheory.CuspRep.GA E a, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖(GlobalTheory.CuspRep.lie E a X φ).1 (g * GlobalTheory.CuspRep.infGL E a y)‖ ≤ C * GlobalTheory.CuspRep.height y ^ N :=
  GlobalTheory.AutGrowth.lie_growth_of_finite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormEqOwnRealLieSmoothingStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphicForm_eq_own_realLieSmoothing : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (φ : Sm E a), IsAutForm φ → ∃ α : Lie E a → ℂ, IsTest (invSet E a) α ∧ smoothing ν α φ.1 = φ.1 := by
  first | exact @GlobalTheory.AutGrowth.SelfSmoothing.exists_smoothing_eq_self | exact GlobalTheory.AutGrowth.SelfSmoothing.exists_smoothing_eq_self | (intros; apply GlobalTheory.AutGrowth.SelfSmoothing.exists_smoothing_eq_self <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormGLTameOfFinitenessAtRank
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology GlobalTheory.HCF

namespace GlobalTheory.AutGrowth.RankLocal

open GlobalTheory.AutGrowth.KilledFin GlobalTheory.AutGrowth.SmoothFinite

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem finite_forms (h : ∀ (L' : Subgroup (GL (Fin a) (Af E))), IsOpen (L' : Set (GL (Fin a) (Af E))) →
      ∀ W' : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W' →
      ∀ X' : Set (Module.End ℂ (Sm E a) → ℂ), X'.Finite → ∀ N' : ℕ,
        FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L' W' X' N')))
    (L : Subgroup (GL (Fin a) (Af E))) (hL : IsOpen (L : Set (GL (Fin a) (Af E))))
    (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E a) W)
    (c : (E →+* ℂ) → ℂ → ℂ) :
    FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.Published.AutFinGL.forms L ρ c)) := by
  classical
  haveI hW' : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := GlobalTheory.T.finiteDimensional_matrixCoefficientSpan _ W ρ
  let χ : Module.End ℂ (Sm E a) → ℂ := fun z =>
    if hz : ∃ s : ℂ, ∀ φ : Sm E a, (∀ τ u, cap τ u φ = c τ u • φ) → z φ = s • φ then hz.choose else 0
  have hsub : GlobalTheory.Published.AutFinGL.forms L ρ c ⊆ formsGL E a L (GlobalTheory.Published.AutFin.coeffSpan ρ) {χ} 1 := by
    rintro φ ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, χ, rfl, ?_⟩
    intro zs hlen hzs
    match zs, hlen with
    | [z], _ =>
      have hz : z ∈ Zalg E a := hzs z (List.mem_singleton_self z)
      have hex := GlobalTheory.T.center_acts_by_scalar_on_eigenforms E a c z hz
      have hχ : χ z = hex.choose := dif_pos hex
      simp only [List.foldr_cons, List.foldr_nil]
      rw [hχ, hex.choose_spec φ h4, sub_self]
  have hfin := h L hL (GlobalTheory.Published.AutFin.coeffSpan ρ) hW' {χ} (Set.finite_singleton χ) 1
  exact Submodule.finiteDimensional_of_le (Submodule.span_mono hsub)

theorem finiteDimensional_capEigen_maps_rank (h : ∀ (L' : Subgroup (GL (Fin a) (Af E))), IsOpen (L' : Set (GL (Fin a) (Af E))) →
      ∀ W' : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W' →
      ∀ X' : Set (Module.End ℂ (Sm E a) → ℂ), X'.Finite → ∀ N' : ℕ,
        FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L' W' X' N')))
    (L : Subgroup (GL (Fin a) (Af E))) (hL : IsOpen (L : Set (GL (Fin a) (Af E))))
    (W : Submodule ℂ (Sm E a)) (hW : ∀ k, ∀ w ∈ W, cptRep E a k w ∈ W) (hWf : FiniteDimensional ℂ W)
    (c : (E →+* ℂ) → ℂ → ℂ) (N : Submodule ℂ (W →ₗ[ℂ] Sm E a)) (hN : N ≤ maps L W hW)
    (hcap : ∀ T ∈ N, ∀ τ u, cap τ u ∘ₗ T = c τ u • T) : FiniteDimensional ℂ N := by
  haveI := hWf
  have hF := finite_forms h L hL W (GlobalTheory.PRep.sub (cptRep E a) W hW) c
  haveI := hF
  have hmem : ∀ T ∈ N, ∀ w, T w ∈ GlobalTheory.Published.AutFinGL.forms L (GlobalTheory.PRep.sub (cptRep E a) W hW) c := by
    intro T hT w
    have hm : (∀ k w, T (GlobalTheory.PRep.sub (cptRep E a) W hW k w) = cptRep E a k (T w)) ∧
        ∀ w, T w ∈ tame E a ∧ (∀ γ g, (T w).1 (ratGL E a γ * g) = (T w).1 g) ∧
          ∀ k ∈ L, finRep E a k (T w) = T w := hN hT
    obtain ⟨heq, hall⟩ := hm
    obtain ⟨htame, hleft, hfix⟩ := hall w
    have hZ : ∀ z ∈ Zalg E a, ∃ s : ℂ, z ∘ₗ T = s • T := by
      intro z hz
      induction hz using Algebra.adjoin_induction with
      | mem x hx => obtain ⟨τ, u, rfl⟩ := hx; exact ⟨c τ u, hcap T hT τ u⟩
      | algebraMap r => exact ⟨r, LinearMap.ext fun v => by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨s, hs⟩ := hx
        obtain ⟨t, ht⟩ := hy
        exact ⟨s + t, by rw [LinearMap.add_comp, hs, ht, add_smul]⟩
      | mul x y _ _ hx hy =>
        obtain ⟨s, hs⟩ := hx
        obtain ⟨t, ht⟩ := hy
        exact ⟨t * s, by rw [Module.End.mul_eq_comp, LinearMap.comp_assoc, ht, LinearMap.comp_smul, hs, smul_smul]⟩
    refine ⟨⟨hleft, ?_, ?_, ?_, ?_⟩, hfix, GlobalTheory.Published.AutFinGL.type_of_map _ T heq w, fun τ u => ?_⟩
    · exact isOpen_stab_of_mem_nhds (finRep E a) (T w)
        (Filter.mem_of_superset (hL.mem_nhds L.one_mem) fun k hk => hfix k hk)
    · refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range T) (Submodule.span_le.2 ?_)
      rintro _ ⟨k, rfl⟩
      exact ⟨_, heq k w⟩
    · refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {T w}) (Submodule.span_le.2 ?_)
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨s, hs⟩ := hZ z hz
      have e : z (T w) = s • T w := LinearMap.congr_fun hs w
      show z (T w) ∈ _
      rw [e]
      exact Submodule.smul_mem _ s (Submodule.mem_span_singleton_self _)
    · exact growth_of_tame htame
    · exact LinearMap.congr_fun (hcap T hT τ u) w
  let Φ : N →ₗ[ℂ] (W →ₗ[ℂ] Submodule.span ℂ (GlobalTheory.Published.AutFinGL.forms L (GlobalTheory.PRep.sub (cptRep E a) W hW) c)) :=
    { toFun := fun T => LinearMap.codRestrict _ T.1 fun w => Submodule.subset_span (hmem T.1 T.2 w)
      map_add' := fun T T' => LinearMap.ext fun w => rfl
      map_smul' := fun r T => LinearMap.ext fun w => rfl }
  have hinj : Function.Injective Φ := fun T T' h =>
    Subtype.ext (LinearMap.ext fun w => congrArg Subtype.val (LinearMap.congr_fun h w))
  exact Module.Finite.of_injective Φ hinj

theorem finiteDimensional_mapsJ_rank (h : ∀ (L' : Subgroup (GL (Fin a) (Af E))), IsOpen (L' : Set (GL (Fin a) (Af E))) →
      ∀ W' : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W' →
      ∀ X' : Set (Module.End ℂ (Sm E a) → ℂ), X'.Finite → ∀ N' : ℕ,
        FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L' W' X' N')))
    (φ : Sm E a) (hφ : IsAutForm φ) (L : Subgroup (GL (Fin a) (Af E)))
    (hL : IsOpen (L : Set (GL (Fin a) (Af E)))) : FiniteDimensional ℂ (mapsJ φ L) := by
  have hcap : ∀ (τ : E →+* ℂ) (u : ℂ), cap (a := a) τ u ∈ Zalg E a := fun τ u =>
    Algebra.subset_adjoin ⟨τ, u, rfl⟩
  let S : Set (Module.End ℂ (mapsJ φ L)) := {s | ∃ τ u, s = postZ φ L (cap τ u) (hcap τ u)}
  refine GlobalTheory.T.finiteDimensional_of_commuting_finiteAlgebra_jointEigen (mapsJ φ L) S ?_ ?_ ?_
  · rintro _ ⟨τ, u, rfl⟩ _ ⟨τ', u', rfl⟩
    refine LinearMap.ext fun T => Subtype.ext (LinearMap.ext fun w => ?_)
    show cap τ u (cap τ' u' (T.1 w)) = cap τ' u' (cap τ u (T.1 w))
    rw [← Module.End.mul_apply, (Zalg_commute (hcap τ u) (hcap τ' u')).eq, Module.End.mul_apply]
  · let ev : Zalg E a →ₗ[ℂ] Sm E a := (LinearMap.applyₗ φ).comp (Zalg E a).val.toLinearMap
    have hker : LinearMap.ker ev ≤ LinearMap.ker (postZAlg φ L).toLinearMap := by
      intro z hz
      rw [LinearMap.mem_ker] at hz ⊢
      refine LinearMap.ext fun T => Subtype.ext (LinearMap.ext fun w => ?_)
      have hT : T.1 ∈ maps L (spanK E a φ) (spanK_stable φ) ∧
          ∀ z ∈ Zalg E a, z φ = 0 → ∀ w, z (T.1 w) = 0 := T.2
      exact hT.2 z.1 z.2 hz w
    have hev : FiniteDimensional ℂ (LinearMap.range ev) := by
      have h1 : LinearMap.range ev ≤
          Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) := by
        rintro _ ⟨z, rfl⟩
        exact Submodule.subset_span ⟨z.1, z.2, rfl⟩
      haveI := hφ.zfin
      exact Submodule.finiteDimensional_of_le h1
    refine fd_adjoin_of_ker_le (mapsJ φ L) (Zalg E a) (Sm E a) (postZAlg φ L) ev hev hker S ?_
    rintro _ ⟨τ, u, rfl⟩
    exact ⟨⟨cap τ u, hcap τ u⟩, rfl⟩
  · intro c
    let J := ⨅ s ∈ S, LinearMap.ker (s - algebraMap ℂ (Module.End ℂ (mapsJ φ L)) (c s))
    let N : Submodule ℂ (spanK E a φ →ₗ[ℂ] Sm E a) := J.map (mapsJ φ L).subtype
    have hNle : N ≤ maps L (spanK E a φ) (spanK_stable φ) := by
      rintro _ ⟨T, _, rfl⟩
      have hT : T.1 ∈ maps L (spanK E a φ) (spanK_stable φ) ∧
          ∀ z ∈ Zalg E a, z φ = 0 → ∀ w, z (T.1 w) = 0 := T.2
      exact hT.1
    have hNe : ∀ T ∈ N, ∀ (τ : E →+* ℂ) (u : ℂ),
        cap τ u ∘ₗ T = c (postZ φ L (cap τ u) (hcap τ u)) • T := by
      rintro _ ⟨T, hT, rfl⟩ τ u
      have hT' : T ∈ ⨅ s ∈ S, LinearMap.ker (s - algebraMap ℂ (Module.End ℂ (mapsJ φ L)) (c s)) := hT
      have h₀ := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hT' (postZ φ L (cap τ u) (hcap τ u))) ⟨τ, u, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, Module.algebraMap_end_apply] at h₀
      exact congrArg Subtype.val h₀
    have hN : FiniteDimensional ℂ N :=
      finiteDimensional_capEigen_maps_rank h L hL (spanK E a φ) (spanK_stable φ) hφ.kfin
        (fun τ u => c (postZ φ L (cap τ u) (hcap τ u))) N hNle hNe
    exact LinearEquiv.finiteDimensional
      (Submodule.equivMapOfInjective (mapsJ φ L).subtype Subtype.val_injective J).symm

theorem exists_finite_space_rank (h : ∀ (L' : Subgroup (GL (Fin a) (Af E))), IsOpen (L' : Set (GL (Fin a) (Af E))) →
      ∀ W' : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W' →
      ∀ X' : Set (Module.End ℂ (Sm E a) → ℂ), X'.Finite → ∀ N' : ℕ,
        FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L' W' X' N')))
    (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (φ : Sm E a) (hφ : IsAutForm φ) :
    ∃ V : Submodule ℂ (Sm E a), FiniteDimensional ℂ V ∧ V ≤ tame E a ∧ ∀ α, IsTest (invSet E a) α → KInv α →
      ∃ h : smoothing ν α φ.1 ∈ Sm E a, (⟨smoothing ν α φ.1, h⟩ : Sm E a) ∈ V := by
  let w0 : spanK E a φ := ⟨φ, self_mem_spanK φ⟩
  haveI := finiteDimensional_mapsJ_rank h φ hφ (stabL φ) hφ.level
  refine ⟨(mapsJ φ (stabL φ)).map (LinearMap.applyₗ w0), inferInstance, ?_, fun α hα hK =>
    ⟨GlobalTheory.T.realLieSmoothing_mem_smoothAdelicFunctions E a ν α hα φ.1 φ.2, smoothMap ν hα _, smoothMap_mem ν hα hK hφ, rfl⟩⟩
  rintro _ ⟨T, hT, rfl⟩
  exact (hT.1.2 w0).1

theorem tame_of_autForm_rank : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ),
    (∀ (L' : Subgroup (GL (Fin n) (Af E))), IsOpen (L' : Set (GL (Fin n) (Af E))) →
      ∀ W' : Submodule ℂ (Kinf E n → ℂ), FiniteDimensional ℂ W' →
      ∀ X' : Set (Module.End ℂ (Sm E n) → ℂ), X'.Finite → ∀ N' : ℕ,
        FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E n L' W' X' N'))) →
    ∀ φ : Sm E n, IsAutForm φ → φ ∈ GlobalTheory.AutGrowth.tame E n := by
  intro E _ _ _ a hfin φ hφ
  let ν : Measure (Lie E a) := Measure.addHaar
  obtain ⟨α, hα, hlim⟩ := GlobalTheory.T.exists_conjInvariant_approxIdentity_realLieSmoothing E a ν
  obtain ⟨V, hVf, hVt, hV⟩ := exists_finite_space_rank hfin ν φ hφ
  let V' : Submodule ℂ (GA E a → ℂ) := V.map (Sm E a).subtype
  have hc : IsClosed (V' : Set (GA E a → ℂ)) := Submodule.closed_of_finiteDimensional V'
  have hmem : ∀ n, smoothing ν (α n) φ.1 ∈ V' := fun n => by
    obtain ⟨h, hv⟩ := hV (α n) (hα n).1 (hα n).2
    exact ⟨_, hv, rfl⟩
  have hφ' : φ.1 ∈ V' :=
    hc.mem_of_tendsto (tendsto_pi_nhds.2 fun g => hlim φ.1 φ.2 g) (Eventually.of_forall hmem)
  obtain ⟨ψ, hψ, e⟩ := hφ'
  have e' : ψ = φ := Subtype.ext e
  exact hVt (e' ▸ hψ)

end GlobalTheory.AutGrowth.RankLocal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcMeasUniv
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.ProjSpace GlobalTheory.HermFrame GlobalTheory.ArInt

namespace GlobalTheory.TautFlag

theorem selfInter (HC : GlobalTheory.Published.ArCalc) : haveI := ProjSpace.isRegSurf_line.isIntegral;
    (ProjSpace.hermitianTwistingSheaf ℤ 1).IsSelfInter (1 / 2) ∧ (ProjSpace.hermitianTwistingSheaf ℤ 1).dual.IsSelfInter (1 / 2) := by
  have := ProjSpace.isRegSurf_line.isIntegral
  have hP := ProjSpace.isArithVar_int 1
  obtain ⟨Ψ, hΨ⟩ := ((HC.arExists ℤ _ _ 1 hP).2 Unit fun _ => hermitianTwistingSheaf ℤ 1).1
  have h₁ := ((HC.arIso ℤ _ _ 1 hP).2 Unit _ Ψ hΨ).1 ()
  have hval : Ψ (MvPolynomial.X () ^ (1 + 1)) = 1 / 2 := FlagZ.Plane.selfInter_line (n := 1) rfl h₁
  have hΦ := ((HC.arIso ℤ _ _ 1 hP).2 Unit _ Ψ hΨ).2.2 Unit (fun _ => (hermitianTwistingSheaf ℤ 1).dual) (fun _ _ => -1)
    fun _ => HermLB.icls_eq_iff.1 (by
      rw [icls_comb, HermLB.icls_dual, Fintype.sum_unique]
      exact neg_one_zsmul _)
  have h₂ := ((HC.arIso ℤ _ _ 1 hP).2 Unit _ _ hΦ).1 ()
  refine ⟨hval ▸ h₁, ?_⟩
  convert h₂ using 1
  rw [← hval]
  simp [lin]

theorem exists_chart (σ : ℤ →+* ℂ) (j : Fin 2) : ∃ c : AlgChart (PSpace.str ℤ 1) σ 1,
    c.e.source = ptsIn _ σ (chart ℤ 1 j) ∧ c.e.target = Set.univ ∧
      ∀ y ∈ c.e.source, c.e y 0 = ev _ σ (chart ℤ 1 j) (ratio ℤ 1 j (j.succAbove 0)) y := by
  let e : MvPolynomial (Fin 1) ℤ ≃ₐ[ℤ] Γ(PSpace ℤ 1, chart ℤ 1 j) :=
    (MvPolynomial.renameEquiv ℤ (finSuccAboveEquiv j)).trans (chartAlgEquiv ℤ 1 j)
  have he : MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (PSpace.str ℤ 1) (chart ℤ 1 j))
      (fun a => ratio ℤ 1 j (j.succAbove a)) = (e : MvPolynomial (Fin 1) ℤ →+* _) :=
    MvPolynomial.ringHom_ext (fun a => (MvPolynomial.eval₂Hom_C _ _ a).trans (e.commutes a).symm)
      fun b => (MvPolynomial.eval₂Hom_X' _ _ b).trans
        ((congrArg (chartAlgEquiv ℤ 1 j) (MvPolynomial.rename_X _ b)).trans
          (chartAlgEquiv_X ℤ 1 j (finSuccAboveEquiv j b))).symm
  obtain ⟨c, hs, ht, hx⟩ := FlagZ.Plane.exists_chart_of_bijective ℤ _ (PSpace.str ℤ 1) σ 1 _
    (isAffineOpen_chart ℤ 1 j) (fun a => ratio ℤ 1 j (j.succAbove a)) (by rw [he]; exact e.bijective)
  exact ⟨c, hs, ht, fun y hy => hx y hy 0⟩

theorem bcMeas_univ (σ : ℤ →+* ℂ) : ((stdH.h.stepMet flag 1).met σ).bcMeas (r := 1) (s := 1)
    (VMetric.stepSeq_shortExact flag 1) (flag.isVB (Fin.castSucc 1)) (flag.isVB_gr 1) Set.univ = 1 := by
  have := CxPts.secondCountableTopology_of_isProjOver σ (isProjOver_pspace_str ℤ 1)
  have H : ((stdH.h.stepMet flag 1).met σ).IsCInf := (stdH.cInf.restrict _ _) σ
  obtain ⟨c, hs, ht, hx⟩ := exists_chart σ 0
  obtain ⟨c', hs', -, hx'⟩ := exists_chart σ 1
  have hm : MeasurableSet c.e.source := c.e.open_source.measurableSet
  have hc (y : CxPts (PSpace.str ℤ 1) σ) (hy : y ∈ c.e.sourceᶜ) : y ∈ c'.e.source := by
    obtain ⟨j, hj⟩ := exists_mem_chart ℤ 1 (y.1 (IsLocalRing.closedPoint ℂ))
    rw [hs']
    rw [hs] at hy
    fin_cases j
    · exact absurd (mem_ptsIn.2 hj) hy
    · exact mem_ptsIn.2 hj
  have h₀ : ((stdH.h.stepMet flag 1).met σ).bcMeas (r := 1) (s := 1) (VMetric.stepSeq_shortExact flag 1)
      (flag.isVB (Fin.castSucc 1)) (flag.isVB_gr 1) c.e.sourceᶜ = 0 := by
    refine (Met.bcMeas_apply (r := 1) (s := 1) _ _ _ c' H hm.compl hc).trans
      (setLIntegral_measure_zero _ _ (measure_mono_null (t := {0}) ?_ (measure_singleton _)))
    rintro _ ⟨y, hy, rfl⟩
    have h₁ : c'.e y 0 = 0 := by
      rw [hx' y (hc y hy)]
      by_contra h
      have h₂ := (mem_ptsIn_basicOpen (hs' ▸ hc y hy) _).2 h
      rw [ratio, basicOpen_ratioOn] at h₂
      exact hy (hs ▸ (mem_ptsIn_inf.1 h₂).2)
    ext i
    rw [Subsingleton.elim i 0, h₁]
    rfl
  have hmem (v) : c.e.symm v ∈ c.e.source := c.e.map_target (ht ▸ trivial)
  have hr (v) : c.e (c.e.symm v) = v := c.e.right_inv (ht ▸ trivial)
  have hz (v) : ev _ σ (chart ℤ 1 0) (ratio ℤ 1 0 1) (c.e.symm v) = v 0 :=
    (hx _ (hmem v)).symm.trans (by rw [hr])
  have h1 (v) : ev _ σ (chart ℤ 1 0) (ratio ℤ 1 0 0) (c.e.symm v) = 1 := by
    rw [ev_eq (hs ▸ hmem v), ratio, ratioOn_self, map_one]
  have hG : (fun v => ((stdH.h.stepMet flag 1).met σ).gram (adapt₁ 0).frame (c.e.symm v)) =
      fun w : ReciprocityTheory.L2DbarEstimates.V 1 => (Matrix.fromBlocks (Matrix.of fun _ _ => 1 + w 0 * starRingEnd ℂ (w 0))
        (Matrix.of fun _ _ => w 0) (Matrix.of fun _ _ => starRingEnd ℂ (w 0)) 1 :
          Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) := funext fun v => by
    have e₁ : nsqV 0 (c.e.symm v) = 1 + v 0 * starRingEnd ℂ (v 0) := by
      rw [nsqV, h1, hz, map_one, mul_one]
    have e₂ : ipVT 0 (c.e.symm v) = v 0 := hz v
    rw [gram_adapt₁ 0 (hs ▸ hmem v), e₁, e₂]
  have hd (v) : ((stdH.h.stepMet flag 1).met σ).bcDens (r := 1) (s := 1) (VMetric.stepSeq_shortExact flag 1)
      (flag.isVB (Fin.castSucc 1)) (flag.isVB_gr 1) c (c.e.symm v) =
        1 / Real.pi * (ArithHeightModel.u v ^ 2)⁻¹ := by
    refine (Met.bcDens_eq (r := 1) (s := 1) _ _ _ (adapt₁ 0) c H (hmem v) (hs ▸ hmem v)).trans ?_
    refine Eq.trans ?_ (GlobalTheory.T.hermitian_matrix_green_value v)
    exact congrArg₂ (fun K w => 2 * diagVal (extTrace K w) (EuclideanSpace.single 0 1)) hG (hr v)
  have hn (v : ReciprocityTheory.L2DbarEstimates.V 1) : 0 ≤ 1 / Real.pi * (ArithHeightModel.u v ^ 2)⁻¹ := by
    have := Real.pi_pos; positivity
  rw [← measure_add_measure_compl hm, h₀, add_zero]
  refine (Met.bcMeas_apply (r := 1) (s := 1) _ _ _ c H hm subset_rfl).trans ?_
  rw [c.e.image_source_eq_target, ht, Measure.restrict_univ]
  refine (lintegral_congr fun v => congrArg ENNReal.ofReal (hd v)).trans ?_
  rw [← ofReal_integral_eq_lintegral_ofReal (Integrable.of_integral_ne_zero
    (ArithHeightModel.integral_dens.trans_ne one_ne_zero)) (.of_forall hn), ArithHeightModel.integral_dens,
    ENNReal.ofReal_one]

theorem flagBc_flag : stdH.h.FlagBcFinite flag ∧ stdH.h.flagBc flag = 1 := by
  have e (σ) : ((stdH.h.stepMet flag 0).met σ).bcMeas (VMetric.stepSeq_shortExact flag 0)
      (flag.isVB (Fin.castSucc 0)) (flag.isVB_gr 0) = 0 := Met.bcMeas_rank_zero _ _ _
  have e' (σ) : ((stdH.h.stepMet flag 1).met σ).bcMeas (VMetric.stepSeq_shortExact flag 1)
      (flag.isVB (Fin.castSucc 1)) (flag.isVB_gr 1) Set.univ = 1 := bcMeas_univ σ
  refine ⟨Fin.forall_fin_two.2 ⟨fun σ => ?_, fun σ => ?_⟩, ?_⟩
  · exact (congrArg (fun μ : Measure _ => μ Set.univ) (e σ)).trans_ne ENNReal.zero_ne_top
  · exact (e' σ).trans_ne ENNReal.one_ne_top
  · rw [VMetric.flagBc, Fin.sum_univ_two]
    refine (congrArg₂ (· + ·) (finsum_eq_zero_of_forall_eq_zero fun σ => ?_)
      ((finsum_eq_single _ (Int.castRingHom ℂ) fun σ h => absurd (RingHom.ext_int _ _) h).trans ?_)).trans
        (zero_add 1)
    · exact congrArg (fun μ : Measure _ => (μ Set.univ).toReal) (e σ)
    · exact congrArg ENNReal.toReal (e' _)

theorem exists_flag : GlobalTheory.Published.ArCalc → haveI := ProjSpace.isRegSurf_line.isIntegral;
    ∃ fl : Vert.Flag (HermVB.std (PSpace.str ℤ 1) 2).E 2,
      (VMetric.grLB fl 0 (HermVB.std (PSpace.str ℤ 1) 2).cInf).Isometric (ProjSpace.hermitianTwistingSheaf ℤ 1).dual ∧
        (HermVB.std (PSpace.str ℤ 1) 2).h.flagBc fl = 1 ∧
          VMetric.IsFlagCh2 (HermVB.std (PSpace.str ℤ 1) 2).cInf fl 0 := fun HC => by
  have := ProjSpace.isRegSurf_line.isIntegral
  obtain ⟨s₁, s₂⟩ := selfInter HC
  have hX := ProjSpace.isArithVar_int 1
  refine ⟨flag, GlobalTheory.T.graded_first_isometric_dual_O1, flagBc_flag.2, flagBc_flag.1, ![1 / 2, 1 / 2], ?_, ?_⟩
  · intro i
    fin_cases i
    · exact GlobalTheory.T.graded_first_isometric_dual_O1.symm.isSelfInter hX s₂
    · exact GlobalTheory.T.graded_second_isometric_O1.symm.isSelfInter hX s₁
  · rw [flagBc_flag.2, Fin.sum_univ_two]
    norm_num

end GlobalTheory.TautFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardAbelianVarietyTorsionSepClosedStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_abelianVariety_torsion_sepClosed : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ g : ℕ, SmoothOfRelativeDimension g A.hom → ∀ m : ℕ, (m : K) ≠ 0 → Nat.card {x : ptOver K Ω ⟶ A // x ^ m = 1} = m ^ (2 * g) := by
  first | exact @GlobalTheory.SepClosedTorsion.card_torsion_sepClosed | exact GlobalTheory.SepClosedTorsion.card_torsion_sepClosed | (intros; apply GlobalTheory.SepClosedTorsion.card_torsion_sepClosed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionTorusExtensionAbelianVarietyLeStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_torsion_torusExtension_abelianVariety_le : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], IsCommMonObj G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Sp k)) [GrpObj B] (i : splitTorus (Sp k) X ⟶ G) (q : G ⟶ B), GlobalTheory.SS.IsQuot i q → IsAbelianScheme B → ∀ a : ℕ, SmoothOfRelativeDimension a B.hom → ∀ m : ℕ, (m : k) ≠ 0 → ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → s.card ≤ m ^ (Module.finrank ℤ X + 2 * a) := by
  first | exact @GlobalTheory.TorusExtTorsion.card_le | exact GlobalTheory.TorusExtTorsion.card_le | (intros; apply GlobalTheory.TorusExtTorsion.card_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAugmentationSubspaceQuotientActionTopStatement
section
open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterAugmentationSubspace_quotientAction_top : ∀ {k O C Idx W V : Type*} [Field k] [Ring O] [CommRing C] [Algebra C O] [Fintype Idx] [AddCommGroup W] [Module k W] [FiniteDimensional k W] [AddCommGroup V] [Module k V] [FiniteDimensional k V] (σW : O →+* Module.End k W) (τ : O →+* Module.End k V) (χ : Idx → C →+* k), Function.Injective χ → jSub τ χ ⊤ = ⊥ → finrank k (homO σW τ) = ∑ i, finrank k (homO σW (qAct τ (mSub τ (χ i) ⊤) (mSub_stable τ (χ i) ⊤ (fun _ _ _ => trivial)))) := by
  first | (exact @GlobalTheory.HTRho.finrank_homO_eq_sum_quot) | (exact GlobalTheory.HTRho.finrank_homO_eq_sum_quot) | (intros; apply GlobalTheory.HTRho.finrank_homO_eq_sum_quot  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartMapIntoAffineConstStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_spMap_comp_eval_zero_of_chart_comp_eq : ∀ (K : Type) [CommRing K] (Y : Scheme.{0}) (W : Y.Opens), IsAffineOpen W → ∀ (g₀ g₁ : Sp (Polynomial K) ⟶ Y), (∀ x, g₀ x ∈ W) → (∀ x, g₁ x ∈ W) → spMap (algebraMap (Polynomial K) (Localization.Away (Polynomial.X : Polynomial K))) ≫ g₀ = spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial K) : Localization.Away (Polynomial.X : Polynomial K))).toRingHom ≫ g₁ → g₀ = spMap (algebraMap K (Polynomial K)) ≫ spMap (Polynomial.evalRingHom 0) ≫ g₀ := by
  first | exact @GlobalTheory.chart_map_into_affine_const | exact GlobalTheory.chart_map_into_affine_const | (intros; apply GlobalTheory.chart_map_into_affine_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernAtOneEq
section
open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.SecForm

theorem chernAt_one_eq_ofValues {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n) :
    chernAt G v 1 = ofValues (chernOne G v) := by
  unfold chernAt ofValues GlobalTheory.GoodMetric.chernPoly chernOne
  rw [Matrix.coeff_charpolyRev_eq_neg_trace, Matrix.trace_neg, neg_neg, pow_one]
  simp only [Matrix.trace, Matrix.diag, GlobalTheory.GoodMetric.curvPoly, Matrix.of_apply, map_sum, map_mul,
    MvPolynomial.aeval_C, MvPolynomial.aeval_X, ← Algebra.smul_def, mul_smul, ← Finset.smul_sum, Finset.sum_smul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

end GlobalTheory.SecForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensDetWeightEqNegLeviLogStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernDens_detWeight_eq_neg_levi_log : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ), (∀ (B : LB X) (φ : Weight p σ B), φ.IsCInf → IsDens fun (c : AlgChart p σ 1) y => c.chernDens φ y) ∧ ∀ (L : X.Modules) (g : Met p σ L 1), g.IsCInf → ∀ (U : X.Opens) (t : Γ(L, U)), IsFrame (fun _ : Fin 1 => t) → ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, y ∈ ptsIn p σ U → c.chernDens g.detWeight y = -(leviForm (fun v => Real.log (g.form t t (c.e.symm v)).re) (c.e y) (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1)).re / Real.pi := by
  first | exact @GlobalTheory.CurveDens.chernDens_curve | exact GlobalTheory.CurveDens.chernDens_curve | (intros; apply GlobalTheory.CurveDens.chernDens_curve <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormOfGramMatrixAtHolomorphicFrameChangeStatement
section
open Set Matrix Filter Topology
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernFormOfGramMatrixAt_holomorphic_frameChange : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (H K A : V n → Matrix r r ℂ) (v : V n), MContDiffAt 2 K v → IsUnit (K v).det → (∀ i j, AnalyticAt ℂ (fun w => A w i j) v) → IsUnit (A v).det → (H =ᶠ[𝓝 v] fun w => chg (A w) (K w)) → ∀ j, chernAt H v j = chernAt K v j := by
  first | exact @GlobalTheory.CxForm.chernAt_changeFrame | exact GlobalTheory.CxForm.chernAt_changeFrame | (intros; apply GlobalTheory.CxForm.chernAt_changeFrame <;> assumption)
end

