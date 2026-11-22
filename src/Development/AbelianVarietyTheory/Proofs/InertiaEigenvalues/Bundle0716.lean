import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0710
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0197
import Formalism.LocalToGlobal.IndefiniteReal.TopMult
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0322
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0704
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0711
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0703
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0706
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0256
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0323
import Formalism.SatakeDualWeyl.Bundle0002
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDeltaPsi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0139
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPrimeIdemOfInert
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0183
import ReciprocityTheory.ResidueCardinality.ArtinOntoB
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeIsobaric
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0023
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CapelliDetDiagonalBlockActsByInfinitesimalCharac

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameEquivApply
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
  Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.CoefDuty
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FormInner

variable {D : D7} {V : HSp D} {n : ℕ}

def RatFrame (P : principalLevelFrame.RowPsi V n) : Prop :=
  ∀ h, h ∈ ReciprocityTheory.Aut.GQ D.host.E n ↔ ∃ γ ∈ Formalism.L2.Theta.GQ V, finHom V γ = finHom V (P.ψ h)

theorem ratF_injective (V : HSp D) : Function.Injective (Bridge.ratF V) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨γ, γ₀, h₀, e⟩ h
  have h1 : finHom V γ = 1 := congrArg Subtype.val h
  have h2 : γ₀ = 1 := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    have h3 : ((finHom V γ).1 i j) = inclR (F := D.host.F) (Af D.host.F) (γ₀.1 i j) := by
      have : (matHom V γ).1 i j = inclR (F := D.host.F) (AF D.host.F) (γ₀.1 i j) :=
        (congrArg (fun g : GL (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E) => g.1 i j) e).symm
      show Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom V γ).1 i j) = _
      rw [this]
      simp [inclR]
    have hi : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (Af D.host.F)) := by
      haveI : Nontrivial (Af D.host.F) := Formalism.L2.DIV.af_nontrivial D.host.F
      exact Algebra.TensorProduct.includeRight_injective (RingHom.injective _)
    apply hi
    rw [← h3, h1]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  subst h2
  exact Subtype.ext (Subtype.ext (e.symm.trans (map_one _)))

def frameEquiv (P : principalLevelFrame.RowPsi V n) : GAf D.host.E n ≃* Bridge.Gf V :=
  MulEquiv.ofBijective ((finHom V).rangeRestrict.comp P.ψ)
    ⟨fun a b e => P.inj (TopMult.lift_unique (P.into a) (P.into b) e), fun y => by
      obtain ⟨h, hh, e⟩ := TopMult.exists_lift y
      obtain ⟨g, rfl⟩ := P.onto h hh
      exact ⟨g, e⟩⟩

theorem frameEquiv_apply (P : principalLevelFrame.RowPsi V n) (g) : frameEquiv P g = (finHom V).rangeRestrict (P.ψ g) := rfl

theorem RatFrame.iff {P : principalLevelFrame.RowPsi V n} (h : RatFrame P) (g) :
    g ∈ ReciprocityTheory.Aut.GQ D.host.E n ↔ ∃ γ, Bridge.ratF V γ = frameEquiv P g :=
  (h g).trans ⟨fun ⟨γ, hγ, e⟩ => ⟨⟨γ, hγ⟩, Subtype.ext e⟩, fun ⟨γ, e⟩ => ⟨γ.1, γ.2, congrArg Subtype.val e⟩⟩

theorem comap_le_Umax {hF : D.host.F = maximalRealSubfield D.host.E} {P : principalLevelFrame.RowPsi V n} (hP : GlobalTheory.Mem.R3.StdFrame hF P)
    {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsBaseFrame V β Λ 1)
    (Lv : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) :
    (levEnv V β Lv).J.comap (frameEquiv P).toMonoidHom ≤ ReciprocityTheory.Aut.Umax D.host.E n := fun κ hκ =>
  (hP.2 κ).2 ((GlobalTheory.FinZeta.LevelOff.finE_mem_St_iff hβ (P.into κ)).1
    (GlobalTheory.FinZeta.LevelOff.finE_mem_St_of_mem_levG (Lv := flag1L Lv) ⟨P.into κ, hκ⟩))

section Read

variable {μ : D.what₂.Tup} {j : ℕ} (X : MtReal D μ j) {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W]
  [InnerProductSpace ℂ W] (ι : Γ →* G) (φ : GAf D.host.E D.R.nV ≃* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ)
  (e : X.wt.W ≃ₗ[ℂ] W) (Fm : D.what₂.Mt μ j → G → W)

theorem weight_match (hFm : ∀ x, Fm x ∈ Bridge.AdForms ι ρ J χ) (hread : ∀ x g, e (X.real x g) = Fm x (φ g))
    {x₀ : D.what₂.Mt μ j} (h₀ : x₀ ≠ 0) (γ : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) (δ : Γ) (hδ : ι δ = φ γ) (v : X.wt.W) :
    e (X.wt.ρ γ v) = ρ δ (e v) := by
  have hA : ∀ x, X.real x ∈ NG.TypeSp X.wt.ρ X.J X.χ := fun x => X.real_range ▸ LinearMap.mem_range_self _ x
  let U : Subrepresentation X.wt.ρ := ⟨Submodule.span ℂ (Set.range (X.real x₀)), fun g w hw => by
    refine Submodule.span_induction (p := fun w _ => X.wt.ρ g w ∈ Submodule.span ℂ (Set.range (X.real x₀))) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨h, rfl⟩
      exact Submodule.subset_span ⟨g * h, (hA x₀).1.1 g h⟩
    · simp
    · intro a b _ _ ha hb
      rw [map_add]; exact add_mem ha hb
    · intro c a _ ha
      rw [map_smul]; exact Submodule.smul_mem _ c ha⟩
  have hU : U = ⊤ := by
    haveI := X.wt.irr
    refine (eq_bot_or_eq_top U).resolve_left fun hb => h₀ (X.real_inj ?_)
    rw [map_zero]
    funext g
    have : X.real x₀ g ∈ U.toSubmodule := Submodule.subset_span ⟨g, rfl⟩
    rw [hb] at this
    exact this
  have hv : v ∈ Submodule.span ℂ (Set.range (X.real x₀)) := by
    show v ∈ U.toSubmodule
    rw [hU]
    exact Submodule.mem_top
  refine Submodule.span_induction (p := fun v _ => e (X.wt.ρ γ v) = ρ δ (e v)) ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨h, rfl⟩
    have := hFm x₀ δ (φ h) 1
    rw [← (hA x₀).1.1 γ h, hread, hread, map_mul, ← hδ]
    simpa using this
  · simp
  · intro a b _ _ ha hb
    simp only [map_add, ha, hb]
  · intro c a _ ha
    simp only [map_smul, ha]

def pullForm : X.wt.W →ₗ⋆[ℂ] X.wt.W →ₗ[ℂ] ℂ := ((innerₛₗ ℂ : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ).comp e.toLinearMap).compl₂ e.toLinearMap

theorem pullForm_apply (a b : X.wt.W) : pullForm X e a b = inner ℂ (e a) (e b) := rfl

theorem classSum_of_read {I : Type} [Fintype I] (y : I → G) (hy : Bridge.IsReps ι J y) (hι : Function.Injective ι)
    (hrat : ∀ h, h ∈ ReciprocityTheory.Aut.GQ D.host.E D.R.nV ↔ ∃ γ, ι γ = φ h) (hρ : ∀ δ (a b : W), inner ℂ (ρ δ a) (ρ δ b) = inner ℂ a b)
    (hJ : IsBounded (J.comap φ.toMonoidHom)) (hX : IsBounded X.J)
    (hFm : ∀ x, Fm x ∈ Bridge.AdForms ι ρ J χ) (hread : ∀ x g, e (X.real x g) = Fm x (φ g))
    (c : ℝ) (hc : 0 < c) (hip : ∀ x x' : D.what₂.Mt μ j, inner ℂ x x' = (c : ℂ) * Bridge.adInner ι J y (Fm x) (Fm x'))
    (h0 : (∀ x : D.what₂.Mt μ j, x = 0) → ∃ β, IsInvForm X.wt β) : ClassSum X := by
  have hA : ∀ x, X.real x ∈ NG.TypeSp X.wt.ρ X.J X.χ := fun x => X.real_range ▸ LinearMap.mem_range_self _ x
  obtain ⟨N, hN, hNJ⟩ := X.J_open
  obtain ⟨T', hT', htr⟩ := classSum_transport (W := W) ι hι φ hrat J y hy
  refine ⟨hX, ?_⟩
  by_cases hz : ∀ x : D.what₂.Mt μ j, x = 0
  · obtain ⟨β, hβ⟩ := h0 hz
    obtain ⟨T, c', hT, -, -⟩ := classSum_compare hβ hX hN (fun κ h => (hNJ κ h).1) hJ hT'
    refine ⟨β, T, 1, hβ, hT, one_pos, fun x x' => ?_⟩
    rw [hz x]
    simp [classSum]
  · obtain ⟨x₀, h₀⟩ := not_forall.1 hz
    have hβ : IsInvForm X.wt (pullForm X e) := by
      refine ⟨fun a b => by rw [pullForm_apply, pullForm_apply, inner_conj_symm], fun a ha => ?_, fun γ a b => ?_⟩
      · rw [pullForm_apply]
        exact (re_inner_self_pos (𝕜 := ℂ) (x := e a)).2 (fun h => ha (e.map_eq_zero_iff.1 h))
      · obtain ⟨δ, hδ⟩ := (hrat _).1 γ.2
        have hw := weight_match X ι φ ρ J χ e Fm hFm hread h₀ γ δ hδ
        exact (congrArg₂ (inner ℂ) (hw a) (hw b)).trans (hρ δ _ _)
    obtain ⟨T, c', hT, hc', hcmp⟩ := classSum_compare hβ hX hN (fun κ h => (hNJ κ h).1) hJ hT'
    have hB : ∀ x, X.real x ∈ NG.TypeSp X.wt.ρ (J.comap φ.toMonoidHom) (χ.comp (φ.toMonoidHom.subgroupComap J)) := fun x =>
      ⟨(hA x).1, fun κ => funext fun g => e.injective (by
        have := hFm x 1 (φ g) ⟨φ κ, κ.2⟩
        show e (X.real x (g * κ)) = e (((χ ⟨φ κ, κ.2⟩ : ℂˣ) : ℂ) • X.real x g)
        rw [map_smul, hread, hread, map_mul]
        simpa using this)⟩
    refine ⟨_, T, c * c', hβ, hT, mul_pos hc hc', fun x x' => ?_⟩
    rw [hip, ← htr X.wt (pullForm X e) (X.real x) (X.real x') _ _ fun g => by rw [pullForm_apply, hread, hread],
      hcmp _ _ _ _ (hA x) (hA x') (hB x) (hB x')]
    push_cast
    ring

end Read

end GlobalTheory.FormInner

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepsOfCgTrue
section
noncomputable section

namespace GlobalTheory.GalAway

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Neutral.B1 Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.Pst
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.HeightCounting

theorem galoisReps_of_cgTrue : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.GaloisRepOfPolarizedCuspidal → ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), GlobalTheory.HeightCounting.CGTrue hL D T → GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GaloisReps D := by
  intro hL hF hG D T C π hc hr l _ ι
  have := host_isCMField D.host
  have ha : 1 ≤ D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  have hr' : (C.e _ π).1.IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    have := (D.naut.ralg_def π).1 hr τ
    rwa [C.inf] at this
  obtain ⟨r, h1, h2, h3⟩ := exists_wdOf_eq_locPar hL hF hG D.nd.Om ι ha (C.e _ π).1 ((C.csd _ π).1 hc) hr'
  refine ⟨r, h1, h2, fun w hw => ?_⟩
  have hl : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := hw
  have e : T.e w (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2)) = wdOf (D.nd.plOm.2 w) hl ι r := by
    rw [T.tw, C.loc, h3]
    rfl
  refine ⟨fun s hs => ?_, ?_, fun hu B s hB hs => ?_⟩
  · rw [T.inePol w _ s hs, e]
    exact inePol_wdOf hl ι h1 hs
  · rw [T.mono0, e]
    exact weilDeligneParam_monodromy_eq_zero_iff hl ι h1
  · have hu' := (D.naut.unr_tw _ ((1 - (D.R.r : ℝ)) / 2)).2 hu
    rw [galPol, T.frobEig w _ hu', e]
    exact frobEig_wdOf hl ι h1 (e ▸ (T.unr w _).1 hu') hB hs

end GlobalTheory.GalAway

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinLocalIdeleInjective
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ArtinLocalInj

theorem artin_localIdele_injective : ChevalleyUnits → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (art : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω), GlobalTheory.HeckeGal.IsGlobalArtin art → ∀ w : HeightOneSpectrum (𝓞 E), Function.Injective fun x : (w.adicCompletion E)ˣ => art (Neutral.B1.localIdele E w x) := by
  intro hC E Ω _ _ _ _ _ art ha w
  have hker : ∀ x : (w.adicCompletion E)ˣ, art (Neutral.B1.localIdele E w x) = 1 → x = 1 := by
    intro x hx
    have hx' : art (Neutral.B1.localIdele E w x⁻¹) = 1 := by rw [map_inv, map_inv, hx, inv_one]
    have hv : Valued.v (x : w.adicCompletion E) = 1 := by
      rcases le_total (Valued.v (x : w.adicCompletion E)) 1 with h | h
      · exact GlobalTheory.T.valuation_eq_one_of_congruent_global_approx E w x x.ne_zero h (GlobalTheory.T.exists_global_approx_of_artin_trivial E Ω art ha w x hx)
      · have h2 : Valued.v ((x⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≤ 1 := by
          rw [Units.val_inv_eq_inv_val, map_inv₀]
          exact inv_le_one_of_one_le₀ h
        have h3 := GlobalTheory.T.valuation_eq_one_of_congruent_global_approx E w _ (x⁻¹).ne_zero h2 (GlobalTheory.T.exists_global_approx_of_artin_trivial E Ω art ha w x⁻¹ hx')
        rw [Units.val_inv_eq_inv_val, map_inv₀, inv_eq_one] at h3
        exact h3
    exact Units.ext (GlobalTheory.T.eq_one_of_approx_by_congruent_global_units hC E w x hv (GlobalTheory.T.exists_global_approx_of_artin_trivial E Ω art ha w x hx))
  intro x y hxy
  have : art (Neutral.B1.localIdele E w (x * y⁻¹)) = 1 := by
    simp only at hxy
    rw [map_mul, map_mul, map_inv, map_inv, hxy, mul_inv_cancel]
  exact mul_inv_eq_one.mp (hker _ this)

end GlobalTheory.ArtinLocalInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorConvMirabolicAvgEqZeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodProjector_conv_mirabolicAvg_eq_zero : GlobalTheory.MirAvg.SeriesKillsAvg → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A), GlobalTheory.LiftRows.Given R F → ∀ (i : Fin D.R.m) (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 →
    ∀ (b : Bool) (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ x : G,
      ∑ y : G, GlobalTheory.DownLift.mirC R i PP a b ε y * RealDat.eC (A := A) (sg0 D A) (y⁻¹ * x) = 0 := by
  first | exact @GlobalTheory.GoodNoChiTr.conv_mirC_eC | exact GlobalTheory.GoodNoChiTr.conv_mirC_eC | (intros; apply GlobalTheory.GoodNoChiTr.conv_mirC_eC <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSatakeGLOfHasSatakeParametersPrincipalSeries
section
noncomputable section

open NumberField ReciprocityTheory.Gal Formalism.ConjugateSelfDual IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
  GlobalTheory.CuspRep GlobalTheory.DefiniteBC

namespace GlobalTheory.LFun.SatBridge

theorem hasSatGL_of_hasSatake : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V)
    (α : Fin n → ℂˣ),
    letI := GlobalTheory.LocalData.complRel w
    haveI := GlobalTheory.LocalData.isLocalField w
    HasSatake π α → GlobalTheory.LFun.HasSatGL w π (Finset.univ.val.map α) := by
  intro E _ _ w n V _ _ π α
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  intro h
  exact GlobalTheory.LFun.SatCompare.hasSatGL_of_hasSatakeGL
    ((GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ π _).2 ⟨α, rfl, h⟩)

end GlobalTheory.LFun.SatBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertPlaceLatticeIndexSumBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.InertIdx

theorem indexSum_inert : ∀ (D : D7) (W : HSp D) (n : ℕ), 2 * W.rank + 5 ≤ n → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (f : Formalism.L2.Theta.AE D), IsFinIdem D v f → (∃ w : HeightOneSpectrum (𝓞 D.host.E), Formalism.UG.IsInertAt D.host.F D.host.E v w) → ∀ C : Finset (GA D W), (∀ g ∈ C, SuppF W f g ∧ g ∉ KsphC W ∅) → (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ KsphC W ∅ → g = g') → ∑ g ∈ C, (latIndex W g : ℝ) ^ (-(n : ℝ) / 2) ≤ 8 * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(4 : ℝ)) := by
  classical
  intro D W n hn v f hf ⟨w, hw⟩ C hC hdist
  obtain ⟨ε, hε, rfl⟩ := hf
  have hP := GlobalTheory.HeckeRowsCompare.isPrimeIdem_of_inert (P := w) hw hε
  have hc := GlobalTheory.LabChar.fixed_of_tie hP
  obtain ⟨ϖ, σ, q, π, hU, -, hCh, hV⟩ := GlobalTheory.InertLoc.exists_chart hc hP
  obtain ⟨β, ι, hFr, hGC⟩ := hV W
  obtain ⟨hσσ, hσv, -, -, ⟨x0, hx0, hx0v⟩, -, -⟩ := hU
  let K := GlobalTheory.InertLoc.LP D w
  let O := w.adicCompletionIntegers D.host.E

  have hσO : ∀ x : O, σ (x : K) ∈ O := fun x => by
    show Valued.v (σ (x : K)) ≤ 1
    rw [hσv]; exact x.2
  let cO : O ≃+* O :=
    { toFun := fun x => ⟨σ x, hσO x⟩, invFun := fun x => ⟨σ x, hσO x⟩,
      left_inv := fun x => Subtype.ext (hσσ x), right_inv := fun x => Subtype.ext (hσσ x),
      map_mul' := fun x y => Subtype.ext (map_mul σ _ _), map_add' := fun x y => Subtype.ext (map_add σ _ _) }
  let cK : K ≃+* K :=
    { toFun := σ, invFun := σ, left_inv := hσσ, right_inv := hσσ, map_mul' := map_mul σ, map_add' := map_add σ }

  let H : GA D W → Formalism.UG.UJ σ (1 : Matrix (Fin W.rank) (Fin W.rank) K) := fun g =>
    if hg : SuppF W (algebraMap (AF D.host.F) (AE D) ε) g then (hGC.2.2.1 g hg).choose else 1
  have hH : ∀ g ∈ C, ι (H g) = g := fun g hg => by
    simp only [H, dif_pos (hC g hg).1]
    exact (hGC.2.2.1 g (hC g hg).1).choose_spec
  have hinj : Set.InjOn (fun g => ((H g : GL (Fin W.rank) K))) C := fun g hg g' hg' e => by
    rw [← hH g hg, ← hH g' hg', Subtype.ext e]
  have hsum := Finset.sum_image (f := fun x : GL (Fin W.rank) K =>
      ((((Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).map (((x : Matrix (Fin W.rank) (Fin W.rank) K)).mulVecLin.restrictScalars O)).toAddSubgroup.relIndex
        (Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).toAddSubgroup : ℕ) : ℝ) ^ (-(n : ℝ) / 2)) hinj
  have hterm : ∀ g ∈ C, (latIndex W g : ℝ) ^ (-(n : ℝ) / 2) = ((((Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).map ((((H g : GL (Fin W.rank) K) : Matrix (Fin W.rank) (Fin W.rank) K)).mulVecLin.restrictScalars O)).toAddSubgroup.relIndex
        (Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).toAddSubgroup : ℕ) : ℝ) ^ (-(n : ℝ) / 2) := fun g hg => by
    conv_lhs => rw [← hH g hg]
    rw [GlobalTheory.T.selfDualLatticeIndex_eq_localUnitaryIndex_at_inert D W v ε hε w σ π β ι hCh hFr hGC (H g)]
  rw [Finset.sum_congr rfl hterm, ← hsum]

  have hcard : Nat.card (IsLocalRing.ResidueField O) = Ideal.absNorm v.asIdeal ^ 2 := by
    rw [ReciprocityTheory.Bridge.ResidueFieldCardinality.card_residue, ← GlobalTheory.LFun.InertChart.absNorm_eq
      (Algebra.IsQuadraticExtension.finrank_eq_two _ _) hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hfin : Finite (IsLocalRing.ResidueField O) := Nat.finite_of_card_ne_zero (by
    rw [hcard]; exact pow_ne_zero _ (by
      have := Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot
      exact this))
  have hunit : IsUnit (cO ⟨x0, hx0⟩ - ⟨x0, hx0⟩) := by
    have hne : σ x0 - x0 ≠ 0 := fun e => by rw [e, map_zero] at hx0v; exact zero_ne_one hx0v
    refine isUnit_iff_exists_inv.2 ⟨⟨(σ x0 - x0)⁻¹, ?_⟩, Subtype.ext ?_⟩
    · show Valued.v ((σ x0 - x0)⁻¹) ≤ 1
      rw [map_inv₀, hx0v, inv_one]
    · exact mul_inv_cancel₀ hne
  have hunitary : ∀ x ∈ C.image (fun g => ((H g : GL (Fin W.rank) K))),
      ((x : Matrix (Fin W.rank) (Fin W.rank) K).map cK)ᵀ * (1 : Matrix (Fin W.rank) (Fin W.rank) O).map (algebraMap O K) *
        (x : Matrix (Fin W.rank) (Fin W.rank) K) = (1 : Matrix (Fin W.rank) (Fin W.rank) O).map (algebraMap O K) := by
    intro x hx
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hx
    have h1 := (H g).2
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    exact h1
  have hnontriv : ∀ x ∈ C.image (fun g => ((H g : GL (Fin W.rank) K))),
      (Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).map ((x : Matrix (Fin W.rank) (Fin W.rank) K).mulVecLin.restrictScalars O) ≠
        Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank))) := by
    intro x hx he
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hx
    have h1 := (GlobalTheory.T.stdLattice_map_eq_iff_mem_GLint_valuationSubring K O W.rank _).1 he
    have h2 := (hGC.2.2.2 (H g)).2 h1
    rw [hH g hg] at h2
    exact (hC g hg).2 h2
  have hdist' : ∀ x ∈ C.image (fun g => ((H g : GL (Fin W.rank) K))), ∀ x' ∈ C.image (fun g => ((H g : GL (Fin W.rank) K))),
      (Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).map ((x : Matrix (Fin W.rank) (Fin W.rank) K).mulVecLin.restrictScalars O) =
        (Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).map ((x' : Matrix (Fin W.rank) (Fin W.rank) K).mulVecLin.restrictScalars O) →
      x = x' := by
    intro x hx x' hx' he
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨g', hg', rfl⟩ := Finset.mem_image.1 hx'
    have hm : (Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).map
        (((((H g)⁻¹ * H g' : Formalism.UG.UJ σ (1 : Matrix (Fin W.rank) (Fin W.rank) K)) : GL (Fin W.rank) K) : Matrix (Fin W.rank) (Fin W.rank) K).mulVecLin.restrictScalars O) =
        Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank))) := by
      have hcomp : ∀ (a b : GL (Fin W.rank) K), ((((a * b : GL (Fin W.rank) K)) : Matrix (Fin W.rank) (Fin W.rank) K).mulVecLin.restrictScalars O) =
          ((a : Matrix (Fin W.rank) (Fin W.rank) K).mulVecLin.restrictScalars O).comp ((b : Matrix (Fin W.rank) (Fin W.rank) K).mulVecLin.restrictScalars O) := by
        intro a b
        ext y : 1
        simp [Matrix.mulVec_mulVec]
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hcomp, Submodule.map_comp, ← he, ← Submodule.map_comp, ← hcomp, inv_mul_cancel]
      ext y
      simp
    have h1 := (GlobalTheory.T.stdLattice_map_eq_iff_mem_GLint_valuationSubring K O W.rank _).1 hm
    have h2 := (hGC.2.2.2 _).2 h1
    rw [map_mul, map_inv, hH g hg, hH g' hg'] at h2
    rw [hdist g hg g' hg' h2]
  have key := GlobalTheory.HermNbr.selfDual_sum_le O K cO cK (fun x => Subtype.ext (hσσ x)) (fun x => rfl)
    ⟨⟨x0, hx0⟩, hunit⟩ W.rank n 1 (by simp) (by simp) hn
    (C.image fun g => ((H g : GL (Fin W.rank) K))) hunitary hnontriv hdist'
  refine key.trans (le_of_eq ?_)
  rw [hcard]
  have hv0 : (0 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := Nat.cast_nonneg _
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hv0]
  norm_num

end GlobalTheory.InertIdx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InfinitesimalCharacterInduced
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.BCWords GlobalTheory.SpehInfChar GlobalTheory.BlockCap GlobalTheory.Published

namespace GlobalTheory.NormIndCap

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem tensorSp_update {c : ℕ} {n : Fin c → ℕ} (V : ∀ i, Submodule ℂ (Sm E (n i))) (i : Fin c)
    (m : ∀ j, GA E (n j)) {F : (∀ j, GA E (n j)) → ℂ} (hF : F ∈ tensorSp V) :
    ∃ θ ∈ V i, ∀ y, F (Function.update m i y) = θ.1 y := by
  classical
  let L : ((∀ j, GA E (n j)) → ℂ) →ₗ[ℂ] (GA E (n i) → ℂ) :=
    { toFun := fun F y => F (Function.update m i y), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hle : tensorSp V ≤ ((V i).map (Sm E (n i)).subtype).comap L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨φ, rfl⟩
    refine ⟨(∏ j ∈ Finset.univ.erase i, (φ j).1.1 (m j)) • (φ i).1, (V i).smul_mem _ (φ i).2, ?_⟩
    funext y
    change (∏ j ∈ Finset.univ.erase i, (φ j).1.1 (m j)) * (φ i).1.1 y =
      ∏ j, (φ j).1.1 (Function.update m i y j)
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  obtain ⟨θ, hθ, e⟩ := hle hF
  exact ⟨θ, hθ, fun y => (congrFun e y).symm⟩

theorem qdet_block_levi {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (V : ∀ i, Submodule ℂ (Sm E (n i)))
    (τ : E →+* ℂ) (i : Fin c) (M : Multiset ℂ) (hM : HasInfCharGL (V i) τ M) (u : ℂ) (ψ : Sm E N)
    (hψ : (fun m => ψ.1 (leviEmb (Ad E) (stdBlocks n h) m)) ∈ tensorSp V) (m : ∀ j, GA E (n j)) :
    (Formalism.REAL.qdet (fun p q : Fin (n i) => Eop (a := N) τ (stdBlocks n h ⟨i, p⟩) (stdBlocks n h ⟨i, q⟩))
      (u + ((n i : ℂ) - 1) / 2) ψ).1 (leviEmb (Ad E) (stdBlocks n h) m) =
      (M.map (u + ·)).prod * ψ.1 (leviEmb (Ad E) (stdBlocks n h) m) := by
  obtain ⟨θ, hθ, hθe⟩ := tensorSp_update V i m hψ
  have hR : restrLin (stdBlocks n h) m i ψ = θ := Subtype.ext (funext fun y => hθe y)
  have key := LinearMap.congr_fun (qdet_intertwine (restrLin (stdBlocks n h) m i) _ (Eop τ)
    (restrLin_Eop (stdBlocks n h) m i τ) (u + ((n i : ℂ) - 1) / 2)) ψ
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hR] at key
  have k2 := congrArg (fun φ : Sm E (n i) => φ.1 (m i)) key
  have hc : Formalism.REAL.qdet (Eop τ) (u + ((n i : ℂ) - 1) / 2) θ = (M.map (u + ·)).prod • θ := hM.2 u θ hθ
  have hm : Function.update m i (m i) = m := Function.update_eq_self i m
  simp only [hc] at k2
  have k3 : (Formalism.REAL.qdet (fun p q : Fin (n i) => Eop (a := N) τ (stdBlocks n h ⟨i, p⟩) (stdBlocks n h ⟨i, q⟩))
      (u + ((n i : ℂ) - 1) / 2) ψ).1 (leviEmb (Ad E) (stdBlocks n h) (Function.update m i (m i))) =
      (M.map (u + ·)).prod * θ.1 (m i) := k2
  rw [hm, ← hθe, hm] at k3
  exact k3

theorem hasInfCharGL_map_mulChi {a : ℕ} {V : Submodule ℂ (Sm E a)} {τ : E →+* ℂ} {m : Multiset ℂ}
    (h : HasInfCharGL V τ m) (χ : HChar E) :
    HasInfCharGL (V.map (mulChi a χ).toLinearMap) τ (m.map (· + expo χ τ)) := by
  refine ⟨by rw [Multiset.card_map]; exact h.1, ?_⟩
  rintro u _ ⟨φ, hφ, rfl⟩
  change cap τ u (mulChi a χ φ) = _ • mulChi a χ φ
  rw [cap_mulChi, h.2 _ φ hφ, map_smul, Multiset.map_map]
  congr 2
  exact Multiset.map_congr rfl fun x _ => by simp only [Function.comp_apply]; ring

end GlobalTheory.NormIndCap
end
end

