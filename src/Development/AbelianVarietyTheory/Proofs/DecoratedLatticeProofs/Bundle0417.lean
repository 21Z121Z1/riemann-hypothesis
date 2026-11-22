import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatNotSelfDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0395
import Formalism.LocalRingCardinality.Bundle0001
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0160
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0353
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0132
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0386
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0189
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0105
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0151
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0109
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqTransposeMulMapOfIdempotent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0381
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0396
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsComOfOf
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelTwistPrimesStepZeroCharacterEqOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeDataLocalRelation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam.UnrWeil

theorem natCast_mem_of_isConjPl {D : D7} (n : ℕ) {PP PP' : Formalism.L2.DIV.Pl D.host.E} (h : Lev.IsConjPl PP' PP)
    (hn : ((n : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) : ((n : ℕ) : 𝓞 D.host.E) ∈ PP'.asIdeal := by
  by_contra hn'
  obtain ⟨y, c, hc, hyc⟩ := PP'.isMaximal.exists_inv hn'
  obtain ⟨c', hc', e⟩ := h c hc
  apply PP.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have key : (1 : 𝓞 D.host.E) = RingOfIntegers.mapRingHom (starRingEnd D.host.E) y * ((n : ℕ) : 𝓞 D.host.E) + c' := by
    have h1 := congrArg (fun z : 𝓞 D.host.E => star (algebraMap (𝓞 D.host.E) D.host.E z)) hyc
    simp only [map_add, map_mul, map_natCast, map_one, star_add, star_mul', star_natCast, star_one] at h1
    have hy : algebraMap (𝓞 D.host.E) D.host.E (RingOfIntegers.mapRingHom (starRingEnd D.host.E) y) =
        star (algebraMap (𝓞 D.host.E) D.host.E y) := rfl
    have hc2 : algebraMap (𝓞 D.host.E) D.host.E c' = star (algebraMap (𝓞 D.host.E) D.host.E c) := e
    apply FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E
    simp only [map_add, map_mul, map_natCast, map_one, hy, hc2]
    rw [← h1]
  rw [key]
  exact PP.asIdeal.add_mem (PP.asIdeal.mul_mem_left _ hn) hc'

theorem not_both_mem {D : D7} {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (PP : Formalism.L2.DIV.Pl D.host.E)
    (h1 : ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) (h2 : ((q : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) : False := by
  obtain ⟨a, b, hab⟩ : IsCoprime ((p : ℕ) : 𝓞 D.host.E) ((q : ℕ) : 𝓞 D.host.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ PP.asIdeal.add_mem (PP.asIdeal.mul_mem_left a h1) (PP.asIdeal.mul_mem_left b h2)))

end GlobalTheory.Fam.UnrWeil

open GlobalTheory.Fam.UnrWeil in

theorem GlobalTheory.Fam.kom_weil_unram : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (f : FamCh W u) (v : VCom f.c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat f.c k ι), f.RowOK → f.ColOK → v.Is → VTie f v → ShapeOff v o → ∀ t j, j < D.R.m → ∃ μ, IsWeilDatumO f.c.ψ _ _ μ μ ((f.t t).kom j) ∧ ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D μ (o.p i).v := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW f v k _ _ _ _ ι o _ hC _ hV hS t j hj
  refine ⟨(pk W).toLevCh.mu t (j + 1), hC.kom t j hj, fun i => ?_⟩
  have lev : (pk W).toLevCh.Is W.P.A3.A.μ0 := hW.bot.hyp.2.2.2.1.lev
  have hp : (o.p i).v ∈ v.tP := (hS.pre.tP _).2 ⟨i, rfl⟩
  have hTF : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (o.p i).v.asIdeal := (hV.tP _).1 hp
  have hTw : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = (o.p i).v →
      (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
    intro w hw
    rw [← hw] at hTF
    have := Ideal.mem_comap.1 hTF
    simpa using this
  show GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (Formalism.IndefR.Lift.tup (pk W).toLevCh.mu0 ((pk W).toLevCh.xi t) (j + 1)) (o.p i).v
  refine GlobalTheory.SeeSaw.WeilLines.charUnram_mul ?_ ?_
  · refine GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w hw => ?_
    refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (lev.mu0 ⟨j, hj⟩) w).2 ?_
    refine ((pk W).toLevCh.C.isMu0 ⟨j, hj⟩).unr w fun kk hk => ?_
    exact not_both_mem (D.mem u).A.T_prime (D.host.g_prime kk) (D.T_ne_g u kk) w (hTw w hw) hk
  · refine GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w hw => ?_
    refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (lev.xi t) w).2 ?_
    by_contra hr
    rcases (lev.Q_ram t w).1 hr with hq | ⟨PP', hq, hc⟩
    · exact (lev.Q_off t w hq).2 u (hTw w hw)
    · exact (lev.Q_off t PP' hq).2 u (natCast_mem_of_isConjPl _ hc (hTw w hw))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedTermBasePointEqFlatMapPairing
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

noncomputable section

namespace GlobalTheory.FlatBase

variable {D : D7}

theorem continuous_psiUni {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) (ρ : ℕ) :
    Continuous fun u : UX D ρ => psiUni ψ u.1 := by
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  have hc : Continuous fun u : UX D ρ => (u.1.1 : Mx D ρ ρ) := Units.continuous_val.comp continuous_subtype_val
  have hu : Continuous fun u : UX D ρ => upSum (u.1.1 : Mx D ρ ρ) := by
    unfold upSum
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    split_ifs
    · exact (continuous_apply j).comp ((continuous_apply i).comp hc)
    · exact continuous_const
  exact hψ.comp (ht.comp hu)

theorem integral_swap_of_majorant {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure α) (μ : Measure β) [IsFiniteMeasure μ] (K : α → β → ℂ)
    (hK : StronglyMeasurable (Function.uncurry K)) (M : α → ℝ) (hM : Integrable M ν) (C : ℝ)
    (hb : ∀ u v, ‖K u v‖ ≤ M u * C) :
    ∫ u, ∫ v, K u v ∂μ ∂ν = ∫ v, ∫ u, K u v ∂ν ∂μ := by
  obtain ⟨t, htm, hMt, hσ⟩ := hM.aefinStronglyMeasurable.exists_set_sigmaFinite
  have h0 : ∀ᵐ u ∂ν, u ∈ tᶜ → M u = 0 := (ae_restrict_iff' htm.compl).1 hMt
  have hz : ∀ᵐ u ∂ν, u ∉ t → ∀ v, K u v = 0 := h0.mono fun u hu hut v => by
    have h := hb u v
    rw [hu hut, zero_mul] at h
    exact norm_le_zero_iff.1 h
  have e1 : ∫ u, ∫ v, K u v ∂μ ∂ν = ∫ u in t, ∫ v, K u v ∂μ ∂ν :=
    (setIntegral_eq_integral_of_ae_compl_eq_zero (hz.mono fun u hu hut => by simp [hu hut])).symm
  have e2 : (fun v => ∫ u, K u v ∂ν) = fun v => ∫ u in t, K u v ∂ν := funext fun v =>
    (setIntegral_eq_integral_of_ae_compl_eq_zero (hz.mono fun u hu hut => hu hut v)).symm
  rw [e1, e2]
  haveI := hσ
  refine integral_integral_swap ?_
  refine Integrable.mono' ((hM.restrict (s := t)).mul_prod (integrable_const C)) hK.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun p => hb p.1 p.2

end GlobalTheory.FlatBase

namespace GlobalTheory.Unf.FB

open GlobalTheory.FlatBase

theorem fl_base_eq_tFlat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vb : VolM D (σ + 1) J.W₀.rank) (vL : VolM D B.L.rank J.W₀.rank) (y : WO J.W₀ B.L → ℂ) (Ψ : WO J.W B.V → ℂ), Quasi ψ J.W₀ B.L y → IsThetaFunO ψ J.W B.V Ψ → fl ψ J.d B.V s.vS vb s.vU (th J ψ B y) (x0 B) Ψ = tFlat s vL y Ψ ∧ ∀ M : ℝ, (∀ w, ‖y w‖ ≤ M) → ‖tFlat s vL y Ψ‖ₑ ≤ ENNReal.ofReal M * ∫⁻ u, ∫⁻ b in vb.𝓕, ‖J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 Ψ (x0 B ⬝ u.1.1) (x0 B ⬝ b)‖ₑ ∂vb.μ ∂s.vU.ν := by
  intro D ψ σ J B s vb vL y Ψ hy hΨ
  have hstd : IsStdChar D ψ (-1) := s.weil.std
  have hchar := hstd.1
  obtain ⟨-, ⟨My, hMy, -⟩, -, -, -, hlaw⟩ := GlobalTheory.T.fourierBesselThetaCharIntegrand_laws D ψ hstd σ J B y hy
  have hnorm : ∀ u : UX D (σ + 1), ‖psiUni ψ u.1‖ = 1 := fun u => hchar.2.1 _

  have hfl : ∀ u : UX D (σ + 1), (∫ b in vb.𝓕, flFun ψ J.d B.V s.vS (th J ψ B y) (x0 B) Ψ u b ∂vb.μ) =
      star (psiUni ψ u.1) * ∫ v in vL.𝓕, evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (x0 B ⬝ u.1.1) 0
        ((B.o.resT J.W₀).symm (0, v)) * star (y v) ∂vL.μ := by
    intro u
    have hf : Quasi ψ J.W₀ B.V (J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 Ψ (x0 B ⬝ u.1.1)) := by
      have h := (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ hstd).1 J.W J.W₀ B.V (σ + 1) J.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ (x0 B ⬝ u.1.1)
      exact ⟨h.quasi, h.cont⟩
    have hh := (GlobalTheory.T.heisenbergIntegral_fourierBesselBasePoint_eq_pairing D ψ hstd σ J.W₀ B vb s.vT vL _ y hf hy).1
    calc (∫ b in vb.𝓕, flFun ψ J.d B.V s.vS (th J ψ B y) (x0 B) Ψ u b ∂vb.μ)
        = ∫ b in vb.𝓕, star (psiUni ψ u.1) * (J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 Ψ (x0 B ⬝ u.1.1) (x0 B ⬝ b) *
            star (y (zl B ⬝ b))) ∂vb.μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
          simp only [flFun]
          rw [hlaw b u.1 u.2]
          ring
      _ = _ := by
          rw [integral_const_mul]
          exact congrArg (star (psiUni ψ u.1) * ·) hh
  have hLeft : fl ψ J.d B.V s.vS vb s.vU (th J ψ B y) (x0 B) Ψ = ∫ u, star (psiUni ψ u.1) *
      ∫ v in vL.𝓕, evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (x0 B ⬝ u.1.1) 0
        ((B.o.resT J.W₀).symm (0, v)) * star (y v) ∂vL.μ ∂s.vU.ν := by
    unfold fl
    exact integral_congr_ae (Filter.Eventually.of_forall hfl)

  obtain ⟨x, hxo, hx⟩ := GlobalTheory.T.exists_mem_orb_rat_eq_x0 D σ B
  obtain ⟨M, hMi, hMb⟩ := GlobalTheory.T.flatThetaIntegrand_locallyUniform_majorant D ψ J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s.vS s.vT s.χV s.χW s.om s.weil s.vU x
    hxo.1 Ψ hΨ {1} isCompact_singleton
  have hom1 : s.om 1 Ψ = Ψ := by rw [map_one]; rfl
  have hbound : ∀ (u : UX D (σ + 1)) (v : WO J.W₀ B.L),
      ‖flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (x0 B) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u * star (y v)‖ ≤
        M u * My := by
    intro u v
    have h := hMb 1 (Set.mem_singleton 1) 0 ((B.o.resT J.W₀).symm (0, v)) u
    rw [hx, hom1] at h
    rw [norm_mul, norm_star]
    exact mul_le_mul h (hMy v) (norm_nonneg _) ((norm_nonneg _).trans h)
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have : BorelSpace (UX D (σ + 1)) := ⟨rfl⟩
  have : BorelSpace (WO J.W₀ B.L) := ⟨rfl⟩
  have : SecondCountableTopology (WO J.W₀ B.L) := (lattice_Mx D B.L.rank J.W₀.rank).2.2.1
  have hE : Continuous fun p : UX D (σ + 1) × WO J.W₀ B.L =>
      evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (x0 B ⬝ p.1.1.1) 0 ((B.o.resT J.W₀).symm (0, p.2)) := by
    have hmc := (GlobalTheory.T.weilMixedCoordinates_continuous_bounded_supNorm D ψ J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s.vS s.vT s.χV s.χW s.om s.weil Ψ hΨ).2
    have hc : Continuous fun p : UX D (σ + 1) × WO J.W₀ B.L => (p.1.1.1 : Mx D (σ + 1) (σ + 1)) :=
      (Units.continuous_val.comp continuous_subtype_val).comp continuous_fst
    have hin : Continuous fun p : UX D (σ + 1) × WO J.W₀ B.L =>
        ((1 : GA D J.W × GA D B.V), x0 B ⬝ p.1.1.1, (0 : Mx D J.W₀.rank σ), (B.o.resT J.W₀).symm (0, p.2)) :=
      continuous_const.prodMk ((continuous_const.matrix_mul hc).prodMk (continuous_const.prodMk
        ((B.o.continuous_resT_symm J.W₀).comp (continuous_const.prodMk continuous_snd))))
    have h := hmc.comp hin
    simpa only [Function.comp_def, hom1] using h
  have hK : Continuous (Function.uncurry fun (u : UX D (σ + 1)) (v : WO J.W₀ B.L) =>
      flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (x0 B) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u * star (y v)) :=
    ((continuous_star.comp ((continuous_psiUni hchar.1 (σ + 1)).comp continuous_fst)).mul hE).mul
      (continuous_star.comp (hy.2.comp continuous_snd))
  haveI : IsFiniteMeasure (vL.μ.restrict vL.𝓕) := isFiniteMeasure_restrict.2 (by rw [vL.covol.2.2]; simp)
  have hswap := integral_swap_of_majorant s.vU.ν (vL.μ.restrict vL.𝓕) (fun u v =>
      flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (x0 B) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u * star (y v))
    hK.stronglyMeasurable M hMi My hbound
  have h1 : fl ψ J.d B.V s.vS vb s.vU (th J ψ B y) (x0 B) Ψ = tFlat s vL y Ψ := by
    rw [hLeft]
    calc (∫ u, star (psiUni ψ u.1) * ∫ v in vL.𝓕, evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (x0 B ⬝ u.1.1) 0
            ((B.o.resT J.W₀).symm (0, v)) * star (y v) ∂vL.μ ∂s.vU.ν)
        = ∫ u, ∫ v in vL.𝓕, flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (x0 B) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u *
            star (y v) ∂vL.μ ∂s.vU.ν := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          dsimp only
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
          simp only [flatFun]
          ring
      _ = ∫ v in vL.𝓕, ∫ u, flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (x0 B) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u *
            star (y v) ∂s.vU.ν ∂vL.μ := hswap
      _ = ∫ v in vL.𝓕, (∫ u, flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (x0 B) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u
            ∂s.vU.ν) * star (y v) ∂vL.μ :=
          integral_congr_ae (Filter.Eventually.of_forall fun v => integral_mul_const _ _)
      _ = tFlat s vL y Ψ := rfl
  refine ⟨h1, fun Mb hMb' => ?_⟩
  rw [← h1]
  unfold fl
  calc ‖∫ u, ∫ b in vb.𝓕, flFun ψ J.d B.V s.vS (th J ψ B y) (x0 B) Ψ u b ∂vb.μ ∂s.vU.ν‖ₑ
      ≤ ∫⁻ u, ‖∫ b in vb.𝓕, flFun ψ J.d B.V s.vS (th J ψ B y) (x0 B) Ψ u b ∂vb.μ‖ₑ ∂s.vU.ν :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ u, ∫⁻ b in vb.𝓕, ‖flFun ψ J.d B.V s.vS (th J ψ B y) (x0 B) Ψ u b‖ₑ ∂vb.μ ∂s.vU.ν :=
        lintegral_mono fun u => enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ u, ∫⁻ b in vb.𝓕, ENNReal.ofReal Mb *
          ‖J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 Ψ (x0 B ⬝ u.1.1) (x0 B ⬝ b)‖ₑ ∂vb.μ ∂s.vU.ν := by
        refine lintegral_mono fun u => lintegral_mono fun b => ?_
        simp only [flFun]
        rw [enorm_mul]
        gcongr
        rw [hlaw b u.1 u.2, ← ofReal_norm_eq_enorm, norm_mul, norm_star, norm_star, hnorm u, one_mul]
        exact ENNReal.ofReal_le_ofReal (hMb' _)
    _ = _ := (lintegral_congr fun u => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).trans
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)

end GlobalTheory.Unf.FB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnimodularHermitianCongrOneAtTamePlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

namespace GlobalTheory.IwaPlace.UnimodNF

section Abstract

variable {A : Type*} [CommRing A] {ε : A} (hid : IsIdempotentElem ε) (O : Set A)
  (h0 : (0 : A) ∈ O) (hadd : ∀ a ∈ O, ∀ b ∈ O, a + b ∈ O) (hneg : ∀ a ∈ O, -a ∈ O)
  (hmul : ∀ a ∈ O, ∀ b ∈ O, a * b ∈ O) (hεO : ε ∈ O)

def sub : Subring hid.Corner where
  carrier := {x | x.1 ∈ O}
  zero_mem' := h0
  add_mem' {x y} hx hy := hadd _ hx _ hy
  neg_mem' {x} hx := hneg _ hx
  mul_mem' {x y} hx hy := hmul _ hx _ hy
  one_mem' := hεO

include hid h0 hadd hneg hmul hεO in

theorem exists_congr_one (c : A →+* A) (hc : ∀ x, c (c x) = x) (hcO : ∀ a ∈ O, c a ∈ O) (hcε : c ε = ε)
    (hεa : ∀ a ∈ O, ε * a = a)
    (hloc : ∀ x ∈ O, c x = x → (∃ y ∈ O, x * y = ε) ∨ (∃ y ∈ O, (ε - x) * y = ε))
    (hw : ∃ w ∈ O, w + c w = ε)
    (hnorm : ∀ u ∈ O, c u = u → (∃ y ∈ O, u * y = ε) → ∃ x ∈ O, x * c x = u)
    {n : ℕ} (H : Matrix (Fin n) (Fin n) A) (hH : ∀ i j, H i j ∈ O) (hherm : ∀ i j, c (H i j) = H j i)
    (hinv : ∃ H' : Matrix (Fin n) (Fin n) A, (∀ i j, H' i j ∈ O) ∧ H * H' = ε • (1 : Matrix (Fin n) (Fin n) A)) :
    ∃ P P' : Matrix (Fin n) (Fin n) A, (∀ i j, P i j ∈ O) ∧ (∀ i j, P' i j ∈ O) ∧
      P * P' = ε • (1 : Matrix (Fin n) (Fin n) A) ∧ P' * P = ε • (1 : Matrix (Fin n) (Fin n) A) ∧
      (P.map c)ᵀ * (H * P) = ε • (1 : Matrix (Fin n) (Fin n) A) := by
  classical
  let R := sub hid O h0 hadd hneg hmul hεO
  have corner_mem : ∀ a ∈ O, a ∈ Subsemigroup.corner ε := fun a ha =>
    (Subsemigroup.mem_corner_iff hid).2 ⟨hεa a ha, by rw [mul_comm]; exact hεa a ha⟩
  let mk : ∀ a, a ∈ O → R := fun a ha => ⟨⟨a, corner_mem a ha⟩, ha⟩
  let val : R →+ A := { toFun := fun x => x.1.1, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have val_mem : ∀ x : R, val x ∈ O := fun x => x.2
  have val_inj : ∀ x y : R, val x = val y → x = y := fun x y h => Subtype.ext (Subtype.ext h)
  let c' : R →+* R :=
    { toFun := fun x => mk (c (val x)) (hcO _ (val_mem x))
      map_one' := val_inj _ _ (show c ε = ε from hcε)
      map_mul' := fun x y => val_inj _ _ (show c (val x * val y) = c (val x) * c (val y) from map_mul c _ _)
      map_zero' := val_inj _ _ (show c 0 = 0 from map_zero c)
      map_add' := fun x y => val_inj _ _ (show c (val x + val y) = c (val x) + c (val y) from map_add c _ _) }
  have hc' : ∀ x, c' (c' x) = x := fun x => val_inj _ _ (show c (c (val x)) = val x from hc _)
  have map_mul_val : ∀ X Y : Matrix (Fin n) (Fin n) R, (X * Y).map val = X.map val * Y.map val := by
    intro X Y
    ext i j
    simp only [Matrix.map_apply, Matrix.mul_apply, map_sum]
    rfl
  have map_one_val : (1 : Matrix (Fin n) (Fin n) R).map val = ε • (1 : Matrix (Fin n) (Fin n) A) := by
    ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · simp only [smul_eq_mul, mul_one]; rfl
    · simp only [smul_eq_mul, mul_zero, map_zero]
  have map_inj : ∀ X Y : Matrix (Fin n) (Fin n) R, X.map val = Y.map val → X = Y := fun X Y h =>
    Matrix.ext fun i j => val_inj _ _ (congrFun (congrFun h i) j)
  let G : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => mk (H i j) (hH i j)
  have hGH : G.map val = H := by ext i j; rfl
  obtain ⟨H', hH'O, hHH'⟩ := hinv
  let G' : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => mk (H' i j) (hH'O i j)
  have hG'H : G'.map val = H' := by ext i j; rfl
  have hGG' : G * G' = 1 := map_inj _ _ (by rw [map_mul_val, map_one_val, hGH, hG'H]; exact hHH')
  have hdet : IsUnit G.det := Matrix.isUnit_det_of_right_inverse hGG'
  have hG : ∀ a b, c' (G a b) = G b a := fun a b => val_inj _ _ (hherm a b)
  have hlocR : ∀ x : R, c' x = x → IsUnit x ∨ IsUnit (1 - x) := by
    intro x hx
    have hx' : c (val x) = val x := congrArg val hx
    rcases hloc (val x) (val_mem x) hx' with ⟨y, hy, hxy⟩ | ⟨y, hy, hxy⟩
    · exact Or.inl (isUnit_iff_exists_inv.2 ⟨mk y hy, val_inj _ _ hxy⟩)
    · exact Or.inr (isUnit_iff_exists_inv.2 ⟨mk y hy, val_inj _ _ hxy⟩)
  have hwR : ∃ w : R, w + c' w = 1 := by
    obtain ⟨w, hw, hw'⟩ := hw
    exact ⟨mk w hw, val_inj _ _ hw'⟩
  have hnormR : ∀ u : R, c' u = u → IsUnit u → ∃ x, x * c' x = u := by
    intro u hu hu'
    obtain ⟨y, hy⟩ := hu'.exists_right_inv
    obtain ⟨x, hx, hx'⟩ := hnorm (val u) (val_mem u) (congrArg val hu) ⟨val y, val_mem y, congrArg val hy⟩
    exact ⟨mk x hx, val_inj _ _ hx'⟩
  obtain ⟨Q, hQ, hGQ⟩ :=
    GlobalTheory.UnramifiedHermitian.exists_eq_transpose_mul_map_of_isUnit_or c' hc' hlocR hwR hnormR hG hdet
  have hmap1 : (1 : Matrix (Fin n) (Fin n) R).map c' = 1 := Matrix.map_one _ (map_zero c') (map_one c')
  refine ⟨((Q⁻¹).map c').map val, (Q.map c').map val, fun i j => val_mem _, fun i j => val_mem _, ?_, ?_, ?_⟩
  · rw [← map_mul_val, ← Matrix.map_mul, Matrix.nonsing_inv_mul Q hQ, hmap1, map_one_val]
  · rw [← map_mul_val, ← Matrix.map_mul, Matrix.mul_nonsing_inv Q hQ, hmap1, map_one_val]
  · have e1 : (((Q⁻¹).map c').map val).map c = (Q⁻¹).map val := by
      ext i j
      exact congrArg val (hc' (Q⁻¹ i j))
    rw [e1, ← Matrix.transpose_map, ← hGH, ← map_mul_val, ← map_mul_val, ← map_one_val]
    congr 1
    have h1 : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQ
    rw [hGQ]
    calc (Q⁻¹)ᵀ * (Qᵀ * Q.map c' * (Q⁻¹).map c') = (Q * Q⁻¹)ᵀ * (Q * Q⁻¹).map c' := by
          rw [Matrix.transpose_mul, Matrix.map_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.transpose_one, hmap1, Matrix.one_mul]

end Abstract

set_option synthInstance.maxHeartbeats 400000

variable {D : D7}

theorem intAt_zero' (P : Pl D → Prop) : (0 : AE D) ∈ intAt D P := ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩

theorem intAt_neg' {P : Pl D → Prop} {a : AE D} (ha : a ∈ intAt D P) : -a ∈ intAt D P :=
  ⟨neg_mem ha.1, by rw [RingHom.map_neg]; exact neg_mem ha.2⟩

theorem cA_mem_intAt' {v : Pl D} {a : AE D} (ha : a ∈ intAt D (· = v)) : cA D a ∈ intAt D (· = v) :=
  ⟨GlobalTheory.FinPl.RootKeep.conj_mem_idAt ha.1, (GlobalTheory.FinPl.FrameLat.cA_int_iff a).2 ha.2⟩

theorem unimodular_congr_one : ∀ (D : D7) (v : Pl D) (ε : AE D) (n : ℕ) (H : Matrix (Fin n) (Fin n) (AE D)), Tame D v → ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) → (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → (∀ i j, H i j ∈ intAt D (· = v)) → (∀ i j, cA D (H i j) = H j i) → (∃ H' : Matrix (Fin n) (Fin n) (AE D), (∀ i j, H' i j ∈ intAt D (· = v)) ∧ H * H' = ε • (1 : Matrix (Fin n) (Fin n) (AE D))) → ∃ P P' : Matrix (Fin n) (Fin n) (AE D), (∀ i j, P i j ∈ intAt D (· = v)) ∧ (∀ i j, P' i j ∈ intAt D (· = v)) ∧ P * P' = ε • (1 : Matrix (Fin n) (Fin n) (AE D)) ∧ P' * P = ε • (1 : Matrix (Fin n) (Fin n) (AE D)) ∧ adj P * (H * P) = ε • (1 : Matrix (Fin n) (Fin n) (AE D)) := by
  intro D v ε n H htame hεε hεc hεI hε hHI hherm hinv
  exact exists_congr_one (hid := hεε) (O := intAt D (· = v)) (intAt_zero' _)
    (fun a ha b hb => GlobalTheory.IwaPlace.SdComap.intAt_add ha hb) (fun a ha => intAt_neg' ha)
    (fun a ha b hb => GlobalTheory.IwaPlace.SdComap.intAt_mul ha hb) hεI (cA D) (fun z => Formalism.L2.Theta.cA_cA z)
    (fun a ha => cA_mem_intAt' ha) hεc (fun a ha => (hε a).1 ha.1)
    (GlobalTheory.T.conjFixed_integral_isUnit_or_idem_sub_unit D v ε htame hεε hεc hεI hε)
    (GlobalTheory.IwaPlace.exists_trace_one_at_tame D v ε hεε hεc hεI hε htame)
    (GlobalTheory.T.exists_norm_of_conjFixed_unit_tamePlace D v ε htame hεε hεc hεI hε) H hHI hherm hinv

end GlobalTheory.IwaPlace.UnimodNF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedHeckeCharAtUniformizerIdeleEqValueStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedHeckeChar_at_uniformizerIdele_eq_value : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (PP : Pl D.host.E), IsProjAt φ PP → ∀ (x : (AE D)ˣ) (ϖ : (Fv D.host.F v)ˣ), IsLocUnif φ x ϖ → ∀ χ : (AE D)ˣ →* Circle, GlobalTheory.LFun.UnrAt (F := D.host.F) χ PP → Circle.toUnits (χ x) = GlobalTheory.LFun.val (F := D.host.F) χ PP := by
  first | exact @GlobalTheory.LocUnifVal.value_eq_val | exact GlobalTheory.LocUnifVal.value_eq_val | (intros; apply GlobalTheory.LocUnifVal.value_eq_val <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValConjSubLt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LatPair

namespace GlobalTheory.SeeSaw.LevChi

open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (colGroup colChar colPos superSum)
open GlobalTheory.SymBridge

section Split

variable {D : D7} {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : GlobalTheory.FinPl.SplitPt D K) {PP : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt q.e PP)
include h

theorem val_rat_lt {y : D.host.E} (hy : PP.valuation D.host.E y < 1) : valuation K (q.pr (incA D y)) < 1 := by
  obtain ⟨r, d, e⟩ := PP.exists_primeCompl_mul_eq_of_integer y hy.le
  have hd : valuation K (q.pr (incA D ((d : 𝓞 D.host.E) : D.host.E))) = 1 :=
    le_antisymm (LevelTest.val_le_one q _) (not_lt.1 fun h' => d.2 ((LevelTest.val_lt_one_iff q h _).1 h'))
  have hr : r ∈ PP.asIdeal := by
    refine (HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.host.E) PP r).1 ?_
    show PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E r) < 1
    rw [← e, map_mul]
    exact (mul_le_of_le_one_right' (PP.valuation_le_one _)).trans_lt hy
  have := (LevelTest.val_lt_one_iff q h r).2 hr
  rwa [show (r : D.host.E) = y * ((d : 𝓞 D.host.E) : D.host.E) from e.symm, map_mul, map_mul, map_mul, hd, mul_one] at this

set_option maxHeartbeats 1000000 in

theorem val_pr_lt {z : AE D} (hz : Valued.v (adAt D.host.F PP (toEAf D z)) < 1) : valuation K (q.pr z) < 1 := by
  obtain ⟨y, N, r, hr, hN, e⟩ := exists_approx_small (F := D.host.F) (toEAf D z) {PP} (γ := 1) one_ne_zero
  have hN' := hN PP (Finset.mem_singleton_self PP)
  have h1 : PP.valuation D.host.E y < 1 := by
    rw [← valued_algebraMap, ← adAt_inclE D.host.F, ← sub_eq_iff_eq_add.2 e, map_sub]
    exact Valuation.map_sub_lt _ hz (valued_nat_mul_lt hr hN')
  have hnat : ∀ M : ℕ, (M : 𝓞 D.host.E) ∈ PP.asIdeal → valuation K (M : K) < 1 := fun M hM => by
    simpa using (LevelTest.val_lt_one_iff q h _).2 hM
  let sw := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E)
  have hf : finPart D (z - incA D y) = (N : Af D.host.F ⊗[D.host.F] D.host.E) * sw.symm r := by
    apply sw.injective
    rw [map_mul, map_natCast, AlgEquiv.apply_symm_apply]
    show toEAf D (z - incA D y) = _
    rw [RingHom.map_sub, e]
    exact add_sub_cancel_left _ _
  have h2 : valuation K (q.pr (z - incA D y)) < 1 := by
    rcases Nat.eq_zero_or_pos N with rfl | hpos
    · refine (GlobalTheory.FinPl.SplitApprox.val_le q (Ideal.absNorm PP.asIdeal)
        (Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact PP.ne_bot)) _ 0 (zero_mem _) ?_).trans_lt
        (hnat _ (Ideal.absNorm_mem _))
      rw [hf, Nat.cast_zero, zero_mul, mul_zero]
    · refine (GlobalTheory.FinPl.SplitApprox.val_le q N hpos _ _ ((GlobalTheory.IdemSupport.mem_intAE_iff _).2 ?_) hf).trans_lt (hnat _ ?_)
      · exact (show Lev.swapAE D (sw.symm r) = r from sw.apply_symm_apply r).symm ▸ hr
      · rw [LevRead.valued_natCast] at hN'
        exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.host.E) PP _).1 hN'
  have h3 := (valuation K).map_add_lt h2 (val_rat_lt q h h1)
  rwa [← map_add, sub_add_cancel] at h3

end Split

section Local

variable {D : D7} {u : D.what₂.Word} {a : XPart D u} {ζ₀ : Fin a.Lz.rank → D.host.E} {PP : Formalism.L2.DIV.Pl D.host.E} (H : GX a ζ₀ PP)

def LamIs (κ : GA D (D.sp.X 0)) (c : ℂ) : Prop :=
  ∀ (g : GL (XIx (Fin D.R.k) (Fin D.R.t) 0) H.k) (hg : embX (H.s + 1) g ∈ H.lev0.J), H.MatAt κ g →
    ((H.lev0.lam ⟨_, hg⟩ : ℂˣ) : ℂ) = c

end Local

end GlobalTheory.SeeSaw.LevChi

end
end

