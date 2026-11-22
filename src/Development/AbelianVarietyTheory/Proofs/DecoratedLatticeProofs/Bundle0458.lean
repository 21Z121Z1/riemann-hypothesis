import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0170
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0421
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0198
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0216
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0437
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotLevGEmpty
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0036
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0438
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0445
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIdAtOfSupp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingIntegralsVanishOfAllLiftsVanish
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.Kill

variable {D : D7}

theorem exists_bound_of_fundamentalDomain {A : HSp D} {m : Measure (GA D A)} [m.IsHaarMeasure] {X K : Set (GA D A)}
    (hX : IsFundamentalDomain (GQ A) X m) (hK : IsCompact K) (hXK : X ⊆ K) {u : GA D A → ℂ} (hu : Continuous u)
    (hi : ∀ γ ∈ GQ A, ∀ g, u (γ * g) = u g) : ∃ C : ℝ, ∀ g, ‖u g‖ ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hu.continuousOn
  refine ⟨C, fun g => ?_⟩
  by_contra hg
  push_neg at hg
  have hopen : IsOpen {x | C < ‖u x‖} := isOpen_lt continuous_const hu.norm
  have hpos : 0 < m {x | C < ‖u x‖} := hopen.measure_pos m ⟨g, hg⟩
  have hnull : m {x | C < ‖u x‖} = 0 := by
    have hcov := hX.ae_covers
    rw [ae_iff] at hcov
    refine measure_mono_null (fun x hx => ?_) hcov
    simp only [Set.mem_setOf_eq, not_exists]
    intro γ hγ
    have h1 := hC _ (hXK hγ)
    rw [Subgroup.smul_def, smul_eq_mul, hi _ γ.2] at h1
    exact absurd h1 (not_le.2 hx)
  exact hpos.ne' hnull

theorem thetaKO_rat {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle} {om : WRep S T}
    (hom : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (h : GA D T) :
    ∀ γ ∈ GQ S, ∀ g, thetaKO om (γ * g) h f = thetaKO om g h f := fun γ hγ g => by
  have e : ((γ * g, h) : GA D S × GA D T) = (γ, 1) * (g, h) := by simp
  simp only [thetaKO]
  rw [e, map_mul, Module.End.mul_apply]
  exact hom.om_aut γ hγ 1 (one_mem _) _ (hom.om_pres _ f hf)

theorem continuous_thetaKO {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle} {om : WRep S T}
    (hom : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (h : GA D T) :
    Continuous fun g => thetaKO om g h f :=
  (hom.om_cont f hf 0).comp (continuous_id.prodMk continuous_const)

theorem kills_of_noLift : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A W : HSp D) (χA χW : (AE D)ˣ →* Circle)
    (om : WRep A W) (omh : WRep (dblSp A) W), HSpace.SigOK A → HSpace.IsPosDef A → IsWeilDatumO ψ A W χA χW om →
    IsWeilDatumO ψ (dblSp A) W 1 χW omh → ∀ m : Measure (GA D A), m.IsHaarMeasure → ∀ u : GA D A → ℂ, Continuous u →
    (∀ γ ∈ GQ A, ∀ g, u (γ * g) = u g) → NoLift ψ om m u → Kills ψ χW omh m u := by
  intro D ψ A W χA χW om omh hsig hpos hom homh m hm u hu hui hno φ hφ h
  haveI := hm
  obtain ⟨-, X, K, hXm, hX, hK, hXK⟩ := GlobalTheory.T.definite_unitary_quotient_compact_fundamentalDomain D A hsig hpos m hm
  have hTC := GlobalTheory.T.doublingMap_thetaIdentity_any_weilData D ψ A W χA χW om omh hom homh
  obtain ⟨C, hC⟩ := exists_bound_of_fundamentalDomain hX hK hXK hu hui
  have hχ : IsHeckeChar D χW := hom.hecT
  have hχi : IsHeckeChar D χW⁻¹ :=
    ⟨continuous_inv.comp hχ.1, fun x => by rw [MonoidHom.inv_apply, hχ.2 x, inv_one]⟩

  have hEc : Continuous fun g => thetaKO omh g h φ := continuous_thetaKO homh hφ h
  have hEi : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ (dblSp A)) fun g => thetaKO omh g h φ := thetaKO_rat homh hφ h
  have hcu : Continuous fun g => conj (u g) := Complex.continuous_conj.comp hu
  have hcui : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ A) fun g => conj (u g) := fun γ hγ g => by
    simp only [hui γ hγ g]

  have hFc := Eis.continuous_dblIntegrand (V := A) hχi hEc hcu hcu
  have hFi := Eis.leftInv_dblIntegrand (V := A) hχi hEi hcui hcui
  have hFint : IntegrableOn (Eis.dblIntegrand A χW⁻¹ (fun g => thetaKO omh g h φ) (fun g => conj (u g))
      (fun g => conj (u g))) (X ×ˢ X) (m.prod m) :=
    (hFc.continuousOn.integrableOn_compact (hK.prod hK)).mono_set (Set.prod_mono hXK hXK)
  have hconv := (Eis.dblConv_iff hFi hFc.measurable hX).2 hFint
  show Eis.dblInt A χW⁻¹ m (fun g => thetaKO omh g h φ) (fun g => conj (u g)) (fun g => conj (u g)) = 0
  rw [(hconv.dblInt_eq hX).2, ← Measure.prod_restrict]
  haveI : IsFiniteMeasure (m.restrict X) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (measure_mono hXK).trans_lt hK.measure_lt_top⟩

  set μ : Measure (GA D A × GA D A) := (m.restrict X).prod (m.restrict X) with hμ
  set c : GA D A × GA D A → ℂ := fun g => u g.1 * conj (u g.2) * (χW (detA A g.2) : ℂ) with hc
  set p : GA D A × GA D A → GA D (dblSp A) × GA D W := fun g => (io A g, h) with hp
  have hint : ∀ G : GA D A × GA D A → ℂ, Continuous G → Integrable G μ := fun G hG => by
    rw [hμ, Measure.prod_restrict]
    exact (hG.continuousOn.integrableOn_compact (hK.prod hK)).mono_set (Set.prod_mono hXK hXK)
  have hFeq : ∀ g, Eis.dblIntegrand A χW⁻¹ (fun g => thetaKO omh g h φ) (fun g => conj (u g))
      (fun g => conj (u g)) g = c g * omh (p g) φ 0 := fun g => by
    simp only [Eis.dblIntegrand, hc, hp, thetaKO, MonoidHom.inv_apply, Circle.coe_inv, inv_inv, Complex.conj_conj]
    ring
  simp_rw [hFeq]
  have hcc : Continuous c :=
    ((hu.comp continuous_fst).mul (Complex.continuous_conj.comp (hu.comp continuous_snd))).mul
      (continuous_subtype_val.comp (hχ.1.comp (Eis.continuous_detA.comp continuous_snd)))
  have hcb : ∀ g, ‖c g‖ ≤ C * C := fun g => by
    simp only [hc, norm_mul, Complex.norm_conj, Circle.norm_coe, mul_one]
    exact mul_le_mul (hC _) (hC _) (norm_nonneg _) ((norm_nonneg _).trans (hC g.1))
  have hpc : Continuous p := (continuous_io A).prodMk continuous_const
  have hK' : IsCompact (p '' (K ×ˢ K)) := (hK.prod hK).image hpc
  have hae : ∀ᵐ x ∂μ, p x ∈ p '' (K ×ˢ K) := by
    rw [hμ, Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (hXm.prod hXm)] with x hx
    exact ⟨x, Set.prod_mono hXK hXK hx, rfl⟩

  set M : Submodule ℂ (WO (dblSp A) W → ℂ) := Submodule.span ℂ
    {φ | ∃ f₁ f₂, IsThetaFunO ψ A W f₁ ∧ IsThetaFunO ψ A W f₂ ∧ φ = delta A W f₁ f₂} with hM
  have h83 : (∀ g ∈ M, IsThetaFunO ψ (dblSp A) W g) ∧ (∀ g ∈ M, ∀ w, heisO ψ (dblSp A) W w g ∈ M) ∧
      ∀ f, IsThetaFunO ψ (dblSp A) W f → GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.UnifLimit M f := GlobalTheory.T.doublingMap_span_dense_heisenbergStable D ψ A W hom.std
  obtain ⟨hMθ, hMh, hMlim⟩ := h83

  have hintθ : ∀ g, IsThetaFunO ψ (dblSp A) W g → Integrable (fun x => c x * omh (p x) g 0) μ := fun g hg =>
    hint _ (hcc.mul ((homh.om_cont g hg 0).comp hpc))

  have hup : ∀ f, IsThetaFunO ψ A W f → ∫ g, thetaKO om g h f * u g ∂(m.restrict X) = 0 := fun f hf => by
    have hinv : ∀ γ ∈ GQ A, ∀ g, thetaKO om (γ * g) h f * u (γ * g) = thetaKO om g h f * u g := fun γ hγ g => by
      rw [thetaKO_rat hom hf h γ hγ g, hui γ hγ g]
    rw [← GlobalTheory.ChainOnto.integral_autMeasure_eq_setIntegral D A m X hm hX (fun g => thetaKO om g h f * u g) hinv
      ((continuous_thetaKO hom hf h).mul hu).aestronglyMeasurable]
    exact hno f hf h
  have hkill : ∀ g ∈ M, ∫ x, c x * omh (p x) g 0 ∂μ = 0 := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f₁, f₂, h₁, h₂, rfl⟩ := hx
      have e : ∀ x : GA D A × GA D A, c x * omh (p x) (delta A W f₁ f₂) 0 =
          (thetaKO om x.1 h f₁ * u x.1) * conj (thetaKO om x.2 h f₂ * u x.2) := by
        rintro ⟨x₁, x₂⟩
        have t := ((hTC f₁ f₂ h₁ h₂).2 x₁ x₂ h).2
        have hz : (χW (detA A x₂) : ℂ) ≠ 0 := Circle.coe_ne_zero _
        change c (x₁, x₂) * thetaKO omh (io A (x₁, x₂)) h (delta A W f₁ f₂) = _
        rw [t, Circle.coe_inv, hc]
        simp only [map_mul]
        field_simp
      simp_rw [e]
      rw [hμ, integral_prod_mul (fun g => thetaKO om g h f₁ * u g) (fun g => conj (thetaKO om g h f₂ * u g)),
        hup f₁ h₁, zero_mul]
    | zero => simp
    | add x y hx hy ihx ihy =>
      simp only [map_add, Pi.add_apply, mul_add]
      rw [integral_add (hintθ x (hMθ x hx)) (hintθ y (hMθ y hy)), ihx, ihy, add_zero]
    | smul a x hx ih =>
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]
      simp_rw [mul_left_comm _ a]
      rw [integral_const_mul, ih, mul_zero]
  exact GlobalTheory.T.weilRep_average_kills_theta_of_dense_family D ψ (dblSp A) W 1 χW omh homh (GA D A × GA D A) μ p c (p '' (K ×ˢ K)) hpc hcc ⟨C * C, hcb⟩ hK'
    hae M hMθ hMh hkill φ hφ (hMlim φ hφ)

end GlobalTheory.Core.Rk.Kill

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsConsistentRowChoices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Fam.LiftSide.rowCh_exists : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ g : GlobalTheory.Fam.Geo D, ∃ r : ∀ t, RowCh (pk W) (lvP W) u g t, (∀ t, (r t).Is) ∧ ∀ t t', (r t).Same (r t') := by
  intro hC D L hT Gi Gl Kc Yd cX ex W u hW g
  have h := hW.bot.hyp.2.2.2.1
  exact ⟨_, fun t => GlobalTheory.Fam.FamInhab.rowOf_is _ hC h.lev h.models h.chain GlobalTheory.Fam.FamInhab.topMult u g t,
    fun t t' => GlobalTheory.Fam.FamInhab.rowOf_same _ hC h.lev h.models h.chain _ u g t t'⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLevelData
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevPin

set_option maxHeartbeats 4000000 in

theorem exists_levelData : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b : ∀ j, GA D (Yc D j)) (v : VCom (commOf (pk W) u (mkGeo m b))), (commOf (pk W) u (mkGeo m b)).Is → v.τ = y.τ → v.NT = a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = PP.under (𝓞 D.host.F)) → GlobalTheory.Core.Mi.IsTypePlaces (pk W).Pg → ∀ (l : ∀ PP : (pk W).Pg, LocX a (pk W).βX PP.1) (S : ∀ PP, SymData (l PP).k (l PP).s D.R.k), SymRead W l S → (∀ PP, LocY (l PP) y v.N (pk W).βY b fun j c hc => ((S PP).T (Fin D.R.t)).bas j c hc) → (∀ PP, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos ((l PP).FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos (l PP).FT) → ∃ JG eG eGT dG, ∃ (n : ℕ) (G : Fin n → GLoc { v with JG := JG, eG := eG, eGT := eGT, dG := dG }) (pl : Fin n ≃ (pk W).Pg), GPin G ∧ (∀ j, GlobalTheory.FinPl.CombAt (· ∈ v.gP) (eG j) ∧ GlobalTheory.FinPl.CombAt (· ∈ v.gP) (dG j) ∧ ∀ h, GlobalTheory.FinPl.CombAt (· ∈ v.gP) (eGT j h)) ∧ (∀ j row col, GRead (⟨mkGeo m b, j, row, col⟩ : FamCh W u) G pl) ∧ ∀ i, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos ((G i).FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos (G i).FT ∧ (G i).z₀ = fun r => (ofSplit (G i).q).pr (a.ζ₀ r) := by
  intro D L hT Gi Gl Kc Yd cX ex W u _ a y m b v hc hτ hNT hgP hTP l S hSym hY hStd
  classical
  have hψ : IsStdChar D (pk W).ψ (-1) := hc.std
  choose ν hν using fun PP : (pk W).Pg => GlobalTheory.SplitWeil.exists_isUnitVol (l PP).k
  choose eg egT cg heg hegT hcm hcp hct sEg sCg using fun PP => exists_locComb (l PP) (S PP) (hY PP) (ν PP) hψ
  have hPv : ∀ PP : (pk W).Pg, (l PP).q.v ∈ v.gP := fun PP => (hgP _).2 ⟨PP.1, PP.2, (l PP).under⟩
  let n := Fintype.card (pk W).Pg
  let pl : Fin n ≃ (pk W).Pg := (Fintype.equivFin _).symm

  have hEG : ∀ j, ∃ c' : WO (Yc D j) (Yc D (j + 1)) →₀ ℂ, (∀ w ∈ c'.support, GlobalTheory.FinPl.MxAt (· ∈ v.gP) w) ∧
      ∀ f, comb (pk W).ψ _ _ c' f = (List.finRange n).foldr (fun i f' => comb (pk W).ψ _ _ (eg (pl i) j) f') f := fun j =>
    exists_fold _ _ _ _ (fun i => eg (pl i) j) (fun i w hw => mxAt_of_half (l (pl i)).q (hPv (pl i)) w (sEg (pl i) j w hw)) _
  choose eG hEGs hEGf using hEG
  have hDG : ∀ j, ∃ c' : WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ, (∀ w ∈ c'.support, GlobalTheory.FinPl.MxAt (· ∈ v.gP) w) ∧
      ∀ f, comb (pk W).ψ _ _ c' f = (List.finRange n).foldr (fun i f' => comb (pk W).ψ _ _ (cg (pl i) j) f') f := fun j =>
    exists_fold _ _ _ _ (fun i => cg (pl i) j) (fun i w hw => mxAt_of_half (l (pl i)).q (hPv (pl i)) w (sCg (pl i) j w hw)) _
  choose dG hDGs hDGf using hDG
  have hsj : ∀ (i : Fin n) (j : ℕ), j + 2 * 0 + 2 = D.R.m → (l (pl i)).s = j := fun i j h => by
    have := (l (pl i)).hs
    omega
  let eT : ∀ (i : Fin n) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m), WO (Yc D (j + 1)) D.sp.X' →₀ ℂ := fun i j h =>
    cast (congrArg (fun n' => WO (Yc D (n' + 1)) D.sp.X' →₀ ℂ) (hsj i j h)) (egT (pl i))
  have hEGT : ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∃ c' : WO (Yc D (j + 1)) D.sp.X' →₀ ℂ,
      (∀ w ∈ c'.support, GlobalTheory.FinPl.MxAt (· ∈ v.gP) w) ∧
      ∀ f, comb (pk W).ψ _ _ c' f = (List.finRange n).foldr (fun i f' => comb (pk W).ψ _ _ (eT i j h) f') f := fun j h =>
    exists_fold _ _ _ _ (fun i => eT i j h) (fun i => mxAt_cast (F := fun n' => Yc D (n' + 1)) (hsj i j h) _
      (fun w hw => mxAt_of_half (l (pl i)).q (hPv (pl i)) w ((hegT (pl i)).1 w hw))) _
  choose eGT hEGTs hEGTf using hEGT

  let JG : ∀ j, Subgroup (GA D (Yc D j)) := fun j => GlobalTheory.FinPl.grpAt (Yc D j) (· ∈ v.gP) ⊓
    ⨅ (i : Fin n) (a' : ℕ) (ha : j + a' = (l (pl i)).s + 1),
      frameSub ((GeneralLinearGroup.map (l (pl i)).q.pr).comp (matHom (Yc D j))) ((hY (pl i)).FY j a' ha)
        ((((S (pl i)).T (Fin D.R.t)).lev j a' ha).J)
  let v' : VCom (commOf (pk W) u (mkGeo m b)) := { v with JG := JG, eG := eG, eGT := eGT, dG := dG }
  let G : Fin n → GLoc v' := fun i =>
    { k := (l (pl i)).k
      ν := ν (pl i)
      unitVol := hν (pl i)
      q := (l (pl i)).q
      unit := (l (pl i)).unit
      s := (l (pl i)).s
      hs := (l (pl i)).hs
      S := S (pl i)
      char := hSym.char (pl i)
      FX := (l (pl i)).FX
      FT := (l (pl i)).FT
      FM := (l (pl i)).FM
      FY := (hY (pl i)).FY
      sc := (hY (pl i)).sc
      sc_unit := (hY (pl i)).sc_unit
      sc_step := (hY (pl i)).sc_step
      hz_unit := (hY (pl i)).hz_unit
      bes := (hY (pl i)).bes
      jac := (hY (pl i)).jac
      z₀ := fun r => (ofSplit (l (pl i)).q).pr (a.ζ₀ r)
      last := (l (pl i)).last
      tau := fun h => by
        rw [show v'.τ = y.τ from hτ]
        exact (hY (pl i)).tau h
      latX := (l (pl i)).latX
      latM := (l (pl i)).latM
      latY := (hY (pl i)).latY
      latT := by
        rw [show v'.NT = a.LT from hNT]
        exact (l (pl i)).latT
      eg := eg (pl i)
      eg_is := heg (pl i)
      egT := egT (pl i)
      egT_is := hegT (pl i)
      cg := cg (pl i)
      cg_mid := hcm (pl i)
      cg_pen := hcp (pl i)
      cg_top := hct (pl i) }
  refine ⟨JG, eG, eGT, dG, n, G, pl, ?_, fun j => ⟨hEGs j, hDGs j, hEGTs j⟩, ?_, fun i => ⟨(hStd (pl i)).1, (hStd (pl i)).2, rfl⟩⟩

  · refine ⟨fun i i' h => pl.injective (Subtype.ext (under_inj hTP (pl i).2 (pl i').2 ?_)), fun p => ?_, fun j _ g => ?_,
      fun j _ f _ => hEGf j f, fun j h => ⟨fun i => eT i j h, fun i => cast_heq _ _, fun f _ => hEGTf j h f⟩,
      fun j _ f _ => hDGf j f⟩
    · have e1 := (l (pl i)).under
      have e2 := (l (pl i')).under
      change (l (pl i)).q.v = (l (pl i')).q.v at h
      rw [← e1, ← e2, h]
    · change p ∈ v.gP ↔ ∃ i, p = (l (pl i)).q.v
      rw [hgP]
      constructor
      · rintro ⟨PP, hPP, rfl⟩
        refine ⟨pl.symm ⟨PP, hPP⟩, ?_⟩
        rw [(l _).under, Equiv.apply_symm_apply]
      · rintro ⟨i, rfl⟩
        exact ⟨(pl i).1, (pl i).2, (l _).under⟩
    · change g ∈ JG j ↔ _
      simp only [JG, Subgroup.mem_inf, Subgroup.mem_iInf, mem_frameSub]
      rfl
  · intro j row col
    refine ⟨fun i => ⟨(l (pl i)).idem, (l (pl i)).under⟩, fun i j h1 h2 => hSym.mu (pl i) j h1 h2,
      fun i j c hc => (hY (pl i)).frame j c hc, fun i => (l (pl i)).frameTop, fun g => ⟨?_, ?_⟩⟩
    · rw [hSym.grp g]
      constructor
      · intro h i
        exact h (pl i)
      · intro h PP
        obtain ⟨i, rfl⟩ := pl.surjective PP
        exact h i
    · intro hg x hx
      rw [hSym.chr g hg (Equiv.piCongrLeft (fun PP => (S PP).P.J) pl x) (fun PP => ?_)]
      · rw [← Equiv.prod_comp pl]
        simp only [Equiv.piCongrLeft_apply_apply]
        rfl
      · obtain ⟨i, rfl⟩ := pl.surjective PP
        rw [Equiv.piCongrLeft_apply_apply]
        exact hx i

end GlobalTheory.LevPin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNonzeroMoveConstantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_move_constant : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (w : World I l Z) (u : B.Word) (A : ColDat I l Z u (w.C.herm.base.Ch u)) ψ θ, A.Is (w.C.forms u) ψ θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m), ∃ c₀ : ℂ, c₀ ≠ 0 ∧ A.MoveAt θ i hi c₀ 1 1 := by
  first | exact @GlobalTheory.AdForm.VacBase.vacuum_reads_base | exact GlobalTheory.AdForm.VacBase.vacuum_reads_base | (intros; apply GlobalTheory.AdForm.VacBase.vacuum_reads_base <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRowFormReadingLevelFormLastSpaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rowForm_reading_levelForm_lastSpace : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ : ℕ → ℂ), PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (a : I.ι), ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → ∀ f : CXP R P t, ∃ G', ReadsG K eW j g.bT G' f.1 := by
  first | exact @GlobalTheory.AdForm.exists_readsG_of_level | exact GlobalTheory.AdForm.exists_readsG_of_level | (intros; apply GlobalTheory.AdForm.exists_readsG_of_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeMovesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_self_dual_lattice_moves : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ j, j < D.R.m → ∀ g : GA D (Yc D j), ∃ M : GlobalTheory.FinPl.Lat (Yc D j), IsSelfDualC (Yc D j) M ∧ ∀ P, GlobalTheory.FinPl.Moves (Yc D j) g ((pk W).ΛY j) M P := by
  first | exact @GlobalTheory.MovedLat.movedLat | exact GlobalTheory.MovedLat.movedLat | (intros; apply GlobalTheory.MovedLat.movedLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLineLatticeSplittingSumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selfDualLineLattice_splitting_sum : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S A B : HSp D) (o : OrthDec S A B) (MS : GlobalTheory.FinPl.Lat S) (MA : GlobalTheory.FinPl.Lat A) (Y : Type) [Fintype Y] [DecidableEq Y] (FA : Frame k A.rank Y) (FS : Frame k S.rank (Y ⊕ Unit)) (z : Fin B.rank → k), IsSelfDualC S MS → IsSelfDualC A MA → (∃ LB : GlobalTheory.FinPl.Lat B, IsSelfDualC B LB) → (∀ r a, FS.β r (Sum.inl a) = (o.iA.map (ofSplit q).pr * FA.β) r a) → (∀ r, FS.β r (Sum.inr ()) = (o.iB.map (ofSplit q).pr *ᵥ z) r) → IntIn q S FS MS → IntIn q A FA MA → ∃ LB : GlobalTheory.FinPl.Lat B, IsSelfDualC B LB ∧ GlobalTheory.FinPl.OrthAt o MS MA LB q.v ∧ ∀ y : k, (y ∈ 𝒪[k] ↔ (fun i => q.sec (z i * y)) ∈ GlobalTheory.FinPl.latV B LB (· = q.v)) := by
  first | exact @GlobalTheory.LineSplit.exists_lineLat | exact GlobalTheory.LineSplit.exists_lineLat | (intros; apply GlobalTheory.LineSplit.exists_lineLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSymmetricDataAtTypePlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SymReadEx
open GlobalTheory.LocMod.PinEx GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

theorem tame_step {D : D7} {T : Type} (L : LevCh D T) {μ0 : T} (hL : L.Is μ0) {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) {PP : Pl D.host.E} (hP : PP ∈ L.Pg)
    (h : Formalism.L2.NTheta.IsIdemAt q.e PP) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) {μ : kˣ →* ℂˣ}
    (hμ : (ofSplit q).IsComp (Lift.chrStep L.mu0 L.eta j).1⁻¹ μ) : IsTame μ := by
  intro x hx
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have e1 : L.mu0 (i + 1) (idl q x) = 1 := res_idl q h (hL.mu0 ⟨i, h2⟩) (hL.chi ⟨i, h2⟩ PP hP) x hx
  have hr : IsRes L.C.eta PP 1 := fun z y v hy hv => by
    haveI : Nontrivial (kP PP) := Ideal.Quotient.nontrivial_iff.2 PP.isPrime.ne_top
    have hzP : z ∉ PP.asIdeal := fun hm => v.ne_zero (hv.trans (Ideal.Quotient.eq_zero_iff_mem.2 hm))
    rw [GlobalTheory.NormOneUnit.locK_unr (L.C.isEta.unr PP) (y := y)
      (by rw [hy]; exact (PP.valuation_eq_one_iff_notMem (K := D.host.E)).2 hzP)]
    rfl
  have e2 : L.eta (idl q x) = 1 := res_idl q h hL.eta hr x hx
  have e3 : (Lift.chrStep L.mu0 L.eta (i + 1)).1 (idl q x) = 1 := by
    unfold Lift.chrStep
    split_ifs
    · change L.mu0 (i + 1) (idl q x) * (L.eta (idl q x))⁻¹ = 1
      rw [e2, inv_one, mul_one]
      exact e1
    · exact e1
  refine Units.ext ((hμ x (idl q x) rfl).trans ?_)
  rw [MonoidHom.inv_apply, e3]
  simp

theorem red_sym {D : D7} {a : XGeo D} {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP)
    (S : SymData l.k l.s D.R.k) {π : Equiv.Perm (Fin D.R.r)} (hπ : IsSymOrd D.R.rS D.R.k π)
    (g g' : GL (Fin D.R.r) (kP PP)) (hg : ∀ i j, g'.val i j = g.val (π i) (π j)) :
    ((∃ x, l.Red S x g) ↔ g' ∈ unipSym (kP PP) D.R.r D.R.rS D.R.k) ∧
    ∀ ψ₀ : AddChar (kP PP) ℂ,
      (∀ z, (S.ψ (((S.ϖ⁻¹ : l.kˣ) : l.k) * prO l.q z) : ℂ) = ψ₀ (Ideal.Quotient.mk _ z)) → ∀ x, l.Red S x g →
        (S.P.lam x : ℂ) = ψ₀ (edgeSum (symEdge D.R.rS D.R.k) g') := by
  have h1 := l.hs
  have h2 := S.odd
  have hρ : D.R.rS = S.ρ := by unfold Ranks.rS; omega
  let e : Fin D.R.k ⊕ Fin (l.s + 1) ≃ Fin D.R.r := finSumFinEquiv.trans (finCongr (by unfold Ranks.r; omega))
  have he : ∀ a, (e a).val = framePos _ _ a := by rintro (a | a) <;> simp [e, framePos]
  have hr : ∀ x, l.Red S x g ↔ ∀ a b z, Ideal.Quotient.mk PP.asIdeal z = g.val (e a) (e b) →
      valuation l.k ((x : GL (Fin D.R.k ⊕ Fin (l.s + 1)) l.k).val a b - prO l.q z) < 1 := fun x =>
    ⟨fun h a b => h a b _ _ (he a) (he b), fun h a b a' b' ha hb => by
      obtain rfl : a' = e a := Fin.ext (ha.trans (he a).symm)
      obtain rfl : b' = e b := Fin.ext (hb.trans (he b).symm)
      exact h a b⟩
  rw [hρ] at hπ ⊢
  simp only [hr]
  exact ⟨sym_grp S (prO l.q) (prO_le l.q l.idem) (prO_lt l.q l.idem) e he hπ g g' hg,
    fun ψ₀ h x hx => sym_chr S (prO l.q) e he hπ g g' hg ψ₀ h x hx⟩

theorem exists_symRead : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → GlobalTheory.Core.Mi.IsTypePlaces (pk W).Pg → ∀ (a : XGeo D) (l : ∀ PP : (pk W).Pg, LocX a (pk W).βX PP.1), ∃ S : ∀ PP, SymData (l PP).k (l PP).s D.R.k, SymRead W l S := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW _ a l
  obtain ⟨ψ₀, hψ₀, -, π, hπ, hH, hχ⟩ := W.Q.charW.base.grp.levels
  have hlev := W.Q.charW.base.lev
  have loc : ∀ PP : (pk W).Pg, ∃ S : SymData (l PP).k (l PP).s D.R.k, (ofSplit (l PP).q).IsChar (pk W).ψ S.ψ ∧
      (∀ j, 1 ≤ j → j ≤ D.R.m → (ofSplit (l PP).q).IsComp (Lift.chrStep (pk W).mu0 (pk W).eta j).1⁻¹ (S.μ j)) ∧
      ∀ z, (S.ψ (((S.ϖ⁻¹ : (l PP).kˣ) : (l PP).k) * prO (l PP).q z) : ℂ) = ψ₀ PP.1 (Ideal.Quotient.mk _ z) := by
    intro PP
    obtain ⟨⟨ψk, hch, hcond⟩, -⟩ := GlobalTheory.WeilCondUnif.cond_unif W u hW a PP.1 (Or.inl PP.2) (l PP)
    obtain ⟨ϖ, hϖ, hres⟩ := exists_unif (l PP).q (l PP).idem hcond (hψ₀ PP.1 PP.2)
    obtain ⟨ρ, hρ⟩ : ∃ ρ, (l PP).s + 1 = 2 * ρ + 1 := by
      obtain ⟨b, hb⟩ := D.R.m_even
      have := (l PP).hs
      exact ⟨b - 1, by omega⟩
    obtain ⟨P, hP'⟩ := GlobalTheory.SymLevelExists.exists_isSymLevel (l PP).k ψk hcond ϖ hϖ ρ D.R.k ((l PP).s + 1)
    choose μ hμ using fun j => GlobalTheory.LocMod.Witness.exists_isComp (ofSplit (l PP).q) (Lift.chrStep (pk W).mu0 (pk W).eta j).1⁻¹
    refine ⟨⟨ψk, ϖ, ρ, P, fun j => if 1 ≤ j ∧ j ≤ D.R.m then μ j else 1, fun j => ?_, hcond, hϖ, hρ, hP'⟩, hch,
      fun j h1 h2 => ?_, hres⟩
    · split_ifs with h
      · exact tame_step (pk W).toLevCh hlev (l PP).q PP.2 (l PP).idem h.1 h.2 (hμ j)
      · exact fun _ _ => rfl
    · simp only [if_pos (And.intro h1 h2)]
      exact hμ j
  choose S h1 h2 h3 using loc
  refine ⟨S, h1, h2, fun x => (hH x).trans ?_, fun x hx y hxy => ?_⟩
  · exact ⟨fun h PP => (red_sym (l PP) (S PP) hπ (x PP) (reord π x PP) fun _ _ => rfl).1.2 (h PP (Set.mem_univ _)),
      fun h PP _ => (red_sym (l PP) (S PP) hπ (x PP) (reord π x PP) fun _ _ => rfl).1.1 (h PP)⟩
  · refine (hχ x hx ((hH _).1 hx)).trans ?_
    refine (MonoidHom.finset_prod_apply _ _ _).trans (Finset.prod_congr rfl fun PP _ => Units.ext ?_)
    exact ((red_sym (l PP) (S PP) hπ (x PP) (reord π x PP) fun _ _ => rfl).2 _ (h3 PP) _ (hxy PP)).symm

end GlobalTheory.SymReadEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDatumFactorsOverTwistPrimesLocalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDatum_factors_over_twistPrimes_local : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → I.IsTw → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀), A.Is → (∀ i (hi : i + 1 ≤ B.R.m) α γ z, A.xi i hi α γ z = xiOff A i hi α γ z * ∏ P ∈ Finset.univ.filter (fun P : BadPr I a => P.1 ∉ (B.primes X).vGs), B.embLL (locXi A i α γ P (homOf I l Z i hi z))) ∧ ∀ (c : Comm (I.rec7 l Z)) (hX : c.X = (I.rec7 l Z).sp.X) (v : VCom c) (Bs : GlobalTheory.Fam.Base c) PP (G : QGeo v Bs PP) χ (E : QExt G χ) hψ sg π (P : BadPr I a), ReadsAt A P E hψ sg π → ∀ j d (H : j + 1 + d = G.s) (hj : j + 1 ≤ B.R.m) (hj' : j + 1 < B.R.m) α γ (e' : XIx (Fin B.R.k) (Fin B.R.t) j ≃ Fin (B.R.N j)) (e : XIx (Fin B.R.k) (Fin B.R.t) (j + 1) ≃ Fin (B.R.N (j + 1))), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e' → GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e → ∀ x, (G.T E.δ E.tame E.η).entry G.ψk G.ν j d H (E.rep j (d + 1) (by omega) (π j α)) (E.rep (j + 1) d H (π (j + 1) γ)) (GlobalTheory.SymBridge.toLoc (G.q.pr.comp (incA (I.rec7 l Z))) e e' (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 j α).1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 (j + 1) γ).1.1 P) x)) = GlobalTheory.TwBridge.sgn I.sel (I.tup a) P (E.tw hψ sg) ((I.idx a).h j ((A.b0 j α).get hj) P) (B.R.N (j + 1) + Formalism.L2.Col.cOf B.R (j + 1)) * GlobalTheory.TwBridge.sgn I.sel (I.tup a) P (E.tw hψ sg) ((I.idx a).h (j + 1) ((A.b0 (j + 1) γ).get hj') P) (B.R.N j + Formalism.L2.Col.cOf B.R j) * B.embLL (locXi A j α γ P x) := by
  first | exact @GlobalTheory.QTw.Join.xi_factor_and_entry | exact GlobalTheory.QTw.Join.xi_factor_and_entry | (intros; apply GlobalTheory.QTw.Join.xi_factor_and_entry <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiNormalFrameIsotropicColumnsPairingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiNormalFrame_isotropicColumns_pairing : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ρ : ℕ) (J : JacLev D ρ) (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (s hh : k) (F₀ : Frame k J.W₀.rank n) (F : Frame k J.W.rank (n ⊕ Fin c)), p.IsJacFrame J s hh F₀ F → ∀ i : Fin ρ, ∃ m₀ m₁ : n ⊕ Fin c, (∀ r, F.β r m₀ = s * p.xi ^ (ρ - i.val) * p.pr (J.d.e r i)) ∧ (∀ r, F.β r m₁ = s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val) * p.pr (J.d.e' r i)) ∧ ∀ m, m ≠ m₁ → ∑ r, ∑ r', p.pr (star (J.d.e r i)) * p.pr (J.W.gram r r') * F.β r' m = 0 := by
  first | exact @GlobalTheory.LocMod.JacCols.cols_pair | exact GlobalTheory.LocMod.JacCols.cols_pair | (intros; apply GlobalTheory.LocMod.JacCols.cols_pair <;> assumption)
end

