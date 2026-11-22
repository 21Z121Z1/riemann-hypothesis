import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergTranslateThetaContinuousDifferentiable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0310
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0230
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0298
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0287
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0313
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0309
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0275
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0247
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0312
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchroedingerFunctionHasDerivAtRealLineDoubledPai
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

namespace GlobalTheory.SchLine

theorem sch_hasDerivAt_line : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ M : ℝ →+ Mx D B.rank A.rank, Continuous M → (∀ t, (M t).map (finPart D) = 0) → ∃ f', IsThetaFunO ψ (dblSp A) B f' ∧ ∀ x, HasDerivAt (fun t : ℝ => sch ψ A B ν 𝓨 f (x + M t)) (sch ψ A B ν 𝓨 f' x) 0 := by
  intro D ψ hψ A B ν 𝓨 hν f hf M hM hMf
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D
  let v : GlobalTheory.Unf.VolM D B.rank A.rank := ⟨ν, 𝓨, hν⟩
  let L : ℝ →+ WO (dblSp A) B := ((dblDec A).extX B).comp M
  have hLc : Continuous L := (continuous_id.matrix_mul continuous_const).comp hM
  have hLf : ∀ t, (L t).map (finPart D) = 0 := by
    intro t
    show (((dblDec A).extX B) (M t)).map (finPart D) = 0
    rw [HypDec.extX_apply, Matrix.map_mul, hMf t, Matrix.zero_mul]
  obtain ⟨_, hT⟩ := GlobalTheory.HeisTaylor.heisO_taylor D ψ hψ θ hθ (dblSp A) B 0 f hf
  obtain ⟨hf', hlim⟩ := hT L hLc hLf
  refine ⟨_, hf', fun x => ?_⟩
  set f' := fun p => deriv (fun t : ℝ => heisO ψ (dblSp A) B (L t) f p) 0 with hf'def
  obtain ⟨C, hC⟩ := GlobalTheory.Unf.mixS_decay D ψ hψ θ hθ (dblSp A) (zeroSp D) B A.rank (dblDec A) v 0
  have hS := (GlobalTheory.HeisMixSource.heis_mixS D ψ hψ (dblSp A) (zeroSp D) B A.rank (dblDec A) v f hf).1
  have hth : ∀ t, IsThetaFunO ψ (dblSp A) B (heisO ψ (dblSp A) B (L t) f) := fun t =>
    GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf _
  have lin := GlobalTheory.StdUnn.sch_linear D ψ hψ A B ν 𝓨 hν

  have htr : ∀ t : ℝ, sch ψ A B ν 𝓨 f (x + M t) = sch ψ A B ν 𝓨 (heisO ψ (dblSp A) B (L t) f) x := by
    intro t
    exact (congrFun (hS x (M t)) 0).symm

  have key : ∀ t : ℝ, IsThetaFunO ψ (dblSp A) B ((t⁻¹ : ℂ) • (heisO ψ (dblSp A) B (L t) f - f) - f') ∧
      sch ψ A B ν 𝓨 ((t⁻¹ : ℂ) • (heisO ψ (dblSp A) B (L t) f - f) - f') x =
        (t⁻¹ : ℂ) * (sch ψ A B ν 𝓨 (heisO ψ (dblSp A) B (L t) f) x - sch ψ A B ν 𝓨 f x) - sch ψ A B ν 𝓨 f' x := by
    intro t
    have e : (t⁻¹ : ℂ) • (heisO ψ (dblSp A) B (L t) f - f) - f' =
        ((t⁻¹ : ℂ) • heisO ψ (dblSp A) B (L t) f + (-(t⁻¹ : ℂ)) • f) + (-1 : ℂ) • f' := by
      funext p
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have h1 := lin _ _ (hth t) hf (t⁻¹ : ℂ)
    have h2 := lin _ _ hf hf (-(t⁻¹ : ℂ))
    have ha := GlobalTheory.OrientedHeis.theta_smul (t⁻¹ : ℂ) (hth t)
    have hb := GlobalTheory.OrientedHeis.theta_smul (-(t⁻¹ : ℂ)) hf
    have hc := GlobalTheory.OrientedHeis.theta_smul (-1 : ℂ) hf'
    have hab := GlobalTheory.OrientedHeis.theta_add ha hb
    rw [e]
    refine ⟨GlobalTheory.OrientedHeis.theta_add hab hc, ?_⟩
    rw [(lin _ _ hab hc 1).2.2.1, (lin _ _ ha hb 1).2.2.1, (lin _ _ (hth t) hf (t⁻¹ : ℂ)).2.2.2,
      (lin _ _ hf hf (-(t⁻¹ : ℂ))).2.2.2, (lin _ _ hf' hf' (-1 : ℂ)).2.2.2]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hasDerivAt_iff_tendsto_slope_zero, tendsto_iff_edist_tendsto_0]
  have hup : Filter.Tendsto (fun t : ℝ => (C : ℝ≥0∞) * GlobalTheory.Unf.supSob ψ θ 0
      ((t⁻¹ : ℂ) • (heisO ψ (dblSp A) B (L t) f - f) - f')) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hlim (Or.inr ENNReal.coe_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun _ => by simp) (fun t => ?_)
  have hb := hC _ (key t).1 x 0
  rw [pow_zero, ENNReal.ofReal_one, mul_one] at hb
  have e2 : t⁻¹ • (sch ψ A B ν 𝓨 f (x + M (0 + t)) - sch ψ A B ν 𝓨 f (x + M 0)) =
      (t⁻¹ : ℂ) * (sch ψ A B ν 𝓨 (heisO ψ (dblSp A) B (L t) f) x - sch ψ A B ν 𝓨 f x) := by
    rw [zero_add, htr t, map_zero, add_zero, Complex.real_smul, Complex.ofReal_inv]
  simp only
  rw [e2, edist_eq_enorm_sub, ← (key t).2]
  exact hb

end GlobalTheory.SchLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawCommonRealDatumBiThetaVacuumContraction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VReal

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem biTheta_add {A S A' : HSp D} {f g : WO A S → WO S A' → ℂ} (hf : IsBiTheta ψ A S A' f)
    (hg : IsBiTheta ψ A S A' g) : IsBiTheta ψ A S A' (f + g) := by
  refine ⟨hf.cont.add hg.cont, ?_, fun γ u v => ?_, fun γ u v => ?_, ?_, ?_⟩
  · intro n L L' hL hL' hLf hL'f u v
    exact (hf.smooth n L L' hL hL' hLf hL'f u v).add (hg.smooth n L L' hL hL' hLf hL'f u v)
  · simp only [Pi.add_apply]; rw [hf.quasiL, hg.quasiL]; ring
  · simp only [Pi.add_apply]; rw [hf.quasiR, hg.quasiR]; ring
  · obtain ⟨U, hU, hUf⟩ := hf.levL
    obtain ⟨V, hV, hVf⟩ := hg.levL
    refine ⟨U ⊓ V, hU.inter hV, fun a ha ha' v => ?_⟩
    funext u
    have h1 := congrFun (hUf a ha.1 ha' v) u
    have h2 := congrFun (hVf a ha.2 ha' v) u
    simp only [heisO, Pi.add_apply] at h1 h2 ⊢
    rw [mul_add, h1, h2]
  · obtain ⟨U, hU, hUf⟩ := hf.levR
    obtain ⟨V, hV, hVf⟩ := hg.levR
    refine ⟨U ⊓ V, hU.inter hV, fun a ha ha' u => ?_⟩
    funext v
    have h1 := congrFun (hUf a ha.1 ha' u) v
    have h2 := congrFun (hVf a ha.2 ha' u) v
    simp only [heisO, Pi.add_apply] at h1 h2 ⊢
    rw [mul_add, h1, h2]

theorem biTheta_zero {A S A' : HSp D} : IsBiTheta ψ A S A' 0 := by
  refine ⟨?_, fun n L L' _ _ _ _ u v => ?_, fun γ u v => by simp, fun γ u v => by simp, ⟨⊤, by rw [AddSubgroup.coe_top]; exact isOpen_univ, fun a _ _ v => ?_⟩,
    ⟨⊤, by rw [AddSubgroup.coe_top]; exact isOpen_univ, fun a _ _ u => ?_⟩⟩
  · simp only [Pi.zero_apply]; exact continuous_const
  · simp only [Pi.zero_apply]; exact contDiff_const
  · funext x; simp [heisO]
  · funext x; simp [heisO]

theorem biTheta_app (hψ : IsStdChar D ψ (-1)) {A S A' : HSp D} (o : BiOp A S A')
    (ho : ∀ i, IsFinComb (o.u i) ∧ IsFinComb (o.u' i)) {C : WO A S → WO S A' → ℂ} (hC : IsBiTheta ψ A S A' C) :
    IsBiTheta ψ A S A' (o.app ψ C) := by
  unfold BiOp.app
  exact Finset.sum_induction _ (IsBiTheta ψ A S A') (fun f g hf hg => biTheta_add hf hg) biTheta_zero
    fun i _ => GlobalTheory.FrComb.biTheta_combL hψ (GlobalTheory.FrComb.biTheta_combR hψ hC (ho i).2) (ho i).1

theorem heisO_add {S T : HSp D} (w : WO S T) (f g : WO S T → ℂ) :
    heisO ψ S T w (f + g) = heisO ψ S T w f + heisO ψ S T w g := by
  funext x; simp only [heisO, Pi.add_apply, mul_add]

theorem heisO_zero {S T : HSp D} (w : WO S T) : heisO ψ S T w 0 = 0 := by
  funext x; simp [heisO]

theorem latVac_add {S T : HSp D} {Λ : AddSubgroup (WO S T)} {f g : WO S T → ℂ} (hf : IsLatVac (heisO ψ S T) Λ f)
    (hg : IsLatVac (heisO ψ S T) Λ g) : IsLatVac (heisO ψ S T) Λ (f + g) :=
  ⟨fun u hu => by rw [heisO_add, hf.1 u hu, hg.1 u hu],
    fun e he u hu hh => by rw [heisO_add, hf.2 e he u hu hh, hg.2 e he u hu hh]⟩

theorem latVac_zero {S T : HSp D} {Λ : AddSubgroup (WO S T)} : IsLatVac (heisO ψ S T) Λ 0 :=
  ⟨fun u _ => heisO_zero _, fun _ _ u _ _ => heisO_zero u⟩

theorem latVac_sum {S T : HSp D} {Λ : AddSubgroup (WO S T)} {ι : Type} (s : Finset ι) (F : ι → WO S T → ℂ)
    (h : ∀ i ∈ s, IsLatVac (heisO ψ S T) Λ (F i)) : IsLatVac (heisO ψ S T) Λ (∑ i ∈ s, F i) :=
  Finset.sum_induction _ _ (fun _ _ hf hg => latVac_add hf hg) latVac_zero h

def combEnd (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) : Module.End ℂ (WO S T → ℂ) where
  toFun := comb ψ S T c
  map_add' f g := by
    funext u; simp only [GlobalTheory.FrComb.comb_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    funext u
    simp only [GlobalTheory.FrComb.comb_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring

theorem vac_of_true {S T : HSp D} {LS : Lat S} {LT : Lat T} {P : Pl D → Prop} {f : WO S T → ℂ}
    (h : Vac ψ S T LS LT (fun _ => True) f) : Vac ψ S T LS LT P f := by
  have hle : latO S T (LS : Set _) (LT : Set _) P ≤ latO S T (LS : Set _) (LT : Set _) fun _ => True := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, -, rest⟩
    exact ⟨α, hα, fun v hv => absurd trivial hv, rest⟩
  unfold Vac IsLatVac at h ⊢
  exact ⟨h.1, fun u hu => h.2.1 u (hle hu), fun e he u hu hh => h.2.2 e he u (hle hu) hh⟩

theorem vac_union (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (P : Pl D → Prop) (LS : Lat S) (LT : Lat T) (f : WO S T → ℂ)
    (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) (h1 : Vac ψ S T LS LT P f) (h2 : Vac ψ S T LS LT (fun p => ¬ P p) f) :
    Vac ψ S T LS LT (fun _ => True) f := by
  have H := (GlobalTheory.DisjComb.main D ψ hψ S T P (fun p => ¬ P p) (fun p hp hq => hq hp)).2.2.2.2 LS LT f hS hT
  have e : (fun p => P p ∨ ¬ P p) = fun _ => True := funext fun p => propext ⟨fun _ => trivial, fun _ => em _⟩
  have h3 := H.2 ⟨h1, h2⟩
  rwa [e] at h3

theorem real_of (hψ : IsStdChar D ψ (-1)) (P : Pl D → Prop)
    (hcomb : ∀ (S T : HSp D) (e : WO S T →₀ ℂ), CombAt P e → IsFinComb e ∧
      ∀ LS LT f, Vac ψ S T LS LT (fun p => ¬ P p) f → Vac ψ S T LS LT (fun p => ¬ P p) (comb ψ S T e f))
    {A S A' : HSp D} {LA : Lat A} {LS : Lat S} {LA' : Lat A'} (hA : IsSelfDualC A LA) (hS : IsSelfDualC S LS)
    (hA' : IsSelfDualC A' LA') (o : BiOp A S A') (ho : ∀ i, CombAt P (o.u i) ∧ CombAt P (o.u' i))
    {C : WO A S → WO S A' → ℂ} (hC : IsBiTheta ψ A S A' C) (hoff : BiVacAt ψ LA LS LA' (fun p => ¬ P p) C)
    (hon : BiVacAt ψ LA LS LA' P (o.app ψ C)) :
    IsBiTheta ψ A S A' (o.app ψ C) ∧ IsBiVac ψ A S A' LA LS LA' (o.app ψ C) ∧ IsBiSmooth (o.app ψ C) := by
  have hfin : ∀ i, IsFinComb (o.u i) ∧ IsFinComb (o.u' i) :=
    fun i => ⟨(hcomb _ _ _ (ho i).1).1, (hcomb _ _ _ (ho i).2).1⟩
  have hB := biTheta_app hψ o hfin hC
  have hoffApp : BiVacAt ψ LA LS LA' (fun p => ¬ P p) (o.app ψ C) := by
    refine ⟨fun v => ⟨GlobalTheory.FrComb.slice_left hB v, ?_⟩, fun u => ⟨GlobalTheory.FrComb.slice_right hB u, ?_⟩⟩
    · have e : (fun u => o.app ψ C u v) = ∑ i, fun u => biComb ψ A S A' (o.u i) (o.u' i) C u v := by
        funext u; simp only [BiOp.app, Finset.sum_apply]
      rw [e]
      refine latVac_sum _ _ fun i _ => ?_
      have hR := GlobalTheory.FrComb.biTheta_combR hψ hC (hfin i).2
      have hg : Vac ψ A S LA LS (fun p => ¬ P p) (fun u' => comb ψ S A' (o.u' i) (C u') v) :=
        ⟨GlobalTheory.FrComb.slice_left hR v, GlobalTheory.FrComb.latVac_opR (fun v => (hoff.1 v).2) (combEnd ψ S A' (o.u' i)) v⟩
      exact ((hcomb _ _ _ (ho i).1).2 LA LS _ hg).2
    · have e : o.app ψ C u = ∑ i, fun v => biComb ψ A S A' (o.u i) (o.u' i) C u v := by
        funext v; simp only [BiOp.app, Finset.sum_apply]
      rw [e]
      refine latVac_sum _ _ fun i _ => ?_
      exact GlobalTheory.FrComb.latVac_opL (K := fun u' => comb ψ S A' (o.u' i) (C u'))
        (fun u' => ((hcomb _ _ _ (ho i).2).2 LS LA' _ (hoff.2 u')).2) (combEnd ψ A S (o.u i)) u
  have hT : BiVacAt ψ LA LS LA' (fun _ => True) (o.app ψ C) :=
    ⟨fun v => vac_union hψ _ _ P _ _ _ hA hS (hon.1 v) (hoffApp.1 v),
      fun u => vac_union hψ _ _ P _ _ _ hS hA' (hon.2 u) (hoffApp.2 u)⟩
  exact ⟨hB, ⟨hB.cont, fun v => hT.1 v, fun u => hT.2 u⟩, hB.smooth⟩

theorem v_real : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VacLaw (t := t) v → TLaw v w → FlatLaw D → (∀ j σ h Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → IsBiTheta c.ψ _ _ _ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂) ∧ c.IsReal j ((v.op j).app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂))) ∧ ∀ j h Ψ₁ Ψ₂, WeilOK (t := t) v → Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) v.NT (fun _ => True) Ψ₂ → IsBiTheta c.ψ _ _ _ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂) ∧ c.IsReal j ((v.op j).app c.ψ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) := by
  intro D c v t w hc hv ht hV hT hF
  have hψ := hc.std
  have hfl := GlobalTheory.Unf.FlatTheta.flat_isThetaFun D hF c.ψ
  have hcomb : ∀ (S T : HSp D) (e : WO S T →₀ ℂ), CombAt (· ∈ v.tP) e → IsFinComb e ∧
      ∀ LS LT f, Vac c.ψ S T LS LT (fun p => ¬ p ∈ v.tP) f → Vac c.ψ S T LS LT (fun p => ¬ p ∈ v.tP) (comb c.ψ S T e f) :=
    fun S T e he => (GlobalTheory.DisjComb.main D c.ψ hψ S T (· ∈ v.tP) (fun p => ¬ p ∈ v.tP) (fun p hp hq => hq hp)).2.1 e he
  refine ⟨fun j σ h Ψ₁ Ψ₂ h1 h2 => ?_, fun j h Ψ₁ Ψ₂ hW h1 h2 => ?_⟩
  · have hC : IsBiTheta c.ψ _ _ _ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂) :=
      (GlobalTheory.ContrComb.contr_comb_main D c.ψ hψ (σ + 1) σ (c.B j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (c.lnk j σ h) (c.X (j + 1))
        (c.vL j σ h) (flatBF (t.sBF j (σ + 1) h) Ψ₁) (flatFB (t.sFB j σ h) Ψ₂)
        (hfl.1 (σ + 1) (c.B j (σ + 1) h) (c.J j (σ + 1) h) (t.sBF j (σ + 1) h) Ψ₁ h1.1)
        (hfl.2 σ (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (t.sFB j σ h) Ψ₂ h2.1)).1
    have R := real_of hψ (· ∈ v.tP) hcomb (hc.x j (by omega)).sd (hc.x (j + 1) (by omega)).sd
      (hc.x (j + 1 + 1) (by omega)).sd (v.op j) (hv.atT j).2 hC (hV.1 j σ h Ψ₁ Ψ₂ (vac_of_true h1) (vac_of_true h2))
      (hT.1 j σ h Ψ₁ Ψ₂ (vac_of_true h1) (vac_of_true h2)).1
    exact ⟨hC, R.2.1, R.2.2⟩
  · have hC : IsBiTheta c.ψ _ _ _ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂) :=
      GlobalTheory.LastBiTheta.isBiTheta_lastBi D c.ψ hψ _ _ _ _ _ _ _ (c.bes j 0 h).o (c.oT (j + 1 + 1) h) (v.τ j h) (hW.tau j h).2 (flatBF (t.sBF j 0 h) Ψ₁) (fun w => Ψ₂ ((c.jac j 0 h).d.ext0 c.T w))
        (hfl.1 0 (c.B j 0 h) (c.J j 0 h) (t.sBF j 0 h) Ψ₁ h1.1) ((GlobalTheory.WeilSrc.Zero.theta_iff (c.jac j 0 h).d Ψ₂).2 h2.1)
    have R := real_of hψ (· ∈ v.tP) hcomb (hc.x j (by omega)).sd (hc.x (j + 1) (by omega)).sd
      (hc.x (j + 1 + 1) (by omega)).sd (v.op j) (hv.atT j).2 hC (hV.2 j h Ψ₁ Ψ₂ (vac_of_true h1) (vac_of_true h2))
      (hT.2 j h Ψ₁ Ψ₂ (vac_of_true h1) (vac_of_true h2)).1
    exact ⟨hC, R.2.1, R.2.2⟩

end GlobalTheory.VReal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFixedLevelCombinationEqSinglePlaceOnVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GSuppComb

theorem foldr_extract {ι X : Type} [DecidableEq ι] (g : ι → X → X) (i : ι)
    (hc : ∀ a, a ≠ i → ∀ x, g a (g i x) = g i (g a x)) :
    ∀ (l : List ι) (x : X), i ∈ l → l.foldr g x = g i ((l.erase i).foldr g x) := by
  intro l x hi
  induction l with
  | nil => simp at hi
  | cons a t ih =>
    by_cases ha : a = i
    · subst ha
      simp
    · have hit : i ∈ t := by
        rcases List.mem_cons.1 hi with h | h
        · exact absurd h.symm ha
        · exact h
      have he : (a :: t).erase i = a :: t.erase i := by
        simp [List.erase_cons, ha]
      rw [he, List.foldr_cons, List.foldr_cons, ih hit, hc a ha]

variable {D : D7}

theorem latO_mono {S T : HSp D} (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    {P P' : Pl D → Prop} (h : ∀ p, P p → P' p) : latO S T LS LT P ≤ latO S T LS LT P' := by
  apply AddSubgroup.closure_mono
  rintro w ⟨α, hα, hv, rest⟩
  exact ⟨α, hα, fun p hp => hv p fun hq => hp (h p hq), rest⟩

theorem vac_mono {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P P' : Pl D → Prop}
    (h : ∀ p, P p → P' p) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P' f) : Vac ψ S T LS LT P f :=
  ⟨hf.1, fun u hu => hf.2.1 u (latO_mono _ _ h hu), fun e he u hu hh => hf.2.2 e he u (latO_mono _ _ h hu) hh⟩

theorem eg_combAt {c : Comm D} {v : VCom c} (G : GLoc v) (j : ℕ) (hj : j ≤ G.s) : CombAt (· = G.q.v) (G.eg j) := by
  intro u hu a b
  have h := (G.eg_is j (G.s - j) (by omega)).1 u hu a b
  exact (GlobalTheory.FinPl.FrameLat.idem_iff G.q _).2 h

theorem comb_eq_at_place : ∀ {D : D7} {c : Comm D} {v : VCom c} {n : ℕ}, c.Is → v.Is → ∀ (G : Fin n → GLoc v), GPin G → ∀ (j : ℕ), j + 1 < D.R.m → ∀ (Ψ : WO (c.V j) (c.V (j + 1)) → ℂ), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) Ψ → ∀ (i : Fin n), ∃ F, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (G i).q.v) F ∧ comb c.ψ _ _ (v.eG j) Ψ = comb c.ψ _ _ ((G i).eg j) F := by
  intro D c v n hc hv G hG j hj Ψ hΨ i
  have hI := GlobalTheory.T.heisenbergCombination_disjoint_places_commute_vacua D c.ψ hc.std (c.V j) (c.V (j + 1))
  have hca : ∀ i', CombAt (· = (G i').q.v) ((G i').eg j) := fun i' =>
    eg_combAt (G i') j (by have := (G i').hs; omega)
  have hdisj : ∀ a b : Fin n, a ≠ b → ∀ p, p = (G a).q.v → ¬ p = (G b).q.v := fun a b hab p ha hb =>
    hab (hG.inj (ha.symm.trans hb))
  let g : Fin n → (WO (c.V j) (c.V (j + 1)) → ℂ) → (WO (c.V j) (c.V (j + 1)) → ℂ) :=
    fun a f => comb c.ψ _ _ ((G a).eg j) f
  refine ⟨((List.finRange n).erase i).foldr g Ψ, ?_, ?_⟩
  · have h0 : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (G i).q.v) Ψ :=
      vac_mono (fun p hp => by rw [hp]; exact (hG.places _).2 ⟨i, rfl⟩) hΨ
    have key : ∀ l : List (Fin n), (∀ a ∈ l, a ≠ i) → Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (G i).q.v) (l.foldr g Ψ) := by
      intro l
      induction l with
      | nil => intro _; exact h0
      | cons a t ih =>
        intro hl
        exact ((hI (· = (G a).q.v) (· = (G i).q.v) (hdisj a i (hl a (List.mem_cons_self ..)))).2.1 _ (hca a)).2 _ _ _
          (ih fun b hb => hl b (List.mem_cons_of_mem _ hb))
    exact key _ fun a ha => ((List.nodup_finRange n).mem_erase_iff.1 ha).1
  · rw [hG.eG j hj Ψ hΨ.1]
    exact foldr_extract g i (fun a ha x => (hI _ _ (hdisj a i ha)).1 _ _ (hca a) (hca i) x) _ Ψ (List.mem_finRange i)

end GlobalTheory.GSuppComb

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawIteratedIntegrandVacuumFormBasePoints
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.VMove

set_option maxHeartbeats 4000000 in

theorem seeSaw_iteratedIntegrand_vacuumForm_base_points_alt : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) P₁ P₂, ∀ a ∈ GinfC (c.V (j + 1)), ∀ a' ∈ GinfC (c.V (j + 1 + 1)), ∀ (φ : t.Ch j → GA D (c.X j) → ℂ) (F : GA D (c.V (j + 1 + 1)) → ℂ) Ψ₁ Ψ₂ f z, Ψ₁ = v.Ψ j P₁ 1 a → Ψ₂ = v.Ψ (j + 1) P₂ a a' → f = rTrans (a' * v.b (j + 1 + 1)) F → Iter2 (c.ρJ j (σ + 1) h) (c.μf (j + 1)) (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1)) (fun q₁ q₂ : _ => ∑ α, ∑ g ∈ (w.ε j α).support, w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) (φ α) g q₁.1 q₂.1) (rTrans q₂.1 f)) z → Iter2 (c.ρJ j (σ + 1) h) (c.μf (j + 1)) (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1)) (fun q₁ q₂ => t.integrand j σ h P₁ P₂ φ F (a * q₁.1) (a' * q₂.1)) (w.sc j * w.sc (j + 1) * z) := by
  intro D c v t w hc hv ht hw j σ h P₁ P₂ a ha a' ha' φ F Ψ₁ Ψ₂ f z hΨ₁ hΨ₂ hf hI
  classical
  obtain ⟨-, -, hcomm₁, -, hright₁, -⟩ := GlobalTheory.T.unitaryAdelic_inf_fin_split_periods_unimodular D (c.V (j + 1))
  obtain ⟨-, -, hcomm₂, -, hright₂, -⟩ := GlobalTheory.T.unitaryAdelic_inf_fin_split_periods_unimodular D (c.V (j + 1 + 1))
  have hj₁ : j + 1 < D.R.m := by omega
  have hj₂ : j + 1 + 1 < D.R.m := by omega

  have key : ∀ p₁ ∈ GfC (c.V (j + 1)), ∀ p₂ ∈ GfC (c.V (j + 1 + 1)),
      t.integrand j σ h P₁ P₂ φ F (a * (p₁ * v.b (j + 1))) (a' * (p₂ * v.b (j + 1 + 1))) =
        w.sc j * w.sc (j + 1) * ∑ α, ∑ g ∈ (w.ε j α).support, w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ
          (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h)
            (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁))
            (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) (φ α) g p₁ p₂) (rTrans p₂ f) := by
    intro p₁ hp₁ p₂ hp₂
    have ec₁ : a * (p₁ * v.b (j + 1)) = p₁ * (a * v.b (j + 1)) := by
      rw [← mul_assoc, hcomm₁ a ha p₁ hp₁, mul_assoc]
    have ec₂ : a' * (p₂ * v.b (j + 1 + 1)) = p₂ * (a' * v.b (j + 1 + 1)) := by
      rw [← mul_assoc, hcomm₂ a' ha' p₂ hp₂, mul_assoc]
    have er : rTrans (a' * (p₂ * v.b (j + 1 + 1))) F = rTrans p₂ f := by
      rw [hf, ec₂]; funext x; simp only [rTrans, mul_assoc]
    unfold Tup.integrand
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [(hw.e j α).1, Finsupp.mapDomain_support_of_injective (mul_left_injective (v.b j)),
      Finset.sum_image (fun x _ y _ hxy => mul_right_cancel hxy), Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finsupp.mapDomain_apply (mul_left_injective (v.b j))]
    have e₁ : (t.sBF j (σ + 1) h).om (g * v.b j, a * (p₁ * v.b (j + 1))) (t.pt j P₁) =
        w.sc j • (t.sBF j (σ + 1) h).om (g, p₁) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) := by
      rw [(ht.sBF j (σ + 1) h).1, ec₁,
        show ((g * v.b j, p₁ * (a * v.b (j + 1))) : GA D (c.V j) × GA D (c.V (j + 1))) =
          (g, p₁) * (1 * v.b j, a * v.b (j + 1)) by simp,
        map_mul, Module.End.mul_apply, hw.vf j hj₁ P₁ 1 (one_mem _) a ha, map_smul, hΨ₁]
    have e₂ : (t.sFB j σ h).om (a * (p₁ * v.b (j + 1)), a' * (p₂ * v.b (j + 1 + 1))) (t.pt (j + 1) P₂) =
        w.sc (j + 1) • (t.sFB j σ h).om (p₁, p₂) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) := by
      rw [(ht.sFB j σ h).1, ec₁, ec₂,
        show ((p₁ * (a * v.b (j + 1)), p₂ * (a' * v.b (j + 1 + 1))) : GA D (c.V (j + 1)) × GA D (c.V (j + 1 + 1))) =
          (p₁, p₂) * (a * v.b (j + 1), a' * v.b (j + 1 + 1)) by simp,
        map_mul, Module.End.mul_apply, hw.vf (j + 1) hj₂ P₂ a ha a' ha', map_smul, hΨ₂]
    have hh := (GlobalTheory.HandHom.hand_hom D c.ψ σ _ _ _ (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (φ α)).1
    simp only [Chain.hand]
    rw [e₁, e₂, hh, er]
    have hp := GlobalTheory.HandHom.per_smul (c.B (j + 1 + 1) σ (idx_step h)) c.ψ (w.sc j * w.sc (j + 1)) 1
      (handFB (t.sFB j σ h) (c.vL j σ h) (handBF (t.sBF j (σ + 1) h) (c.lnk j σ h) (φ α)
        (flatBF (t.sBF j (σ + 1) h) ((t.sBF j (σ + 1) h).om (g, p₁) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)))))
        (flatFB (t.sFB j σ h) ((t.sFB j σ h).om (p₁, p₂) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)))))
      (rTrans p₂ f)
    rw [one_smul] at hp
    rw [hp]
    ring
  obtain ⟨f₁, h1, h2⟩ := hI
  haveI := hright₁ _ (hc.μf (j + 1))
  haveI := hright₂ _ (hc.μf (j + 1 + 1))
  set B₁ : GfC (c.V (j + 1)) := ⟨v.b (j + 1), hv.b (j + 1)⟩ with hB₁
  set B₂ : GfC (c.V (j + 1 + 1)) := ⟨v.b (j + 1 + 1), hv.b (j + 1 + 1)⟩ with hB₂
  refine ⟨fun q => (w.sc j * w.sc (j + 1)) * f₁ (q * B₁⁻¹), ?_, fun q => ?_⟩
  · exact (h1.mul_right B₁⁻¹).smul (w.sc j * w.sc (j + 1))
  · have := ((h2 (q * B₁⁻¹)).mul_right B₂⁻¹).smul (w.sc j * w.sc (j + 1))
    convert this using 1
    funext q₂
    have eq₁ : (q : GA D (c.V (j + 1))) = ((q * B₁⁻¹ : GfC (c.V (j + 1))) : GA D (c.V (j + 1))) * v.b (j + 1) := by
      simp [hB₁]
    have eq₂ : (q₂ : GA D (c.V (j + 1 + 1))) =
        ((q₂ * B₂⁻¹ : GfC (c.V (j + 1 + 1))) : GA D (c.V (j + 1 + 1))) * v.b (j + 1 + 1) := by
      simp [hB₂]
    rw [Pi.smul_apply, smul_eq_mul]
    beta_reduce
    rw [eq₁, eq₂]
    exact key _ (q * B₁⁻¹).2 _ (q₂ * B₂⁻¹).2

end GlobalTheory.VMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawScalarFormsContinuousAutomorphicCentral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

variable {D : D7}

theorem RealD.r_center_scalar {c : Comm D} (ρ : RealD c) (hρ : ρ.Is) (j : ℕ) (hj : j ≤ D.R.m) {z : GA D (c.X j)}
    (hz : z ∈ GinfC (c.X j)) (hzc : z ∈ Subgroup.center (GA D (c.X j))) (τ : D.what₂.Tau) :
    ρ.r j hj z τ = (Matrix.trace (ρ.r j hj z τ) / (ρ.N j : ℂ)) • (1 : Matrix (Fin (ρ.N j)) (Fin (ρ.N j)) ℂ) := by
  have hu := hρ.uni j hj
  obtain ⟨ζ, hζ⟩ := GlobalTheory.CenterScalar.scalar_of_comm_unitary (ρ.r j hj z τ) fun U hU => by
    obtain ⟨k, hk⟩ := hu.onto (fun _ => U) fun _ => (Matrix.mem_unitaryGroup_iff').2 hU
    have e1 := hu.mul k ⟨z, hz⟩ τ
    have e2 := hu.mul ⟨z, hz⟩ k τ
    have hkz : (k * ⟨z, hz⟩ : GinfC (c.X j)) = ⟨z, hz⟩ * k :=
      Subtype.ext ((Subgroup.mem_center_iff.1 hzc) k.1)
    rw [hkz, e2] at e1
    have hk' : ρ.r j hj k.1 τ = U := congrFun hk τ
    rw [hk'] at e1
    exact e1.symm
  rcases Nat.eq_zero_or_pos (ρ.N j) with h0 | hpos
  · ext a
    exact absurd a.2 (by omega)
  · rw [hζ, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul,
      mul_div_assoc, div_self (by exact_mod_cast hpos.ne'), mul_one]

theorem rdX_of_clsPinD : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), c.Is → (∀ s, (t s).Is) → ClsPinD t → RdX t := by
  intro D c 𝒯 t hc _ hP j hj
  obtain ⟨ρ, hρ, H⟩ := hP
  refine ⟨fun z => ∏ τ, (Matrix.trace (ρ.r j hj z τ) / (ρ.N j : ℂ)) ^ (∑ i, (ρ.lam j τ).w i), fun s ψ hψ α y => ?_⟩
  obtain ⟨⟨A, hA⟩, -⟩ := H s
  obtain ⟨h1, -, h3, h4⟩ := GlobalTheory.T.seesaw_scalar_forms_laws_on_class_data D c (t s) ρ A hc hρ hA.1 j hj ψ hψ α
  refine ⟨h1 y, fun z hz hzc g => ?_⟩
  have hdet : ∀ τ, IsUnit (ρ.r j hj z τ).det := fun τ =>
    Matrix.isUnit_det_of_left_inverse ((Matrix.mem_unitaryGroup_iff').1 ((hρ.uni j hj).uni ⟨z, hz⟩ τ))
  set w := (ρ.fr j y).tr (ρ.r j hj z) hdet with hw
  have e1 : (t s).rd j α ψ y (g * z) = (t s).rd j α ψ ((ρ.fr j).symm w) g :=
    h3 y _ g z hz (by rw [Equiv.apply_symm_apply]; exact Frames.isTr_tr _ hdet _)
  have e2 := (GlobalTheory.KJInf.valC_poly _ _ _ _ |>.2.2.2) _ (h4 g) (fun τ => Matrix.trace (ρ.r j hj z τ) / (ρ.N j : ℂ)) (ρ.fr j y) w
    (fun τ => by
      show ρ.r j hj z τ * (ρ.fr j y).1 τ = _
      conv_lhs => rw [ρ.r_center_scalar hρ j hj hz hzc τ]
      rw [Matrix.smul_mul, Matrix.one_mul])
  simp only [Equiv.symm_apply_apply] at e2
  rw [e1, e2]

end GlobalTheory.SeeSaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TermSumBoundOfPairsAmplitudeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deg_termSumBoundOfPairsAmplitude : GlobalTheory.Core.Deg.TermSumBoundOfPairsAmplitude := by
  first | exact @GlobalTheory.Core.Deg.termSumBound_of_pairsAmplitude | exact GlobalTheory.Core.Deg.termSumBound_of_pairsAmplitude | (intros; apply GlobalTheory.Core.Deg.termSumBound_of_pairsAmplitude <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainOccurringParamsNormHalfRankBoundStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_chain_occurring_params_norm_half_rank_bound : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, LevFacts D → ParBoundW D := by
  first | exact @GlobalTheory.ChainOnto.parBoundW | exact GlobalTheory.ChainOnto.parBoundW | (intros; apply GlobalTheory.ChainOnto.parBoundW <;> assumption)
end

