import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0502
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0027
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0501
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0275
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainCompositeLiftIntertwinesFiniteGroupActions
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0200
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0166
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0237
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0401
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0335
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0016
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0368
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0509
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0037
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0464
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0466
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0470
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0506
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0385

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SupportedStabilizerConjSatisfiesDeepCongruence
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.KTwoAwayLevel

theorem mem_mL_of_fix {I : AutInst} (g : ℕ) {t : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F} (ht : t ∈ IntAf I.F I.E) {z : VA I}
    (hz : z ∈ I.Lf) (hfix : ((g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * t) • z = z) : z ∈ mL I g := by
  have e : z = (g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • (t • z) := by rw [smul_smul]; exact hfix.symm
  rw [e]
  exact Submodule.subset_span ⟨t • z, I.Lf.smul_mem (⟨t, ht⟩ : IntAf I.F I.E) hz, rfl⟩

theorem conj_fix {I : AutInst} {a y : I.Gf} (ha : a ∈ I.Kset) (hy : y ∈ I.Kset) (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)
    (hc : ∀ i j, c * (I.fmat y - 1) i j = (I.fmat y - 1) i j) {w : VA I} (hw : w ∈ I.Lf) :
    (I.fmat (a⁻¹ * y * a) - 1) *ᵥ w ∈ I.Lf ∧
      c • ((I.fmat (a⁻¹ * y * a) - 1) *ᵥ w) = (I.fmat (a⁻¹ * y * a) - 1) *ᵥ w := by
  have hK : a⁻¹ * y * a ∈ I.Kset := by
    show ((a⁻¹ * y * a : I.Gf) : GL _ _) ∈ Formalism.UG.stabGL I.Lf
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact mul_mem (mul_mem (inv_mem ha) hy) ha
  refine ⟨?_, ?_⟩
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact sub_mem (Formalism.L2.SG.Pf.unitaryCongruence.K_mv I hK hw) hw
  · have hM : c • (I.fmat y - 1) = I.fmat y - 1 := by
      ext i j
      rw [Matrix.smul_apply, smul_eq_mul, hc]
    have hinv : I.fmat a⁻¹ * I.fmat a = 1 := by
      simp only [Formalism.MainNotions.S.AutInst.fmat]
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
    have e : I.fmat (a⁻¹ * y * a) - 1 = I.fmat a⁻¹ * (I.fmat y - 1) * I.fmat a := by
      simp only [Formalism.MainNotions.S.AutInst.fmat] at hinv ⊢
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, Matrix.mul_sub, Matrix.sub_mul,
        Matrix.mul_one, ← hinv]
    rw [e, ← Matrix.smul_mulVec]
    conv_rhs => rw [← hM]
    rw [Matrix.mul_smul, Matrix.smul_mul]

variable {D : D7}

open Classical in
theorem exists_div_indP (v : GlobalTheory.FinPl.Pl D) (g : ℕ) (hg : (g : 𝓞 D.host.F) ∉ v.asIdeal) :
    ∃ s : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F, s ∈ Formalism.UG.intAd D.host.F ∧
      (g : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) * s = GlobalTheory.FinPl.KOpen.indP D (· = v) := by
  have hg' : g ≠ 0 := by rintro rfl; exact hg (by simp)
  have hg0 : (g : D.host.F) ≠ 0 := Nat.cast_ne_zero.2 hg'
  refine ⟨GlobalTheory.FinPl.KOpen.indP D (· = v) * algebraMap D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (g : D.host.F)⁻¹,
    fun w => ?_, ?_⟩
  · have e : (GlobalTheory.FinPl.KOpen.indP D (· = v) * algebraMap D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (g : D.host.F)⁻¹) w =
        (if w = v then 1 else 0) * algebraMap D.host.F (w.adicCompletion D.host.F) (g : D.host.F)⁻¹ := rfl
    rw [e]
    by_cases hw : w = v
    · subst hw
      have h2 : Valued.v (algebraMap D.host.F (w.adicCompletion D.host.F) (g : D.host.F)⁻¹) =
          w.valuation D.host.F (g : D.host.F)⁻¹ := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
      rw [if_pos rfl, one_mul, HeightOneSpectrum.mem_adicCompletionIntegers, h2, map_inv₀]
      have h1 : w.valuation D.host.F (g : D.host.F) = 1 := by
        have := HeightOneSpectrum.valuation_of_algebraMap (K := D.host.F) w (g : 𝓞 D.host.F)
        rw [HeightOneSpectrum.intValuation_eq_one_iff.2 hg] at this
        simpa using this
      rw [h1, inv_one]
    · rw [if_neg hw, zero_mul]; exact zero_mem _
  · rw [mul_left_comm, ← map_natCast (algebraMap D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) g, ← map_mul,
      mul_inv_cancel₀ hg0, map_one, mul_one]

open Classical in
theorem fix_of_grpAt {I : AutInst} (h : I = Formalism.L2.SG.InstExistsPf.instOf D) (v : GlobalTheory.FinPl.Pl D) (g : ℕ)
    (hg : (g : 𝓞 D.host.F) ∉ v.asIdeal) (κ : GA D (D.sp.Y 0)) (hκ : κ ∈ grpAt (D.sp.Y 0) (· = v)) :
    ∃ t ∈ IntAf I.F I.E, ∀ i j, (g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * t *
      (I.fmat ((((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm)) κ).2) - 1) i j =
      (I.fmat ((((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm)) κ).2) - 1) i j := by
  subst h
  obtain ⟨s, hs, hgs⟩ := exists_div_indP v g hg
  refine ⟨(1 : (Formalism.L2.SG.InstExistsPf.instOf D).E) ⊗ₜ[(Formalism.L2.SG.InstExistsPf.instOf D).F] s, Subring.subset_closure (Or.inr ⟨⟨s, hs⟩, rfl⟩), fun i j => ?_⟩
  have e := Formalism.L2.SG.EvalTIota.finE_brg_i (Formalism.IndefR.RationalEmbedding.iota D κ)
  rw [ContinuousMulEquiv.symm_apply_apply] at e
  have hf : (Formalism.L2.SG.InstExistsPf.instOf D).fmat ((((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA rfl)) κ).2) =
      (Formalism.L2.Theta.mt (D.sp.Y 0) κ).map (Formalism.IndefR.Datum.toEAf D) :=
    (congrArg Units.val e).symm
  have key : ∀ i j : Fin (D.sp.Y 0).rank, (1 ⊗ₜ[D.host.F] GlobalTheory.FinPl.KOpen.indP D (· = v)) *
      ((Formalism.L2.Theta.mt (D.sp.Y 0) κ).map (Formalism.IndefR.Datum.toEAf D) - 1) i j =
      ((Formalism.L2.Theta.mt (D.sp.Y 0) κ).map (Formalism.IndefR.Datum.toEAf D) - 1) i j := by
    intro i j
    have hb : (Formalism.L2.Theta.mt (D.sp.Y 0) κ - 1) i j ∈ idAt D (· = v) :=
      (GlobalTheory.FinPl.SetCut.mem_congGrp_iff _ _ κ).1 hκ i j
    have hent : ((Formalism.L2.Theta.mt (D.sp.Y 0) κ).map (Formalism.IndefR.Datum.toEAf D) - 1) i j =
        Formalism.IndefR.Datum.toEAf D ((Formalism.L2.Theta.mt (D.sp.Y 0) κ - 1) i j) := by
      rw [Matrix.sub_apply, Matrix.sub_apply, RingHom.map_sub, Matrix.map_apply]
      congr 1
      by_cases hij : i = j
      · subst hij; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
      · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, RingHom.map_zero]
    have hm := congrArg (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E)
      (GlobalTheory.FinPl.KOpen.e_mul_fin hb)
    rw [map_mul, Algebra.TensorProduct.comm_tmul] at hm
    rw [hent]
    exact hm
  have hg1 : ((g : ℕ) : D.host.E ⊗[D.host.F] Formalism.MainNotions.S.Af D.host.F) * ((1 : D.host.E) ⊗ₜ[D.host.F] s) =
      1 ⊗ₜ[D.host.F] GlobalTheory.FinPl.KOpen.indP D (· = v) := by
    rw [← hgs, ← map_natCast (Algebra.TensorProduct.includeRight (R := D.host.F) (A := D.host.E)) g,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [hf]
  exact (congrArg (fun c => c * ((Formalism.L2.Theta.mt (D.sp.Y 0) κ).map (Formalism.IndefR.Datum.toEAf D) - 1) i j) hg1).trans
    (key i j)

theorem k2cong_conj_of_grpAt : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (v : GlobalTheory.FinPl.Pl D), ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal → ∀ κ : GA D (D.sp.Y 0), κ ∈ grpAt (D.sp.Y 0) (· = v) → (iotaX X h κ).2 ∈ X.B.I.Kset → K2cong X.B.I X.B.g X.e0 X.z0 X.bw ((X.xu u)⁻¹ * (iotaX X h κ).2 * X.xu u) := by
  intro D X h u v hv κ hκ hK
  obtain ⟨t, ht, hfix⟩ := fix_of_grpAt h v _ hv κ hκ
  have hc : ∀ i j, ((X.B.g : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * t) * (X.B.I.fmat (iotaX X h κ).2 - 1) i j =
      (X.B.I.fmat (iotaX X h κ).2 - 1) i j := by
    rw [X.g_eq]; exact hfix
  have key : ∀ w ∈ X.B.I.Lf,
      (X.B.I.fmat ((X.xu u)⁻¹ * (iotaX X h κ).2 * X.xu u) - 1) *ᵥ w ∈ mL X.B.I X.B.g := by
    intro w hw
    obtain ⟨h1, h2⟩ := conj_fix (X.xu_K u) hK _ hc hw
    exact mem_mL_of_fix X.B.g ht h1 h2
  unfold K2cong InMod
  exact ⟨fun a => Submodule.mem_sup_right (key _ (X.vectorsInLattice.1 a).1), Submodule.mem_sup_right (key _ X.vectorsInLattice.2.1),
    fun i => Submodule.mem_sup_right (key _ (X.vectorsInLattice.2.2 i).1)⟩

end GlobalTheory.Core.Mi.KTwoAwayLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftTopScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.IoTop

theorem liftS_smul_domain {D : D7} {S T : HSp D} (om : Om S T) (ν μ : Measure (GA D T)) (c : ENNReal) (hc0 : c ≠ 0)
    (hμ : μ = c • ν) (hH : μ.IsHaarMeasure) {𝓕 𝓖 : Set (GA D T)} (h₁ : IsFundamentalDomain (GQ T) 𝓕 μ)
    (h₂ : IsFundamentalDomain (GQ T) 𝓖 ν) (G : GA D T → ℂ) (φ : WO S T → ℂ) (x : GA D S)
    (hinv : ∀ γ ∈ GQ T, ∀ y, om (x, γ * y) φ 0 * G (γ * y) = om (x, y) φ 0 * G y) :
    liftS om μ 𝓕 G φ x = (c.toReal : ℂ) • liftS om ν 𝓖 G φ x := by
  have : IsTopologicalGroup (GA D T) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have : BorelSpace (GA D T) := ⟨rfl⟩
  have : Countable (GQ T) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig T.gram
  have h₂' : IsFundamentalDomain (GQ T) 𝓖 μ := h₂.mono (hμ ▸ Measure.smul_absolutelyContinuous)
  rw [liftS_apply, liftS_apply, h₁.setIntegral_eq h₂' fun γ y => hinv γ.1 γ.2 y, hμ, Measure.restrict_smul,
    integral_smul_measure, Complex.real_smul]
  rfl

theorem omT_weil {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex)
    (hc : W.Q.Rl.Char3 W.Q.F) (t : W.P.T) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) :
    IsWeilDatumO (pk W).ψ (Yc D (j + 1)) D.sp.X' (Lift.chrStep ((pk W).toLevCh.mu t) (pk W).eta D.R.m).1
      (Lift.chrStep ((pk W).toLevCh.mu t) (pk W).eta D.R.m).2 (omT (pk W) t j h) := by
  have key : ∀ n (e : D.R.m - 1 = n), IsWeilDatumO (pk W).ψ (Yc D n) D.sp.X' (Lift.chrStep ((pk W).toLevCh.mu t) (pk W).eta D.R.m).1
      (Lift.chrStep ((pk W).toLevCh.mu t) (pk W).eta D.R.m).2
      (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') ((pk W).ωX t) e) := by
    rintro n rfl
    exact hc.chain.ωX t
  exact key (j + 1) (idx_top h)

theorem smul_const (a b : ℝ) (H z : ℂ) (hab : 0 ≤ a * b) :
    ((ENNReal.ofReal (a * b)).toReal : ℂ) • (H • z) = (H * (a : ℂ) * (b : ℂ)) • z := by
  rw [ENNReal.toReal_ofReal hab, smul_eq_mul, smul_eq_mul, smul_eq_mul, Complex.ofReal_mul]
  ring

end GlobalTheory.Fam.IoTop

set_option maxHeartbeats 1000000 in
open GlobalTheory.Fam.IoTop in
theorem GlobalTheory.Fam.ioT_lift : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ f : FamCh W u, f.RowOK → ∀ t j (h : j + 2 * 0 + 2 = D.R.m) (F : (f.t t).CT) P v, liftS ((f.t t).omT j h) f.c.volT.μ f.c.volT.𝓕 (F.1 v) ((f.t t).ptT j h P) = (f.t t).cI (j + 1) • ((f.t t).ioT j h F).1 (f.c.ItT j h P v) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP f hR t j h F P v
  have hc := hP.bot.hyp.2.2.2.1
  obtain ⟨h', -, hL⟩ := GlobalTheory.T.extra_column_range_membership W u hP f.g t j h F
  have key := hL ((f.row t).vT j h) ((hR.row t).vT j h) P v
  obtain ⟨h'', hio⟩ := (hR.row t).ioT j h F
  have hm := hR.meas.volT t
  rw [show D.R.m - 1 = j + 1 by omega, show f.g.κ D.R.m = f.g.κ (j + 1 + 1) from congrArg f.g.κ (by omega)] at hm
  have hom := omT_weil W hc t j h
  have hth : IsThetaFunO (pk W).ψ (Yc D (j + 1)) D.sp.X' (pureTensorO (pk W).ψ (pk W).θ (Yc D (j + 1)) D.sp.X'
      (cart ((pk W).MY (j + 1))) (cart (pk W).MX) (onb ((pk W).MY (j + 1))) (onb (pk W).MX) ((f.row t).vT j h) P) := by
    obtain ⟨cY, hcY⟩ := hc.lev.βY (j + 1) (by omega)
    obtain ⟨cX', hcX⟩ := hc.lev.βX
    have hf := (GlobalTheory.VecTheta.vecThetaSD D).1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hcY) (GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hcX) hcY.1 hcX.1
      ((hR.row t).vT j h)
    have e0 : ∀ (V : HSp D) (ρ : D.what₂.Tau), compAt (pk W).θ ρ (Formalism.L2.Theta.mt V 1) = 1 := fun V ρ => by
      have : Formalism.L2.Theta.mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]
      rw [this]
      exact Matrix.map_one _ (by simp) (by simp)
    exact (GlobalTheory.OrientedHeis.om_pureTensorO D _ _ _ _ _ _ _ hom hc.models.inf (cart ((pk W).MY (j + 1))) (cart ((pk W).MY (j + 1)))
      (onb ((pk W).MY (j + 1))) (onb ((pk W).MY (j + 1))) (cart (pk W).MX) (cart (pk W).MX) (onb (pk W).MX) (onb (pk W).MX) 1 1
      (fun ρ => by rw [e0, Matrix.mul_one, Matrix.one_mul]) (fun ρ => by rw [e0, Matrix.mul_one, Matrix.one_mul]) (fun ρ => by rw [e0, Matrix.one_mul]) (fun ρ => by rw [e0, Matrix.one_mul]) _ hf P).1
  have hκ := hR.meas.κ (j + 1 + 1)
  have hvl : 0 ≤ volLev (pk W) f.g t (j + 1) := by unfold volLev; split_ifs <;> exact ENNReal.toReal_nonneg
  have hc0 : ENNReal.ofReal (f.g.κ (j + 1 + 1) * volLev (pk W) f.g t (j + 1)) ≠ 0 := by
    have := (hR.meas.cIOf_ne_zero (lvP W) t (j + 1) (by omega))
    unfold cIOf at this
    intro h0
    rw [ENNReal.ofReal_eq_zero] at h0
    refine this ?_
    have : f.g.κ (j + 1 + 1) * volLev (pk W) f.g t (j + 1) = 0 := le_antisymm h0 (mul_nonneg hκ.le hvl)
    rw [mul_assoc, ← Complex.ofReal_mul, this, Complex.ofReal_zero, mul_zero]
  have hfd := (hc.models.νX t).2
  show liftS (omT (pk W) t j h) f.g.volT.μ f.g.volT.𝓕 (F.1 v) _ = cIOf (pk W) (lvP W) f.g t (j + 1) • _
  funext x
  have e1 := liftS_smul_domain (omT (pk W) t j h) ((pk W).νX t) f.g.volT.μ _ hc0 hm f.g.volT.haar f.g.volT.fund hfd
    (F.1 v) (pureTensorO (pk W).ψ (pk W).θ (Yc D (j + 1)) D.sp.X' (cart ((pk W).MY (j + 1))) (cart (pk W).MX)
      (onb ((pk W).MY (j + 1))) (onb (pk W).MX) ((f.row t).vT j h) P) x (fun γ hγ y => by
        have a1 : (omT (pk W) t j h) (x, γ * y) = (omT (pk W) t j h) (1, γ) * (omT (pk W) t j h) (x, y) := by
          rw [← map_mul, Prod.mk_mul_mk, one_mul]
        rw [a1, Module.End.mul_apply, hom.om_aut 1 (one_mem _) γ hγ _ (hom.om_pres _ _ hth),
          GlobalTheory.ChainLiftEquiv.multT_left _ _ _ _ F.1 F.2 v γ hγ y])
  have hio' : (((f.t t).ioT j h) F).1 = ((ioXT (pk W) t j h) ⟨F.1, h'⟩).1 := hio
  have e2 : (((f.t t).ioT j h) F).1 (((f.c.ItT j h) P) v) x = ((ioXT (pk W) t j h) ⟨F.1, h'⟩).1 (((f.c.ItT j h) P) v) x :=
    congrFun (LinearMap.congr_fun hio' _) x
  have e3 := congrFun key x
  rw [Pi.smul_apply] at e3
  exact e1.trans ((congrArg _ e3).trans ((smul_const _ _ _ _ (mul_nonneg hκ.le hvl)).trans (congrArg _ e2.symm)))

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftWittIndexVanishing
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem normSq_theta_modGrowth : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DoublingMethod → ∀ D : D7, SiegelWeilFock D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → (wittIndex B = 0 ∨ wittIndex B < t) → ∀ mH : Measure (GA D B), mH.IsHaarMeasure → ∀ Φ, IsFockVec ψ θ A B sA sB Φ → (∀ g, MemL2Quotient (GQ B) mH fun h => thetaKO om g h Φ) ∧ GlobalTheory.Grow.ModGrowth A fun g => petersson B mH (fun h => thetaKO om g h Φ) fun h => thetaKO om g h Φ := by
  intro hW hDM D hSW ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP hwitt mH hmH Φ hΦ
  obtain ⟨ha, ht, hb, -⟩ := hP.setting
  obtain ⟨omh, homh⟩ := GlobalTheory.Core.Rk.exists_doubled_weilDatum hW D ψ A B χA χB om hP.weil
  have hTC := GlobalTheory.DoublingTheta.thetaClause D ψ A B χA χB om omh hP.weil homh
  obtain ⟨hφ, hid⟩ := hTC Φ Φ hΦ.1 hΦ.1
  have hK := GlobalTheory.Core.Rk.IP.delta_isKFinVec D ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP omh homh Φ Φ hΦ hΦ
  have hab : A.rank < B.rank := by omega
  have hw : wittIndex B = 0 ∨ A.rank + wittIndex B < B.rank := by
    rcases hwitt with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  obtain ⟨-, -, -, hθ', -, -, hcA, hcB, -⟩ := hP.setting
  have hc := GlobalTheory.Core.Rk.IP.Cartan.cartan_dbl D θ A sA a hθ' hcA hP.maj_eq
  have hF := GlobalTheory.Core.Rk.FockBox.isFockVec_delta D ψ θ A B sA sB hP.weil.std hθ' Φ Φ hΦ hΦ
  obtain ⟨hint, hEV⟩ := hSW ψ A B ha hab hw χB omh homh a hP.maj θ _ sB hθ' hc.1 hcB hc.2 ν 𝓕 hP.covol mH hmH _ hF

  have key : ∀ g h, thetaKO om g h Φ * conj (thetaKO om g h Φ) =
      ((χB (detA A g) : Circle) : ℂ) * thetaKO omh (io A (g, g)) h (delta A B Φ Φ) := by
    intro g h
    rw [(hid g g h).2]
    have e : ((χB (detA A g) : Circle) : ℂ) * (((χB (detA A g))⁻¹ : Circle) : ℂ) = 1 := by
      rw [← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]
    linear_combination (-(thetaKO om g h Φ * conj (thetaKO om g h Φ))) * e
  have knorm : ∀ g h, ‖thetaKO om g h Φ‖ ^ 2 = ‖thetaKO omh (io A (g, g)) h (delta A B Φ Φ)‖ := by
    intro g h
    have := congrArg norm (key g h)
    rw [norm_mul, norm_mul, Circle.norm_coe, one_mul, Complex.norm_conj, ← sq] at this
    rw [this]
  have hleft : ∀ g, LeftInv (GQ B) fun h => thetaKO om g h Φ := fun g γ hγ h => by
    show thetaKO om g (γ * h) Φ = thetaKO om g h Φ
    have e : ((g, γ * h) : GA D A × GA D B) = (1, γ) * (g, h) := by simp
    unfold thetaKO
    rw [e, map_mul]
    exact hP.weil.om_aut 1 (one_mem _) _ hγ _ (hP.weil.om_pres _ _ hΦ.1)
  have hcont : ∀ g, Continuous fun h => thetaKO om g h Φ := fun g =>
    (hP.weil.om_cont Φ hΦ.1 0).comp (Continuous.prodMk_right g)
  have hL2 : ∀ g, MemL2Quotient (GQ B) mH fun h => thetaKO om g h Φ := by
    intro g
    refine ⟨hleft g, ?_⟩
    have hm : AEStronglyMeasurable (descend (GQ B) fun h => thetaKO om g h Φ) (GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ B) mH) := by
      rw [aestronglyMeasurable_quotMeasure_iff_lift, (hleft g).lift_descend]
      exact (hcont g).aestronglyMeasurable
    refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
    refine (hint (io A (g, g))).norm.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [GlobalTheory.AutomorphicL2Unitary.descend]
    exact (knorm g _).symm
  refine ⟨hL2, ?_⟩

  have hI : HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) :=
    GlobalTheory.Core.Rk.IP.hasIwasawa_KAd_selfDual D A (frameLat A) a (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A) hP.maj
  have hmem := GlobalTheory.SwSecMem.swSec_mem_degPS hW D ψ A B χB omh homh ν 𝓕 hP.covol (delta A B Φ Φ) hφ a hK
  have hHk : IsHeckeChar D χB⁻¹ := by
    have h := homh.hecT
    refine ⟨?_, fun x => ?_⟩
    · have : (χB⁻¹ : (AE D)ˣ →* Circle) = fun x => (χB x)⁻¹ := rfl
      rw [this]; exact h.1.inv
    · rw [MonoidHom.inv_apply, h.2 x, inv_one]
  obtain ⟨k, hk⟩ := (hDM D A (by omega) a hP.maj hI χB⁻¹ B.rank hHk (resEta_inv homh.resT) (sZero A B)
    (swSec A B omh ν 𝓕 (delta A B Φ Φ)) hmem).1.2 (sZero A B)
  obtain ⟨r, hr, -, -, C₁, N, hC₁⟩ := GlobalTheory.Eis.EisRegularAt.of_eisValueAt hk hEV
  have hE : ∀ x, ‖ThetaMean.thetaMean omh mH (delta A B Φ Φ) x‖ ≤ C₁ * GlobalTheory.Grow.height (dblSp A) x ^ N := by
    intro x
    have e := (hEV.2 x).valueAt.cont_eq
    have := hC₁ (sZero A B) (Metric.mem_ball_self hr) x
    rw [GlobalTheory.Eis.eisCont, e] at this
    exact this
  have hC₁0 : 0 ≤ C₁ := by
    have h1 := (norm_nonneg _).trans (hE 1)
    exact nonneg_of_mul_nonneg_left h1 (pow_pos (GlobalTheory.Grow.height_pos _ _) _)
  obtain ⟨C₂, c, hC₂⟩ := GlobalTheory.Grow.IoHeight.main D A

  have hvol := GlobalTheory.RallisIP.Model.vol_pos (B := B) mH
  have hfin : IsFiniteMeasure (autMeasure B mH) := by
    refine ⟨lt_top_iff_ne_top.2 fun h => ?_⟩
    simp [Measure.real, h] at hvol
  have hpet : ∀ g, ‖petersson B mH (fun h => thetaKO om g h Φ) (fun h => thetaKO om g h Φ)‖ =
      (autMeasure B mH).real Set.univ * ‖ThetaMean.thetaMean omh mH (delta A B Φ Φ) (io A (g, g))‖ := by
    intro g
    have e1 : petersson B mH (fun h => thetaKO om g h Φ) (fun h => thetaKO om g h Φ) =
        ((χB (detA A g) : Circle) : ℂ) *
          ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ B) (fun h => thetaKO omh (io A (g, g)) h (delta A B Φ Φ)) q ∂autMeasure B mH := by
      rw [← integral_const_mul]
      simp only [petersson, pet, GlobalTheory.AutomorphicL2Unitary.descend]
      congr 1
      funext q
      exact key g _
    rw [e1, norm_mul, Circle.norm_coe, one_mul, ← measure_smul_average, norm_smul, ThetaMean.thetaMean,
      Real.norm_of_nonneg measureReal_nonneg]
  refine ⟨(autMeasure B mH).real Set.univ * C₁ * C₂ ^ N, 2 * c * N, fun g => ?_⟩
  rw [hpet g]
  have hg := GlobalTheory.Grow.height_pos A g
  have h2 : GlobalTheory.Grow.height (dblSp A) (io A (g, g)) ^ N ≤ (C₂ * GlobalTheory.Grow.height A g ^ (2 * c)) ^ N := by
    refine pow_le_pow_left₀ (GlobalTheory.Grow.height_pos _ _).le ?_ N
    have := hC₂ g g
    rwa [← sq, ← pow_mul] at this
  calc (autMeasure B mH).real Set.univ * ‖ThetaMean.thetaMean omh mH (delta A B Φ Φ) (io A (g, g))‖
      ≤ (autMeasure B mH).real Set.univ * (C₁ * GlobalTheory.Grow.height (dblSp A) (io A (g, g)) ^ N) :=
        mul_le_mul_of_nonneg_left (hE _) hvol.le
    _ ≤ (autMeasure B mH).real Set.univ * (C₁ * (C₂ * GlobalTheory.Grow.height A g ^ (2 * c)) ^ N) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hC₁0) hvol.le
    _ = (autMeasure B mH).real Set.univ * C₁ * C₂ ^ N * GlobalTheory.Grow.height A g ^ (2 * c * N) := by
        rw [mul_pow, ← pow_mul]; ring

end GlobalTheory.Core.Rk.IP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowChoiceValueStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_uniformizer_sub_qOf_lt_of_gRead : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u) (row : ∀ t, RowCh (pk W) (lvP W) u a.g t) (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))), GRead (a.fam row col) a.G a.pl → ∀ n : Fin a.n, valuation (a.G n).k ((((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k) - ((Formalism.L2.Col.qOf (a.pl n).1 : ℕ) : (a.G n).k)) < valuation (a.G n).k (((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k) := by
  first | exact @GlobalTheory.LevUnif.unif_of_gRead | exact GlobalTheory.LevUnif.unif_of_gRead | (intros; apply GlobalTheory.LevUnif.unif_of_gRead <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.TopLevQ.red_eq_zero_iff : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (t h : GA D V) (N M : Matrix (Fin V.rank) (Fin V.rank) k), GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit q) V t β N → (Formalism.L2.Theta.mt V h).map q.pr * N = N * M → Lev.finE V (t⁻¹ * h * t) ∈ Formalism.L2.DIV.St β → ∀ i j, ((Formalism.L2.DIV.redFn β PP (Lev.finE V (t⁻¹ * h * t))).val i j = 0 ↔ ValuativeRel.valuation k (M i j) < 1) := by
  intro D k _ _ _ _ q PP hPP V β t h N M hN hM hSt i j
  constructor
  · intro h0
    have := GlobalTheory.SeeSaw.LevRed.red_of_movedTo q PP hPP V β t h N M hN hM hSt i j 0 (by rw [h0, map_zero])
    have e0 : (GlobalTheory.LocMod.ofSplit q).pr ((0 : 𝓞 D.host.E) : D.host.E) = 0 := by
      show (GlobalTheory.LocMod.ofSplit q).π ((incA D) ((0 : 𝓞 D.host.E) : D.host.E)) = 0
      rw [show ((0 : 𝓞 D.host.E) : D.host.E) = 0 from rfl, map_zero, map_zero]
    rwa [e0, sub_zero] at this
  · intro hv
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective ((Formalism.L2.DIV.redFn β PP (Lev.finE V (t⁻¹ * h * t))).val i j)
    have h1 := GlobalTheory.SeeSaw.LevRed.red_of_movedTo q PP hPP V β t h N M hN hM hSt i j z hz
    have h2 : ValuativeRel.valuation k ((GlobalTheory.LocMod.ofSplit q).pr (z : D.host.E)) < 1 := by
      have e : (GlobalTheory.LocMod.ofSplit q).pr (z : D.host.E) = M i j - (M i j - (GlobalTheory.LocMod.ofSplit q).pr (z : D.host.E)) := by ring
      rw [e]
      exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hv h1)
    obtain ⟨π', hπ, hred, -⟩ := GlobalTheory.T.exists_finiteAdele_projection_integral_reduction D k q PP hPP
    have h6 : (GlobalTheory.LocMod.ofSplit q).pr (z : D.host.E) = (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E z) := (hπ _).symm
    rw [h6, ← hred.ker, Formalism.L2.DIV.resS_oToS] at h2
    rw [← hz, h2]

set_option maxHeartbeats 2000000 in

theorem GlobalTheory.TopLevQ.mem_levS_top_iff : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ (t : W.P.T) (PP : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E) (hP : PP ∈ (pk W).Q t) (E : QExt (a.Q PP ⟨t, hP⟩) (chrK W t)), ∀ x ∈ GlobalTheory.SplitWeil.KO (a.Q PP ⟨t, hP⟩).k (GlobalTheory.StepData.Ix (Fin (I.rec7 l Z).R.k ⊕ Fin ((a.Q PP ⟨t, hP⟩).s + 1)) (Fin (I.rec7 l Z).R.t) ((a.Q PP ⟨t, hP⟩).s + 2)), ∀ g, (ofSplit (a.Q PP ⟨t, hP⟩).q).IsLoc (a.Q PP ⟨t, hP⟩).FT g x → (a.g.bT⁻¹ * g * a.g.bT ∈ levS _ (pk W).βX (datXP (pk W) (lvP W) t) ↔ x ∈ ((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).levTop.J) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha1 ha2 t PP hP E x hx g hg
  have hTop : x ∈ ((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).levTop.J ↔ x ∈ GlobalTheory.SplitWeil.KO (a.Q PP ⟨t, hP⟩).k _ ∧ GlobalTheory.StepData.MaxM x.val.toBlocks₂₁ := by
    show x ∈ ((GlobalTheory.StepData.parahoric _ _ E.δ E.tame).toLevel.map (GlobalTheory.StepData.LatFrame.refl _ _).conj).J ↔ _
    rw [GlobalTheory.StepData.Level.mem_map]
    have e1 : (GlobalTheory.StepData.LatFrame.refl (a.Q PP ⟨t, hP⟩).k (GlobalTheory.StepData.Ix (Fin (I.rec7 l Z).R.k ⊕ Fin ((a.Q PP ⟨t, hP⟩).s + 1)) (Fin (I.rec7 l Z).R.t) ((a.Q PP ⟨t, hP⟩).s + 2))).conj.symm x = x := by
      ext i j
      simp [GlobalTheory.StepData.LatFrame.conj, GlobalTheory.StepData.LatFrame.refl, GlobalTheory.StepData.reGL_symm_val]
      rfl
    rw [e1]
    exact GlobalTheory.StepData.mem_parahoric
  rw [hTop]
  obtain ⟨e, he, hmv⟩ := (a.Q PP ⟨t, hP⟩).frameTop
  have hmv' : GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit (a.Q PP ⟨t, hP⟩).q) (I.rec7 l Z).sp.X' a.g.bT (pk W).βX
      ((a.Q PP ⟨t, hP⟩).FT.β.submatrix id e.symm) := hmv
  have hidem : Formalism.L2.NTheta.IsIdemAt (a.Q PP ⟨t, hP⟩).q.e PP := (a.Q PP ⟨t, hP⟩).idem
  have hβX : Formalism.IndefR.Links.IsSDFrame (I.rec7 l Z).sp.X' (pk W).βX (pk W).ΛX 1 := W.Q.charW.base.lev.βX
  obtain ⟨hGfC, hStIff, hoff⟩ := GlobalTheory.T.splitPlace_conj_stabilizes_framedLattice_iff (I.rec7 l Z) (a.Q PP ⟨t, hP⟩).k (a.Q PP ⟨t, hP⟩).q PP hidem (I.rec7 l Z).sp.X' (pk W).βX
    (pk W).ΛX 1 hβX _ (a.Q PP ⟨t, hP⟩).FT e.symm a.g.bT hmv' g x hg
  obtain ⟨hsupp, hmat⟩ := hg
  have hM : (Formalism.L2.Theta.mt _ g).map (a.Q PP ⟨t, hP⟩).q.pr * (a.Q PP ⟨t, hP⟩).FT.β.submatrix id e.symm =
      (a.Q PP ⟨t, hP⟩).FT.β.submatrix id e.symm * x.val.submatrix e.symm e.symm := by
    have h1 : (Formalism.L2.Theta.mt _ g).map (a.Q PP ⟨t, hP⟩).q.pr = (a.Q PP ⟨t, hP⟩).FT.β * x.val * (a.Q PP ⟨t, hP⟩).FT.γ := hmat
    rw [h1]
    exact GlobalTheory.TopLevQ.moved_mat _ _ (a.Q PP ⟨t, hP⟩).FT.γβ _ e
  have hsupp' : Formalism.L2.Theta.SuppAt (a.Q PP ⟨t, hP⟩).q.e _ (a.g.bT⁻¹ * g * a.g.bT) := GlobalTheory.TopLevQ.suppAt_conj g a.g.bT hsupp
  have hr : (I.rec7 l Z).R.r = (I.rec7 l Z).R.k + ((a.Q PP ⟨t, hP⟩).s + 1) := by
    have := (a.Q PP ⟨t, hP⟩).hs
    unfold Ranks.r
    omega
  have hPg := (GlobalTheory.PkFrame.pk_frame_places W hW t PP hP 0 (by have := (a.Q PP ⟨t, hP⟩).hs; omega)).2
  have hord := GlobalTheory.TopLevQ.blk_iff e he x.val
  rw [← hr] at hord
  rw [GlobalTheory.TopLevQ.mem_levS_iff]
  have hred := GlobalTheory.TopLevQ.red_eq_zero_iff (a.Q PP ⟨t, hP⟩).q PP hidem (I.rec7 l Z).sp.X' (pk W).βX a.g.bT g _ _ hmv' hM
  constructor
  · rintro ⟨-, ⟨hSt, -, hQt⟩, -⟩
    refine ⟨hx, hord.1 fun i j hij => (hred hSt i j).1 ?_⟩
    exact (hQt PP hP) hij
  · rintro ⟨hx', hmax⟩
    have hSt : Lev.finE (I.rec7 l Z).sp.X' (a.g.bT⁻¹ * g * a.g.bT) ∈ Formalism.L2.DIV.St (pk W).βX := hStIff.2 hx'
    have hone : ∀ PP' : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E, PP'.under (𝓞 (I.rec7 l Z).host.F) ≠ PP.under (𝓞 (I.rec7 l Z).host.F) →
        Formalism.L2.DIV.redFn (pk W).βX PP' (Lev.finE (I.rec7 l Z).sp.X' (a.g.bT⁻¹ * g * a.g.bT)) = 1 :=
      fun PP' hne => GlobalTheory.SplitOffRed.redFn_eq_one_off (a.Q PP ⟨t, hP⟩).q hidem _ _ _ hsupp' hSt PP' hne
    refine ⟨hGfC, ⟨hSt, fun PP' hPP' => ?_, fun PP' hPP' => ?_⟩, ?_⟩
    · rw [hone PP' (hPg PP' hPP')]
      exact Subgroup.one_mem _
    · by_cases hPe : PP' = PP
      · subst hPe
        intro i j hij
        exact (hred hSt i j).2 (hord.2 hmax i j hij)
      · rw [hone PP' fun hu => hPe (hW.pk.sel PP' PP ⟨t, hPP'⟩ ⟨t, hP⟩ hu)]
        exact Subgroup.one_mem _
    · have h1 : Formalism.L2.DIV.rTup (pk W).βX (datXP (pk W) (lvP W) t) (Lev.finE (I.rec7 l Z).sp.X' (a.g.bT⁻¹ * g * a.g.bT)) = 1 := by
        funext PP'
        show Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn (pk W).βX PP'.1 _) = 1
        rw [hone PP'.1 (hPg PP'.1 PP'.2)]
        exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
      rw [h1]
      exact Subgroup.one_mem _

end
end

