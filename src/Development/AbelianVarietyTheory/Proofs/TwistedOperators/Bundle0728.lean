import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittCoreInclusionMemCompletedHomLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartTraceCharacterIdempotentInverseDiffere
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0721
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0566
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0320
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0272
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0115
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0116
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittUnfoldedIntegralLeCoreQuotientHeightStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0722
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0560
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1439
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualHomLatticeModulusShiftLocalEqLatO
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.BigLoc

variable {D : D7}

theorem latO_tgt_le {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT LT' : Set (Fin T.rank → D.host.E)}
    (v : GlobalTheory.FinPl.Pl D) (c : 𝓞 D.host.F) (hc : c ∉ v.asIdeal)
    (h : ∀ t ∈ LT, (((c : D.host.F) : D.host.E)) • t ∈ LT') :
    latO S T LS LT (· = v) ≤ latO S T LS LT' (· = v) := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro w ⟨α, hα, hsupp, a, ha, s, hs, t, ht, rfl⟩
  refine AddSubgroup.subset_closure ⟨GlobalTheory.IdeleAA.gam v c * α, GlobalTheory.IdeleAA.gam_mul_int v c hc hα,
    GlobalTheory.IdeleAA.gam_mul_supp v c α, a, ha, s, hs, _, h t ht, ?_⟩
  ext i j
  simp only [Matrix.of_apply]
  rw [← GlobalTheory.IdeleAA.pair_scale v c α hsupp]
  congr 1
  have h0 := GlobalTheory.IdeleAA.coe_ne_zero v c hc
  rw [Pi.smul_apply, smul_eq_mul]
  field_simp

end GlobalTheory.BigLoc

namespace GlobalTheory.BigLoc

variable {D : D7}

theorem coe_alg (c : 𝓞 D.host.F) :
    algebraMap (𝓞 D.host.E) D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c) = ((c : D.host.F) : D.host.E) := rfl

theorem exists_c {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D} (hv : v ∉ P.S0) :
    ∃ c : 𝓞 D.host.F, c ∉ v.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ P.modul sc ∧
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ P.modulBar sc := by
  classical
  set J : Ideal (𝓞 D.host.F) := ∏ v' ∈ P.S0, v'.asIdeal ^ P.depth sc v' with hJdef
  have hJ : ¬ J ≤ v.asIdeal := by
    intro h
    obtain ⟨v', hv', hle⟩ := (Ideal.IsPrime.prod_le v.isPrime).1 h
    have h1 : v'.asIdeal ≤ v.asIdeal := Ideal.IsPrime.le_of_pow_le (hP := v.isPrime) hle
    have : v' = v := HeightOneSpectrum.ext (v'.isMaximal.eq_of_le v.isPrime.ne_top h1)
    exact hv (this ▸ hv')
  obtain ⟨c, hcJ, hcv⟩ := Set.not_subset.1 hJ
  have hmap : J.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ P.modul sc := by
    rw [hJdef]
    change Ideal.mapHom (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) _ ≤ _
    rw [map_prod]
    refine Finset.prod_le_prod' fun v' hv' => ?_
    rw [map_pow]
    refine pow_le_pow_left' ?_ _
    refine Ideal.map_le_iff_le_comap.2 (le_of_eq ?_)
    have := congrArg HeightOneSpectrum.asIdeal (P.under_w hv')
    exact this.symm
  have hmod : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ P.modul sc := hmap (Ideal.mem_map_of_mem _ hcJ)
  refine ⟨c, hcv, hmod, ?_⟩
  have hfix : D.host.conj • algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c := by
    apply FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E
    rw [Formalism.L2.Pj.algebraMap_conj_smul, coe_alg]
    exact GlobalTheory.IdeleAA.conj_F c
  unfold Places.modulBar
  rw [← hfix]
  exact Ideal.smul_mem_pointwise_smul _ _ _ hmod

end GlobalTheory.BigLoc

namespace GlobalTheory.BigLoc

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem smul_mem_idLat (G : GridData L sc) {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {c : 𝓞 D.host.F}
    (hc : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ G.pl.modul sc) (hne : G.pl.modulBar sc ≠ ⊥)
    {y : Fin n → D.host.E} (hy : y ∈ Λ) : ((c : D.host.F) : D.host.E) • y ∈ idLat (shiftId G) Λ := by
  refine Submodule.subset_span ⟨_, ?_, y, hy, rfl⟩
  unfold shiftId
  rw [← mul_one ((c : D.host.F) : D.host.E)]
  exact FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal (𝓞 D.host.E)⁰).2 ⟨_, hc, coe_alg c⟩)
    (FractionalIdeal.one_mem_inv_coe_ideal hne)

theorem smul_idLat_mem (G : GridData L sc) {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {c : 𝓞 D.host.F}
    (hcb : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ G.pl.modulBar sc) (hne : G.pl.modulBar sc ≠ ⊥)
    {z : Fin n → D.host.E} (hz : z ∈ idLat (shiftId G) Λ) : ((c : D.host.F) : D.host.E) • z ∈ Λ := by
  refine Submodule.span_induction (p := fun z _ => ((c : D.host.F) : D.host.E) • z ∈ Λ) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨s, hs, y, hy, rfl⟩
    have hm : ((c : D.host.F) : D.host.E) * s ∈ ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
      have := FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal (𝓞 D.host.E)⁰).2 ⟨_, hcb, coe_alg c⟩) hs
      have h0 : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
        rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
      rwa [shiftId, mul_left_comm, mul_inv_cancel₀ h0, mul_one] at this
    obtain ⟨o, -, ho⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 D.host.E)⁰).1 hm
    rw [smul_smul, ← ho, algebraMap_smul]
    exact Λ.smul_mem o hy
  · simp
  · intro x y _ _ hx hy; rw [smul_add]; exact add_mem hx hy
  · intro a x _ hx; rw [smul_comm]; exact Λ.smul_mem a hx

end GlobalTheory.BigLoc

theorem GlobalTheory.BigLoc.latBig_at : All fun {D} _ _ _ {G} _ _ => ∀ i, i < D.R.m → ∀ v ∉ G.pl.S0,
    ∀ u : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)), MxAt (· = v) u →
      (u ∈ latBig G i ↔ u ∈ latO _ _ (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (· = v)) := by
  intro D _ T L μ0 _ sc G W M _ i _ v hv u hu
  obtain ⟨c, hcv, hc, hcb⟩ := GlobalTheory.BigLoc.exists_c G.pl sc hv
  have hne : G.pl.modulBar sc ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hcb
    apply GlobalTheory.IdeleAA.coe_ne_zero v c hcv
    rw [← GlobalTheory.BigLoc.coe_alg, hcb, map_zero]
  unfold latBig
  rw [GlobalTheory.AscFinWit.mem_latO_at hu]
  exact ⟨fun h => GlobalTheory.BigLoc.latO_tgt_le v c hcv (fun t ht => GlobalTheory.BigLoc.smul_idLat_mem G hcb hne ht) h,
    fun h => GlobalTheory.BigLoc.latO_tgt_le v c hcv (fun t ht => GlobalTheory.BigLoc.smul_mem_idLat G hc hne ht) h⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftHorizontalOfCuspTypeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_horizontal_of_cusp_type : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g Φ * φ g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) → ∀ C : Set (GA D (G.V i j).V), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ (n : ℕ) (f : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol (G.V i j) (G.V i (j + 1))) (F : Fin n → (G.V i (j + 1)).Maps) (v : Fin n → SmT (G.V i (j + 1)).M), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f l)) ∧ (∀ l, F l ∈ (G.V i (j + 1)).Cusp R.θ) ∧ ∀ h ∈ C, ‖(∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g Φ * φ g ∂(G.meas t i (j + 1)).ν) - ∑ l, ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g (GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f l) (p l)) * F l (v l) g ∂(G.meas t i (j + 1)).ν‖ < δ := by
  first | exact @GlobalTheory.ThetaArrowApprox.thetaLift_approx | exact GlobalTheory.ThetaArrowApprox.thetaLift_approx | (intros; apply GlobalTheory.ThetaArrowApprox.thetaLift_approx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftUnfoldingIntegratedOverFamily
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.Asc.Gen

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W : HSp D} {ρ : ℕ} {Y : Type} [TopologicalSpace Y]
  [MeasurableSpace Y]

set_option maxHeartbeats 400000 in

theorem tot_continuous (a : Gen ψ V V₀ W ρ Y) (ha : a.Is) (G : GA D W → ℂ) (Φ : WO V W → ℂ) (hG : RapidDec W G)
    (hΦ : IsThetaFunO ψ V W Φ) : Continuous (a.tot G Φ) := by
  obtain ⟨vT⟩ := (GlobalTheory.T.unfoldingLevelsAndSteps_haarMeasures_exist D).2.2.1 0 V₀.rank
  have hmix := (GlobalTheory.MixCont.mixed_coords_continuous D ψ V V₀ W W ρ 0 a.d (hypZero W) a.vS vT a.χV a.χW a.om
    ha.weil Φ hΦ).1
  have hpos : Continuous fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank =>
      (⟨a.d.nB p.2.2 * a.d.levi p.2.1.1, mul_mem (a.d.nB_mem_NFlag _) (a.d.levi_mem_NFlag p.2.1.2)⟩ : flagN a.d) :=
    ((a.d.continuous_nB.comp continuous_snd.snd).mul
      ((a.d.continuous_levi.comp continuous_subtype_val).comp continuous_snd.fst)).subtype_mk _
  have hTh : Continuous fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank =>
      a.Th p.1.2 (a.d.nB p.2.2 * a.d.levi p.2.1.1) :=
    ha.cont.comp (continuous_fst.snd.prodMk hpos)
  have hM : Continuous fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank =>
      a.d.mixS W ψ a.vS.μ a.vS.𝓕 (a.om (a.d.emb0 (a.g p.1.2), p.1.1) Φ) ((rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.1.1.1)
        ((rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.2) :=
by
    have h1 : Continuous fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank => a.d.emb0 (a.g p.1.2) :=
      a.d.continuous_embed.comp (ha.g.comp continuous_fst.snd)
    have h2 : Continuous fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank =>
        ((rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.1.1.1 : Mx D W.rank ρ) :=
      continuous_const.matrix_mul (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd.fst))
    have h3 : Continuous fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank =>
        ((rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.2 : WO V₀ W) :=
      continuous_const.matrix_mul continuous_snd.snd
    have hq : Continuous fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank =>
        (((a.d.emb0 (a.g p.1.2), p.1.1), ((rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.1.1.1, (rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.2)) :
          (GA D V × GA D W) × Mx D W.rank ρ × WO V₀ W) :=
      (h1.prodMk continuous_fst.fst).prodMk (h2.prodMk h3)
    have hc := hmix.comp hq
    exact hc
  have hfin := (hG.2.1.comp continuous_fst.fst).mul (hTh.mul hM)
  exact hfin

theorem inner_unfold (a : Gen ψ V V₀ W ρ Y) (ha : a.Is) (G : GA D W → ℂ) (Φ : WO V W → ℂ) (hG : RapidDec W G)
    (hΦ : IsThetaFunO ψ V W Φ) (𝓑 : Set (GA D W))
    (h𝓑 : IsFundamentalDomain (GQ W ⊓ Rgrp W (rat a.x₀) : Subgroup (GA D W)) 𝓑 a.vW.μ) (y : Y) :
    IntegrableOn (fun h => G h * fl ψ a.d W a.vS a.vb a.vU (a.Th y) (rat a.x₀) (a.om (a.d.emb0 (a.g y), h) Φ)) 𝓑
      a.vW.μ ∧
    ∫ n in a.vN.𝓝, a.Th y n.1 * liftS a.om a.vW.μ a.vW.𝓕 G Φ (n.1 * a.d.emb0 (a.g y)) ∂a.vN.ν =
      ∫ h in 𝓑, G h * fl ψ a.d W a.vS a.vb a.vU (a.Th y) (rat a.x₀) (a.om (a.d.emb0 (a.g y), h) Φ) ∂a.vW.μ := by
  have hD : Descent D := GlobalTheory.Unf.descent_of_weilDatumExists D (GlobalTheory.WeilDatumExistence.weilDatumExists D)
  obtain ⟨om', hom'⟩ := (hD ψ V W a.χV a.χW a.om ha.weil).1 V₀ ρ a.d
  have hΦ' := ha.weil.om_pres (a.d.emb0 (a.g y), 1) Φ hΦ
  obtain ⟨h1, h2⟩ := GlobalTheory.Unf.unfold_over_N_lift D hD ψ V V₀ W ρ a.d a.χV a.χW a.om om' ha.weil hom' a.vS a.vN a.vb
    a.vU a.vW a.x₀ (a.Th y) ha.base (ha.th y) G (a.om (a.d.emb0 (a.g y), 1) Φ) hG hΦ' 𝓑 h𝓑
  have hsplit : ∀ h, a.om (1, h) (a.om (a.d.emb0 (a.g y), 1) Φ) = a.om (a.d.emb0 (a.g y), h) Φ := by
    intro h
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  have hlift : ∀ n, liftS a.om a.vW.μ a.vW.𝓕 G (a.om (a.d.emb0 (a.g y), 1) Φ) n =
      liftS a.om a.vW.μ a.vW.𝓕 G Φ (n * a.d.emb0 (a.g y)) := by
    intro n
    have ht := (GlobalTheory.Unf.LiftRapid.lift_conv_cont_growth D ψ V W a.χV a.χW a.om ha.weil a.vW G Φ hG hΦ).2.2.2.2
      (a.d.emb0 (a.g y)) 1
    have hr : rTrans (1 : GA D W) G = G := by funext x; simp [rTrans]
    rw [hr] at ht
    rw [ht]; rfl
  simp only [hsplit, hlift] at h1 h2
  exact ⟨h1, h2⟩

end GlobalTheory.Asc.Gen

namespace GlobalTheory.Asc.Gen

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W : HSp D} {ρ : ℕ} {Y : Type} [TopologicalSpace Y]
  [MeasurableSpace Y]

set_option maxHeartbeats 1000000 in

theorem tot_integrable [SecondCountableTopology Y] [BorelSpace Y] (a : Gen ψ V V₀ W ρ Y) (ha : a.Is)
    (G : GA D W → ℂ) (Φ : WO V W → ℂ) (hG : RapidDec W G) (hΦ : IsThetaFunO ψ V W Φ) (𝓑 : Set (GA D W))
    (h𝓑 : IsFundamentalDomain (GQ W ⊓ Rgrp W (rat a.x₀) : Subgroup (GA D W)) 𝓑 a.vW.μ) :
    Integrable (a.tot G Φ) (a.totMeas 𝓑) := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨-, -, i3, -⟩ := lattice_Mx D ρ V₀.rank
  haveI : BorelSpace (Mx D ρ V₀.rank) := ⟨rfl⟩
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  haveI := a.vW.haar
  haveI : SFinite a.vW.μ := inferInstance
  haveI := ha.sfin
  obtain ⟨sb, sU⟩ := GlobalTheory.Unf.sFinite_vol D ρ V₀.rank a.vb a.vU
  obtain ⟨C, A, hCA⟩ := GlobalTheory.T.wittUnfoldedIntegral_le_coreQuotientHeight D ψ V V₀ W ρ a.d a.χV a.χW a.om ha.weil a.vS a.vb a.vU a.vW a.x₀ ha.base G Φ
    hG hΦ 𝓑 h𝓑
  obtain ⟨M, -, hMb, hMi⟩ := ha.small
  have hM0 : ∀ y, 0 ≤ M y := fun y => (norm_nonneg _).trans (hMb y 1 (one_mem _))
  set Bd : GA D V₀ → GA D W → ENNReal := fun g h => ∫⁻ u, ∫⁻ b in a.vb.𝓕,
    ‖a.d.mixS W ψ a.vS.μ a.vS.𝓕 (a.om (a.d.emb0 g, h) Φ) ((rat a.x₀ : Mx D W.rank ρ) ⬝ u.1.1)
      ((rat a.x₀ : Mx D W.rank ρ) ⬝ b)‖ₑ ∂a.vb.μ ∂a.vU.ν with hBd
  set F : GA D W × Y → ENNReal := fun q => ENNReal.ofReal (M q.2) * (‖G q.1‖ₑ * Bd (a.g q.2) q.1) with hF
  haveI : SecondCountableTopology (GA D W × Y) := inferInstance
  haveI : OpensMeasurableSpace (GA D W × Y) := Prod.opensMeasurableSpace
  haveI : SecondCountableTopologyEither (UX D ρ) (Mx D ρ V₀.rank) := secondCountableTopologyEither_of_right _ _
  haveI : OpensMeasurableSpace (UX D ρ × Mx D ρ V₀.rank) := Prod.opensMeasurableSpace
  haveI : SecondCountableTopologyEither (GA D W × Y) (UX D ρ × Mx D ρ V₀.rank) :=
    secondCountableTopologyEither_of_left _ _
  haveI : OpensMeasurableSpace ((GA D W × Y) × UX D ρ × Mx D ρ V₀.rank) := Prod.opensMeasurableSpace
  have hmeas : Measurable (a.tot G Φ) := (tot_continuous a ha G Φ hG hΦ).measurable
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  show ∫⁻ p, ‖a.tot G Φ p‖ₑ ∂(((a.vW.μ.restrict 𝓑).prod a.m).prod (a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕))) < ⊤
  have hpt : ∀ q : GA D W × Y, ∫⁻ r, ‖a.tot G Φ (q, r)‖ₑ ∂(a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕)) ≤ F q := by
    intro q
    have hc : ENNReal.ofReal (M q.2) * ‖G q.1‖ₑ ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top enorm_ne_top
    calc ∫⁻ r, ‖a.tot G Φ (q, r)‖ₑ ∂(a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕))
        ≤ ∫⁻ u, ∫⁻ b, ‖a.tot G Φ (q, (u, b))‖ₑ ∂(a.vb.μ.restrict a.vb.𝓕) ∂a.vU.ν := lintegral_prod_le _
      _ ≤ ∫⁻ u, ∫⁻ b, ENNReal.ofReal (M q.2) * ‖G q.1‖ₑ *
            ‖a.d.mixS W ψ a.vS.μ a.vS.𝓕 (a.om (a.d.emb0 (a.g q.2), q.1) Φ) ((rat a.x₀ : Mx D W.rank ρ) ⬝ u.1.1)
              ((rat a.x₀ : Mx D W.rank ρ) ⬝ b)‖ₑ ∂(a.vb.μ.restrict a.vb.𝓕) ∂a.vU.ν := by
          refine lintegral_mono fun u => lintegral_mono fun b => ?_
          have hmem : a.d.nB b * a.d.levi u.1 ∈ flagN a.d := mul_mem (a.d.nB_mem_NFlag b) (a.d.levi_mem_NFlag u.2)
          have hth : ‖a.Th q.2 (a.d.nB b * a.d.levi u.1)‖ₑ ≤ ENNReal.ofReal (M q.2) := by
            rw [← ofReal_norm_eq_enorm]; exact ENNReal.ofReal_le_ofReal (hMb _ _ hmem)
          show ‖G q.1 * (a.Th q.2 (a.d.nB b * a.d.levi u.1) * a.d.mixS W ψ a.vS.μ a.vS.𝓕
            (a.om (a.d.emb0 (a.g q.2), q.1) Φ) ((rat a.x₀ : Mx D W.rank ρ) ⬝ u.1.1)
              ((rat a.x₀ : Mx D W.rank ρ) ⬝ b))‖ₑ ≤ _
          rw [enorm_mul, enorm_mul, ← mul_assoc, mul_comm (‖G q.1‖ₑ), mul_assoc, mul_assoc]
          gcongr
      _ = ENNReal.ofReal (M q.2) * ‖G q.1‖ₑ * Bd (a.g q.2) q.1 := by
          simp only [hBd]
          rw [← lintegral_const_mul' _ _ hc]
          refine lintegral_congr fun u => ?_
          rw [← lintegral_const_mul' _ _ hc]
      _ = F q := by simp only [hF, mul_assoc]
  calc ∫⁻ p, ‖a.tot G Φ p‖ₑ ∂(((a.vW.μ.restrict 𝓑).prod a.m).prod (a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕)))
      ≤ ∫⁻ q, ∫⁻ r, ‖a.tot G Φ (q, r)‖ₑ ∂(a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕)) ∂((a.vW.μ.restrict 𝓑).prod a.m) :=
        lintegral_prod_le _
    _ ≤ ∫⁻ q, F q ∂((a.vW.μ.restrict 𝓑).prod a.m) := lintegral_mono hpt
    _ = ∫⁻ z, F z.swap ∂(a.m.prod (a.vW.μ.restrict 𝓑)) := (lintegral_prod_swap F).symm
    _ ≤ ∫⁻ y, ∫⁻ h, F (h, y) ∂(a.vW.μ.restrict 𝓑) ∂a.m := lintegral_prod_le _
    _ = ∫⁻ y, ENNReal.ofReal (M y) * ∫⁻ h in 𝓑, ‖G h‖ₑ * Bd (a.g y) h ∂a.vW.μ ∂a.m := by
        simp only [hF, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∫⁻ y, ENNReal.ofReal (M y) * ENNReal.ofReal (C * quotHeight V₀ (a.g y) ^ A) ∂a.m := by
        refine lintegral_mono fun y => ?_
        gcongr
        exact hCA (a.g y)
    _ = ∫⁻ y, ENNReal.ofReal (C * (M y * quotHeight V₀ (a.g y) ^ A)) ∂a.m := by
        refine lintegral_congr fun y => ?_
        rw [← ENNReal.ofReal_mul (hM0 y)]
        ring_nf
    _ < ⊤ := ((hMi A).const_mul C).lintegral_lt_top

theorem fubini_tot (a : Gen ψ V V₀ W ρ Y) (ha : a.Is) (G : GA D W → ℂ) (Φ : WO V W → ℂ) (B₀ : Set (GA D W))
    (hI : Integrable (a.tot G Φ) (a.totMeas B₀)) :
    IntegrableOn (a.ker G Φ) B₀ a.vW.μ ∧ ∫ p, a.tot G Φ p ∂(a.totMeas B₀) = ∫ h in B₀, a.ker G Φ h ∂a.vW.μ ∧
    ∫ p, a.tot G Φ p ∂(a.totMeas B₀) = ∫ y, ∫ h in B₀,
      G h * fl ψ a.d W a.vS a.vb a.vU (a.Th y) (rat a.x₀) (a.om (a.d.emb0 (a.g y), h) Φ) ∂a.vW.μ ∂a.m := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  haveI := a.vW.haar
  haveI : SFinite a.vW.μ := inferInstance
  haveI := ha.sfin
  obtain ⟨sb, sU⟩ := GlobalTheory.Unf.sFinite_vol D ρ V₀.rank a.vb a.vU
  have hI' : Integrable (a.tot G Φ) (((a.vW.μ.restrict B₀).prod a.m).prod (a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕))) :=
    hI
  set K : GA D W × Y → ℂ := fun q =>
    G q.1 * fl ψ a.d W a.vS a.vb a.vU (a.Th q.2) (rat a.x₀) (a.om (a.d.emb0 (a.g q.2), q.1) Φ) with hK
  have hae : (fun q => ∫ r, a.tot G Φ (q, r) ∂(a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕))) =ᵐ[(a.vW.μ.restrict B₀).prod a.m]
      K := by
    filter_upwards [hI'.prod_right_ae] with q hq
    rw [integral_prod _ hq]
    simp only [Gen.tot, integral_const_mul, hK, fl]
  have hKi : Integrable K ((a.vW.μ.restrict B₀).prod a.m) := hI'.integral_prod_left.congr hae
  have hker : ∀ h, ∫ y, K (h, y) ∂a.m = a.ker G Φ h := by
    intro h
    simp only [hK, Gen.ker, integral_const_mul]
  have htot : ∫ p, a.tot G Φ p ∂(a.totMeas B₀) = ∫ q, K q ∂((a.vW.μ.restrict B₀).prod a.m) := by
    show ∫ p, a.tot G Φ p ∂(((a.vW.μ.restrict B₀).prod a.m).prod (a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕))) = _
    rw [integral_prod _ hI']
    exact integral_congr_ae hae
  refine ⟨?_, ?_, ?_⟩
  · have := hKi.integral_prod_left
    simp only [hker] at this
    exact this
  · rw [htot, integral_prod _ hKi]
    simp only [hker]
  · rw [htot, integral_prod_symm _ hKi]

end GlobalTheory.Asc.Gen

namespace GlobalTheory.Asc

set_option maxHeartbeats 1000000 in

theorem unfold_family : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (Y : Type) [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (a : Gen ψ V V₀ W ρ Y), a.Is → ∀ (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∀ 𝓑 : Set (GA D W), IsFundamentalDomain (GQ W ⊓ Rgrp W (rat a.x₀) : Subgroup (GA D W)) 𝓑 a.vW.μ → Integrable (a.tot G Φ) (a.totMeas 𝓑) ∧ IntegrableOn (a.ker G Φ) 𝓑 a.vW.μ ∧ a.lhs G Φ = ∫ p, a.tot G Φ p ∂(a.totMeas 𝓑) ∧ ∀ S : Set (GA D W), MeasurableSet S → ∫ h in 𝓑 ∩ S, a.ker G Φ h ∂a.vW.μ = ∫ p in {p | p.1.1 ∈ S}, a.tot G Φ p ∂(a.totMeas 𝓑) := by
  intro D ψ V V₀ W ρ Y _ _ _ _ a ha G Φ hG hΦ 𝓑 h𝓑
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  haveI := a.vW.haar
  haveI : SFinite a.vW.μ := inferInstance
  haveI := ha.sfin
  obtain ⟨sb, sU⟩ := GlobalTheory.Unf.sFinite_vol D ρ V₀.rank a.vb a.vU
  have hI := Gen.tot_integrable a ha G Φ hG hΦ 𝓑 h𝓑
  obtain ⟨hker, -, hE⟩ := Gen.fubini_tot a ha G Φ 𝓑 hI
  refine ⟨hI, hker, ?_, ?_⟩
  · rw [hE, Gen.lhs]
    exact integral_congr_ae (ae_of_all _ fun y => (Gen.inner_unfold a ha G Φ hG hΦ 𝓑 h𝓑 y).2)
  · intro S hS
    have hset : {p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank | p.1.1 ∈ S} =
        (S ×ˢ (Set.univ : Set Y)) ×ˢ (Set.univ : Set (UX D ρ × Mx D ρ V₀.rank)) := by
      ext p; simp
    have hres : (a.totMeas 𝓑).restrict {p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank | p.1.1 ∈ S} =
        a.totMeas (𝓑 ∩ S) := by
      simp only [Gen.totMeas]
      rw [hset, ← Measure.prod_restrict, ← Measure.prod_restrict, Measure.restrict_univ, Measure.restrict_univ,
        Measure.restrict_restrict hS, Set.inter_comm]
    have hI' : Integrable (a.tot G Φ) (a.totMeas (𝓑 ∩ S)) := by
      rw [← hres]; exact hI.restrict
    rw [hres]
    exact ((Gen.fubini_tot a ha G Φ (𝓑 ∩ S) hI').2.1).symm

end GlobalTheory.Asc

example : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (Y : Type) [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (a : Gen ψ V V₀ W ρ Y), a.Is → ∀ (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∀ 𝓑 : Set (GA D W), IsFundamentalDomain (GQ W ⊓ Rgrp W (rat a.x₀) : Subgroup (GA D W)) 𝓑 a.vW.μ → Integrable (a.tot G Φ) (a.totMeas 𝓑) ∧ IntegrableOn (a.ker G Φ) 𝓑 a.vW.μ ∧ a.lhs G Φ = ∫ p, a.tot G Φ p ∂(a.totMeas 𝓑) ∧ ∀ S : Set (GA D W), MeasurableSet S → ∫ h in 𝓑 ∩ S, a.ker G Φ h ∂a.vW.μ = ∫ p in {p | p.1.1 ∈ S}, a.tot G Φ p ∂(a.totMeas 𝓑) :=
  GlobalTheory.Asc.unfold_family
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaPairCompactActionStatement
section
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_pair_compact_action : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ X B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (k, 1)) f f₁ →
      f₁ - f ∈ Submodule.span ℂ {g₁ | g₁ ∈ M.Pol B.ψ B.emb ∧ ∃ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, ∃ g ∈ M.Pol B.ψ B.emb,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) g g₁} := by
  first | exact @GlobalTheory.KExpLine.sub_mem_span_derivs | exact GlobalTheory.KExpLine.sub_mem_span_derivs | (intros; apply GlobalTheory.KExpLine.sub_mem_span_derivs <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistCharacterMemTwistFiniteValueProductSubgroupStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistCharacter_mem_twistFiniteValueProductSubgroup : Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (x : (AE D)ˣ), Circle.toUnits (R.toLevCh.xi t x) ∈ xiVals R.toLevCh t := by
  first | exact @GlobalTheory.XiVals.xi_mem | exact GlobalTheory.XiVals.xi_mem | (intros; apply GlobalTheory.XiVals.xi_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSplitPlaceIndicatorDualStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_split_place_indicator_dual : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.V'.J) (dbl (incM F G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (cA σ) (dbl (incM F G.W.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (dbl (incM F G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ p ∈ GlobalTheory.InertDbl.ParD σ G.W v, omd p (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  first | exact @GlobalTheory.SplitDblPar.parD_fix_split | exact GlobalTheory.SplitDblPar.parD_fix_split | (intros; apply GlobalTheory.SplitDblPar.parD_fix_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSplitPlaceIndicatorLiftedStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_split_place_indicator_lifted : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ (d' : Darboux (symp (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J)) (Fin a' × Fin (a + a'))),
      (∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (cA σ) (dbl (incM F G.V'.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) d' dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.W.J) (dbl (incM F G.V'.J)) dd (X.α / X.β) (diagCols (Fin a')) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ n ∈ GlobalTheory.InertDbl.NabD σ G.V' v, omd n (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  first | exact @GlobalTheory.NabFixSplitV.nab_fix_splitV | exact GlobalTheory.NabFixSplitV.nab_fix_splitV | (intros; apply GlobalTheory.NabFixSplitV.nab_fix_splitV <;> assumption)
end

