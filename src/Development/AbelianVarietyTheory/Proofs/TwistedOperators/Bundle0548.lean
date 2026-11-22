import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1839
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0947
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0517
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0503
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0293
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1522
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0500
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0025
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0194
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0310
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0518
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0174
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0178
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0523

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThGEquiv
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaGoodEquiv

theorem thG_equiv : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsThP → R.grp_record → A.v0 = InfinitePlace.mk D.what₂.embLL → ∀ (i : Fin D.R.m) (t : T) (g0 : G0 R.Pg D.R.r) (κ : GA D (Vc D i)) (κ' : GA D (Wc D i)), IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ → IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ' → ∀ S : (R.HV i t).H →ₗ[ℂ] (R.HV i t).H, (∀ y h, R.extV i t (S y) h = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.extV i t y (h * κ)) → ∀ y, R.thG i t (S y) = R.gW i (sg0 D A) (R.eG.symm g0) (R.thG i t y) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL hM hP hgr _ i t g0 κ κ' hκ hκ' S hS y
  have hinj := (hM.HW i (sg0 D A)).1
  apply hinj
  have hX := hP.thF_mem i t y
  have hsh := GlobalTheory.ThetaShiftSmooth.thF_shift_all R hL hM hP i t g0 κ κ' hκ hκ' y (S y) (hS y)
  have hcomm := (GlobalTheory.ProjComm.proj_comm R hL hgr).2
  have e1 := hP.thG i t (S y)
  have e2 := hM.gW i (sg0 D A) (R.eG.symm g0) (R.thG i t y)
  have e3 := hP.thG i t y
  have hκ'' : IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG (R.eG.symm g0)) κ' := by
    rw [MulEquiv.apply_symm_apply]; exact hκ'
  have hT : ∀ v, HasType (Wc D i) (R.βW i) (R.datWp i R.triv) (R.thF i t y v) := fun v k hk h =>
    (GlobalTheory.mult_value_left_cont_level R.θ (R.MW i (sg0 D A)) _ _ (R.thF i t y) hX v).2.2 k hk h
  have h2 := GlobalTheory.ThetaShiftSmooth.levChi_flag_eq_one R i κ'
  have hUe : ∀ v, R.thF i t (S y) v =
      actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG (R.eG.symm g0)) (R.thF i t y v) := fun v => by
    funext z
    have h1 := level_action_spec (V := Wc D i) (β := R.βW i) (L := R.datWp i R.triv) (hT v) ⟨κ', hκ''⟩ κ' hκ'' z
    have h3 := congrArg (fun c : ℂ => c⁻¹ * R.thF i t y v (z * κ')) h2
    have h4 : (1 : ℂ)⁻¹ * R.thF i t y v (z * κ') = R.thF i t y v (z * κ') := by simp
    exact (hsh v z).trans (h1.trans (h3.trans h4)).symm
  have key : postOn _ (R.eWf i (sg0 D A)) (R.thF i t (S y)) =
      postOn _ (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG (R.eG.symm g0)))
        (postOn _ (R.eWf i (sg0 D A)) (R.thF i t y)) := by
    refine MultilinearMap.ext fun v => ?_
    exact (congrArg (R.eWf i (sg0 D A)) (hUe v)).trans (hcomm i (sg0 D A) (R.eG.symm g0) (R.thF i t y v) (hT v))
  exact e1.trans (key.trans ((congrArg _ e3).symm.trans e2.symm))

end GlobalTheory.ThetaGoodEquiv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainLiftsAreCuspForms
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftCuspObj

variable {D : D7}

theorem multT_induction {W : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel W S)
    (J : Set (GA D W)) (χ : GA D W → ℂ) (P : (GA D W → ℂ) → Prop) (h0 : P 0)
    (hadd : ∀ φ φ', P φ → P φ' → P (φ + φ')) (hsmul : ∀ (c : ℂ) φ, P φ → P (c • φ))
    (hcusp : ∀ φ, IsAutFunSm θ W φ → IsCuspFun W φ → P φ)
    (F : SmT M →ₗ[ℂ] (GA D W → ℂ)) (hF : F ∈ MultT θ M J χ) (v : SmT M) : P (F v) := by
  obtain ⟨T, hT, rfl⟩ := Submodule.mem_map.1 hF
  have key : ∀ m, P (T m) := by
    intro m
    have hT' : T ∈ Submodule.span ℂ {T | IsMultMap θ M J χ T} := hT
    clear hF hT
    induction hT' using Submodule.span_induction with
    | mem x hx => exact hcusp _ ((show IsMultMap θ M J χ x from hx).aut m) ((show IsMultMap θ M J χ x from hx).cusp m)
    | zero => simpa using h0
    | add x y _ _ hx hy => simpa using hadd _ _ hx hy
    | smul a x _ hx => simpa using hsmul a _ hx
  induction v using PiTensorProduct.induction_on with
  | smul_tprod a m => simpa using hsmul a _ (key m)
  | add x y hx hy => simpa using hadd _ _ hx hy

theorem liftInt_add {G H S : Type*} [MeasurableSpace H] {ν : Measure H} {𝓕 : Set H} {th : G → H → S → ℂ} {s : S}
    {φ φ' : H → ℂ} {g : G} (h : IntegrableOn (fun x => th g x s * φ x) 𝓕 ν)
    (h' : IntegrableOn (fun x => th g x s * φ' x) 𝓕 ν) :
    Lift.liftInt ν 𝓕 th s (φ + φ') g = Lift.liftInt ν 𝓕 th s φ g + Lift.liftInt ν 𝓕 th s φ' g := by
  simp only [Lift.liftInt, Pi.add_apply, mul_add]
  exact integral_add h h'

theorem liftInt_smul {G H S : Type*} [MeasurableSpace H] {ν : Measure H} {𝓕 : Set H} {th : G → H → S → ℂ} {s : S}
    (c : ℂ) (φ : H → ℂ) (g : G) :
    Lift.liftInt ν 𝓕 th s (c • φ) g = c * Lift.liftInt ν 𝓕 th s φ g := by
  simp only [Lift.liftInt, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  ext x
  ring

theorem liftInt_zero {G H S : Type*} [MeasurableSpace H] {ν : Measure H} {𝓕 : Set H} {th : G → H → S → ℂ} {s : S}
    (g : G) : Lift.liftInt ν 𝓕 th s (0 : H → ℂ) g = 0 := by
  simp [Lift.liftInt]

structure Good {V V' W : HSp D} {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ))
    (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (κ : Measure (NI V C)) (𝓝 : Set (NI V C))
    (f : WO V W → ℂ) (f' : WO V' W → ℂ) (g : GA D V) (c : ℂ) (φ : GA D W → ℂ) : Prop where
  integ : ∀ g₁, IntegrableOn (fun h => thetaKO ω g₁ h f * φ h) 𝓕 ν
  integ' : IntegrableOn (fun h => thetaKO ω' 1 h f' * φ h) 𝓕 ν
  mean : IntegrableOn (fun n : NI V C => Lift.liftInt ν 𝓕 (thetaKO ω) f φ ((n : GA D V) * g)) 𝓝 κ
  eq : ∫ n in 𝓝, Lift.liftInt ν 𝓕 (thetaKO ω) f φ ((n : GA D V) * g) ∂κ =
    c * Lift.liftInt ν 𝓕 (thetaKO ω') f' φ 1

section Good

variable {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)}
  {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} {κ : Measure (NI V C)} {𝓝 : Set (NI V C)}
  {f : WO V W → ℂ} {f' : WO V' W → ℂ} {g : GA D V} {c : ℂ}

theorem Good.zero : Good C ω ω' ν 𝓕 κ 𝓝 f f' g c 0 where
  integ g₁ := by simp
  integ' := by simp
  mean := by
    simp only [liftInt_zero]
    exact integrableOn_zero
  eq := by simp [liftInt_zero]

theorem Good.add {φ φ' : GA D W → ℂ} (h : Good C ω ω' ν 𝓕 κ 𝓝 f f' g c φ)
    (h' : Good C ω ω' ν 𝓕 κ 𝓝 f f' g c φ') : Good C ω ω' ν 𝓕 κ 𝓝 f f' g c (φ + φ') := by
  have e : ∀ x : GA D V, Lift.liftInt ν 𝓕 (thetaKO ω) f (φ + φ') x =
      Lift.liftInt ν 𝓕 (thetaKO ω) f φ x + Lift.liftInt ν 𝓕 (thetaKO ω) f φ' x :=
    fun x => liftInt_add (h.integ x) (h'.integ x)
  refine ⟨fun g₁ => ?_, ?_, ?_, ?_⟩
  · simp only [Pi.add_apply, mul_add]
    exact Integrable.add (h.integ g₁) (h'.integ g₁)
  · simp only [Pi.add_apply, mul_add]
    exact Integrable.add h.integ' h'.integ'
  · simp only [e]
    exact Integrable.add h.mean h'.mean
  · simp only [e]
    rw [integral_add h.mean h'.mean, h.eq, h'.eq, liftInt_add h.integ' h'.integ', mul_add]

theorem Good.smul {φ : GA D W → ℂ} (a : ℂ) (h : Good C ω ω' ν 𝓕 κ 𝓝 f f' g c φ) :
    Good C ω ω' ν 𝓕 κ 𝓝 f f' g c (a • φ) := by
  refine ⟨fun g₁ => ?_, ?_, ?_, ?_⟩
  · have e : (fun x => thetaKO ω g₁ x f * (a • φ) x) = fun x => a * (thetaKO ω g₁ x f * φ x) := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact Integrable.const_mul (h.integ g₁) a
  · have e : (fun x => thetaKO ω' 1 x f' * (a • φ) x) = fun x => a * (thetaKO ω' 1 x f' * φ x) := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact Integrable.const_mul h.integ' a
  · simp only [liftInt_smul]
    exact Integrable.const_mul h.mean a
  · simp only [liftInt_smul]
    rw [integral_const_mul, h.eq]
    ring

end Good

theorem constTerm_multT (hct : TowerConstTerm D) (hP : GlobalTheory.Published.CuspRapidDecay)
    {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B)
    {θ : InfFam D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} {χS χT χT' : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)}
    (hω : IsWeilDatumO ψ V W χS χT ω) (hω' : IsWeilDatumO ψ V' W χS χT' ω')
    {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ W) 𝓕 ν)
    {S : D.what₂.Tau → SPar} (M : DSModel W S) (J : Set (GA D W)) (χ : GA D W → ℂ)
    (F : SmT M →ₗ[ℂ] (GA D W → ℂ)) (hF : F ∈ MultT θ M J χ) (v : SmT M)
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
    (hlow : ∀ f', IsThetaFunO ψ V' W f' → Lift.liftInt ν 𝓕 (thetaKO ω') f' (F v) 1 = 0)
    (κ : Measure (NI V C)) (𝓝 : Set (NI V C)) (hκ : κ.IsHaarMeasure) (h𝓝 : IsFundamentalDomain (NIQ V C) 𝓝 κ)
    (g : GA D V) : ∫ n in 𝓝, Lift.liftInt ν 𝓕 (thetaKO ω) f (F v) ((n : GA D V) * g) ∂κ = 0 := by
  obtain ⟨μ, 𝓨, h𝓨⟩ : ∃ μ 𝓨, IsCovolOne (ratMx D W.rank r) μ 𝓨 := GlobalTheory.MixModel.exists_isCovolOne D W.rank r
  have hfor := hct V V' W r C B hs ψ χS χT χT' ω ω' hω hω' μ 𝓨 h𝓨 ν 𝓕 hν h𝓕 κ 𝓝 hκ h𝓝
  have hgood : Good C ω ω' ν 𝓕 κ 𝓝 f (res V V' W C B μ 𝓨 (ω (g, 1) f)) g ((κ 𝓝).toReal : ℂ) (F v) :=
    multT_induction θ M J χ
      (fun φ => Good C ω ω' ν 𝓕 κ 𝓝 f (res V V' W C B μ 𝓨 (ω (g, 1) f)) g ((κ 𝓝).toReal : ℂ) φ)
      Good.zero (fun _ _ h h' => Good.add h h') (fun a _ h => Good.smul a h)
      (fun φ hφ hc => by
        obtain ⟨-, -, -, h1, h2, h3, h4⟩ := hfor φ (GlobalTheory.Grow.rapidDec_of_cuspForm hP hθ hφ hc) hc f hf g
        exact ⟨h1, h2, h3, h4⟩) F hF v
  obtain ⟨-, -, hres, -⟩ := hfor 0 GlobalTheory.Grow.RapidDec.zero (by intro _ _ _ _ _ _ _ _; simp) f hf g
  rw [hgood.eq, hlow _ hres, mul_zero]

theorem liftCusp : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    ∀ D : D7, GlobalTheory.Chain.LiftCusp D := by
  intro hDS hHC hP D k V W M M' θ ψ hθ hch ω hω ν 𝓕 hν h𝓕 J χ F hF v f hf r C hC κ 𝓝 hκ h𝓝 g
  obtain ⟨V', B, hs, hsig⟩ := GlobalTheory.T.exists_lowerWittTower_isotropicSplitEmbedding D V _ M r C hC
  have hr : 1 ≤ r := by
    obtain ⟨h0, -⟩ := hC
    exact h0
  obtain ⟨χS, χT, hW, hexp⟩ := hω
  obtain ⟨η, h1, h2, h3, h4⟩ := GlobalTheory.Mem.EtaTilde.exists_etaTilde D
  obtain ⟨ω', hW'⟩ := GlobalTheory.T.exists_weilDatum_of_splittingCharacters D ψ hW.std V' W χS χT (Exists.intro η (And.intro h1 (And.intro h4 (And.intro h3 h2))))
    hW.hecS hW.hecT (resEta_parity hW.resS (by have := hs.rank; omega)) hW.resT
  have hst : GlobalTheory.Chain.IsStepWeil k ψ V' W ω' := Exists.intro χS (Exists.intro χT (And.intro hW' hexp))
  exact constTerm_multT (GlobalTheory.T.constantTermLift_isotropicSubspace D) hP hs hθ hW hW' hν h𝓕 M' J χ F hF v hf
    (fun f' hf' => congrFun (GlobalTheory.T.thetaLift_lowerTower_vanishing hDS hHC hP D k r V' W M' θ ψ hθ hch hr hsig ω' hst ν 𝓕 hν h𝓕 J χ F hF v f'
      hf') 1) κ 𝓝 hκ h𝓝 g

end GlobalTheory.LiftCuspObj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftBoundedNorm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DownLiftGrowth

theorem growthSize_lift_le_decayInt : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∃ N : ℕ, ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∃ C : NNReal, ∀ f : GA D (G.P (i + 1)).V → ℂ, GlobalTheory.Size.growthSize (G.P i).V N (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * f g ∂(G.mP (i + 1)).ν) ≤ (C : ENNReal) * GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt (G.mP (i + 1)).ν (G.mP (i + 1)).fd N f := by
  intro _ D _ G₀ _ _ Pl0 T Af Ks _ _ _ R G hB hG i hi
  obtain ⟨N, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D (GlobalTheory.Grid.sgn true (G.P (i + 1)).V).rank (G.P i).V.rank
  refine ⟨N, fun Φ hΦ => ?_⟩
  have hω := (hG.arrows.dn i hi).weil
  obtain ⟨U, hU, hl⟩ := GlobalTheory.Size.isTheta_iff_level.1 hΦ
  obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.Size.exists_isCovolOne (GlobalTheory.Grid.sgn true (G.P (i + 1)).V) (G.P i).V
  obtain ⟨C, hC0, hC⟩ := (H _ _ rfl rfl).real R.ψ hB.inf hU
  have hb := (hC _ _ _ hω μ 𝓕 hμ Φ hl).2
  set K := C * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d Φ).toReal with hK
  have hK0 : 0 ≤ K := mul_nonneg hC0 ENNReal.toReal_nonneg
  have e : ∀ g h, thetaKO (G.dn i).ω g h Φ =
      thetaKO ((G.dn i).ω.toSgn true) ((GlobalTheory.Grid.ofSgn true _).symm g) h Φ := fun g h => by
    show (G.dn i).ω (g, h) Φ 0 = (G.dn i).ω (GlobalTheory.Grid.ofSgn true _ ((GlobalTheory.Grid.ofSgn true _).symm g), h) Φ 0
    rw [MulEquiv.apply_symm_apply]
  have hinv : ∀ h, ∀ γ ∈ GQ (G.P (i + 1)).V, ∀ g,
      thetaKO (G.dn i).ω (γ * g) h Φ = thetaKO (G.dn i).ω g h Φ := fun h γ hγ g => by
    rw [e, e, map_mul]
    refine GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_left_fst hω hΦ h _ ?_ _
    rw [GlobalTheory.SgnIdent.mem_GQ_sgn, MulEquiv.apply_symm_apply]
    exact hγ
  have hk : ∀ g h, ‖thetaKO (G.dn i).ω g h Φ‖ ≤
      K * 2 ^ N * GlobalTheory.Grow.height (G.P i).V h ^ N * GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ N := by
    intro g h
    have h1 : ∀ g, ‖thetaKO (G.dn i).ω g h Φ‖ ≤
        (K * GlobalTheory.Grow.height (G.P i).V h ^ N) * GlobalTheory.Grow.height (G.P (i + 1)).V g ^ N := fun g => by
      rw [e]
      have h2 := hb ((GlobalTheory.Grid.ofSgn true _).symm g) h
      have hh : GlobalTheory.Grow.height (GlobalTheory.Grid.sgn true (G.P (i + 1)).V) ((GlobalTheory.Grid.ofSgn true _).symm g) =
          GlobalTheory.Grow.height (G.P (i + 1)).V g := rfl
      rw [hh] at h2
      exact h2.trans_eq (by rw [hK, mul_pow]; ring)
    exact (GlobalTheory.Grow.norm_le_quotHeight_pow (hinv h) h1 g).trans_eq (by ring)
  refine ⟨(K * 2 ^ N).toNNReal, fun f => iSup_le fun h => ?_⟩
  have hg := pow_pos (GlobalTheory.Grow.height_pos (G.P i).V h) N
  rw [ENNReal.ofReal_div_of_pos hg, ofReal_norm_eq_enorm]
  refine ENNReal.div_le_of_le_mul ((enorm_integral_le_lintegral_enorm _).trans ?_)
  rw [mul_right_comm, GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt]
  refine (lintegral_mono fun g => ?_).trans_eq
    (lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top))
  have hq := (pow_pos (GlobalTheory.Grow.quotHeight_pos (G.P (i + 1)).V g) N).le
  rw [← ofReal_norm_eq_enorm]
  change ENNReal.ofReal _ ≤ ENNReal.ofReal (K * 2 ^ N) * _ * _
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [norm_mul]
  calc ‖thetaKO (G.dn i).ω g h Φ‖ * ‖f g‖
      ≤ (K * 2 ^ N * GlobalTheory.Grow.height (G.P i).V h ^ N * GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ N) * ‖f g‖ :=
        mul_le_mul_of_nonneg_right (hk g h) (norm_nonneg _)
    _ = _ := by ring

end GlobalTheory.DownLiftGrowth

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalFunctionBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped ComplexConjugate

namespace GlobalTheory.UpArrowApprox

theorem ptF_eq_fock {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : GlobalTheory.Grid.Node D)
    (f : WO S.V T.V → ℂ) (p : GlobalTheory.Grid.Pol S T) :
    GlobalTheory.ChainFr.ptF ψ θ (GlobalTheory.PairLift.frSgn true (GlobalTheory.ChainFr.Fr.ofModel S.M)) (GlobalTheory.ChainFr.Fr.ofModel T.M) f p =
      GlobalTheory.Grid.fock ψ θ true S T f p := by
  have : (GlobalTheory.PairLift.frSgn true (GlobalTheory.ChainFr.Fr.ofModel S.M)).cart = GlobalTheory.Grid.cartS true S :=
    funext fun τ => GlobalTheory.PairLift.cart_frSgn true _ τ
  unfold GlobalTheory.ChainFr.ptF GlobalTheory.Grid.fock
  rw [this]
  rfl

theorem isFinVec_of_isVacF {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : GlobalTheory.Grid.Node D}
    {f : WO S.V T.V → ℂ}
    (h : GlobalTheory.ChainFr.IsVacF ψ θ (GlobalTheory.PairLift.frSgn true (GlobalTheory.ChainFr.Fr.ofModel S.M)) (GlobalTheory.ChainFr.Fr.ofModel T.M) f) :
    GlobalTheory.Grid.IsFinVec ψ θ true S T f :=
  ⟨h.1, fun τ => by have := h.2 τ; rwa [GlobalTheory.PairLift.cart_frSgn] at this⟩

end GlobalTheory.UpArrowApprox

namespace GlobalTheory.UpArrowApprox

theorem approx : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ F : (G.P i).Maps, F ∈ (G.P i).Cusp R.θ → ∀ v : SmT (G.P i).M, (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F v g) (G.mP i).fd (G.mP i).ν) → ∀ C : Set (GA D (G.P (i + 1)).V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (f : Fin n → (WO (G.P (i + 1)).V (G.P i).V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i)), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l)) ∧ ∀ h ∈ C, ‖(∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F v g ∂(G.mP i).ν) - ∑ l, ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l))) * F v g ∂(G.mP i).ν‖ < ε := by
  intro hLC hP D hSz G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i hi Φ hΦ F hF v hint C hC ε hε
  have hθ : IsInfFam R.θ := hR.inf
  have hω := (hG.arrows.dn i hi).weil
  have hψ : IsStdChar D R.ψ (-1) := IsWeilDatumO.std hω
  have hm := (hG.meas.P i hi.le).2 (by omega)
  have hCA := hLC D hSz G₀ Pl0 T A Ks R G hR hG
  obtain ⟨-, -, hFr⟩ := GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hP.cuspRapidDecay D _ _ _ R.θ hθ _ _ F hF v
  obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.Size.exists_isCovolOne (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V
  obtain ⟨U, hU, hΦU, hdense⟩ := GlobalTheory.FockDensity.fockDense D _ _
    (GlobalTheory.PairLift.frSgn true (GlobalTheory.ChainFr.Fr.ofModel (G.P (i + 1)).M)) (GlobalTheory.ChainFr.Fr.ofModel (G.P i).M) R.θ R.ψ hψ hθ
    μ 𝓕 hμ Φ hΦ
  obtain ⟨a, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D (GlobalTheory.Grid.neg (G.P (i + 1)).V).rank (G.P i).V.rank
  obtain ⟨K, hK0, hK⟩ := (H (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V rfl rfl).real R.ψ hθ hU
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ h ∈ C,
      GlobalTheory.Grow.height (GlobalTheory.Grid.neg (G.P (i + 1)).V) ((GlobalTheory.Grid.ofSgn true (G.P (i + 1)).V).symm h) ≤ M := by
    obtain ⟨M, hM⟩ := hC.bddAbove_image
      ((GlobalTheory.Grow.continuous_height _).comp (GlobalTheory.Grid.continuous_ofSgn_symm true _)).continuousOn
    exact ⟨M, fun h hh => hM ⟨h, hh, rfl⟩⟩
  obtain ⟨B, hB⟩ := hFr.decay a
  have hfin : (G.mP i).ν (G.mP i).fd < ⊤ := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol _ _ _ hm.1.1 hm.2
  set L : ℝ := K * max M 1 ^ a * 2 ^ a * max B 0 * ((G.mP i).ν (G.mP i).fd).toReal with hL
  have hL0 : 0 ≤ L := by
    have : 0 ≤ max M 1 := le_trans zero_le_one (le_max_right _ _)
    have : 0 ≤ max B 0 := le_max_right _ _
    positivity
  have hδ : 0 < ε / (2 * (L + 1)) := div_pos hε (by linarith)
  obtain ⟨g₀, hg₀, hg₀U, hg₀d⟩ := hdense d (ENNReal.ofReal (ε / (2 * (L + 1)))) (ENNReal.ofReal_pos.2 hδ)
  obtain ⟨n, c, w, hw⟩ := Submodule.mem_span_set'.1 hg₀
  choose f₀ P hvac hlev hgeq using fun l => (w l).2
  refine ⟨n, f₀, fun l => c l • P l, fun l => isFinVec_of_isVacF (hvac l), fun h hh => ?_⟩
  have hsum : g₀ = ∑ l, GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f₀ l) (c l • P l) := by
    rw [← hw]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hgeq l, ← ptF_eq_fock]
    simp only [GlobalTheory.ChainFr.ptF, map_smul]
  have he : Φ - g₀ ∈ GlobalTheory.Size.thetaLevel R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V U := sub_mem hΦU hg₀U
  have hint' : ∀ l, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g
      (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f₀ l) (c l • P l))) * F v g) (G.mP i).fd (G.mP i).ν :=
    fun l => ((hCA.up i hi (f₀ l) (isFinVec_of_isVacF (hvac l)) F hF).choose_spec.2 (c l • P l) v h).1
  have hlin : ∀ g, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F v g -
      ∑ l, starRingEnd ℂ (thetaKO (G.dn i).ω h g
        (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f₀ l) (c l • P l))) * F v g =
      starRingEnd ℂ (thetaKO (G.dn i).ω h g (Φ - g₀)) * F v g := by
    intro g
    rw [hsum]
    simp only [thetaKO, map_sub, map_sum, Pi.sub_apply, Finset.sum_apply, sub_mul, Finset.sum_mul]
  rw [← integral_finset_sum _ fun l _ => hint' l, ← integral_sub (hint h) (integrable_finset_sum _ fun l _ => hint' l)]
  have e0 : (∫ g in (G.mP i).fd, (starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F v g -
      ∑ l, starRingEnd ℂ (thetaKO (G.dn i).ω h g
        (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f₀ l) (c l • P l))) * F v g) ∂(G.mP i).ν) =
      ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g (Φ - g₀)) * F v g ∂(G.mP i).ν := by
    congr 1
    funext g
    exact hlin g
  rw [e0]

  set s : ℝ := (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d (Φ - g₀)).toReal with hs
  have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
  set h' := (GlobalTheory.Grid.ofSgn true (G.P (i + 1)).V).symm h with hh'
  have hpt : ∀ g, ‖starRingEnd ℂ (thetaKO (G.dn i).ω h g (Φ - g₀)) * F v g‖ ≤ K * max M 1 ^ a * 2 ^ a * max B 0 * s := by
    intro g
    have e1 : thetaKO (G.dn i).ω h g (Φ - g₀) = thetaKO ((G.dn i).ω.toSgn true) h' g (Φ - g₀) :=
      GlobalTheory.UpArrowConv.thetaKO_toSgn _ _ _ _
    have hbd : ∀ g, ‖thetaKO ((G.dn i).ω.toSgn true) h' g (Φ - g₀)‖ ≤
        (K * s * GlobalTheory.Grow.height (GlobalTheory.Grid.neg (G.P (i + 1)).V) h' ^ a) * GlobalTheory.Grow.height (G.P i).V g ^ a := fun g => by
      have := (hK _ _ _ hω μ 𝓕 hμ _ he).2 h' g
      rw [mul_pow, ← mul_assoc] at this
      exact this
    have hq := GlobalTheory.Grow.norm_le_quotHeight_pow (f := fun g => thetaKO ((G.dn i).ω.toSgn true) h' g (Φ - g₀))
      (GlobalTheory.UpArrowConv.thetaKO_left_snd hω he.1 h') hbd g
    rw [norm_mul, RCLike.norm_conj, e1]
    have hh1 : GlobalTheory.Grow.height (GlobalTheory.Grid.neg (G.P (i + 1)).V) h' ^ a ≤ max M 1 ^ a :=
      pow_le_pow_left₀ (GlobalTheory.Grow.height_pos _ _).le ((hM h hh).trans (le_max_left _ _)) a
    have hFB : ‖F v g‖ * GlobalTheory.Grow.quotHeight (G.P i).V g ^ a ≤ max B 0 := (hB g).trans (le_max_left _ _)
    have a0 : 0 ≤ K * s * GlobalTheory.Grow.height (GlobalTheory.Grid.neg (G.P (i + 1)).V) h' ^ a * 2 ^ a :=
      mul_nonneg (mul_nonneg (mul_nonneg hK0 hs0) (pow_nonneg (GlobalTheory.Grow.height_pos _ _).le _)) (by positivity)
    have a1 : K * s * GlobalTheory.Grow.height (GlobalTheory.Grid.neg (G.P (i + 1)).V) h' ^ a * 2 ^ a ≤ K * s * max M 1 ^ a * 2 ^ a :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh1 (mul_nonneg hK0 hs0)) (by positivity)
    calc ‖thetaKO ((G.dn i).ω.toSgn true) h' g (Φ - g₀)‖ * ‖F v g‖
        ≤ K * s * GlobalTheory.Grow.height (GlobalTheory.Grid.neg (G.P (i + 1)).V) h' ^ a * 2 ^ a *
            GlobalTheory.Grow.quotHeight (G.P i).V g ^ a * ‖F v g‖ := mul_le_mul_of_nonneg_right hq (norm_nonneg _)
      _ = K * s * GlobalTheory.Grow.height (GlobalTheory.Grid.neg (G.P (i + 1)).V) h' ^ a * 2 ^ a *
            (‖F v g‖ * GlobalTheory.Grow.quotHeight (G.P i).V g ^ a) := by ring
      _ ≤ K * s * max M 1 ^ a * 2 ^ a * max B 0 :=
          mul_le_mul a1 hFB (mul_nonneg (norm_nonneg _) (pow_nonneg (GlobalTheory.Grow.quotHeight_pos _ _).le _))
            (a0.trans a1)
      _ = K * max M 1 ^ a * 2 ^ a * max B 0 * s := by ring
  refine (norm_setIntegral_le_of_norm_le_const hfin fun g _ => hpt g).trans_lt ?_
  have hslt : s < ε / (2 * (L + 1)) := ENNReal.toReal_lt_of_lt_ofReal hg₀d
  calc K * max M 1 ^ a * 2 ^ a * max B 0 * s * ((G.mP i).ν (G.mP i).fd).toReal = L * s := by rw [hL]; ring
    _ ≤ (L + 1) * s := by nlinarith
    _ < (L + 1) * (ε / (2 * (L + 1))) := mul_lt_mul_of_pos_left hslt (by linarith)
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

end GlobalTheory.UpArrowApprox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftHorizontalAlgebraicCoeffs
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ThetaArrowGrowth

theorem thetaKO_le_quotHeight_arrow : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∃ a b : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ h g, ‖thetaKO (G.th t i j).ω h g Φ‖ ≤ C * GlobalTheory.Grow.quotHeight (G.V i j).V h ^ a * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b := by
  intro _ _ D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj Φ hΦ
  have hω : IsWeilDatumO R.ψ (G.V i j).V (G.V i (j + 1)).V _ _ (G.th t i j).ω :=
    (GlobalTheory.Grid.isWeil_false _ _ _ _ _ _).1 (hG.arrows.th t i j hi hj).weil
  obtain ⟨K, n, hK, hb⟩ := GlobalTheory.ChainOnto.ThetaSwap.thetaKO_le_quotHeight hRB.inf hω hΦ
  refine ⟨n, n, K, hK, fun h g => ?_⟩
  rw [mul_assoc, ← mul_pow]
  exact hb h g

end GlobalTheory.ThetaArrowGrowth

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftHorizontalFiniteSums
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FinLift

theorem th_finLift : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ (n : ℕ) (fs : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ)) (ps : Fin n → PolF D (G.V i (j + 1)).V.rank (G.V i j).V.rank), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l)) → ∀ (n' : ℕ) (Fs : Fin n' → (G.V i (j + 1)).Maps) (vs : Fin n' → SmT (G.V i (j + 1)).M), (∀ k, Fs k ∈ (G.V i (j + 1)).Cusp R.θ) → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) * (∑ k, Fs k (vs k) g)) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) ∧ IsAutFun (G.V i j).V (fun h => ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) * (∑ k, Fs k (vs k) g) ∂(G.meas t i (j + 1)).ν) ∧ IsCuspFun (G.V i j).V (fun h => ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) * (∑ k, Fs k (vs k) g) ∂(G.meas t i (j + 1)).ν) := by
  intro LC _ D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj n fs ps hfs n' Fs vs hFs
  have hC := LC D hS G₀ Pl0 T A Ks R G hRB hG
  simp only [thetaKO_sum]
  exact lift_finSum (fun l p h g => thetaKO (G.th t i j).ω h g (GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) p))
    (fun p v => (G.th t i j).It p v) (fun l => hC.th t i j hi hj (fs l) (hfs l)) ps Fs vs hFs

end GlobalTheory.FinLift

end
end

