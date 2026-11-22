import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0837
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0825
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0822
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0134
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0832
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0830
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0838

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftSetupOverExtendedDataIntegralFormsEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

local macro:max "kc% " e:term:max : term => `((by kexactB $e))

namespace GlobalTheory.TwInputs.Move.TieUp

variable {D : D7} (r : Rest D)

theorem placeModel_up {mm nn : ℕ} {ψ B hs e Λ c f₀ T} (h : @IsPlaceModel D mm nn ψ B hs e Λ c f₀ T) :
    @IsPlaceModel (overD D r) mm nn ((ψ)) ((B)) ((hs)) ((e)) ((Λ)) c ((f₀)) ((T)) :=
  @IsPlaceModel.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (trans := (by with_unfolding_all exact (h.trans :))) (modul := (by with_unfolding_all exact (h.modul :)))
    (vac := (by with_unfolding_all exact (h.vac :)))

theorem placeModel_dn {mm nn : ℕ} {ψ B hs e Λ c f₀ T} (h : @IsPlaceModel (overD D r) mm nn ψ B hs e Λ c f₀ T) :
    @IsPlaceModel D mm nn ((ψ)) ((B)) ((hs)) ((e)) ((Λ)) c ((f₀)) ((T)) :=
  @IsPlaceModel.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (trans := (by with_unfolding_all exact (h.trans :))) (modul := (by with_unfolding_all exact (h.modul :)))
    (vac := (by with_unfolding_all exact (h.vac :)))

theorem placeMap_up {S T : HSp D} (B : Base S T) (a : AE D) :
    (baseUp r B).F.placeMap ((a)) = (B.F.placeMap a) := by
  have hP : (fun L : (WO (D := overD D r) ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :))) → ℂ) →ₗ[ℂ] (WO (D := overD D r) ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :))) → ℂ) =>
      IsPlaceModel (baseUp r B).F.ψ (symplO ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :))))
        (heisO (baseUp r B).F.ψ ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :)))) ((by with_unfolding_all exact (a :))) (baseUp r B).F.lat 1 (baseUp r B).F.f₀ L) =
      (by with_unfolding_all exact ((fun L : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) =>
        IsPlaceModel B.F.ψ (symplO S T) (heisO B.F.ψ S T) a B.F.lat 1 B.F.f₀ L) :)) :=
    funext fun L => propext ⟨fun h => (by with_unfolding_all exact ((placeModel_dn r h) :)), fun h => (by with_unfolding_all exact ((placeModel_up r h) :))⟩
  unfold Frame.placeMap
  exact (by with_unfolding_all exact ((congrArg Classical.epsilon hP) :))

theorem vec_up {S T : HSp D} (B : Base S T) (Q ω) :
    (baseUp r B).F.vec (baseUp r B).G (kc% Q) (kc% ω) = kc% (B.F.vec B.G Q ω) := by
  have e := placeMap_up r B (halfIdem B.G.Pg Q)
  show (baseUp r B).F.placeMap (kc% (halfIdem B.G.Pg Q)) (kc% (B.F.datumFn B.G Q ω)) = _
  rw [e]
  exact kc% rfl

open Classical in

theorem vecAt_up {S T : HSp D} (B : Base S T) (Q φ) :
    (baseUp r B).vecAt (kc% Q) (kc% φ) = kc% (B.vecAt Q φ) := by
  show (baseUp r B).F.vec (baseUp r B).G (kc% (B.de.Q ∪ Q)) (kc% (B.locFn Q φ)) = _
  exact vec_up r B _ _

theorem series_up {S T : HSp D} (B : Base S T) (ω : PairRep S T) (Q φ h) :
    series (baseUp r B).F (kc% ω) ((baseUp r B).vecAt (kc% Q) (kc% φ)) (kc% h) = kc% (series B.F ω (B.vecAt Q φ) h) := by
  rw [vecAt_up r B]
  exact kc% rfl

theorem theta_up {S T : HSp D} (B : Base S T) (ω : PairRep S T) (h : GA D S) :
    (baseUp r B).theta ((ω)) ((h)) = (B.theta ω h) :=
  series_up r B ω ∅ (fun _ _ => 1) h

theorem vecFlat_up {S T : HSp D} (B : Base S T) (ψ : Twist D Circle) :
    (baseUp r B).vecFlat (twistUp r ψ) = (B.vecFlat ψ) :=
  vecAt_up r B ψ.Q _

theorem gen_up {S T : HSp D} (B : Base S T) (ω : PairRep S T) (ψ : Twist D Circle) :
    (baseUp r B).gen ((ω)) (twistUp r ψ) = (B.gen ω ψ) := by
  unfold Base.gen
  rw [vecFlat_up]
  exact (by with_unfolding_all exact (rfl :))

theorem genSet_up {S T : HSp D} (B : Base S T) (ω : PairRep S T) (ψ : Twist D Circle) (h P) :
    (baseUp r B).genSet ((by with_unfolding_all exact (ω :))) (twistUp r ψ) (kc% h) (kc% P) = kc% (B.genSet ω ψ h P) := by
  unfold Base.genSet
  rw [gen_up]
  exact kc% rfl

def univUp {C : Type} [AddCommGroup C] (u : UnivTwist D C) : UnivTwist (overD D r) C := ⟨(by with_unfolding_all exact (u.del :)), (by with_unfolding_all exact (u.kap :))⟩

theorem vecFam_up {S T : HSp D} (B : Base S T) {C : Type} (Q : Finset (Pl D.host.E))
    (Φ : ∀ PP : Pl D.host.E, C → Matrix (Fin T.rank) (Fin S.rank) (kP PP) → ℚ) :
    (baseUp r B).vecFam (C := C) ((by with_unfolding_all exact (Q :))) ((by with_unfolding_all exact (Φ :))) = (by with_unfolding_all exact ((B.vecFam (C := C) Q Φ) :)) :=
  funext fun a => vecAt_up r B Q _

theorem xiCoef_up {S T : HSp D} (B : Base S T) {C : Type} [AddCommGroup C] [Fintype C] (ω : PairRep S T) (u : UnivTwist D C)
    (Q : Finset (Pl D.host.E)) (Φ : ∀ PP : Pl D.host.E, C → Matrix (Fin T.rank) (Fin S.rank) (kP PP) → ℚ) (h : GA D S)
    (P : PolF D T.rank S.rank) :
    (baseUp r B).xiCoef ((ω)) (univUp r u) ((Q)) ((Φ)) ((h)) ((P)) = (B.xiCoef ω u Q Φ h P) := by
  unfold Base.xiCoef Base.xi
  rw [vecFam_up]
  exact (by with_unfolding_all exact (rfl :))

theorem classSum_up {S T : HSp D} (B : Base S T) (ω : PairRep S T) (ψ : Twist D Circle) {I : Type} [Fintype I] (h : I → GA D S) :
    (baseUp r B).classSum (I := I) ((by with_unfolding_all exact (ω :))) (twistUp r ψ) ((by with_unfolding_all exact (h :))) = (by with_unfolding_all exact ((B.classSum ω ψ h) :)) := by
  unfold Base.classSum
  rw [vecFlat_up]
  exact (by with_unfolding_all exact (rfl :))

theorem coefLat_of_equiv {S T : HSp D} (B : Base S T) {K : Type} [Field K] [NumberField K] (e : K ≃+* ↥D.LL0) (σ : K →+* ℂ)
    (emb : D.what₂.Tau → (D.host.E →+* K)) (hσ : ∀ x, embLL0 D (e x) = σ x) (hemb : ∀ τ, σ.comp (emb τ) = tauE D τ)
    (O : Subring ℂ) : B.coefLat σ emb O = B.coefLat (embLL0 D) (labLL0 D) O := by
  obtain rfl : (embLL0 D).comp e.toRingHom = σ := RingHom.ext hσ
  have h : (fun τ => e.toRingHom.comp (emb τ)) = labLL0 D := funext fun τ => RingHom.ext fun x => (embLL0 D).injective
    ((DFunLike.congr_fun (hemb τ) x).trans (DFunLike.congr_fun (embLL0_labLL0 τ) x).symm)
  funext x
  rw [Base.coefLat, Base.coefLat, harmLat, harmLat, GlobalTheory.CoefLatIso.coefLatFn_ringEquiv, h]

theorem mtLat_of_equiv {S T : HSp D} (B : Base S T) {K : Type} [Field K] [NumberField K] (e : K ≃+* ↥D.LL0) (σ : K →+* ℂ)
    (emb : D.what₂.Tau → (D.host.E →+* K)) (hσ : ∀ x, embLL0 D (e x) = σ x) (hemb : ∀ τ, σ.comp (emb τ) = tauE D τ)
    (O : Subring ℂ) (t : Twist D Circle) : B.mtLat σ emb O t = B.mtLat (embLL0 D) (labLL0 D) O t := by
  rw [Base.mtLat, Base.mtLat, coefLat_of_equiv B e σ emb hσ hemb]

section Setup

variable (ρ : Setup D.ntw) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)

theorem liftSetupOverExtendedData_theta_eq : (setupUp r ρ).theta ((i)) ((j)) b = (ρ.theta i j b) :=
  (by with_unfolding_all exact ((funext fun h => congrArg DFunLike.coe (theta_up r (ρ.B i j b) (ρ.om i j b 1) h)) :))

theorem liftSetupOverExtendedData_gens_eq : (setupUp r ρ).gens ((i)) ((j)) b = (ρ.gens i j b) :=
  (by with_unfolding_all exact ((funext fun k => funext fun Q => funext fun ψ => funext fun h => funext fun P =>
    genSet_up r (ρ.B i j b) (ρ.om i j b 1) (ρ.tw i b k Q ψ) h P) :))

theorem liftSetupOverExtendedData_classSum_eq : (setupUp r ρ).sum ((i)) ((j)) b = (ρ.sum i j b) :=
  (by with_unfolding_all exact ((funext fun k => funext fun Q => funext fun ψ =>
    classSum_up r (ρ.B i j b) (ρ.om i j b (ρ.tw i b k Q ψ).chi) (ρ.tw i b k Q ψ) (ρ.rep i j b (ρ.tw i b k Q ψ))) :))

theorem liftSetupOverExtendedData_xi_eq : (setupUp r ρ).xi ((i)) ((j)) b (overD D r).nexp = (ρ.xi i j b D.nexp) :=
  (by with_unfolding_all exact ((funext fun Q => funext fun M => funext fun h => funext fun P =>
    xiCoef_up r (ρ.B i j b) (ρ.om i j b 1) (univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc)
      (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M)) (Base.univFam (univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc) (ρ.β j)) h P) :))

variable {r} {ι : D.what₂.LL →+* (overD D r).what₂.LL} {e : ↥(overD D r).LL0 ≃+* ↥D.LL0} (hc : CopyTw D (overD D r) ι e)
include hc

theorem liftSetupOverExtendedData_lat_eq : (setupUp r ρ).lat ((i)) ((j)) b = (ρ.lat i j b) := by
  funext O x
  have := coefLat_of_equiv (ρ.B i j b) e (embLL0 (overD D r)) ((by with_unfolding_all exact ((labLL0 (overD D r)) :))) hc.embLL0_eq
    ((by with_unfolding_all exact ((embLL0_labLL0 (D := overD D r)) :))) O
  exact (by with_unfolding_all exact ((congrFun this (finPt _ x)) :))

theorem liftSetupOverExtendedData_integralForms_eq : (setupUp r ρ).mt ((i)) ((j)) b = (ρ.mt i j b) := by
  have H := mtLat_of_equiv (ρ.B i j b) e (embLL0 (overD D r)) ((by with_unfolding_all exact ((labLL0 (overD D r)) :))) hc.embLL0_eq
    ((by with_unfolding_all exact ((embLL0_labLL0 (D := overD D r)) :)))
  have H' := fun (k : ℕ) (Q : Finset (Pl D.host.E)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) =>
    H (ρ.eOk i b k).range (ρ.tw i b k Q ψ)
  funext k Q ψ
  exact (by with_unfolding_all exact ((H' k ((Q)) ((ψ))) : _))

theorem liftSetupOverExtendedData_isDatum_eq : (setupUp r ρ).IsDatum ((i)) ((j)) b = (ρ.IsDatum i j b) := by
  funext s x P
  have hl := liftSetupOverExtendedData_lat_eq ρ i j b hc
  refine propext ⟨fun d => ?_, fun d => ?_⟩
  · have m := d.mem
    rw [hl] at m
    exact (⟨(by with_unfolding_all exact (d.split :)), (by with_unfolding_all exact (d.off :)), (by with_unfolding_all exact (d.fin :)), (by with_unfolding_all exact (d.supp :)), (by with_unfolding_all exact (m :))⟩ : ρ.IsDatum i j b ((by with_unfolding_all exact (s :))) ((by with_unfolding_all exact (x :))) ((by with_unfolding_all exact (P :))))
  · have d' : ρ.IsDatum i j b ((by with_unfolding_all exact (s :))) ((by with_unfolding_all exact (x :))) ((by with_unfolding_all exact (P :))) := d
    refine ⟨(by with_unfolding_all exact (d'.split :)), (by with_unfolding_all exact (d'.off :)), (by with_unfolding_all exact (d'.fin :)), (by with_unfolding_all exact (d'.supp :)), ?_⟩
    rewrite [hl]
    exact (by with_unfolding_all exact (d'.mem :))

end Setup

section Cell

variable {ι : D.what₂.LL →+* (overD D r).what₂.LL} {e : ↥(overD D r).LL0 ≃+* ↥D.LL0} (hc : CopyTw D (overD D r) ι e)
  {ρ : Setup D.ntw} {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool}

def cellUp {hρ : ρ.Good} (hρ' : (setupUp r ρ).Good) {rd : Rd ρ D.nexp i j b} (t : CellTie hρ D.nexp rd) :
    CellTie hρ' (overD D r).nexp (i := (by with_unfolding_all exact (i :))) (j := (by with_unfolding_all exact (j :))) (b := b) ((by with_unfolding_all exact (rd :))) where
  supp := (by with_unfolding_all exact (t.supp :))
  cls := (by with_unfolding_all exact (t.cls :))
  coef := (by with_unfolding_all exact (t.coef :))
  rdV := (by with_unfolding_all exact (t.rdV :))
  U_eq := (by with_unfolding_all exact (t.U_eq :))
  psiU_eq := (by with_unfolding_all exact (t.psiU_eq :))
  dat := by rewrite [liftSetupOverExtendedData_isDatum_eq ρ i j b hc]; exact (by with_unfolding_all exact (t.dat :))
  dat_onto := by rewrite [liftSetupOverExtendedData_isDatum_eq ρ i j b hc, liftSetupOverExtendedData_theta_eq r ρ i j b]; exact (by with_unfolding_all exact (t.dat_onto :))
  lev_iff := (by with_unfolding_all exact (t.lev_iff :))
  th_eq := by rewrite [liftSetupOverExtendedData_theta_eq r ρ i j b]; exact (by with_unfolding_all exact (t.th_eq :))
  thPsi_iff := by rewrite [liftSetupOverExtendedData_gens_eq r ρ i j b]; exact (by with_unfolding_all exact (t.thPsi_iff :))
  thU_eq := by rewrite [liftSetupOverExtendedData_xi_eq r ρ i j b]; exact (by with_unfolding_all exact (t.thU_eq :))
  thU_off := by rewrite [liftSetupOverExtendedData_xi_eq r ρ i j b]; exact (by with_unfolding_all exact (t.thU_off :))
  rdV_inj := (by with_unfolding_all exact (t.rdV_inj :))
  mtLat_iff := by rewrite [liftSetupOverExtendedData_integralForms_eq ρ i j b hc]; exact (by with_unfolding_all exact (t.mtLat_iff :))
  thP_eq := by rewrite [liftSetupOverExtendedData_classSum_eq r ρ i j b]; exact (by with_unfolding_all exact (t.thP_eq :))

theorem cellUp_rdV {hρ : ρ.Good} (hρ' : (setupUp r ρ).Good) {rd : Rd ρ D.nexp i j b} (t : CellTie hρ D.nexp rd) :
    HEq t.rdV (cellUp r hc hρ' t).rdV := HEq.rfl

include hc in

theorem rat_up (hρ : ρ.Good) (hρ' : (setupUp r ρ).Good) (rd : Rd ρ D.nexp i j b) :
    SeriesTie.Rat hρ' (Y := (overD D r).nexp) (i := (by with_unfolding_all exact (i :))) (j := (by with_unfolding_all exact (j :))) (b := b) ((by with_unfolding_all exact (rd :))) ↔ SeriesTie.Rat hρ rd := by
  conv_lhs => delta SeriesTie.Rat RatBase RatTwist RatUniv
  rewrite [liftSetupOverExtendedData_isDatum_eq ρ i j b hc, liftSetupOverExtendedData_theta_eq r ρ i j b, liftSetupOverExtendedData_gens_eq r ρ i j b, liftSetupOverExtendedData_xi_eq r ρ i j b]
  exact (by with_unfolding_all exact ((Iff.refl (SeriesTie.Rat hρ rd)) :))

end Cell

end GlobalTheory.TwInputs.Move.TieUp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfRaisingOperatorsJointHarmonics
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section
namespace GlobalTheory.RaiseGen

open MvPolynomial GlobalTheory.FockIsotypic

theorem exists_ker_add_range {E : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] (A : E →ₗ[ℂ] E)
    (h : ∀ x, A (A x) = 0 → A x = 0) (x : E) : ∃ x₀ y, A x₀ = 0 ∧ x = x₀ + A y := by
  have hd : Disjoint (LinearMap.ker A) (LinearMap.range A) := by
    rw [Submodule.disjoint_def]
    rintro _ hz ⟨y, rfl⟩
    exact h y hz
  have ht : LinearMap.ker A ⊔ LinearMap.range A = ⊤ :=
    Submodule.eq_top_of_disjoint _ _ (by have := LinearMap.finrank_range_add_finrank_ker A; omega) hd
  obtain ⟨x₀, h0, _, ⟨y, rfl⟩, e⟩ := Submodule.mem_sup.1 (ht ▸ Submodule.mem_top (x := x))
  exact ⟨x₀, y, h0, e.symm⟩

theorem mem_of_filtration {V W K ι : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] [Fintype ι] (act : K → V →ₗ[ℂ] V) (ρ : K → W →ₗ[ℂ] W) (R L : ι → V →ₗ[ℂ] V)
    (S : ℕ → Submodule ℂ V) [∀ d, FiniteDimensional ℂ (S d)]
    (hR : ∀ i k x, act k (R i x) = R i (act k x)) (hL : ∀ i k x, act k (L i x) = L i (act k x))
    (hL0 : ∀ i, ∀ x ∈ S 0, L i x = 0) (hLs : ∀ i d, ∀ x ∈ S (d + 1), L i x ∈ S d)
    (hRL : ∀ i d, ∀ x ∈ S d, R i (L i x) ∈ S d)
    (hker : ∀ x, ∑ i, R i (L i x) = 0 → ∀ i, L i x = 0)
    (hAA : ∀ x, (∀ j, L j (∑ i, R i (L i x)) = 0) → ∑ i, R i (L i x) = 0)
    (N : Submodule ℂ (W →ₗ[ℂ] V))
    (hN0 : ∀ φ : W →ₗ[ℂ] V, (∀ k w, φ (ρ k w) = act k (φ w)) → (∀ w i, L i (φ w) = 0) → φ ∈ N)
    (hNR : ∀ ψ ∈ N, ∀ i, R i ∘ₗ ψ ∈ N) (d : ℕ) :
    ∀ φ : W →ₗ[ℂ] V, (∀ k w, φ (ρ k w) = act k (φ w)) → (∀ w, φ w ∈ S d) → φ ∈ N := by
  induction d with
  | zero => exact fun φ hφ hS => hN0 φ hφ fun w i => hL0 i _ (hS w)
  | succ d ih =>
    intro φ hφ hS
    let E : Submodule ℂ (W →ₗ[ℂ] V) :=
      { carrier := {ψ | (∀ k w, ψ (ρ k w) = act k (ψ w)) ∧ ∀ w, ψ w ∈ S (d + 1)}
        add_mem' := fun {a b} ha hb => ⟨fun k w => by simp [ha.1, hb.1], fun w => add_mem (ha.2 w) (hb.2 w)⟩
        zero_mem' := ⟨fun k w => by simp, fun w => zero_mem _⟩
        smul_mem' := fun c a ha => ⟨fun k w => by simp [ha.1], fun w => Submodule.smul_mem _ c (ha.2 w)⟩ }
    haveI : FiniteDimensional ℂ E := by
      refine Submodule.finiteDimensional_of_le
        (S₂ := LinearMap.range (LinearMap.compRight (M := W) ℂ (S (d + 1)).subtype)) ?_
      intro ψ hψ
      exact ⟨ψ.codRestrict _ hψ.2, rfl⟩
    let A : V →ₗ[ℂ] V := ∑ i, R i ∘ₗ L i
    have hA : ∀ x, A x = ∑ i, R i (L i x) := fun x => by simp [A, LinearMap.sum_apply]
    have hE : ∀ ψ ∈ E, LinearMap.compRight (M := W) ℂ A ψ ∈ E := fun ψ hψ =>
      ⟨fun k w => by
        change A (ψ (ρ k w)) = act k (A (ψ w))
        simp only [hA, hψ.1, map_sum, hR, hL], fun w => by
        change A (ψ w) ∈ _
        rw [hA]
        exact Submodule.sum_mem _ fun i _ => hRL i _ _ (hψ.2 w)⟩
    obtain ⟨φ₀, ψ, h0, e⟩ := exists_ker_add_range ((LinearMap.compRight (M := W) ℂ A).restrict hE) (fun ψ h => by
      refine Subtype.ext (LinearMap.ext fun w => ?_)
      have h1 : A (A (ψ.1 w)) = 0 := LinearMap.congr_fun (congrArg Subtype.val h) w
      change A (ψ.1 w) = 0
      rw [hA] at h1
      have h2 := hker _ h1
      rw [hA] at h2 ⊢
      exact hAA _ h2) ⟨φ, hφ, hS⟩
    have e' : φ = φ₀.1 + ∑ i, R i ∘ₗ (L i ∘ₗ ψ.1) := by
      refine LinearMap.ext fun w => ?_
      have h1 : φ w = φ₀.1 w + A (ψ.1 w) := LinearMap.congr_fun (congrArg Subtype.val e) w
      rw [h1, hA]
      simp [LinearMap.sum_apply]
    rw [e']
    refine add_mem (hN0 _ φ₀.2.1 fun w => hker _ ?_) (Submodule.sum_mem _ fun i _ => hNR _ (ih _ ?_ ?_) i)
    · rw [← hA]
      exact LinearMap.congr_fun (congrArg Subtype.val h0) w
    · intro k w
      simp only [LinearMap.comp_apply, ψ.2.1, hL]
    · exact fun w => hLs i d _ (ψ.2.2 w)

section Fischer

variable {σ : Type} [Fintype σ]

theorem fis_X_mul (v : σ) (P Q : MvPolynomial σ ℂ) : fis (X v * P) Q = fis P (pderiv v Q) := by
  classical
  unfold fis
  rw [mul_comm, map_mul, rename_X, ReciprocityTheory.PGsh.fischer_mul_X, pderiv_rename (flat σ).injective]

theorem fis_sum_left {α : Type} (s : Finset α) (f : α → MvPolynomial σ ℂ) (Q : MvPolynomial σ ℂ) :
    fis (∑ i ∈ s, f i) Q = ∑ i ∈ s, fis (f i) Q := by
  unfold fis
  rw [map_sum, ReciprocityTheory.PGsh.fischer_sum_left]

theorem fis_sum_right {α : Type} (s : Finset α) (P : MvPolynomial σ ℂ) (f : α → MvPolynomial σ ℂ) :
    fis P (∑ i ∈ s, f i) = ∑ i ∈ s, fis P (f i) := by
  unfold fis
  rw [map_sum, ReciprocityTheory.PGsh.fischer_sum_right]

theorem fis_zero_left (Q : MvPolynomial σ ℂ) : fis 0 Q = 0 := by
  simpa using fis_smul_left 0 0 Q

theorem fis_zero_right (P : MvPolynomial σ ℂ) : fis P 0 = 0 := by
  simpa using fis_smul_right 0 P 0

theorem fis_neg_right (P Q : MvPolynomial σ ℂ) : fis P (-Q) = -fis P Q := by
  simpa using fis_smul_right (-1) P Q

theorem eq_zero_of_fis_re (P : MvPolynomial σ ℂ) (h : (fis P P).re = 0) : P = 0 := by
  by_contra hP
  exact fis_self_ne_zero hP (Complex.ext h (Complex.conj_eq_iff_im.1 (fis_conj P P)))

variable {ι : Type} [Fintype ι] (R L : ι → MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ)
  (hadj : ∀ i P Q, fis (R i P) Q = -fis P (L i Q))

include hadj

theorem lower_eq_zero (P : MvPolynomial σ ℂ) (h : ∑ i, R i (L i P) = 0) (i : ι) : L i P = 0 := by
  have h1 : fis (∑ i, R i (L i P)) P = 0 := by rw [h, fis_zero_left]
  rw [fis_sum_left] at h1
  simp only [hadj, Finset.sum_neg_distrib, neg_eq_zero] at h1
  have h2 := congrArg Complex.re h1
  rw [Complex.re_sum, Complex.zero_re,
    Finset.sum_eq_zero_iff_of_nonneg fun i _ => fis_self_re_nonneg _] at h2
  exact eq_zero_of_fis_re _ (h2 i (Finset.mem_univ i))

theorem sum_eq_zero_of_lower (P : MvPolynomial σ ℂ) (h : ∀ j, L j (∑ i, R i (L i P)) = 0) :
    ∑ i, R i (L i P) = 0 := by
  refine eq_zero_of_fis_re _ ?_
  rw [fis_sum_left]
  simp only [hadj, h, fis_zero_right, neg_zero, Finset.sum_const_zero, Complex.zero_re]

end Fischer

theorem fockT_raise {D : D7} {n m : ℕ} (τ : D.what₂.Tau) (p : D.what₂.Tau → ℕ) (i l : Fin m)
    (hi : (i : ℕ) < p τ) (hl : p τ ≤ (l : ℕ)) (P : PolF D m n) :
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ))
      (Matrix.single i l (1 : ℂ)) P = ∑ j : Fin n, X (τ, i, j) * (X (τ, l, j) * P) := by
  classical
  have hil : i ≠ l := by intro h; subst h; omega
  have h1 : decide ((l : ℕ) < p τ) = false := decide_eq_false (by omega)
  have h2 : decide ((i : ℕ) < p τ) = true := decide_eq_true hi
  unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT
  rw [Finset.sum_eq_single i, Finset.sum_eq_single l]
  · simp [GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.raiO, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.lowO, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn, h1, h2, hil, LinearMap.sum_apply]
  · intro k _ hk; simp [Matrix.single_apply, Ne.symm hk]
  · simp
  · intro k _ hk; simp [Matrix.single_apply, Ne.symm hk]
  · simp

theorem raise_deg {D : D7} {n m : ℕ} (τ : D.what₂.Tau) (p : D.what₂.Tau → ℕ) (i l : Fin m)
    (hi : (i : ℕ) < p τ) (hl : p τ ≤ (l : ℕ)) (P : PolF D m n) (k : ℕ) (h : P.totalDegree ≤ k) :
    (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ))
      (Matrix.single i l (1 : ℂ)) P).totalDegree ≤ k + 2 := by
  rw [fockT_raise τ p i l hi hl]
  refine totalDegree_finsetSum_le fun j _ => (totalDegree_mul _ _).trans ?_
  have := totalDegree_mul (X (τ, l, j) : PolF D m n) P
  rw [totalDegree_X] at this ⊢
  omega

theorem mem_of_raise : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (BS : GlobalTheory.ExportSeries.GLR D n) (K : Type) [Group K] (r : K →* GlobalTheory.ExportSeries.GLR D n), (∀ (k : K) (τ : D.what₂.Tau), ((GlobalTheory.ExportSeries.inBasis BS (r k) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : K →* Module.End ℂ W), ∀ N : Submodule ℂ (W →ₗ[ℂ] PolF D m n), (∀ φ : W →ₗ[ℂ] PolF D m n, (∀ (k : K) (w' : W), φ (ρ k w') = GlobalTheory.ExportSeries.fockGL m w BS (r k) (φ w')) → (∀ w' : W, ∀ (τ' : D.what₂.Tau) (i l : Fin m), w.p τ' ≤ (i : ℕ) → (l : ℕ) < w.p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ')) (Matrix.single i l (1 : ℂ)) (φ w') = 0) → φ ∈ N) → (∀ ψ ∈ N, ∀ (τ : D.what₂.Tau) (i l : Fin m), (i : ℕ) < w.p τ → w.p τ ≤ (l : ℕ) → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) (Matrix.single i l (1 : ℂ)) ∘ₗ ψ ∈ N) → ∀ φ : W →ₗ[ℂ] PolF D m n, (∀ (k : K) (w' : W), φ (ρ k w') = GlobalTheory.ExportSeries.fockGL m w BS (r k) (φ w')) → φ ∈ N := by
  intro D n m w BS K _ r _ W _ _ _ ρ N hN0 hNR φ hφ
  classical
  let ι : Type := {t : D.what₂.Tau × Fin m × Fin m // (t.2.1 : ℕ) < w.p t.1 ∧ w.p t.1 ≤ (t.2.2 : ℕ)}
  let T : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ → PolF D m n →ₗ[ℂ] PolF D m n := fun τ Y =>
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) Y
  let R : ι → PolF D m n →ₗ[ℂ] PolF D m n := fun t => T t.1.1 (Matrix.single t.1.2.1 t.1.2.2 1)
  let L : ι → PolF D m n →ₗ[ℂ] PolF D m n := fun t => T t.1.1 (Matrix.single t.1.2.2 t.1.2.1 1)
  have hT : ∀ τ Y k x, GlobalTheory.ExportSeries.fockGL m w BS (r k) (T τ Y x) =
      T τ Y (GlobalTheory.ExportSeries.fockGL m w BS (r k) x) := fun τ Y k x => by
    rw [GlobalTheory.ExportSeries.fockGL_apply, GlobalTheory.ExportSeries.fockGL_apply, map_smul]
    exact congrArg _ (GlobalTheory.FockSubstComm.fockSubst_fockT D m n w.p _ τ Y x)
  have hadj : ∀ i P Q, fis (R i P) Q = -fis P (L i Q) := fun t P Q => by
    simp only [R, L, T]
    rw [fockT_raise _ _ _ _ t.2.1 t.2.2, GlobalTheory.LowerHarm.fockT_lower _ _ _ _ t.2.2 t.2.1, fis_neg_right, neg_neg,
      fis_sum_left, fis_sum_right]
    exact Finset.sum_congr rfl fun j _ => by rw [fis_X_mul, fis_X_mul]
  have hdeg : ∃ d, ∀ w', (φ w').totalDegree ≤ d := by
    let b := Module.finBasis ℂ W
    refine ⟨Finset.univ.sup fun j => (φ (b j)).totalDegree, fun w' => ?_⟩
    rw [← b.sum_repr w', map_sum]
    refine totalDegree_finsetSum_le fun j _ => ?_
    rw [map_smul]
    exact (totalDegree_smul_le _ _).trans
      (Finset.le_sup (f := fun j => (φ (b j)).totalDegree) (Finset.mem_univ j))
  obtain ⟨d, hd⟩ := hdeg
  refine mem_of_filtration (fun k => GlobalTheory.ExportSeries.fockGL m w BS (r k)) (fun k => ρ k) R L
    (fun d => restrictTotalDegree (FVar D m n) ℂ d) (fun t => hT _ _) (fun t => hT _ _) ?_ ?_ ?_
    (lower_eq_zero R L hadj) (sum_eq_zero_of_lower R L hadj) N ?_ ?_ d φ hφ
    fun w' => (mem_restrictTotalDegree _ _ _).2 (hd w')
  · intro t x hx
    rw [mem_restrictTotalDegree] at hx
    exact GlobalTheory.LowerHarm.lower_zero _ _ _ _ t.2.2 t.2.1 x (by omega)
  · intro t k x hx
    rw [mem_restrictTotalDegree] at hx ⊢
    exact GlobalTheory.LowerHarm.lower_deg _ _ _ _ t.2.2 t.2.1 x k (by omega)
  · intro t k x hx
    rw [mem_restrictTotalDegree] at hx ⊢
    rcases Nat.lt_or_ge k 2 with h2 | h2
    · have : L t x = 0 := GlobalTheory.LowerHarm.lower_zero _ _ _ _ t.2.2 t.2.1 x (by omega)
      simp [this]
    · obtain ⟨k, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      exact raise_deg _ _ _ _ t.2.1 t.2.2 _ k (GlobalTheory.LowerHarm.lower_deg _ _ _ _ t.2.2 t.2.1 x k hx)
  · exact fun ψ hψ h => hN0 ψ hψ fun w' τ i l hi hl => h w' ⟨(τ, l, i), hl, hi⟩
  · exact fun ψ hψ t => hNR ψ hψ _ _ _ t.2.1 t.2.2

end GlobalTheory.RaiseGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionTrivialOffSupport
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.ExportSeries.DualType
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.ExportSeries

theorem idemAt_mul_idem_add_conj {D : D7} {P Q' : Finset (Pl D.host.E)} (hP : SplitSet P) (hQ : Q' ⊆ P)
    {PP : Pl D.host.E} (hPP : PP ∈ P) (hPQ : PP ∉ Q') : idemAt PP * (idem Q' + cA D (idem Q')) = 0 := by
  rw [mul_add, idem, map_sum, Finset.mul_sum, Finset.mul_sum]
  rw [Finset.sum_eq_zero fun q hq => hP.mul_eq_zero hPP (hQ hq) (fun e => hPQ (e ▸ hq)),
    Finset.sum_eq_zero fun q hq => hP.mul_conj hPP (hQ hq), add_zero]

set_option maxHeartbeats 6000000 in

theorem redFn_eq_one_of_suppAt : ∀ {D : D7} {V : HSp D} (β : GL (Fin V.rank) (Lev.EAf D)) {P Q' : Finset (Pl D.host.E)}, SplitSet P → Q' ⊆ P → ∀ {PP : Pl D.host.E}, PP ∈ P → PP ∉ Q' → ∀ {κ : GA D V}, Lev.finE V κ ∈ St β → SuppAt (idem Q') V κ → redFn β PP (Lev.finE V κ) = 1 := by
  intro D V β P Q' hP hQ PP hPP hPQ κ hS hSupp
  obtain ⟨y, hy⟩ := hS
  obtain ⟨hint, h1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D (idemAt PP) PP (hP.isIdemAt hPP)
  have h0 := idemAt_mul_idem_add_conj hP hQ hPP hPQ

  have hk : ∀ i j, idemAt PP * (Formalism.L2.Theta.mt V κ - 1) i j = 0 := fun i j => by
    rw [← hSupp i j, ← mul_assoc, h0, zero_mul]
  have hval : (Lev.finE V κ).val = (Formalism.L2.Theta.mt V κ).map (toEAf D) := rfl

  have hA : toEAf D (idemAt PP) • ((Lev.finE V κ).val - 1) = 0 := by
    ext i j
    have := congrArg (toEAf D) (hk i j)
    rw [RingHom.map_mul, RingHom.map_zero, Matrix.sub_apply, RingHom.map_sub] at this
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, hval, Matrix.map_apply, Matrix.zero_apply]
    convert this using 3
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hY : toEAf D (idemAt PP) • ((intGL D.host.F D.host.E _ y).val - 1) = 0 := by
    have hg : intGL D.host.F D.host.E _ y = β⁻¹ * Lev.finE V κ * β := by
      rw [← hy]; simp [frGL, MulAut.conj_apply, mul_assoc]
    have e1 : (intGL D.host.F D.host.E _ y).val - 1 = (β⁻¹).val * ((Lev.finE V κ).val - 1) * β.val := by
      rw [hg, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← Units.val_mul β⁻¹ β, inv_mul_cancel, Units.val_one,
        Units.val_mul, Units.val_mul]
    rw [e1, ← Matrix.smul_mul, ← Matrix.mul_smul, hA, Matrix.mul_zero, Matrix.zero_mul]
  rw [← hy, redFn_frGL]
  ext i j
  have hij := congrFun (congrFun hY i) j
  have hsub : (⟨toEAf D (idemAt PP), hint⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * y.val i j = (⟨toEAf D (idemAt PP), hint⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j := by
    have hij' : toEAf D (idemAt PP) * ((intGL D.host.F D.host.E _ y).val i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) i j) = 0 := by
      simpa only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Matrix.zero_apply] using hij
    have h1ij : ((1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)) i j : Lev.EAf D) =
        (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) i j := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    apply Subtype.ext
    rw [MulMemClass.coe_mul, MulMemClass.coe_mul, h1ij, ← sub_eq_zero, ← mul_sub]
    exact hij'
  have := congrArg (resS D.host.F PP) hsub
  rw [RingHom.map_mul, RingHom.map_mul, h1, one_mul, one_mul] at this
  change (resS D.host.F PP) (y.val i j) = _
  rw [this, Units.val_one, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory.ExportSeries

end
end

