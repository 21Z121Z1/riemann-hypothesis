import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2079
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0934
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1594
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1553
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1039
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1051
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatiblePhaseExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralShiftExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1332
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1081
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1090
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1028
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0461
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1989
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LUnifOfRhoGeoEquivAll
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0929
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowEqSpan
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0797
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1605
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1616
import Formalism.LocalToGlobal.Divisibility.RecBridgeNum
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Development.AbelianVarietyTheory.Definitions.Divisors.RealisedChainTorusEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1095
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishingStatement
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2081
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatThetaQuotientAtPrincipalLevelProof
section
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseCmp

open GlobalTheory.PlaceModel

open Classical in

theorem resC_eq_of_kerDat {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}
    {ξ : Formalism.L2.Host.HChar D.host.E} {χ : (AE D)ˣ →* Circle} {ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    {ω : WeilRep D i} {φ : WO (Vc D i) (Wc D i) → ℂ} {B : Base (Vc D i) (Wc D i)} (hB : B.Good)
    (hK : KerDat R i ξ χ ξR B.de.Q ω φ) (hc : ChrEq B.de.chi ξ) {PP : Pl D.host.E} (hPP : PP ∈ B.de.Q) :
    ξR PP = B.de.resC PP := by
  refine MonoidHom.ext fun u => Units.ext ?_
  obtain ⟨x, hx⟩ := exists_isLocUnit (hB.de.split.isIdemAt hPP) u
  obtain ⟨k1, k2⟩ := hx.res
  have e1 := eq_res_of_chrEq hc (hB.de.split.isIdemAt hPP) (hK.tame PP) (hK.res PP hPP) x hx.off k1 u k2
  have e2 := hx.eq (hB.de.res PP hPP)
  rw [← e1, e2]
  rfl

open Classical in

theorem omegaFlat_eq_locFn_empty {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}
    {ξ : Formalism.L2.Host.HChar D.host.E} {χ : (AE D)ˣ →* Circle} {ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    {ω : WeilRep D i} {φ : WO (Vc D i) (Wc D i) → ℂ} {B : Base (Vc D i) (Wc D i)} (hB : B.Good)
    (hK : KerDat R i ξ χ ξR B.de.Q ω φ) (hc : ChrEq B.de.chi ξ) (y : Reds D (Wc D i).rank (Vc D i).rank) :
    omegaFlat B.de.Q (Wc D i).rank ξR y = (GlobalTheory.FlatVecSum.princ B).locFn ∅ (fun _ _ => 1) y := by
  rw [GlobalTheory.FlatVecSum.omegaFlat_eq_prod, Base.locFn]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  exact Finset.prod_congr rfl fun PP hP => by rw [resC_eq_of_kerDat hB hK hc hP]; rfl

open Classical in

theorem flatTwoStep_holds : FlatTwoStep := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i ξ χ ξR ω φ B hB h hK hc
  obtain ⟨hvac, e, he, -⟩ := hK.vec
  have hψ := hvac.1
  have sV : IsSelfDualC (Vc D i) (R.ΛV i) :=
    GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hR.lev.βV i))
  have sW : IsSelfDualC (Wc D i) (R.ΛW i) :=
    GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hR.lev.βW i))
  have hdisj : Disjoint R.Pg B.de.Q := h.Pg ▸ hB.places.disj
  obtain ⟨eg, eQ, hg, hq, h1, h2, h3⟩ := GlobalTheory.FlatVecExist.idemSum_split he hdisj
  have hinfg := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hg)
  obtain ⟨fg, hfg⟩ := GlobalTheory.PlaceVec.exists_isThetaAt hψ sV sW (a := cA D eg)
    (by rw [← RingHom.map_mul, GlobalTheory.PlaceVec.idemSum_mul_self hg]) hinfg
    (GlobalTheory.PlaceModelSum.placeModelExistsSum D R.ψ hψ _ _ _ _ sV sW _ eg hg _ hvac.2.theta hvac.2.lat).2
    (GlobalTheory.PlaceVec.isSBHalf_of_red sV.1 sW.1 hinfg (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
      (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _) R.Pg
      (fun y => omegaK R.Pg y) fun y y' h => GlobalTheory.PlaceVec.omegaK_congr R.Pg h)
  have hoQ := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hq
  have fix : ∀ u, (∀ a b, cA D eg * u a b = 0 ∧ eg * u a b = 0) →
      heisO R.ψ (Vc D i) (Wc D i) u (R.vacP i) = R.vacP i → heisO R.ψ (Vc D i) (Wc D i) u fg = fg :=
    fun u hu h0 => GlobalTheory.Hk3.heisO_fix_thetaAt_off R.ψ _ _ (cA D eg) _ 1 _ _ fg hfg u
      (fun a b => by rw [GlobalTheory.DualPairCheck.cA_cA]; exact hu a b) h0
  have hPM := GlobalTheory.FlatVecExist.exists_model_of_fix hψ sV sW hoQ hq.2
    (fun u hu => fix u (fun a b => (GlobalTheory.FlatVecExist.off_of_half h1 (by rw [mul_comm, h3])
        ((isHalf_iff _ _).2 hu.2) a b).symm)
      (hoQ.heisO_eq (by rw [mul_comm, hq.2]) hvac.2.lat u hu))
    (fun u hu => fix u (fun a b => (GlobalTheory.FlatVecExist.off_of_half h2
        (by rw [← RingHom.map_mul, h1, map_zero]) ((isHalf_iff _ _).2 hu.2) a b).symm)
      (hoQ.conj.heisO_eq (by rw [GlobalTheory.DualPairCheck.cA_cA, hq.2]) hvac.2.lat u hu))
  have hinfQ := GlobalTheory.PlaceDatum.infPart_idemSum hq
  obtain ⟨K, hK', hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO sV.1 sW.1 (R.βV i) (R.βW i)
  obtain ⟨f, hf⟩ := GlobalTheory.PlaceDatum.exists_isThetaAt hψ sV sW (GlobalTheory.PlaceDatum.idemSum_mul_self hq) hinfQ hPM
    (GlobalTheory.PlaceDatum.isSBHalf_of_red eQ _ (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)) (GlobalTheory.PlaceDatum.frMapO_add _ _)
      (GlobalTheory.PlaceDatum.exists_den_frMapO sV.1.fg sW.1.fg _ _)
      ⟨K, hK', fun x hx => hC x (GlobalTheory.PlaceDatum.infPart_of_half hinfQ hx)⟩ B.de.Q
      (fun y => GlobalTheory.ConjTwist.omegaFlat B.de.Q (Wc D i).rank ξR y) fun y y' h => GlobalTheory.FlatVecExist.omegaFlat_congr _ _ _ h)
  have hfeq : f = (GlobalTheory.FlatVecSum.princ B).vecBase := by
    have k1 := hfg
    have k2 := hf
    simp only [omegaFlat_eq_locFn_empty hB hK hc] at k2
    rw [← idem_eq hg] at k1
    rw [← idem_eq hq] at k2
    rw [← h.ψ, ← h.ΛS, ← h.ΛT, ← h.βS, ← h.βT] at k1 k2
    rw [← h.vac, ← h.Pg] at k1
    unfold Base.vecBase Base.vecAt
    rw [Finset.union_empty]
    refine GlobalTheory.FlatVecSum.eq_vec_of_two_steps (G := GlobalTheory.FlatVecSum.princG B.G) hB.frame hB.places (fun y y' hy => ?_)
      (fg := fg) ?_ k2
    · unfold Base.locFn
      rw [Finset.prod_congr rfl fun PP hPP => by rw [hy PP hPP]]
    · simp only [GlobalTheory.FlatVecSum.omegaG_princ]
      exact k1
  refine ⟨eg, eQ, fg, hg, hq, hfg, ?_⟩
  rw [← hfeq]
  exact hf

end GlobalTheory.BaseCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalLiftOfOneMap
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
open Formalism.IndefR.Arith

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GalLift.Assembly

section Abstract

variable {L : Type} [Field L] {G : Type} [Group G] [Fintype G] {C Y H : Type} [AddCommGroup Y] [Module L Y]
  [AddCommGroup H] [Module ℂ H]

theorem read_sum (σ : L →+* ℂ) (J : Y →ₛₗ[σ] H) (ι : C → Y) (act : G → C → C) (chi : G →* Lˣ) (ρ : Representation ℂ G H)
    (h : ∀ g f, J (ι (act g f)) = σ (chi g : L) • ρ g (J (ι f))) (e : G → L) {n : ℕ} (b : Fin n → L) (f : Fin n → C) :
    J (∑ g, (e g * (((chi g)⁻¹ : Lˣ) : L)) • ∑ k, b k • ι (act g (f k))) =
      ∑ g, σ (e g) • ρ g (∑ k, σ (b k) • J (ι (f k))) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smulₛₗ, map_sum, map_sum, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smulₛₗ, h, map_smul, smul_smul, smul_smul, smul_smul, ← map_mul, ← map_mul, ← map_mul]
  congr 2
  have := (chi g).inv_mul
  linear_combination (e g * b k) * this

theorem shift_sum (ρ : Representation ℂ G H) (e : G → ℂ) {z₀ z : G} (h₀ : z₀ ∈ Subgroup.center G) (hz : z ∈ Subgroup.center G)
    (α β κ : ℂ) (hβ : β ≠ 0) (S T : H) (hT : κ • T = ∑ g, e g • ρ g (β • ρ z S)) :
    ∑ g, e g • ρ g (α • ρ z₀ S) = (α * β⁻¹ * κ) • ρ (z₀ * z⁻¹) T := by
  rw [mul_smul, ← map_smul (ρ (z₀ * z⁻¹)) κ, hT, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  have h1 : ρ (z₀ * z⁻¹) (ρ g (ρ z S)) = ρ g (ρ z₀ S) := by
    have e1 : z₀ * z⁻¹ * (g * z) = g * z₀ := by
      rw [Subgroup.mem_center_iff.1 hz g, Subgroup.mem_center_iff.1 h₀ g]; group
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_assoc, e1, map_mul, Module.End.mul_apply]
  simp only [map_smul, h1, smul_smul]
  congr 1
  field_simp

theorem norm_of_pow {a : ℂ} {m : ℕ} (hm : 0 < m) (h : a ^ m = 1) : ‖a‖ = 1 :=
  (pow_eq_one_iff_of_nonneg (norm_nonneg a) hm.ne').1 (by rw [← norm_pow, h, norm_one])

theorem norm_chi (σ : L →+* ℂ) (chi : G →* Lˣ) (g : G) : ‖σ (chi g : L)‖ = 1 :=
  norm_of_pow (m := Fintype.card G) Fintype.card_pos (by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one, map_one])

variable {P : Type} [AddCommGroup P] [Module ℂ P]

theorem conj_abstract (σ : L →+* ℂ) (J : Y →ₛₗ[σ] H) (ι : C → Y) (act : G → C → C) (chi : G →* Lˣ) (ρ : Representation ℂ G H)
    (h : ∀ g f, J (ι (act g f)) = σ (chi g : L) • ρ g (J (ι f))) (e : G → L) (ev : H →ₗ[ℂ] P) (hev : Function.Injective ev)
    (W : P →ₗ[ℂ] P) (hW : ∀ y, W (ev y) = ev (∑ g, σ (e g) • ρ g y)) {z₀ z : G} (h₀ : z₀ ∈ Subgroup.center G)
    (hz : z ∈ Subgroup.center G) (ze : L) (κ : ℂ) {n : ℕ} (a : Fin n → L) (f : Fin n → C) (θ : P)
    (hθ : κ • θ = ∑ k, σ (a k) • ev (J (ι (act z (f k))))) (T : H) (hT : ev T = W θ) :
    J (∑ g, (e g * (((chi g)⁻¹ : Lˣ) : L)) • ∑ k, (ze * a k) • ι (act g (act z₀ (f k)))) =
      (σ ze * σ (chi z₀ : L) * (σ (chi z : L))⁻¹ * κ) • ρ (z₀ * z⁻¹) T := by
  have e1 : ∑ k, σ (a k) • ev (J (ι (act z (f k)))) = ev (σ (chi z : L) • ρ z (∑ k, σ (a k) • J (ι (f k)))) := by
    rw [map_sum, Finset.smul_sum, map_sum]
    exact Finset.sum_congr rfl fun k _ => by simp only [h, map_smul]; rw [smul_comm]
  have h3 : ∑ k, σ (ze * a k) • J (ι (act z₀ (f k))) = (σ ze * σ (chi z₀ : L)) • ρ z₀ (∑ k, σ (a k) • J (ι (f k))) := by
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [h, map_smul, smul_smul, smul_smul, map_mul]
    congr 1
    ring
  rw [read_sum σ J ι act chi ρ h e (fun k => ze * a k) (fun k => act z₀ (f k)), h3]
  refine shift_sum ρ _ h₀ hz _ _ κ (norm_ne_zero_iff.1 (by rw [norm_chi]; exact one_ne_zero)) _ _ (hev ?_)
  rw [map_smul, hT, ← map_smul, hθ, e1, hW]

theorem exists_ev (ev : H →ₗ[ℂ] P) {κ : ℂ} (hκ : ‖κ‖ = 1) {n : ℕ} (a : Fin n → ℂ) (t : Fin n → H) (θ : P)
    (hθ : κ • θ = ∑ k, a k • ev (t k)) : ∃ s, ev s = θ := by
  have hκ0 : κ ≠ 0 := norm_ne_zero_iff.1 (by rw [hκ]; exact one_ne_zero)
  refine ⟨κ⁻¹ • ∑ k, a k • t k, ?_⟩
  rw [map_smul, map_sum, ← inv_smul_smul₀ hκ0 θ, hθ]
  simp only [map_smul]

def evL {I : Type} {M : I → Type} [∀ τ, AddCommGroup (M τ)] [∀ τ, Module ℂ (M τ)] (e : H →ₗ[ℂ] MultilinearMap ℂ M P)
    (v : ∀ τ, M τ) : H →ₗ[ℂ] P where
  toFun y := e y v
  map_add' x y := by rw [map_add]; rfl
  map_smul' a x := by rw [map_smul]; rfl

end Abstract

section Main

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

def crdF (fw : FWTie T R κw v₀) (i : Fin D.R.m) (f : Cu T κw i) : Fin (R.nW i) → D.what₂.LL := (fw.e i f : (R.FW i).WK)

def ratOf (fw : FWTie T R κw v₀) (i : Fin D.R.m) (act : G → Cu T κw i → Cu T κw i) (z : G) (ze : D.what₂.LL) {n : ℕ}
    (a : Fin n → D.what₂.LL) (f : Fin n → Cu T κw i) : Fin (R.nW i) → D.what₂.LL :=
  ∑ g, ((idemOf A.X).coeff g * ((((R.FW i).chi g)⁻¹ : D.what₂.LLˣ) : D.what₂.LL)) •
    ∑ k, (ze * a k) • crdF fw i (act g (act z (f k)))

theorem sign_at_base_place_eq_embedding (R : RealDat D A T.Q.c.F) : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0

theorem exists_reps {i : Fin D.R.m} {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)} (hP : OMPins T R κw v₀ O i) :
    ∃ h, RepsAt (O i) (v₀ i (sg0 D A)) h := (hP.2.tuple ()).reps

end Main

section Final

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

theorem smul_inv_of {H : Type} [AddCommGroup H] [Module ℂ H] (L : H →ₗ[ℂ] H) {κ κ' : ℂ} (h : ‖κ'‖ = 1) {a b : H}
    (e : b = κ' • a) : κ • L a = (κ * κ'⁻¹) • L b := by
  have h0 : κ' ≠ 0 := norm_ne_zero_iff.1 (by rw [h]; exact one_ne_zero)
  rw [e, map_smul, smul_smul, mul_assoc, inv_mul_cancel₀ h0, mul_one]

end Final

end GlobalTheory.GalLift.Assembly

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterConjHalfIdeleEqProdLocal
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IdemSumChar

open Formalism.L2.JoinChr

theorem locE_sum {D : D7} {ι : Type} (s : Finset ι) (f : ι → AE D)
    (hf : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i * f j = 0) (k : D.host.E) :
    locE D (∑ i ∈ s, f i) k = ∏ i ∈ s, locE D (f i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [locE]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha,
      ← ih fun i hi j hj hij => hf i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij]
    have h0 : f a * ∑ i ∈ s, f i = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun i hi => hf a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
        (fun h => ha (h ▸ hi))
    unfold locE
    linear_combination (-(incA D k - 1) * (incA D k - 1)) * h0

theorem char_eq_prod : ∀ (D : D7) (Q : Finset (Pl D.host.E)) (eQ : AE D), IsIdemSum eQ Q → ∀ (k : D.host.Eˣ) (y : (AE D)ˣ), (y : AE D) = Formalism.L2.JoinChr.locE D (cA D eQ) (k : D.host.E) → ∀ (c : (AE D)ˣ →* Circle) (ψ : Formalism.L2.Host.HChar D.host.E), ChrEq c ψ → ((c y : Circle) : ℂ) = ∏ P ∈ Q, ((ψ.locK (conjPl P) k : ℂˣ) : ℂ) := by
  intro D Q eQ h k y hy c ψ hψ
  classical
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  have hIP : ∀ P ∈ Q, Formalism.L2.NTheta.IsIdemAt (cA D (es P)) (conjPl P) := fun P hP =>
    GlobalTheory.MovedIdem.isIdemAt_conj (hes P hP) fun _ => Iff.rfl
  let g : Pl D.host.E → AE D := fun P => if P ∈ Q then cA D (es P) else 0
  have hg : ∀ P, g P * g P = g P := fun P => by
    by_cases hP : P ∈ Q
    · simp only [g, if_pos hP]; exact (hIP P hP).1.1
    · simp only [g, if_neg hP, mul_zero]
  have horth : ∀ P ∈ Q, ∀ P' ∈ Q, P ≠ P' → g P * g P' = 0 := fun P hP P' hP' hne => by
    simp only [g, if_pos hP, if_pos hP', ← map_mul]
    rw [idem_orth (idemAt_split (hes P hP)) (hes P hP) (hes P' hP') hne, map_zero]
  have hsum : cA D (∑ P ∈ Q, es P) = ∑ P ∈ Q, g P := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun P hP => by simp only [g, if_pos hP]
  have hy' : y = ∏ P ∈ Q, locU (hg P) k := by
    apply Units.ext
    rw [hy, Units.coe_prod, hsum, locE_sum Q g horth]
    rfl
  rw [hy', map_prod]
  have hcoe : ∀ (s : Finset (Pl D.host.E)) (u : Pl D.host.E → Circle),
      (((∏ P ∈ s, u P : Circle)) : ℂ) = ∏ P ∈ s, ((u P : Circle) : ℂ) := fun s u =>
    map_prod Circle.coeHom u s
  rw [hcoe]
  refine Finset.prod_congr rfl fun P hP => ?_
  have hpl : IsPlIdem D (g P) (conjPl P) := by
    simp only [g, if_pos hP]; exact GlobalTheory.HeckeDetChar.isPlIdem (hIP P hP)
  exact hψ.2 (conjPl P) (g P) hpl k (locU (hg P) k) (locU_val _ _)

end GlobalTheory.IdemSumChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantAdmissibleFormEqMulDiagonalInStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergInvariant_admissibleForm_eq_mul_diagonalIntegral : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (κ : Type) [Fintype κ] (l : ((κ ⊕ κ → AF F) → ℂ) →ₗ[ℂ] ℂ), l ∈ (adeleClass F).adm (κ ⊕ κ) →
      (∀ x y : κ → AF F, ∀ Φ ∈ schA F (κ ⊕ κ), l (schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) = l Φ) →
      ∀ μ : @MeasureTheory.Measure (κ → AF F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∃ c : ℂ, ∀ Φ ∈ schA F (κ ⊕ κ), l Φ = c * GlobalTheory.DiagSiegel.diagInt μ Φ := by
  first | exact @GlobalTheory.DiagUniq.eq_mul_diagInt | exact GlobalTheory.DiagUniq.eq_mul_diagInt | (intros; apply GlobalTheory.DiagUniq.eq_mul_diagInt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HookLogSumSubSizeTermLeLowerBoundStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hookLogSum_sub_sizeTerm_le_lowerBound : ∀ (D : D7) (L : SizeData₂ D) (Del h0 : ℕ) (Csz : ℝ) (j : Fin D.R.m), 8 ≤ Csz → Sizes D j L.sc.b → (∑ ρ, (ofRecord D L Del h0).logHook ((j : ℕ) + 1) ρ) - Csz * ((D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * (ofRecord D L Del h0).Lp) ≤ lowB D j L.sc.b := by
  first | exact @GlobalTheory.LowMainTerm.main_le_lowB | exact GlobalTheory.LowMainTerm.main_le_lowB | (intros; apply GlobalTheory.LowMainTerm.main_le_lowB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweFiniteLengthUniqueMaximalOfCyclic
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem howe_finiteLength_uniqueMaximal_of_cyclic : ∀ (T : Type) [Fintype T] [DecidableEq T] (R S : T → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ V), (∀ w, Good (a w)) → (∀ w w', w ≠ w' → ∀ Z Z' v, a w Z (a w' Z' v) = a w' Z' (a w Z v)) → ∀ (C : Submodule ℂ V) (α β α' β' : T → ℂ), (∀ w, QuadMod (a w) (α w) (β w) (α' w) (β' w) C ⊤) → (∀ B : ℚ, ∃ U : Submodule ℂ V, FiniteDimensional ℂ U ∧ ∀ μ : ∀ w, Ix (R w) (S w) → ℚ, (∀ w c, |μ w c| ≤ B) → (⨅ w, hwSub (a w) (μ w)) ≤ U ⊔ C) → (∃ (μ : ∀ w, Ix (R w) (S w) → ℚ) (v : V), (∀ w, v ∈ hwSub (a w) (μ w)) ∧ (∀ N : Submodule ℂ V, (∀ w, Stab (a w) N) → C ≤ N → v ∈ N → N = ⊤) ∧ (⨅ w, hwSub (a w) (μ w)) ≤ Submodule.span ℂ {v} ⊔ C) → HoweAlg a C := by
  intro T _ _ R S V _ _ a hG hc C α β α' β' hQ hAdm hCyc
  refine ⟨?_, ?_⟩
  · obtain ⟨B, hB⟩ := Places.multi_place_step T R S α β α' β'
    obtain ⟨U, hU, hUC⟩ := hAdm B
    let G : Submodule ℂ V := ⨆ (μ : ∀ w, Ix (R w) (S w) → ℚ) (_ : ∀ w c, |μ w c| ≤ B), ⨅ w, hwSub (a w) (μ w)
    have hGUC : G ≤ U ⊔ C := iSup_le fun μ => iSup_le fun h => hUC μ h
    refine ⟨Module.finrank ℂ U + 1, fun m N hN hNk => ?_⟩
    refine chain_length_le_finrank_add_one V G U C hU hGUC m N hN (fun k => (hNk k).2) ?_
    intro k l hkl
    have hQ' : ∀ w, QuadMod (a w) (α w) (β w) (α' w) (β' w) (N k) (N l) := fun w c d u _ =>
      ⟨(hNk k).2 (hQ w c d u Submodule.mem_top).1, (hNk k).2 (hQ w c d u Submodule.mem_top).2⟩
    obtain ⟨μ, hμB, v, hvl, hvhw, hvk⟩ :=
      hB V a hG hc (N k) (N l) (hN hkl) (fun w => (hNk k).1 w) (fun w => (hNk l).1 w) hQ'
    refine ⟨v, hvl, ?_, hvk⟩
    have hv : v ∈ ⨅ w, hwSub (a w) (μ w) := Submodule.mem_iInf _ |>.mpr hvhw
    exact (le_iSup_of_le μ (le_iSup_of_le hμB le_rfl) : (⨅ w, hwSub (a w) (μ w)) ≤ G) hv
  · intro N N' hN hCN hNt hN' hCN' hN't hsup
    obtain ⟨μ, v, hvhw, hgen, hmult⟩ := hCyc
    have hv : v ∈ ⨅ w, hwSub (a w) (μ w) := Submodule.mem_iInf _ |>.mpr hvhw
    have hv2 : v ∈ (N ⊔ N') ⊓ ⨅ w, hwSub (a w) (μ w) := ⟨by rw [hsup]; exact Submodule.mem_top, hv⟩
    have hsp := hw_joint_split T R S V a hG hc N N' hN hN' μ hv2
    obtain ⟨n, hn, n', hn', hnn⟩ := Submodule.mem_sup.mp hsp
    obtain ⟨y, hy, c, hc', hyc⟩ := Submodule.mem_sup.mp (hmult hn.2)
    obtain ⟨x, rfl⟩ := Submodule.mem_span_singleton.mp hy
    by_cases hx : x = 0
    · subst hx
      have hnC : n = c := by rw [← hyc]; simp
      have hvN' : v ∈ N' := by
        rw [← hnn]; exact N'.add_mem (hCN' (hnC ▸ hc')) hn'.1
      exact hN't (hgen N' hN' hCN' hvN')
    · have hvN : v ∈ N := by
        have h1 : x • v ∈ N := by
          have : x • v = n - c := by rw [← hyc]; simp
          rw [this]; exact N.sub_mem hn.1 (hCN hc')
        have := N.smul_mem x⁻¹ h1
        rwa [smul_smul, inv_mul_cancel₀ hx, one_smul] at this
      exact hNt (hgen N hN hCN hvN)

end GlobalTheory.HoweR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceDoubledUnitaryVacuumTensorEigenStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_doubledUnitary_vacuumTensor_eigen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.V'.J) (dbl (incM F G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (cA σ) (dbl (incM F G.W.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (dbl (incM F G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M'.vac v) R →
    ∀ g ∈ GlobalTheory.InertDbl.KAtD σ G.W v, ∃ c : ℂ, omd g (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      c • GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  first | exact @GlobalTheory.InertDblLine.line | exact GlobalTheory.InertDblLine.line | (intros; apply GlobalTheory.InertDblLine.line <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveICRows
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Indef Formalism.IndefR.Cx GlobalTheory.BigTop GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.BigTop.Fun

theorem iC_base_factor_of_rows : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), p.Rows → Function.Injective ((p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0) ∧ ∀ (t : Tup p) (y : Fin ((Df p).dQ t) → D.what₂.LL), (p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0 (cpt p.P.A3.fam3.base3.v0.embedding (((p.S false).ι t).mulVec y)) = (p.R.toCx3 p.F).iC p.F.cr false t (cpt p.P.A3.fam3.base3.v0.embedding y) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hp
  have hCx := Formalism.IndefR.Links.complex_data_conditions_base_level_of_primitive_links hp.ok hp.sep p.charW hp.prim
  have h2 := (hCx.what₂ false).1
  have hr := hCx.ratMu false
  refine ⟨h2.1, fun t y => ?_⟩
  have hspec := relMat_spec ((p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0)
    ((p.R.toCx3 p.F).iC p.F.cr false t)
    (fun k => by rw [← (h2.2.1 t).2]; exact LinearMap.mem_range_self _ _)
  show (p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0
      (cpt p.P.A3.fam3.base3.v0.embedding ((kMat p.P.A3.fam3.base3.v0.embedding ((p.R.toCx3 p.F).rowMatC p.F.cr false t)).mulVec y)) = _
  rw [cpt_mulVec, kMat_map _ (hr t)]
  exact hspec _

end GlobalTheory.BigTop.Fun

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTotallySplitRationalPrimeOfSplitsCompletelyStatement
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTotallySplitRationalPrime_of_splitsCompletely : ∀ (E : Type) [Field E] [NumberField E] (g : ℕ), SplitsCompletely E g → GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g := by
  first | exact @GlobalTheory.SplitLevelsBall.isTotallySplitPrime_of_splitsCompletely | exact GlobalTheory.SplitLevelsBall.isTotallySplitPrime_of_splitsCompletely | (intros; apply GlobalTheory.SplitLevelsBall.isTotallySplitPrime_of_splitsCompletely <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KroneckerCharacterFrameSecondStatement
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kronecker_character_frame_second : GlobalTheory.UCls.MassBound → GlobalTheory.UCls.TorusBound → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → GoodW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) → latW U (wtZ a n) ≠ ⊥ → slopeMax_sq (normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n)) (latW U (wtZ a n)) ≤ 2 * lamSup D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re ((absA Dw a : ℕ) : ℝ) ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 2 * Real.log (supConst D.host.E D.R.r D.host.d l.M (((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1)) + Real.log |(discr c.F : ℝ)| / (Module.finrank ℚ c.F : ℝ) := by
  first | exact @GlobalTheory.LamMuMax.slopeMax_le | exact GlobalTheory.LamMuMax.slopeMax_le | (intros; apply GlobalTheory.LamMuMax.slopeMax_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSumOfPublishedInputsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_sum_of_published_inputs : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.RowClaim.SumOKK := by
  first | exact @GlobalTheory.RowClaim.rowSum_of_hypotheses | exact GlobalTheory.RowClaim.rowSum_of_hypotheses | (intros; apply GlobalTheory.RowClaim.rowSum_of_hypotheses <;> assumption)
end

