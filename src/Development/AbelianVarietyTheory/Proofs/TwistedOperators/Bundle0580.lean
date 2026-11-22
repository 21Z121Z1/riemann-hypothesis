import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0559
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0503
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0451
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0272
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0173
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0565
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1729
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0450
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0456
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0461
import Formalism.LocalToGlobal.Divisibility.TiedLemmas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0471
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0486
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0244
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0379
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0485
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0563
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0177
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonvanishingThetaTowerBottomRung
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section
namespace GlobalTheory.AscBottom

variable {D : D7}

theorem rapidDec_star {V : HSp D} {f : GA D V → ℂ} (h : RapidDec V f) : RapidDec V (star f) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun γ hγ g => by simp [Pi.star_apply, h1 γ hγ g], h2.star, fun N => ?_⟩
  obtain ⟨C, hC⟩ := h3 N
  exact ⟨C, fun g => by simpa [Pi.star_apply, norm_star] using hC g⟩

theorem rung0 (hF : FockTot) : Rung0 := by
  intro D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu hper h
  have hm : 0 < D.R.m := by omega
  obtain ⟨hom, homC, -, hev, hdep, hdn, hpart, -, -, -⟩ := GlobalTheory.T.gridConjugation_weilData_inverseCharacter D hq T L μ0 hL sc G W M hM 0 hm
  obtain ⟨hchT, hchS⟩ := hev ⟨0, rfl⟩
  obtain ⟨hrap, hch⟩ := hΨ
  obtain ⟨f, hf, hΨ0⟩ := hch 0 hm
  have hhf := (hM.row 0 (Nat.zero_le _)).haar_fund
  let vT : GlobalTheory.Unf.Vol (Yc D 0) := ⟨M.ν (.grid 0 0), M.fd (.grid 0 0), hhf.1, hhf.2⟩
  let ρ₀ : G.RealVec := fun _ => 0
  let Φ₀ : G.Datum := fun _ => default
  have hu' : RapidDec (Yc D 0) (star u) := rapidDec_star (hu ρ₀ Φ₀ 0 (Nat.zero_le _))
  have hφ : RapidDec (G.V (.core 1)) (star (Ψ 1)) := rapidDec_star (hrap 1 (by omega))

  set a := G.ch.chi (D.R.m - 0) with ha
  have homR : IsWeilDatumO W.ψ _ _ a⁻¹ (a⁻¹ * L.eta) (omRow W 0) := by
    have := hom
    rwa [hchS, hchT] at this
  have homX : IsWeilDatumO W.ψ _ _ a⁻¹ (a⁻¹ * L.eta * L.eta⁻¹) (omCore W 0) := by
    rw [mul_inv_cancel_right]; exact homC
  have hHeta : IsHeckeChar D L.eta := by
    have := GlobalTheory.HeckeCharsOfSquare.isHeckeChar_mul (GlobalTheory.HeckeCharsOfSquare.isHeckeChar_inv homR.hecS) homR.hecT
    rwa [inv_inv, mul_inv_cancel_left] at this
  have hReta : ResEta D L.eta (negSp F.Lz).rank := by
    have h1 := Formalism.L2.Theta.resEta_mul (Formalism.L2.Theta.resEta_inv homC.resT) homR.resT
    rw [inv_inv, mul_inv_cancel_left] at h1
    refine Formalism.L2.Theta.resEta_parity h1 ?_
    have hr : (G.V (.grid 0 0)).rank + 1 = (G.V (.core 0)).rank := by
      have := F.oz.rank_add; rw [F.rk] at this; exact this
    show _ = F.Lz.rank % 2
    rw [F.rk]
    omega
  obtain ⟨omz, homz⟩ := GlobalTheory.WeilDatumExistence.weilDatumExists D (G.V (.core 1)) (negSp F.Lz) W.ψ a⁻¹⁻¹ L.eta W.ψ_std
    (GlobalTheory.HeckeCharsOfSquare.isHeckeChar_inv homX.hecS) hHeta (Formalism.L2.Theta.resEta_inv homX.resS) hReta

  have hΞ : VacG W.ψ _ _ (latCore G 0) (star f) := (hdep f).1 hf
  have hlift : liftT (omCore W 0) (v 1).μ (v 1).𝓕 (star (Ψ 1)) (star f) = star (Ψ 0) := by
    rw [hΨ0]; exact (hdn v f (Ψ 1)).symm
  have hint : (∫ x in vT.𝓕, liftT (omCore W 0) (F.jac v 0 h).v0.μ (F.jac v 0 h).v0.𝓕 (star (Ψ 1)) (star f) (F.oz.emb (x, 1)) *
      star u x ∂vT.μ) ≠ 0 := by
    have e : (fun x : GA D (Yc D 0) => liftT (omCore W 0) (F.jac v 0 h).v0.μ (F.jac v 0 h).v0.𝓕 (star (Ψ 1)) (star f)
        (F.oz.emb (x, 1)) * star u x) = fun x => (starRingEnd ℂ) (Ψ 0 (stabilizerEmbedding G.sp.dec0 x) * u x) := by
      funext x
      have hl : liftT (omCore W 0) (F.jac v 0 h).v0.μ (F.jac v 0 h).v0.𝓕 (star (Ψ 1)) (star f) = star (Ψ 0) := hlift
      rw [hl, hE.bot x, map_mul]; rfl
    rw [e, integral_conj]
    intro h0
    apply hper
    have := congrArg (starRingEnd ℂ) h0
    rw [Complex.conj_conj, map_zero] at this
    exact this
  obtain ⟨Φ', Φz, hΦ', hΦz, hne⟩ := GlobalTheory.T.lastSeesaw_periodNonvanishing D W.ψ (F.jac v 0 h) (G.V (.core 0)) (Yc D 0) F.Lz F.oz (latRow G 0) (ΓL 0)
    (latCore G 0) F.rk (hG.last h) (F.ζ 0) a⁻¹ (a⁻¹ * L.eta) L.eta (omRow W 0) (omCore W 0) omz homR homX homz vT
    (star (Ψ 1)) (star u) hφ hu' (star f) hΞ hint

  let ℓ : (WO (G.V (.grid 1 0)) (G.V (.grid 0 0)) → ℂ) → ℂ := fun Φ =>
    (F.jac v 0 h).per W.ψ (F.ζ 0) omz (star (Ψ 1)) (liftS (omRow W 0) vT.μ vT.𝓕 (star u) Φ) Φz
  have hT : Tame W.ψ _ _ ℓ :=
    (GlobalTheory.T.thetaLift_periods_isTameThetaFunctional D W.ψ (Yc D 0) vT (star u) hu').2 0 (F.jac v 0 h) a⁻¹ (a⁻¹ * L.eta) (omRow W 0) homR (negSp F.Lz)
      (F.ζ 0) a⁻¹⁻¹ L.eta omz homz (star (Ψ 1)) Φz hφ hΦz.1
  have hK : ∃ κ P, ℓ (star (W.fock (.chi 0 0) (W.cosVec 0 κ) P)) ≠ 0 := by
    by_contra hno
    push_neg at hno
    exact hne (hF D hq T L μ0 hL sc G W M hM ⟨0, hm⟩ ℓ hT hno Φ' hΦ')
  obtain ⟨κ, P, hκP⟩ := hK
  let ρ : G.RealVec := Function.update ρ₀ ⟨0, hm⟩ P
  let Φ : G.Datum := Function.update Φ₀ ⟨0, hm⟩ κ
  refine ⟨a⁻¹⁻¹, omz, homz, ρ, Φ, Φz, hΦz, ?_⟩
  have hp := hpart ρ Φ u
  have hd : W.datum ρ Φ ⟨0, hm⟩ = W.fock (.chi 0 0) (W.cosVec 0 κ) P := by
    show W.fock (.chi 0 0) (W.cosVec 0 (Φ ⟨0, hm⟩)) (ρ ⟨0, hm⟩) = _
    simp only [ρ, Φ, Function.update_self]
  rw [hd] at hp
  change ℓ _ ≠ 0 at hκP
  convert hκP using 2
  exact hp

end GlobalTheory.AscBottom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OffPlacesPartMovedLevelKeepsStandardHomLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.OffPartLattice

open GlobalTheory.StdFrames

variable {D : D7}

open Classical in

theorem cpt_idemSum {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) (Q : Pl D.host.E) :
    cpt Q (toEAf D e) = if Q ∈ P then 1 else 0 := by
  classical
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [map_sum, map_sum]
  have h : ∀ PP ∈ P, cpt Q (toEAf D (es PP)) = if Q = PP then 1 else 0 := fun PP hP => by
    by_cases hq : Q = PP
    · subst hq; rw [if_pos rfl]; exact (cpt_of_isIdemAt (hes _ hP)).1
    · rw [if_neg hq]; exact (cpt_of_isIdemAt (hes PP hP)).2 Q hq
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq]

open Classical in

theorem cpt_cA_idemSum (V : HSp D) {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) (Q : Pl D.host.E) :
    cpt Q (toEAf D (cA D e)) = if GlobalTheory.IdemSupport.cP Q ∈ P then 1 else 0 := by
  classical
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [map_sum, map_sum, map_sum]
  have hc := (GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.2
  have h : ∀ PP ∈ P, cpt Q (toEAf D (cA D (es PP))) = if GlobalTheory.IdemSupport.cP Q = PP then 1 else 0 := fun PP hP => by
    have hi := hc PP (GlobalTheory.IdemSupport.cP PP) (es PP) (hes PP hP) ((GlobalTheory.IdemSupport.isConjPl_iff PP _).2 rfl)
    by_cases hq : GlobalTheory.IdemSupport.cP Q = PP
    · subst hq
      rw [if_pos rfl, cP_cP] at *
      exact (cpt_of_isIdemAt hi).1
    · rw [if_neg hq]
      exact (cpt_of_isIdemAt hi).2 Q fun h' => hq (by rw [h', cP_cP])
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq]

theorem cpt_pair_zero (V : HSp D) {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) (Q : Pl D.host.E)
    (hQ : ∀ w ∈ P, Q.under (𝓞 D.host.F) ≠ w.under (𝓞 D.host.F)) : cpt Q (toEAf D (e + cA D e)) = 0 := by
  rw [map_add, map_add, cpt_idemSum he, cpt_cA_idemSum V he, if_neg, if_neg, add_zero]
  · exact fun h => hQ _ h (GlobalTheory.IdemSupport.under_cP Q).symm
  · exact fun h => hQ Q h rfl

theorem cpt_pair_one (V : HSp D) {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) (Q : Pl D.host.E)
    (hQ : ∃ w ∈ P, Q.under (𝓞 D.host.F) = w.under (𝓞 D.host.F)) : cpt Q (toEAf D (e + cA D e)) = 1 := by
  have h0 : cpt Q (toEAf D e) * cpt Q (toEAf D (cA D e)) = 0 := by
    rw [← map_mul, ← map_mul, he.2, map_zero, map_zero]
  rw [cpt_idemSum he, cpt_cA_idemSum V he] at h0
  rw [map_add, map_add, cpt_idemSum he, cpt_cA_idemSum V he]
  obtain ⟨w, hw, hu⟩ := hQ
  rcases GlobalTheory.IdemSupport.eq_or_eq_cP hu with rfl | rfl
  · rw [if_pos hw, one_mul] at h0
    rw [if_pos hw, h0, add_zero]
  · rw [cP_cP, if_pos hw, mul_one] at h0
    rw [cP_cP, if_pos hw, h0, zero_add]

end GlobalTheory.OffPartLattice

namespace GlobalTheory.OffPartLattice

open GlobalTheory.StdFrames Matrix

variable {D : D7}

theorem mix_map' {A B : Type} [CommRing A] [CommRing B] {n : Type} [DecidableEq n] (ψ : A →+* B) (f : A)
    (a : Matrix n n A) :
    (f • a + (1 - f) • (1 : Matrix n n A)).map ψ = ψ f • a.map ψ + (1 - ψ f) • (1 : Matrix n n B) := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem mix_conj' {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (f : A) (β : GL n A)
    (y : Matrix n n A) :
    β.val * (f • y + (1 - f) • (1 : Matrix n n A)) * (β⁻¹).val =
      f • (β.val * y * (β⁻¹).val) + (1 - f) • (1 : Matrix n n A) := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, Units.mul_inv]

theorem finE_cutPart {a : AE D} (h : a * a = a) (hc : cA D a = a) (V : HSp D) (g : GA D V) :
    (Lev.finE V (cutPart a V g)).val = toEAf D a • (Lev.finE V g).val + (1 - toEAf D a) • (1 : Matrix _ _ (Lev.EAf D)) := by
  change (mt V (cutPart a V g)).map (toEAf D) = _
  rw [mt_cutPart h hc, mix_map']
  rfl

theorem inBasis_mix {n : ℕ} (β X Y : GL (Fin n) (Lev.EAf D)) (c : Lev.EAf D)
    (hX : X.val = c • Y.val + (1 - c) • (1 : Matrix (Fin n) (Fin n) (Lev.EAf D))) (Q : Pl D.host.E) :
    (cpt Q c = 0 → inBasis rfl β Q X = 1) ∧ (cpt Q c = 1 → inBasis rfl β Q X = inBasis rfl β Q Y) := by
  have hM : (β⁻¹ * X * β).val = c • (β⁻¹ * Y * β).val + (1 - c) • (1 : Matrix (Fin n) (Fin n) (Lev.EAf D)) := by
    have := mix_conj' c β⁻¹ Y.val
    rw [inv_inv] at this
    rw [Units.val_mul, Units.val_mul, hX, this, Units.val_mul, Units.val_mul]
  have h1 : (β⁻¹ * 1 * β : GL (Fin n) (Lev.EAf D)) = 1 := by group
  constructor
  · intro h0
    rw [← map_one (inBasis rfl β Q)]
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [inBasis_apply, inBasis_apply, hM, h1]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub, map_one, h0, zero_mul,
      zero_add, sub_zero, one_mul, Units.val_one]
  · intro h0
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [inBasis_apply, inBasis_apply, hM]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub, map_one, h0, one_mul,
      sub_self, zero_mul, add_zero]

theorem mulVec_mem_hatL_of_St {n : ℕ} {β : GL (Fin n) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hβ : IsFrame β Λ) {x : GL (Fin n) (Lev.EAf D)} (hx : x ∈ St β) (v : Fin n → Lev.EAf D)
    (hv : v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) : x.val *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  obtain ⟨y, rfl⟩ := hx
  rw [hβ] at hv ⊢
  intro i
  have e0 : β⁻¹ * frGL β y = intGL D.host.F D.host.E n y * β⁻¹ := by
    simp only [frGL, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.conj_apply]
    group
  have e : ((β⁻¹ : GL (Fin n) (Lev.EAf D)) : Matrix (Fin n) (Fin n) (Lev.EAf D)) * (frGL β y).val =
      (intGL D.host.F D.host.E n y).val * (β⁻¹ : GL (Fin n) (Lev.EAf D)).val := by
    rw [← Units.val_mul, e0, Units.val_mul]
  rw [Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (y.val i k).2 (hv k)

theorem actO_mem_latO_of (S T : HSp D) (g : GA D S) (h : GA D T)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hg : ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS, (mt S g).map (toEAf D) *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS)
    (hh : ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT, (mt T h).map (toEAf D) *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT)
    (u : WO S T)
    (hu : u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :
    actO S T g h u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hu
    have e := GlobalTheory.AdelicLatMove.rankOne_pure S T a s t 1 α
    rw [mul_one] at e
    rw [← e, GlobalTheory.AdelicLatMove.actO_rankOne]
    exact GlobalTheory.AdelicLatMove.rankOne_mem_latO S T ΛS ΛT a ha _
      (hg _ (GlobalTheory.AdelicLatMove.pure_mem_hatL ΛS 1 (one_mem _) s hs)) _
      (hh _ (GlobalTheory.AdelicLatMove.pure_mem_hatL ΛT α hα t ht))
  | zero => simp only [actO, Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => simp only [actO, Matrix.mul_add, Matrix.add_mul] at hy hz ⊢; exact add_mem hy hz
  | neg y _ hy => simp only [actO, Matrix.mul_neg, Matrix.neg_mul] at hy ⊢; exact neg_mem hy

end GlobalTheory.OffPartLattice

namespace GlobalTheory.OffPartLattice

open GlobalTheory.StdFrames Matrix

variable {D : D7}

theorem isFrame_moved {n : ℕ} (Λ₀ Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (β Uf : GL (Fin n) (Lev.EAf D))
    (hβ : IsFrame β Λ) (hU : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ₀ ↔ Uf.val *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    IsFrame (Uf⁻¹ * β) Λ₀ := by
  intro x
  rw [hU, hβ]
  have e : ((Uf⁻¹ * β)⁻¹ : GL (Fin n) (Lev.EAf D)).val = (β⁻¹ : GL (Fin n) (Lev.EAf D)).val * Uf.val := by
    rw [_root_.mul_inv_rev, inv_inv, Units.val_mul]
  rw [e, ← Matrix.mulVec_mulVec]

theorem finE_cut_mem_St (V : HSp D) (β Uf K : GL (Fin V.rank) (Lev.EAf D)) (g : GA D V) (hg : Lev.finE V g = Uf⁻¹ * K * Uf)
    {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P)
    (hK : ∀ Q : Pl D.host.E, (∀ w ∈ P, Q.under (𝓞 D.host.F) ≠ w.under (𝓞 D.host.F)) →
      inBasis rfl β Q K ∈ GlobalTheory.SplitWeil.KO (Kw Q) (Fin V.rank)) :
    Lev.finE V (cutPart (1 - (e + cA D e)) V g) ∈ St (Uf⁻¹ * β) := by
  have hf := idem_conj_sum (GlobalTheory.PlaceVec.idemSum_mul_self he) he.2
  have h2 := idem_compl hf
  have hX := finE_cutPart h2.1 h2.2 V g
  refine StabilizerBasis.GlobalTheory.CompanionTheory.StabBasis.mem_St_of_inBasis_mem_KO _ _ fun Q => ?_
  have hm := inBasis_mix (Uf⁻¹ * β) _ _ _ hX Q
  by_cases hQ : ∃ w ∈ P, Q.under (𝓞 D.host.F) = w.under (𝓞 D.host.F)
  · rw [hm.1 (by simp only [map_sub, map_one, cpt_pair_one V he Q hQ, sub_self])]
    exact one_mem _
  · push_neg at hQ
    rw [hm.2 (by simp only [map_sub, map_one, cpt_pair_zero V he Q hQ, sub_zero])]
    have e1 : (Uf⁻¹ * β)⁻¹ * (Uf⁻¹ * K * Uf) * (Uf⁻¹ * β) = β⁻¹ * K * β := by group
    have e2 : inBasis rfl (Uf⁻¹ * β) Q (Lev.finE V g) = inBasis rfl β Q K := by
      refine Units.ext (Matrix.ext fun a b => ?_)
      rw [inBasis_apply, inBasis_apply, hg, e1]
    rw [e2]
    exact hK Q hQ

end GlobalTheory.OffPartLattice

open GlobalTheory.OffPartLattice Matrix in

theorem GlobalTheory.OffPartLattice.offPart_keeps_stdLatO : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T},
    t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ u : WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)),
      u ∈ stdLatO S (.top t (j + 1)) ↔ ∃ u₀ ∈ stdLatO S (.top t (j + 1)),
        u = actO _ _ (cutPart (1 - (e + cA D e)) (G.V (.top (j + 1)))
          ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))))) 1 u₀ := by
  intro D T L sc G W U S t _ Φ β j hj k hk e he u
  have hdef : DefNode D.R.m (.top (j + 1)) := by show j + 1 ≤ D.R.m; omega
  have hfr := isFrame_moved (colLat (S.N.fr (.top (j + 1)))) (G.Λ (.top (j + 1))) (S.βp (j + 1))
    (Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1) (S.βp_is (j + 1) hdef) (S.N.u_lat _ hdef)
  have hk2 : finG (G.V (.top (j + 1))) k ∈ prodLev (S.βp (j + 1)) (locPl G t) (fun w => topRank_eq G t w hj.le)
      (fun w => (S.term t Φ β w).pr _ j.succ_pos hj) := hk
  have hSt := finE_cut_mem_St (G.V (.top (j + 1))) (S.βp (j + 1)) (Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1)
    (finG (G.V (.top (j + 1))) k) (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D _)
    (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]; rfl) he (fun Q hQ => by
      have h3 := (Subgroup.mem_inf.1 hk2).2
      rw [Subgroup.mem_iInf] at h3
      have h4 := h3 Q
      rw [Subgroup.mem_iInf] at h4
      exact Subgroup.mem_comap.1 (h4 hQ))
  have hpres : ∀ y : GA D (G.V (.top (j + 1))),
      Lev.finE (G.V (.top (j + 1))) y ∈ St ((Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1)⁻¹ * S.βp (j + 1)) →
      ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.top (j + 1)))),
        (mt (G.V (.top (j + 1))) y).map (toEAf D) *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.top (j + 1)))) :=
    fun y hy x hx => mulVec_mem_hatL_of_St hfr hy x hx
  have h1 : ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (S.N.latT (.top t (j + 1))),
      (mt (G.pT (.top t (j + 1) : Pair T)) 1).map (toEAf D) *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (S.N.latT (.top t (j + 1))) := by
    intro x hx
    rw [GlobalTheory.AdelicLatMove.mt_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
    exact hx
  have key : ∀ g₂ : GA D (G.V (.top (j + 1))),
      Lev.finE (G.V (.top (j + 1))) g₂ ∈ St ((Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1)⁻¹ * S.βp (j + 1)) →
      (u ∈ stdLatO S (.top t (j + 1)) ↔ ∃ u₀ ∈ stdLatO S (.top t (j + 1)),
        u = actO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) g₂ 1 u₀) := by
    intro g₂ hg₂
    constructor
    · intro hu
      refine ⟨actO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) g₂⁻¹ 1⁻¹ u, ?_,
        (GlobalTheory.AdelicLatMove.actO_actO_inv (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) g₂ 1 u).symm⟩
      exact actO_mem_latO_of (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) g₂⁻¹ 1⁻¹
        (colLat (S.N.fr (.top (j + 1)))) (S.N.latT (.top t (j + 1)))
        (hpres _ (by rw [map_inv]; exact inv_mem hg₂)) (by rw [inv_one]; exact h1) u hu
    · rintro ⟨u₀, hu₀, rfl⟩
      exact actO_mem_latO_of (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) g₂ 1
        (colLat (S.N.fr (.top (j + 1)))) (S.N.latT (.top t (j + 1))) (hpres _ hg₂) h1 u₀ hu₀
  exact key _ hSt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OtherInstanceFormFlagPairingIntegralOnFrameLatti
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SeeConjRead

noncomputable section
namespace GlobalTheory.SeeConjChar
open Classical

theorem hT_pairAt_int : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β : GL (Fin (Yc D 0).rank) (EAf D)), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ (PP : Pl D.host.E) (a : Fin (Yc D 0).rank) (z : Fin (Yc D 0).rank → EAf D), (∀ i, Matrix.mulVec (β⁻¹).val z i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → GlobalTheory.SeeConjChar.hT X h (pairAt X h PP a) z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D X h β hβ PP a z hz
  have hLf := GlobalTheory.KgFrame.Lf_eq D
  have hzL : z ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf := by
    rw [hLf]
    exact (hβ z).2 hz
  set S : Set (Fin (Yc D 0).rank → EAf D) := {v | v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf} with hS
  have h0 : (0 : Fin (Yc D 0).rank → EAf D) ∈ S := by
    show (0 : Fin (Yc D 0).rank → EAf D) ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf
    exact zero_mem _
  obtain ⟨hef, hz0, hbw⟩ := X.vectorsInLattice
  have he : ∀ a, e0T X h a ∈ S := GlobalTheory.SeeConjRead.cast_fun_mem_Lf h X.e0 (fun a => (hef a).1)
  have hf : ∀ a, f0T X h a ∈ S := GlobalTheory.SeeConjRead.cast_fun_mem_Lf h X.f0 (fun a => (hef a).2)
  have hb : ∀ a, bwT X h a ∈ S := GlobalTheory.SeeConjRead.cast_fun_mem_Lf h X.bw (fun a => (hbw a).1)
  have hbd : ∀ a, bwdT X h a ∈ S := GlobalTheory.SeeConjRead.cast_fun_mem_Lf h X.bwd (fun a => (hbw a).2)
  have hzz : z0T X h ∈ S := GlobalTheory.SeeConjRead.cast_mem_Lf h X.z0 hz0
  have hv : pairAt X h PP a ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf := by
    show pairAt X h PP a ∈ S
    unfold pairAt
    split_ifs
    · exact GlobalTheory.SeeConjRead.flagV_mem S h0 _ _ _ _ _ _ _ hf he hbd hzz a
    · exact GlobalTheory.SeeConjRead.flagV_mem S h0 _ _ _ _ _ _ _ hf he (fun i => hb _) hzz a
  unfold hT
  exact intAf_cast X h _ (Formalism.L2.SG.Pf.unitaryCongruence.hA_int _ (GlobalTheory.SeeConjRead.cast_mem_Lf h.symm _ hv)
    (GlobalTheory.SeeConjRead.cast_mem_Lf h.symm _ hzL))

end GlobalTheory.SeeConjChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankPiLeAleph0
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

theorem GlobalTheory.SquareAgree.rank_pi_le_aleph0 : GlobalTheory.Published.HoweDualityUnitary → GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    Module.rank ℂ Pi ≤ Cardinal.aleph0 := by
  intro _ _ _ D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB _ _ hO hT R Rf _ Pm rf rl p p' hm
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hO.psi ▸ hT.base.std
  let S := GlobalTheory.WeilM.schA D.host.F (Fin W.rank × Fin (W.rank + W₁.rank))
  let T : S →ₗ[ℂ] (WO W X → ℂ) :=
    { toFun := fun Φ x => GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho ψ (cA.symm x) Φ.1)
      map_add' := fun Φ Ψ => funext fun x => by
        have e : Γ.M.co.rho ψ (cA.symm x) (Φ.1 + Ψ.1) = Γ.M.co.rho ψ (cA.symm x) Φ.1 + Γ.M.co.rho ψ (cA.symm x) Ψ.1 := by
          funext z; simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.add_apply]; ring
        simp only [Submodule.coe_add, Pi.add_apply, e]
        exact GlobalTheory.WeilM.thetaSum_add _ (GlobalTheory.HeisSchA.rho_mem_schA Γ.M ψ hstd _ _ Φ.2) (GlobalTheory.HeisSchA.rho_mem_schA Γ.M ψ hstd _ _ Ψ.2)
      map_smul' := fun c Φ => funext fun x => by
        have e : Γ.M.co.rho ψ (cA.symm x) (c • Φ.1) = c • Γ.M.co.rho ψ (cA.symm x) Φ.1 := by
          funext z; simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul]; ring
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, e]
        exact GlobalTheory.WeilM.thetaSum_smul _ c _ }
  let Q := (algD Γ.M Bs.ψ Bs.emb).comap S.subtype
  have hle : algF ψ θ true A B ≤ Q.map T := by
    intro Φ hΦ
    obtain ⟨ΦD, hD, hDat⟩ := hO.algA Φ hΦ
    refine ⟨⟨ΦD, hDat.1⟩, hD, funext fun x => ?_⟩
    have := hDat.2 (cA.symm x)
    rw [AddEquiv.apply_symm_apply] at this
    exact this
  have hQ : Module.rank ℂ Q ≤ Module.rank ℂ (algD Γ.M Bs.ψ Bs.emb) := by
    rw [(Submodule.equivMapOfInjective S.subtype Subtype.val_injective Q).rank_eq]
    exact Submodule.rank_mono (Submodule.map_comap_le _ _)
  have hD : Module.rank ℂ (algD Γ.M Bs.ψ Bs.emb) ≤ Cardinal.aleph0 :=
    GlobalTheory.T.rank_algebraicData_schrodingerModel_le_aleph0 Γ.M Bs.ψ Bs.emb hT.geo.hM (GlobalTheory.T.rank_polynomialFock_schrodingerModel_le_aleph0 Bs Γ.M hT.base hT.geo.hV hT.geo.hW hT.geo.hM) (fun v => GlobalTheory.T.rank_schwartzBruhat_finitePlaceCompletion_le_aleph0 v _)
  calc Module.rank ℂ Pm = Module.rank ℂ (⊤ : Submodule ℂ Pm) := (rank_top ℂ Pm).symm
    _ = Module.rank ℂ ((algF ψ θ true A B).map p) := by rw [hm.mapA.onto]
    _ ≤ Module.rank ℂ (algF ψ θ true A B) := rank_map_le _ _
    _ ≤ Module.rank ℂ (Q.map T) := Submodule.rank_mono hle
    _ ≤ Module.rank ℂ Q := rank_map_le _ _
    _ ≤ _ := hQ.trans hD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestAtRealisationOfHilbertModels
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowClaim

theorem GlobalTheory.RowTest.rowTest_realisation : GlobalTheory.Published.CuspRapidDecay → LinK → InjK → ConstK → SumOKK → Formula2K → SumRatK → RatioK → ∃ CF0 : ℝ, ∀ ε CF : ℝ, CF0 ≤ CF → ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x → ∀ (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.RowClaim.HidaSetting large₂ R.toRealDat F.lv2 → (∃ ch : GlobalTheory.RowTest.Choice R.toRealDat, ch.Is ∧ ch.AtScale CF large₂.sc.b ∧ ch.FieldOK) → Formalism.IndefR.Rat.RowTest (R.toCx3 F) := by
  intro hC hL hI hCo hS hF hSR hR
  obtain ⟨CF0, hCF0⟩ := GlobalTheory.T.rowTest_hilbertModels_of_choiceClaims hC hL hI hCo hS hF hSR hR
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx₀⟩ := hCF0 ε CF hCF
  refine ⟨x₀, fun D large₂ hε hx G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hSet hch => ?_⟩
  exact GlobalTheory.T.rowTest_complexSide_of_hilbert_models D G Pl0 I0 T0 A3 Ks R F (hx₀ D large₂ hε hx G Pl0 T0 _ Ks R.toRealDat F.lv2 hSet hch)
end

