import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0518
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspRapidDecayOfSobolev
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0513
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemGluedIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0426
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0388
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0302
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0373
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0365
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0503
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0408
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MulVecSingleAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0392
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0197
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0502
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0279
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0191
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0512
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0421
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0341
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0221
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0181
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0224
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1500
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0971
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0167
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0255
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0037

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrbitSumModerateGrowth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ENNReal NNReal

set_option maxHeartbeats 1000000

namespace GlobalTheory.Unf

theorem orbit_sum_moderate_growth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (vW : Vol W) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∃ (C : ℝ) (A : ℕ), ∀ g : GA D V, ∫⁻ p in vN.𝓝 ×ˢ vW.𝓕, ∑' y : Orb W x₀, ‖G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) y.1‖ₑ ∂(vN.ν.prod vW.μ) ≤ ENNReal.ofReal (C * height V g ^ A) := by
  intro D ψ V V₀ W ρ d χV χW om om' hw hw' vS vN vW x₀ G Φ hG hΦ
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag V (isIsoSub_e d)
  haveI := vN.unit.1
  haveI := vW.haar
  obtain ⟨C, A, hC⟩ := GlobalTheory.T.thetaTermSeries_summable_moderateGrowth_uniform D ψ V V₀ W ρ d χV χW om om' hw hw' vS Φ hΦ
  obtain ⟨B, hBd⟩ := hG.2.2 A
  have hB0 : 0 ≤ B := (mul_nonneg (norm_nonneg _) (pow_nonneg (quotHeight_pos W 1).le _)).trans (hBd 1)
  have hfin : (vN.ν.prod vW.μ) (vN.𝓝 ×ˢ vW.𝓕) ≠ ⊤ := by
    rw [Measure.prod_prod, vN.unit.2.2, one_mul]
    exact GlobalTheory.Chain.LiftReg.vol_ne_top vW.haar vW.fund
  have hK0 : 0 ≤ max C 0 * B := mul_nonneg (le_max_right _ _) hB0
  have hm0 : 0 ≤ ((vN.ν.prod vW.μ) (vN.𝓝 ×ˢ vW.𝓕)).toReal := ENNReal.toReal_nonneg
  refine ⟨max C 0 * B * ((vN.ν.prod vW.μ) (vN.𝓝 ×ˢ vW.𝓕)).toReal, A, fun g => ?_⟩
  have hg0 : 0 ≤ height V g ^ A := pow_nonneg (height_pos V g).le _
  have hpt : ∀ (n : flagN d) (h : GA D W),
      ∑' y : Orb W x₀, ‖G h * term ψ d W vS (om (n.1 * g, h) Φ) y.1‖ₑ ≤
        ENNReal.ofReal (max C 0 * B * height V g ^ A) := by
    intro n h
    have h1 : ∑' y : Orb W x₀, ‖G h * term ψ d W vS (om (n.1 * g, h) Φ) y.1‖ₑ =
        ‖G h‖ₑ * ∑' y : Orb W x₀, ‖term ψ d W vS (om (n.1 * g, h) Φ) y.1‖ₑ := by
      simp_rw [enorm_mul]
      exact ENNReal.tsum_mul_left
    have h2 : ∑' y : Orb W x₀, ‖term ψ d W vS (om (n.1 * g, h) Φ) y.1‖ₑ ≤
        ∑' x : Matrix (Fin W.rank) (Fin ρ) D.host.E, ‖term ψ d W vS (om (n.1 * g, h) Φ) x‖ₑ :=
      ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _
    have hq0 : 0 ≤ quotHeight W h ^ A := pow_nonneg (quotHeight_pos W h).le _
    have h3 : ∑' x : Matrix (Fin W.rank) (Fin ρ) D.host.E, ‖term ψ d W vS (om (n.1 * g, h) Φ) x‖ₑ ≤
        ENNReal.ofReal (max C 0 * height V g ^ A * quotHeight W h ^ A) := by
      refine (hC g h n.1 n.2).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [mul_pow, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hg0) hq0
    have h4 : ‖G h‖ * (max C 0 * height V g ^ A * quotHeight W h ^ A) ≤ max C 0 * B * height V g ^ A := by
      have e : ‖G h‖ * (max C 0 * height V g ^ A * quotHeight W h ^ A) =
          max C 0 * height V g ^ A * (‖G h‖ * quotHeight W h ^ A) := by ring
      rw [e, mul_right_comm (max C 0) B]
      exact mul_le_mul_of_nonneg_left (hBd h) (mul_nonneg (le_max_right _ _) hg0)
    rw [h1]
    refine (mul_le_mul' le_rfl (h2.trans h3)).trans ?_
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal h4
  calc ∫⁻ p in vN.𝓝 ×ˢ vW.𝓕, ∑' y : Orb W x₀, ‖G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) y.1‖ₑ ∂(vN.ν.prod vW.μ)
      ≤ ∫⁻ p in vN.𝓝 ×ˢ vW.𝓕, ENNReal.ofReal (max C 0 * B * height V g ^ A) ∂(vN.ν.prod vW.μ) :=
        lintegral_mono fun p => hpt p.1 p.2
    _ = ENNReal.ofReal (max C 0 * B * height V g ^ A) * (vN.ν.prod vW.μ) (vN.𝓝 ×ˢ vW.𝓕) := setLIntegral_const _ _
    _ = ENNReal.ofReal (max C 0 * B * ((vN.ν.prod vW.μ) (vN.𝓝 ×ˢ vW.𝓕)).toReal * height V g ^ A) := by
        rw [← ENNReal.ofReal_toReal hfin, ENNReal.toReal_ofReal hm0, ← ENNReal.ofReal_mul (mul_nonneg hK0 hg0)]
        congr 1; ring

end GlobalTheory.Unf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselAwayPlaces
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix

noncomputable section

namespace GlobalTheory.MiTop.LineAtT

variable {D : D7}

def UnitScal (v : GlobalTheory.FinPl.Pl D) (t : D.host.E) : Prop :=
  ∀ a ∈ idAt D (· = v), incA D t * a ∈ intAt D (· = v) ↔ a ∈ intAt D (· = v)

theorem UnitScal.mul {v : GlobalTheory.FinPl.Pl D} {s t : D.host.E} (hs : UnitScal v s) (ht : UnitScal v t) : UnitScal v (s * t) := fun a ha => by
  rw [RingHom.map_mul, mul_assoc, hs _ (Ideal.mul_mem_left _ _ ha), ht a ha]

theorem UnitScal.cancel {v : GlobalTheory.FinPl.Pl D} {s t : D.host.E} (hst : UnitScal v (s * t)) (ht : UnitScal v t) : UnitScal v s := fun a ha => by
  rw [← hst a ha, ← ht _ (Ideal.mul_mem_left _ _ ha), RingHom.map_mul, ← mul_assoc, mul_comm (incA D t)]

theorem unitAt_one (v : GlobalTheory.FinPl.Pl D) : UnitScal v 1 := fun a _ => by rw [RingHom.map_one, one_mul]

theorem UnitScal.pow {v : GlobalTheory.FinPl.Pl D} {s : D.host.E} (hs : UnitScal v s) (n : ℕ) : UnitScal v (s ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact unitAt_one v
  | succ n ih => rw [pow_succ]; exact ih.mul hs

theorem UnitScal.neg {v : GlobalTheory.FinPl.Pl D} {s : D.host.E} (hs : UnitScal v s) : UnitScal v (-s) := fun a ha => by
  rw [← hs a ha, RingHom.map_neg, neg_mul]
  exact ⟨fun h => neg_neg (incA D s * a) ▸ GlobalTheory.IdVGen.intAt_neg' h, GlobalTheory.IdVGen.intAt_neg'⟩

theorem unitAt_of {v : GlobalTheory.FinPl.Pl D} {s : D.host.E} (hs : s ≠ 0)
    (h : ∀ a ∈ intAt D (· = v), incA D s * a ∈ intAt D (· = v) ∧ incA D s⁻¹ * a ∈ intAt D (· = v)) : UnitScal v s := fun a _ => by
  refine ⟨fun h1 => ?_, fun h1 => (h a h1).1⟩
  have := (h _ h1).2
  rwa [← mul_assoc, ← RingHom.map_mul, inv_mul_cancel₀ hs, RingHom.map_one, one_mul] at this

theorem unitAt_nat {v : GlobalTheory.FinPl.Pl D} {N : ℕ} (hv : (N : 𝓞 D.host.F) ∉ v.asIdeal) : UnitScal v (N : D.host.E) := by
  have hN : (N : D.host.E) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    rintro rfl
    exact hv (by simp)
  refine unitAt_of hN fun a ha => ⟨GlobalTheory.SeeSaw.StdOff.incA_mul_mem_intAt hv ?_ a ha, GlobalTheory.SeeSaw.StdOff.incA_mul_mem_intAt hv ?_ a ha⟩
  · rw [← Nat.cast_mul]; exact isIntegral_natCast _
  · rw [mul_inv_cancel₀ hN]; exact isIntegral_one

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unitAt_val (p : SplitPt D k) {t : D.host.E} (h1 : valuation k (p.pr (incA D t)) = 1)
    (h2 : valuation k (p.pr (incA D (star t))) = 1) : UnitScal p.v t := fun a ha => by
  rw [GluedLine.mem_intAt_iff p (Ideal.mul_mem_left _ _ ha), GluedLine.mem_intAt_iff p ha, RingHom.map_mul, RingHom.map_mul (cA D),
    RingHom.map_mul, GlobalTheory.FinPl.FrameLat.cA_incA]
  simp only [Valuation.mem_integer_iff, map_mul, h1, h2, one_mul]

theorem psiE_triv {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (p : SplitPt D k) (hU : p.UnitAA) {s : AE D}
    (hs : s ∈ idAt D (· = p.v)) : (∀ o ∈ intAt D (· = p.v), psiE ψ (s * o) = 1) ↔ s ∈ intAt D (· = p.v) := by
  rw [← GlobalTheory.SeeSaw.DiffDual.idV_dI_iff D ψ hψ p.v s hs, ← (GlobalTheory.Core.Mi.LatMatch.idV_dI_pow_unit D k p hU 1 s).1, pow_one]

theorem psiE_ne {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (p : SplitPt D k) (hU : p.UnitAA)
    (q : GlobalTheory.LatPair.Unif k) : ∃ s, psiE ψ s ≠ 1 := by
  by_contra hc
  push_neg at hc
  have h := (psiE_triv hψ p hU (GlobalTheory.FinPl.FrameLat.sec_mem_idAt p q.inv)).1 fun o _ => hc _
  have h1 := GluedLine.pr_mem_of_intAt p h.2
  rw [p.pr_sec] at h1
  have h2 : IsUnit (q.1 : 𝒪[k]) := IsUnit.of_mul_eq_one ⟨_, h1⟩ (Subtype.ext (mul_inv_cancel₀ q.ne_zero))
  exact q.mem_max h2

theorem ne_zero_of_line {L : TH.HSp D} {ζ : Fin L.rank → D.host.E} (h : IsLineVec L ζ) : ζ ≠ 0 := by
  rintro rfl
  exact h.2 (by simp)

theorem vecB_ne {S A L : TH.HSp D} (o : OrthDec S A L) {ζ : Fin L.rank → D.host.E} (h : IsLineVec L ζ) : vecB o ζ ≠ 0 := fun e => by
  apply h.2
  have e' : o.iB *ᵥ ζ = 0 := e
  rw [← o.isoB, ← Matrix.mulVec_mulVec, e', Matrix.mulVec_zero, dotProduct_zero]

theorem wittDecomposition_inclusion_mulVec_rationalVector {S S₀ : TH.HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (z : Fin S₀.rank → D.host.E) :
    d.j0 *ᵥ ratV z = ratV (d.i₀ *ᵥ z) := funext fun r => (RingHom.map_mulVec (incA D) d.i₀ z r).symm

theorem first_scale (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word)
    {ψ : AddChar (AF D.host.F) ℂ} (F₀ : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F₀) (hE : IdE X)
    (hψ : IsStdChar D ψ (-1)) (hne : ∃ s, psiE ψ s ≠ 1) (hr : 0 < D.R.rS) (B : SBes X h u ψ (D.sp.X 0)) {μ : D.host.E}
    (hμ : μ ≠ 0) (hz : ∀ r, (B.d.i₀ *ᵥ vecB B.o B.ζ) r = μ * X.ιE (X.zR u (Fin.cast (rank_eq X h) r))) :
    ∃ lam : D.host.E, (lam = (X.B.g : D.host.E) ∨ lam = -(X.B.g : D.host.E)) ∧ ∀ r, B.d.jX r ⟨0, hr⟩ =
      incA D (μ * lam ^ D.R.rS) * incA D (X.ιE (X.eR ⟨0, hr⟩ (Fin.cast (rank_eq X h) r))) := by
  obtain ⟨lam, hl, hB⟩ := exists_sBes_scaled_dual D X h u ψ F₀ tr hE hψ
  obtain ⟨B', -, -, hz', he, -⟩ := hB μ B.vA hμ
  refine ⟨lam, hl, fun r => ?_⟩
  rw [FirstVec.first_eq (d' := B'.d) (z := vecB B.o B.ζ) (z' := vecB B'.o B'.ζ) hne (vecB_ne _ B.line) (vecB_ne _ B'.line)
    (by rw [wittDecomposition_inclusion_mulVec_rationalVector, wittDecomposition_inclusion_mulVec_rationalVector, funext hz, funext hz']) (Subgroup.ext fun n => (B.tieN n).trans (B'.tieN n).symm)
    (fun n hn => star_injective ((B.tieψ n hn).trans (B'.tieψ n ((B'.tieN n).2 ((B.tieN n).1 hn))).symm)) hr r,
    ← RingHom.map_mul]
  exact congrArg (incA D) (he r ⟨0, hr⟩)

end GlobalTheory.MiTop.LineAtT

set_option maxHeartbeats 800000 in
open GlobalTheory.MiTop.LineAtT GlobalTheory.MiTop.Scale GlobalTheory.GoodPos GlobalTheory.IwaPlace GlobalTheory.FinPlLoc in

theorem GlobalTheory.MiTop.line_ideal_at_own_prime : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ (hr : 1 ≤ D.R.rS) u (f : FamCh W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), GlobalTheory.MiTop.PlacedP f B → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ (pk W).Pg, PP.under (𝓞 D.host.F) ≠ v) → (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal → ∀ c ∈ GlobalTheory.FinPl.idAt D (· = v), (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹) ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) ∈ GlobalTheory.FinPl.latV (D.sp.Y 0) ((pk W).ΛY 0) (· = v) ↔ c ∈ GlobalTheory.FinPl.intAt D (· = v)) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hr u f B hP v hv hTv c hc
  obtain ⟨k, _, _, _, _, ι, v', o, n, G, pl, hcI, hvI, hVT, hSh, hGP, hGR, hBT, hpr⟩ := GlobalTheory.MiTop.placedPrim_iff.2 hP
  have h0 : 0 + 2 * D.R.rS + 2 = D.R.m := by
    show 0 + 2 * (D.R.m / 2 - 1) + 2 = D.R.m
    obtain ⟨k, hk⟩ := D.R.m_even
    have := D.R.two_le_m
    omega
  obtain ⟨i, rfl⟩ := (hSh.pre.tP v).1 ((hVT.tP v).2 hTv)
  have hU := (hSh.pre.char i).2
  have hψ : IsStdChar D W.Q.Rl.ψ (-1) := hcI.std
  have hm := GlobalTheory.StMoves.moves_inv (hVT.moves 0 (by omega) (· = (o.p i).v) fun p hp hg => by
    obtain ⟨PP, h1, h2⟩ := (hVT.gP p).1 hg
    exact hv PP h1 (h2.symm.trans hp))
  refine (hm _ fun r => Ideal.mul_mem_right _ _ hc).symm.trans ?_
  obtain ⟨μ, lam, hml, hz, hτ⟩ := hBT.norm
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  have hμ : μ ≠ 0 := left_ne_zero_of_mul (by rw [hml]; exact neg_ne_zero.2 (pow_ne_zero _ hξ))
  have hj : 2 * D.R.rS + 2 * 0 + 2 = D.R.m := by omega
  obtain ⟨lam', hl', hval⟩ := hSh.pre.lam _ hj
  have hll : lam = lam' := smul_left_injective _ (ne_zero_of_line (f.c.bes _ 0 hj).line) ((hτ _ hj).symm.trans hl')
  subst hll
  have uμ : UnitScal (o.p i).v μ := UnitScal.cancel (hml ▸ ((unitAt_of hξ hU.1).pow _).neg) (unitAt_val _ (hval i).1 (hval i).2)
  have hcop : Nat.Coprime (D.mem u).A.T W.S.X.B.g := by
    obtain ⟨M, h1, h2⟩ := GlobalTheory.TorusCong.one_sub_T_zmod D W.S.X u
    exact GlobalTheory.TorusCop.natCoprime_of_zmod_mul_one_sub _ _ _ M (Nat.pos_of_ne_zero (Formalism.L2.SG.Pf.modulus_g_ne_zero W.S.X)) h1 h2
  have ug : UnitScal (o.p i).v (W.S.X.B.g : D.host.E) := unitAt_nat fun hg => by
    obtain ⟨a, b, hab⟩ := (Nat.Coprime.cast (R := 𝓞 D.host.F) hcop)
    exact (o.p i).v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ add_mem (Ideal.mul_mem_left _ _ hTv) (Ideal.mul_mem_left _ _ hg)))
  obtain ⟨l, hl, he⟩ := first_scale W.S.X W.Q.instEq u _ (W.S.tr u) hW.bot.idE hψ (psiE_ne hψ _ hU o.q) hr B hμ hz
  have ul : UnitScal (o.p i).v l := by
    rcases hl with e | e <;> rw [e]
    exacts [ug, ug.neg]
  have hl0 : l ≠ 0 := by
    have hg : ((W.S.X.B.g : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (Formalism.L2.SG.Pf.modulus_g_ne_zero W.S.X)
    rcases hl with e | e <;> rw [e]
    exacts [hg, neg_ne_zero.2 hg]
  have ht0 : μ * l ^ D.R.rS ≠ 0 := mul_ne_zero hμ (pow_ne_zero _ hl0)
  have ut := uμ.mul (ul.pow D.R.rS)
  have hQ : ∀ Bl : BesLev D D.R.rS, Bl = f.c.B 0 D.R.rS h0 → ∀ LV : GlobalTheory.FinPl.Lat Bl.V, HEq LV (v'.N 0) → ∀ j,
      ∀ a ∈ idAt D (· = (o.p i).v), colMul Bl.d.jX j a ∈ latV Bl.V LV (· = (o.p i).v) ↔ a ∈ intAt D (· = (o.p i).v) := by
    rintro _ rfl LV hLV
    obtain rfl := eq_of_heq hLV
    intro j a ha
    have hlam : lam ≠ 0 := right_ne_zero_of_mul (by rw [hml]; exact neg_ne_zero.2 (pow_ne_zero _ hξ))
    obtain ⟨α, hα⟩ := GlobalTheory.IdeleAA.exists_idele_AA D f.c.ψ hcI.std
    have u1 := isU_alpha hU hSh.pre.line (hα _).1
    have u2 : IsU (o.p i).v ((xiU D * cU α : (AE D)ˣ) : AE D) := (isU_xi hU).mul u1.conj
    have u3 : IsU (o.p i).v ((α * (xiU D * cU α)⁻¹ : (AE D)ˣ) : AE D) := u1.mul (u2.inv (Units.mul_inv _))
    have u4 : IsU (o.p i).v ((xiU D * α * cU α : (AE D)ˣ) : AE D) := ((isU_xi hU).mul u1).mul u1.conj
    have u5 : IsU (o.p i).v (((xiU D * α * cU α) ^ (D.R.rS - j.1) *
        ((α * (xiU D * cU α)⁻¹) ^ (D.R.rS + 1) * inU lam hlam) : (AE D)ˣ) : AE D) := by
      rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
      exact (u4.pow _).mul ((u3.pow _).mul (isU_of_val _ (hval i).1 (hval i).2))
    refine (iso_line_all hcI hSh hpr (rank_pos f) hlam hτ (hα _).1 (fun s hs => ?_) _ 0 h0 j a ha).trans
      (u5.inv (Units.mul_inv _) a ha).symm
    rw [(hα _).2 s hs, mul_inv, mul_inv, Units.val_mul, Units.val_mul, cU_inv, xiU, inU_inv]
  generalize μ * l ^ D.R.rS = t at he ht0 ut
  have hc' : incA D t⁻¹ * c ∈ idAt D (· = (o.p i).v) := Ideal.mul_mem_left _ _ hc
  have e1 : incA D t * (incA D t⁻¹ * c) = c := by
    rw [← mul_assoc, ← RingHom.map_mul, mul_inv_cancel₀ ht0, RingHom.map_one, one_mul]
  have h1 := (hQ B.lev (hBT.lev h0) (v'.N 0) HEq.rfl ⟨0, hr⟩ _ hc').trans (ut _ hc').symm
  rw [e1] at h1
  refine Iff.trans (iff_of_eq (congrArg (· ∈ latV (D.sp.Y 0) (v'.N 0) (· = (o.p i).v)) (funext fun r => ?_))) h1
  refine Eq.trans ?_ (congrArg (incA D t⁻¹ * c * ·) (he r)).symm
  exact (congrArg (· * _) e1.symm).trans (by rw [mul_comm (incA D t), mul_assoc])

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselTranslateVector
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
noncomputable section

namespace GlobalTheory.MiTop

theorem fixAux {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (hId : GlobalTheory.Core.Mi.IdE X) (S : Set (Fin X.B.I.n → X.B.I.E)) (p : Fin X.B.I.n → X.B.I.E) (hp : p ∈ S)
    (g : GA D (D.sp.Y 0))
    (hg : (iotaX X h g).1 ∈ Formalism.L2.SG.PoincareInHH.HinfS X.B.I S ∧ (iotaX X h g).2 ∈ Formalism.L2.SG.PoincareInHH.HfinS X.B.I S) :
    Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) g) (fun k => Formalism.L2.Theta.incA D (X.ιE (p (Fin.cast (GlobalTheory.Core.Mi.rank_eq X h) k)))) =
      fun k => Formalism.L2.Theta.incA D (X.ιE (p (Fin.cast (GlobalTheory.Core.Mi.rank_eq X h) k))) := by
  have hR := (GlobalTheory.Core.SBesLevi.transport_fix D X.B.I X.ιE hId h (GlobalTheory.Core.Mi.rank_eq X h) S
    (Formalism.IndefR.RationalEmbedding.iota D g)).1 hg
  exact (GlobalTheory.Core.SBesLevi.bridge_fix D g _).2 (hR p hp)

end GlobalTheory.MiTop

theorem GlobalTheory.MiTop.tOf_fix_eR : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ (hr : 1 ≤ D.R.rS) u (f : FamCh W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), GlobalTheory.MiTop.PlacedP f B → ∀ a₀ a, IsAt f B a₀ a → ∀ c : AE D, Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (tOf f B a₀ a)⁻¹) ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) = Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹) ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) := by
  intro D L hT Gi Gl Kc Yd cX ex W hP hr u f B hB a₀ a hA c
  have hId : GlobalTheory.Core.Mi.IdE W.S.X := hP.bot.idE
  set v0 : Fin (D.sp.Y 0).rank → AE D := fun i => Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩
    (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))) with hv0
  have hv : (fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i)))) = c • v0 := rfl
  rw [hv]
  set x : GA D (D.sp.Y 0) := (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) with hxdef
  set E : GA D (D.sp.Y 0) := embA B.d B.o (a₀ * a) with hEdef
  set b : GA D (D.sp.Y 0) := (show GA D (D.sp.Y 0) from f.g.b 0) with hbdef
  have hx : Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) x) v0 = v0 := by
    refine GlobalTheory.MiTop.fixAux W.S.X W.Q.instEq hId {W.S.X.eR ⟨0, hr⟩} _ rfl x ?_
    have e : iotaX W.S.X W.Q.instEq x = (1, W.S.X.xu u) := (iotaX W.S.X W.Q.instEq).apply_symm_apply _
    rw [e]
    refine ⟨Subgroup.one_mem _, ?_⟩
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (W.S.X.xu_fix u ⟨0, hr⟩).1
  have hE : Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) E⁻¹) v0 = v0 := by
    refine GlobalTheory.MiTop.fixAux W.S.X W.Q.instEq hId (Formalism.L2.SG.PoincareInHH.PoincareSetting.fixSet W.S.X u) (W.S.X.eR ⟨0, hr⟩) (Or.inl (Or.inl ⟨⟨0, hr⟩, rfl⟩)) E⁻¹ ?_
    exact (B.tieH E⁻¹).1 ((embA B.d B.o).range.inv_mem ⟨a₀ * a, rfl⟩)
  have e : (tOf f B a₀ a)⁻¹ = b⁻¹ * (E⁻¹ * x) := by
    show (x⁻¹ * E * b)⁻¹ = _
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  rw [e]
  show Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) b⁻¹ * (Formalism.L2.Theta.mt (D.sp.Y 0) E⁻¹ * Formalism.L2.Theta.mt (D.sp.Y 0) x)) (c • v0) = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul, Matrix.mulVec_smul, hx, hE]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealMatrixCoeffFockVectorsLeDoublingHeightPow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Doubling GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero)

noncomputable section

namespace GlobalTheory.TwBound

theorem hgt_io_eq_prod (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)) (ha : IsMaj V a) (g : GA D V) (hg : g ∈ GinfC V) :
    (hgt V a (io V (g, 1)) : ℝ) = ∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW V a w (GlobalTheory.AdelicU.projArch D.sp.cm.sig V.gram w g) := by
  haveI := GlobalTheory.Doubling.t2Space_adeleRing' (F := D.host.F)
  have hI := GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D V (frameLat V) a (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat V) ha
  rw [hgt, hI.hgtAd_eq (isCMExt_host D)]
  have hf : ∀ v, hgtFin D.sp.cm.sig (dblSp V).gram (frameLat V) v (proj D.sp.cm.sig (dblSp V).gram v (io V (g, 1))) = 1 := by
    intro v
    have e : proj D.sp.cm.sig (dblSp V).gram v (io V (g, 1)) = 1 := by
      rw [io, proj_ioH, mem_infPts_iff_forall.1 hg v, map_one, ioH_one]
    rw [e]
    exact hgtH_of_mem (continuous_absEv v) (isCompact_KFin v) (one_mem _)
  simp only [hf, finprod_one, mul_one, NNReal.coe_prod]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [io, projArch_ioH, map_one]
  rfl

theorem tw_bound : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → ∀ (m : Measure (WO V W)) (X : Set (WO V W)), IsCovolOne (ratL W V) m X → ∀ f, IsVacVec ψ θ M M' f → ∀ a : GL (Fin V.rank) (AE D), GlobalTheory.Doubling.IsMaj V a → (∀ τ, (compAt θ τ a.1)ᴴ * (gramAt D V τ * cart M τ) * compAt θ τ a.1 = 1) → ∀ P Q, ∃ C : ℝ, ∀ g ∈ GinfC V, ‖GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X (ω (g, 1) (ptOf ψ θ M M' f P)) (ptOf ψ θ M M' f Q)‖ ≤ C * (∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW V a w (GlobalTheory.AdelicU.projArch D.sp.cm.sig V.gram w g)) ^ ((W.rank : ℝ) / 2) := by
  intro D V W S S' M M' θ ψ χS χT ω hθ hω m X hm f hf a ha hmaj P Q
  have hpr : GlobalTheory.Published.WeilRepresentationUnitaryPair := fun D ψ S T χS χT hψ hS hT rS rT =>
    GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ S T χS χT (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hS hT rS rT
  obtain ⟨omh, homh⟩ := GlobalTheory.T.exists_weilDatum_hermitianSpaceDoubled hpr D ψ V W χS χT ω hω
  have hth := GlobalTheory.T.doublingMap_thetaIdentity_any_weilData D ψ V W χS χT ω omh hω homh
  have hco := GlobalTheory.T.siegelWeilSection_doubling_eq_matrixCoefficient D ψ V W χS χT ω omh hω hth m X hm
  have h1 := GlobalTheory.T.isFockVec_ptOf_of_isVacVec D V W S S' M M' θ ψ hω.std hθ f hf P
  have h2 := GlobalTheory.T.isFockVec_ptOf_of_isVacVec D V W S S' M M' θ ψ hω.std hθ f hf Q
  have hS := fun τ => GlobalTheory.FrameEquiv.isCartanInv_cart_model M τ
  have hT := fun τ => GlobalTheory.FrameEquiv.isCartanInv_cart_model M' τ
  have hc := GlobalTheory.T.doubled_cartanInvolution_commute_maximalCompact D θ V (cart M) a hθ hS hmaj
  have hb := GlobalTheory.T.doublingSeesawTensorMap_polynomial_fock_vector D ψ θ V W (cart M) (cart M') hω.std hθ _ _ h1 h2
  have hk := GlobalTheory.T.fock_vector_finite_under_compact_commuting_cartan D ψ θ (dblSp V) W 1 χT omh _ (cart M') homh hθ hc.1 hT (Khat V a) (isCompact_Khat V a) hc.2 _ hb
  have hmem := GlobalTheory.T.doublingSiegelWeilSection_mem_degeneratePrincipalSeries hpr D ψ V W χT omh homh m X hm _ (hth _ _ h1.1 h2.1).1 a hk
  have hI := GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D V (frameLat V) a (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat V) ha
  haveI := GlobalTheory.Doubling.t2Space_adeleRing' (F := D.host.F)
  obtain ⟨C, hC⟩ := GlobalTheory.Doubling.HasIwasawa.exists_norm_le continuous_absE (isCompact_Khat V a) hI hmem
  refine ⟨C, fun g hg => ?_⟩
  have e1 := (hco _ _ h1.1 h2.1).2 g
  have e2 : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X (ω (g, 1) (ptOf ψ θ M M' f P)) (ptOf ψ θ M M' f Q) =
      swSec V W omh m X (delta V W (ptOf ψ θ M M' f P) (ptOf ψ θ M M' f Q)) (io V (g, 1)) := by
    rw [e1]; rfl
  rw [e2, ← hgt_io_eq_prod D V a ha g hg]
  have ex : (sZero V W).re + (V.rank : ℝ) / 2 = (W.rank : ℝ) / 2 := by
    simp only [sZero, Complex.div_ofNat_re, Complex.sub_re, Complex.natCast_re]; ring
  have := hC (io V (g, 1))
  rw [ex] at this
  exact this

end GlobalTheory.TwBound

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RegularisedThetaPairingIdentity
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

namespace GlobalTheory.Core.Rk.Exh

theorem zeta_eq_integral_integrand : GlobalTheory.Published.DoublingMethod → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → ∀ omh : WRep (dblSp A) B, IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ m : Measure (GA D A), m.IsHaarMeasure → ∀ Φ, IsFockVec ψ θ A B sA sB Φ → ∀ u ∈ A0 θ A cA, GlobalTheory.Eis.IsZetaFamily A χB⁻¹ m (flat A a (swSec A B omh ν 𝓕 (delta A B Φ Φ)) (sZero A B)) (fun g => conj (u g)) (fun g => conj (u g)) ∧ GlobalTheory.Eis.EisContinues A (flat A a (swSec A B omh ν 𝓕 (delta A B Φ Φ)) (sZero A B)) ∧ (∀ g, AnalyticOnNhd ℂ (GlobalTheory.Eis.eisSer A (flat A a (swSec A B omh ν 𝓕 (delta A B Φ Φ)) (sZero A B)) g) (rightOf (A.rank / 2))) ∧ (∀ s₀, ∃ k, GlobalTheory.Eis.EisRegularAt A (flat A a (swSec A B omh ν 𝓕 (delta A B Φ Φ)) (sZero A B)) s₀ k) ∧ ∀ s : ℂ, (A.rank : ℝ) / 2 < s.re → Integrable (integrand om m ν 𝓕 (frameLat A) a Φ Φ u u s) m ∧ GlobalTheory.Eis.zeta A χB⁻¹ m (flat A a (swSec A B omh ν 𝓕 (delta A B Φ Φ)) (sZero A B)) (fun g => conj (u g)) (fun g => conj (u g)) s = ∫ g, integrand om m ν 𝓕 (frameLat A) a Φ Φ u u s g ∂m := by
  intro hDM D ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP omh homh m hm Φ hΦ u hu
  obtain ⟨ha, ht, hb, hθ, hSig, hCart, -⟩ := hP.setting
  have hW := GlobalTheory.weilRepresentationUnitaryPair
  have hTC := GlobalTheory.T.doublingMap_thetaIdentity_any_weilData D ψ A B χA χB om omh hP.weil homh
  have hCC := GlobalTheory.T.siegelWeilSection_doubling_eq_matrixCoefficient D ψ A B χA χB om omh hP.weil hTC ν 𝓕 hP.covol
  obtain ⟨hφ, -⟩ := hTC Φ Φ hΦ.1 hΦ.1
  have hK := GlobalTheory.T.doublingVector_fockPair_isCompactFinite D ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP omh homh Φ Φ hΦ hΦ
  have hI : HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) :=
    GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D A (frameLat A) a (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A) hP.maj
  have hmem := GlobalTheory.T.doublingSiegelWeilSection_mem_degeneratePrincipalSeries hW D ψ A B χB omh homh ν 𝓕 hP.covol (delta A B Φ Φ) hφ a hK
  have hHk : IsHeckeChar D χB⁻¹ := by
    have h := homh.hecT
    refine ⟨?_, fun x => ?_⟩
    · have : (χB⁻¹ : (AE D)ˣ →* Circle) = fun x => (χB x)⁻¹ := rfl
      rw [this]; exact h.1.inv
    · rw [MonoidHom.inv_apply, h.2 x, inv_one]
  obtain ⟨hDM1, -, hDM3⟩ := hDM D A (by omega) a hP.maj hI χB⁻¹ B.rank hHk (resEta_inv homh.resT) (sZero A B)
    (swSec A B omh ν 𝓕 (delta A B Φ Φ)) hmem
  have hf := GlobalTheory.T.cuspFormsArchimedeanKFinite_star_comp_mem D θ A cA hθ u hu
  obtain ⟨hBI, -⟩ := hDM3 θ hθ hSig cA hCart m hm _ hf _ hf
  have hpt : ∀ s g, flat A a (swSec A B omh ν 𝓕 (delta A B Φ Φ)) (sZero A B) s (io A (g, 1)) *
      conj (GlobalTheory.Eis.petCoef A m (fun x => conj (u x)) (fun x => conj (u x)) g) =
      integrand om m ν 𝓕 (frameLat A) a Φ Φ u u s g := by
    intro s g
    have e1 : swSec A B omh ν 𝓕 (delta A B Φ Φ) (io A (g, 1)) = wcoef om ν 𝓕 Φ Φ g :=
      (hCC Φ Φ hΦ.1 hΦ.1).2 g
    have e2 : conj (GlobalTheory.Eis.petCoef A m (fun x => conj (u x)) (fun x => conj (u x)) g) = rcoef m u u g := by
      simp only [GlobalTheory.Eis.petCoef, rcoef, petersson, pet, rTr, GlobalTheory.AutomorphicL2Unitary.descend]
      rw [← integral_conj]
      congr 1
      funext q
      simp
    rw [integrand, ← e1, ← e2]
    rfl
  have hEF := hDM1.1.1
  refine ⟨⟨hEF, fun s hs => (hBI s hs).1⟩, hDM1.1, fun g => hEF.analyticOnNhd_flat g, hDM1.2, fun s hs => ?_⟩
  obtain ⟨-, hconv, heq⟩ := hBI s hs
  refine ⟨?_, ?_⟩
  · have e : integrand om m ν 𝓕 (frameLat A) a Φ Φ u u s = fun g =>
        flat A a (swSec A B omh ν 𝓕 (delta A B Φ Φ)) (sZero A B) s (io A (g, 1)) *
          starRingEnd ℂ (GlobalTheory.Eis.petCoef A m (fun x => conj (u x)) (fun x => conj (u x)) g) :=
      funext fun g => (hpt s g).symm
    rw [e]
    exact hconv
  · rw [GlobalTheory.Eis.zeta, heq]
    unfold zetaH pairInt
    exact integral_congr_ae (.of_forall fun g => hpt s g)

end GlobalTheory.Core.Rk.Exh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarFormTransportedColumnStepZeroStandardStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalarForm_transportedColumn_stepZero_standard : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (C : Formalism.L2.Forms.ColsTiedSym (I.rec7 l Z)), I.StdC l Z C → ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (β : Ch 0), A.kb 0 β = TC.kStd X u (B.R.N 0) → ∀ θ, IsInfFam θ → ∀ ψ₀ ∈ ((I.rec7 l Z).mem u).A.Mram, ∀ y, A.rd θ 0 (Nat.zero_le _) β ((I.rec7 l Z).e0Tw u a ψ₀) y = (GlobalTheory.Core.Mi.chart0 (C.forms u).to0).rd θ ψ₀ y := by
  first | exact @GlobalTheory.Fam.rd_zero_std | exact GlobalTheory.Fam.rd_zero_std | (intros; apply GlobalTheory.Fam.rd_zero_std <;> assumption)
end

