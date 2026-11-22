import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0355
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0543
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0514
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyIntIn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0548
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0352
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0155
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0158
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0133
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0923
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0356
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0149
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0005
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0216
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0133
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandBesselPeriodInvariantProof
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleUnfoldingStepAtGluedFinitePlace
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StabMatch
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0339
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0475
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0446
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0480
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodCharacterPrimitiveNormalFrames
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PrimNormal

theorem z_pair {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (v : Fin S₀.rank → D.host.E) (i : Fin ρ) :
    ∑ r, ∑ t, star ((d.i₀ *ᵥ v) r) * HSpace.gram S r t * d.e t i = 0 := by
  have hent : ∀ c, ∑ r, ∑ t, star (d.i₀ r c) * HSpace.gram S r t * d.e t i = 0 := fun c => by
    rw [← GlobalTheory.SplitPrimJac.mat_entry S d.i₀ d.e c i, d.i₀e, Matrix.zero_apply]
  have e : ∑ r, ∑ t, star ((d.i₀ *ᵥ v) r) * HSpace.gram S r t * d.e t i =
      ∑ c, star (v c) * ∑ r, ∑ t, star (d.i₀ r c) * HSpace.gram S r t * d.e t i := by
    simp only [Matrix.mulVec, dotProduct, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
    calc _ = ∑ r, ∑ c, ∑ t, star (d.i₀ r c) * star (v c) * HSpace.gram S r t * d.e t i :=
            Finset.sum_congr rfl fun r _ => Finset.sum_comm
      _ = ∑ c, ∑ r, ∑ t, star (d.i₀ r c) * star (v c) * HSpace.gram S r t * d.e t i := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun t _ => by ring
  rw [e]
  simp [hent]

end GlobalTheory.PrimNormal

namespace GlobalTheory.PrimNormal

theorem prim_of_normal : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ {a : XGeo D} (y : YRat a) {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) (FY : FYFam l) (sc : ℕ → l.k), IsNormalFr l y FY sc → (∀ j, j ≤ D.R.m → (a.x j).Is) → ∀ (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M : ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) → (∀ j c (hc : j + c = l.s + 1), IntIn l.q (Yc D j) (FY j c hc) (N j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M j ρ h)) → (∀ j ρ h (hj : j ≤ l.s + 1) (F₀ : Frame l.k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit l.q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc j) (l.FX j hj) F₀ → IntIn l.q _ F₀ (M j ρ h)) → ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.PrimAt ψ ((y.bes j ρ h).lev (a.x j).vol).d (N j) (PP.under (𝓞 D.host.F)) := by
  intro D ψ hψ a y βT PP l FY sc hN hx N M hNsd hNint hMsd hMcore j ρ h
  rw [← l.under]
  have hc : j + (2 * ρ + 1) = l.s + 1 := by have := l.hs; omega
  have hB := hN.2.2.2.1 j ρ h (2 * ρ + 1) hc
  have hξ : valuation l.k (ofSplit l.q).xi = 1 := GlobalTheory.QTw.GeoInhab.xi_unit l.q l.unit
  have hsc := hN.1 j
  have hz := hN.2.2.1 j ρ h
  have inner0 : ∀ (x : Fin (Yc D j).rank → D.host.E) (i : Fin ρ),
      (∑ r, ∑ t, star (x r) * HSpace.gram (Yc D j) r t * ((y.bes j ρ h).lev (a.x j).vol).d.e t i) = 0 →
      ∀ (b : l.k) (col : Fin (Yc D j).rank → l.k), (∀ r, col r = b * l.q.pr (incA D (x r))) →
      ∑ r, ∑ t, col r * l.q.pr (cA D (incA D (HSpace.gram (Yc D j) r t))) *
        l.q.pr (cA D (incA D (((y.bes j ρ h).lev (a.x j).vol).d.e t i))) = 0 := by
    intro x i hx b col hcol
    rw [GlobalTheory.SplitPrimJac.colPair_smul l.q _ b x _ col hcol, hx, star_zero, map_zero, map_zero, mul_zero]
  have line : ∀ (i : Fin ρ) (b : AE D), GlobalTheory.FinPl.colMul ((y.bes j ρ h).lev (a.x j).vol).d.jX i b ∈
      GlobalTheory.FinPl.latV (Yc D j) (N j) (· = l.q.v) ↔ b ∈ GlobalTheory.FinPl.intAt D (· = l.q.v) := by
    intro i b
    refine GlobalTheory.PrimSplitLine.colMul_mem_latV_iff D l.k l.q _ _ ρ ((y.bes j ρ h).lev (a.x j).vol).d (N j) _
      (FY j (2 * ρ + 1) hc) i (Sum.inr ⟨i.val, by omega⟩) (Sum.inr ⟨2 * ρ - i.val, by omega⟩)
      (sc j * (ofSplit l.q).xi ^ (ρ - i.val))
      (sc j * (-(ofSplit l.q).hz ((y.bes j ρ h).lev (a.x j).vol) / (ofSplit l.q).xi) * (-1 / (ofSplit l.q).xi) ^ (ρ - 1 - i.val))
      (hNsd j (by omega)) (hNint j _ hc) ?_ ?_ ?_ ?_ b
    · rw [map_mul, map_pow, hsc, hξ, one_pow, one_mul]
    · simp only [map_mul, map_div₀, map_pow, Valuation.map_neg, map_one, hsc, hz, hξ]; simp
    · intro r; exact hB.2.2.1 i ⟨i.val, by omega⟩ rfl r
    · intro m
      rcases m with b | m
      · rw [if_neg Sum.inl_ne_inr]
        have hcol : ∀ r, (FY j (2 * ρ + 1) hc).β r (Sum.inl b) = ∑ e, (l.FX j (by omega)).β e b *
            l.q.pr (incA D ((((y.bes j ρ h).lev (a.x j).vol).d.i₀ * ((y.bes j ρ h).lev (a.x j).vol).o.iA) r e)) := by
          intro r
          rw [hB.2.1 r b, Matrix.mul_apply]
          exact Finset.sum_congr rfl fun e _ => mul_comm _ _
        simp only [hcol, Finset.sum_mul]
        rw [Finset.sum_congr rfl fun r _ => Finset.sum_comm, Finset.sum_comm]
        refine Finset.sum_eq_zero fun e _ => ?_
        simp only [mul_assoc]
        simp only [← mul_assoc]
        refine inner0 (fun r => (((y.bes j ρ h).lev (a.x j).vol).d.i₀ * ((y.bes j ρ h).lev (a.x j).vol).o.iA) r e) i ?_ _ _
          fun r => rfl
        rw [← GlobalTheory.SplitPrimJac.mat_entry, Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc,
          ← Matrix.mul_assoc _ (HSpace.gram _), ((y.bes j ρ h).lev (a.x j).vol).d.i₀e, Matrix.mul_zero, Matrix.zero_apply]
      · by_cases hm : m.val < ρ
        · rw [if_neg (fun he => by cases he; simp at hm; omega)]
          refine inner0 (fun r => ((y.bes j ρ h).lev (a.x j).vol).d.e r ⟨m.val, hm⟩) i ?_ _ _ (hB.2.2.1 ⟨m.val, hm⟩ m rfl)
          rw [← GlobalTheory.SplitPrimJac.mat_entry, ((y.bes j ρ h).lev (a.x j).vol).d.ee, Matrix.zero_apply]
        · by_cases hm' : m.val = ρ
          · rw [if_neg (fun he => by cases he; simp at hm'; omega)]
            refine inner0 (fun r => (((y.bes j ρ h).lev (a.x j).vol).d.i₀ *ᵥ
              vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ) r) i ?_ _ _ (hB.2.2.2.1 m hm')
            exact z_pair _ _ i
          · have hi' : 2 * ρ - m.val < ρ := by omega
            have hcol := hB.2.2.2.2 ⟨2 * ρ - m.val, hi'⟩ m (by simp; omega)
            rw [GlobalTheory.SplitPrimJac.colPair_smul l.q _ _ _ _ _ hcol, ← GlobalTheory.SplitPrimJac.mat_entry,
              ((y.bes j ρ h).lev (a.x j).vol).d.e'e, Matrix.one_apply]
            by_cases hii : (⟨2 * ρ - m.val, hi'⟩ : Fin ρ) = i
            · have hmv : m.val = 2 * ρ - i.val := by rw [← hii]; simp; omega
              rw [if_pos hii, if_pos (by congr 1; exact Fin.ext hmv), star_one, map_one, map_one, mul_one, ← hii]
            · rw [if_neg hii, if_neg (fun he => hii (by cases he; ext; simp; omega)), star_zero, map_zero, map_zero,
                mul_zero]
  obtain ⟨ψk, hχ, hcond⟩ := GlobalTheory.QTw.GeoInhab.exists_char l.q l.unit hψ
  have hε : l.q.e + cA D l.q.e ∈ GlobalTheory.FinPl.intAt D (· = l.q.v) :=
    ⟨GlobalTheory.FinPl.FrameLat.sum_mem_idAt l.q, by
      rw [RingHom.map_add]
      exact add_mem (GlobalTheory.FinPl.FrameLat.e_mem_intAt l.q).2
        ((GlobalTheory.FinPl.FrameLat.cA_int_iff _).2 (GlobalTheory.FinPl.FrameLat.e_mem_intAt l.q).2)⟩
  intro i i' hii' t ht
  rw [← GlobalTheory.SplitIntChar.int_iff_psiE D l.k l.q ψ ψk hξ hχ hcond t ht]
  constructor
  · intro H
    have h1 := H (l.q.e + cA D l.q.e) ((line i' _).2 hε)
    have ht' : t * (l.q.e + cA D l.q.e) = t := by rw [mul_comm]; exact (GlobalTheory.FinPl.FrameLat.idem_iff l.q t).1 ht
    rwa [line i, ht'] at h1
  · intro H b hb
    rw [line i'] at hb
    rw [line i]
    exact ⟨Ideal.mul_mem_right _ _ H.1, by rw [RingHom.map_mul]; exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE H.2 hb.2⟩

end GlobalTheory.PrimNormal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainMoveCharactersEqRhoUpToBase
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.AdForm.TwDat

set_option maxHeartbeats 800000 in

theorem chr_root_mul_base {B : Base} {X : PreX B.toPre} {I : TC B X} (hI : I.Ok) {l : I.Laws} {Z : TC.Later B (I.cols l)}
    {u : B.Word} {a : I.ι} {Ch : ℕ → Type} {A : TwDat I l Z u a Ch} (hA : A.Is) (j : Fin B.R.m) (k : ℕ) (hk : k ≤ B.R.m)
    (β : Ch k) (c : {c // A.chOf k c = β}) (x : (AE (I.rec7 l Z))ˣ) (hx : IsDetRoot _ (A.h k β c) x) :
    (A.chr ((j : ℕ) + 1) x : ℂ) * (A.chr ((j : ℕ) + 1) (A.xr k β) : ℂ) =
      ((tildeQ B.host I.SQ (I.C.mu0 j * I.xi a) (detPt B.host I.SQ ((I.stp u a k).rep c.1).1.1) : ℂˣ) : ℂ) := by
  obtain ⟨c, rfl⟩ := c
  have hlev := GlobalTheory.Mem.LevTwist.levOk_twists B X I hI
  have hpt := (hA.reads k hk).pt c
  obtain ⟨a', ha'⟩ := GlobalTheory.Mem.DetLift.exists_isDetLift B.R B.host (B.R.N k) _ hpt.uni
  obtain ⟨hkA, hkAm, hxr⟩ := hA.kA k hk (A.chOf k c)
  obtain ⟨hh, hhm⟩ := hA.h k hk (A.chOf k c) ⟨c, rfl⟩
  have hg : A.h k (A.chOf k c) ⟨c, rfl⟩ * A.kA k (A.chOf k c) ∈ GfC _ := mul_mem hh hkA
  have hfin : finM _ (rankN (I.rec7 l Z) k hk) (A.h k (A.chOf k c) ⟨c, rfl⟩ * A.kA k (A.chOf k c)) =
      ((((show TC.GA B (B.R.N k) from ((A.K k hk (A.chOf k c)).y ⟨c, rfl⟩).1) * A.kb k (A.chOf k c) : TC.GA B (B.R.N k))) :
        Matrix (Fin (B.R.N k)) (Fin (B.R.N k)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) := by
    rw [GlobalTheory.RepLattice.finM_mul', hhm, hkAm, Units.val_mul]
    rfl
  have hroot := GlobalTheory.TwistFinPart.isDetRoot_mul' _ _ _ _ _ hx hxr
  have htw := (GlobalTheory.Mem.ReadTwist.isTwist_of_reads B.R B.host _ B.embLL I.S (I.tup a) (I.xi a) (hI.xi_reads a)).1
  have key := GlobalTheory.DetRootRead.chr_at_detRoot (I.rec7 l Z) (A.chr ((j : ℕ) + 1)) (I.C.mu0 j * I.xi a) (hA.chr j)
    (Formalism.L2.Host.HChar.TrivOn.mul (I.C.isMu0 j).triv htw.2.1) _ _ _ _ hg hfin _ hroot a' ha'
  have hm := reference_characters_factor_tame I.SQ I.C j
  have hxi : KDq B.host I.SQ ≤ ((I.xi a).1.comp (Chr.finPartI B.host.E)).ker :=
    (KDq_anti B.host (I.Q_subset_SQ a)).trans (hlev.2.2 a).1
  have hfac : KDq B.host I.SQ ≤ ((I.C.mu0 j * I.xi a).1.comp (Chr.finPartI B.host.E)).ker := fun b hb => by
    have e : (I.C.mu0 j).1 (Chr.finPartI B.host.E b) = 1 := hm hb
    have e' : (I.xi a).1 (Chr.finPartI B.host.E b) = 1 := hxi hb
    show (I.C.mu0 j).1 (Chr.finPartI B.host.E b) * (I.xi a).1 (Chr.finPartI B.host.E b) = 1
    rw [e, e', one_mul]
  rw [← GlobalTheory.Mem.Col2.DetSpec.mk_eq_detPt B.R B.host _ _ _ _ _ _ _ a' hlev.1 hpt ha', tildeQ_mk _ _ hfac, ← Circle.coe_mul, ← map_mul]
  exact key

theorem rho_eq {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i + 1 ≤ B.R.m)
    (c : (I.stp u a i).Cl) : (I.chIn u a).rho i c =
      ((tildeQ B.host I.SQ (I.C.mu0 ⟨i, hi⟩ * I.xi a) (detPt B.host I.SQ ((I.stp u a i).rep c).1.1) : ℂˣ) : ℂ)⁻¹ *
        chiId I.C.chiPsi (Th.detId B.host (Th.stdL B.host (B.R.N i)) ((I.stp u a i).rep c).1.1.deco.1.N) ^
          (-((B.R.N (i + 1) / 2 : ℕ) : ℤ)) := by
  have hlev := GlobalTheory.Mem.LevTwist.levOk_twists B X I hI
  have hxi : KDq B.host I.SQ ≤ ((I.xi a).1.comp (Chr.finPartI B.host.E)).ker :=
    (KDq_anti B.host (I.Q_subset_SQ a)).trans (hlev.2.2 a).1
  show ((rhoAt I.SQ I.C (I.xi a) i ((I.stp u a i).rep c).1.1 : ℂˣ) : ℂ) = _
  rw [rhoAt, muTilQ_succ B.host I.SQ I.C.mu0 ⟨i, hi⟩, xiDet, tildeQ_mul B.host I.SQ (reference_characters_factor_tame I.SQ I.C ⟨i, hi⟩) hxi,
    MonoidHom.mul_apply]
  rw [← GlobalTheory.Mem.ChiDet.tildeQ_detPt_eq_chiId B.R B.host _ I.C _ _ _ _ I.SQ _ hlev.1]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, mul_inv]

theorem rho'_eq {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i + 1 ≤ B.R.m)
    (c' : (I.stp u a (i + 1)).Cl) : (I.chIn u a).rho' i c' =
      ((tildeQ B.host I.SQ (I.C.mu0 ⟨i, hi⟩ * I.xi a) (detPt B.host I.SQ ((I.stp u a (i + 1)).rep c').1.1) : ℂˣ) : ℂ) *
        chiId I.C.chiPsi (Th.detId B.host (Th.stdL B.host (B.R.N (i + 1))) ((I.stp u a (i + 1)).rep c').1.1.deco.1.N) ^
          ((B.R.N i / 2 : ℕ) : ℤ) := by
  have hlev := GlobalTheory.Mem.LevTwist.levOk_twists B X I hI
  have hxi : KDq B.host I.SQ ≤ ((I.xi a).1.comp (Chr.finPartI B.host.E)).ker :=
    (KDq_anti B.host (I.Q_subset_SQ a)).trans (hlev.2.2 a).1
  show ((rhoAt' I.SQ I.C (I.xi a) i ((I.stp u a (i + 1)).rep c').1.1 : ℂˣ) : ℂ) = _
  rw [rhoAt', muTilQ_succ B.host I.SQ I.C.mu0 ⟨i, hi⟩, xiDet, tildeQ_mul B.host I.SQ (reference_characters_factor_tame I.SQ I.C ⟨i, hi⟩) hxi,
    MonoidHom.mul_apply]
  rw [← GlobalTheory.Mem.ChiDet.tildeQ_detPt_eq_chiId B.R B.host _ I.C _ _ _ _ I.SQ _ hlev.1]
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val]

theorem moves_alg (X Y r₀ r₁ a b : ℂ) (p q : ℤ) (hX : X ≠ 0) (hY : Y ≠ 0) (h₀ : r₀ ≠ 0) (h₁ : r₁ ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    X⁻¹ * Y = r₀ * r₁⁻¹ * ((X * r₀)⁻¹ * a ^ (-p) * (Y * r₁ * b ^ q)) * (a ^ p * b ^ (-q)) := by
  have h1 : a ^ p ≠ 0 := zpow_ne_zero p ha
  have h2 : b ^ q ≠ 0 := zpow_ne_zero q hb
  rw [_root_.zpow_neg, _root_.zpow_neg]
  field_simp

theorem chr_moves_eq_rho_base : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (c : {c // A.chOf i c = α}) (c' : {c // A.chOf (i + 1) c = γ}) x y, IsDetRoot _ (A.h i α c) x → IsDetRoot _ (A.h (i + 1) γ c') y → (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) = (A.chr (i + 1) (A.xr i α) : ℂ) * (A.chr (i + 1) (A.xr (i + 1) γ) : ℂ)⁻¹ * ((I.chIn u a).rho i c.1 * (I.chIn u a).rho' i c'.1) * I.A.chiF (B.R.N i) (B.R.N (i + 1)) ((I.stp u a i).rep c.1).1.1.deco.1.N ((I.stp u a (i + 1)).rep c'.1).1.1.deco.1.N := by
  intro B X I hI _ l Z u a Ch A hA i hi α γ c c' x y hx hy
  have h0 := chr_root_mul_base hI hA ⟨i, hi⟩ i (Nat.le_of_succ_le hi) α c x hx
  have h1 := chr_root_mul_base hI hA ⟨i, hi⟩ (i + 1) hi γ c' y hy
  rw [rho_eq I hI u a i hi, rho'_eq I hI u a i hi]
  simp only [ColIn.A, AmbIn.amb, Th.chiFac, ColIn.chi]
  rw [← h0, ← h1]
  exact moves_alg _ _ _ _ _ _ _ _ (Circle.coe_ne_zero _) (Circle.coe_ne_zero _) (Circle.coe_ne_zero _)
    (Circle.coe_ne_zero _) (chiId_ne_zero _ _) (chiId_ne_zero _ _)

end GlobalTheory.AdForm.TwDat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteStepSmallVectorFockVacuumSpherical
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

namespace GlobalTheory.Core.Rk.SmallVac

theorem smallVec_vac_sph : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A H : HSp D) (χA : (AE D)ˣ →* Circle) (om : WRep A H) (sA : RealMat A) (sH : RealMat H), IsInfFam θ → (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) → IsWeilDatumO ψ A H χA 1 om → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → A.rank ≤ H.rank → ∀ (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)), Places A β Z → ∀ (βH : GL (Fin H.rank) (Formalism.IndefR.Lev.EAf D)) (f₀ f : WO A H → ℂ), Formalism.L2.DIV.IsFrame βH (frameLat H) → IsStepVecOf ψ θ A H sA sH (frameLat A) (frameLat H) β βH (prinDat A Z) (fun _ => 1) ∅ (fun _ => 1) f₀ f → IsThetaFunO ψ A H f ∧ f ≠ 0 ∧ (∀ τ, IsFockVacAt (heisO ψ A H) θ τ (cplxO (sA τ) (sH τ)) f) ∧ IsSphOff ψ A H (frameLat A) (frameLat H) (under Z) f := by
  classical
  intro D ψ θ A H χA om sA sH hθ hη hω hsA hsH hr β Z hZ βH f₀ f hβH h
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.Chain.StepVac.stepVec_vac (GlobalTheory.Core.Rk.IP.frameLat_isSelfDualC A)
    (GlobalTheory.Core.Rk.IP.frameLat_isSelfDualC H) hr h
  refine ⟨h1, h2, h3, ?_⟩
  obtain ⟨hvac, e, he, hth⟩ := h
  have hle : latO A H (frameLat A) (frameLat H) (fun v => v ∉ under Z) ≤
      latO A H (frameLat A) (frameLat H) fun _ => True :=
    GlobalTheory.PlaceTensor.latO_mono fun _ _ => trivial
  have hlat := hvac.2.lat
  have hZu : ∀ PP ∈ (prinDat A Z).Pg ∪ ∅, PP.under (𝓞 D.host.F) ∈ under Z := by
    intro PP hPP
    rw [Finset.union_empty] at hPP
    unfold under
    exact Finset.mem_image_of_mem _ hPP
  have fix : ∀ u ∈ latO A H (frameLat A) (frameLat H) (fun v => v ∉ under Z), heisO ψ A H u f₀ = f₀ →
      heisO ψ A H u f = f := fun u hu h0 =>
    GlobalTheory.Hk3.heisO_fix_thetaAt_off ψ A H e _ 1 f₀ _ f hth u
      (GlobalTheory.FockSph.idemSum_mul_of he (fun PP hPP hn => hn (hZu PP hPP)) hu) h0
  exact ⟨fun u hu => fix (2 • u) (AddSubgroup.nsmul_mem _ hu 2) (hlat.1 u (hle hu)),
    fun e' he' u hu hh => fix u hu (hlat.2 e' he' u (hle hu) hh)⟩

end GlobalTheory.Core.Rk.SmallVac

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandBesselPeriodInvariantProofStatement
section
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleStepIntegrandBesselPeriodInvariant_proof : ∀ D : D7, GlobalTheory.FinPl.HandInv D := by
  first | exact @GlobalTheory.FinPl.HandInvPf.handInv | exact GlobalTheory.FinPl.HandInvPf.handInv | (intros; apply GlobalTheory.FinPl.HandInvPf.handInv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleUnfoldingStepAtGluedFinitePlaceStatement
section
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleUnfoldingStep_at_glued_finite_place : ∀ D : D7, GlobalTheory.FinPl.VertexGlued D := by
  first | exact @GlobalTheory.FinPl.Vertex.vertexGlued | exact GlobalTheory.FinPl.Vertex.vertexGlued | (intros; apply GlobalTheory.FinPl.Vertex.vertexGlued <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralAdaptedElement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.LevZero.StabMatch

variable {D : D7}

def Facts {c : Comm D} {v : VCom c} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ι : Type} (o : TDat c k ι) {n : ℕ} (G : Fin n → GLoc v) (Lm : Lat (c.V 0)) (b : BesAt (c.V 0) (c.X 0) D.R.rS) : Prop :=
  ∃ M : Lat b.V₀,
    (∀ p, IsSelfDualC b.V₀ M ∧ MonoAt b.d (v.N 0) M p ∧ PrimAt c.ψ b.d (v.N 0) p ∧ LastAt c.ψ b.d (vecB b.o b.ζ) (v.N 0) M p) ∧
    (∀ p, p ∉ v.tP → ∃ LL, IsSelfDualC b.L LL ∧ OrthAt b.o M (c.x 0).L LL p) ∧
    (∀ i, ∃ β₀ : GlobalTheory.FinPl.Frame (o.p i) b.V₀ (Fin (c.X 0).rank ⊕ Fin 1), IsSumFrame b.o b.ζ (o.β 0 i) β₀ ∧
      β₀.IsLat M (GlobalTheory.LatPair.gluedS o.q 1 (o.Q 0 i).ker (o.Q 0 i).vec)) ∧
    ∀ i, valuation (G i).k ((G i).q.pr (incA D (star b.ζ ⬝ᵥ b.L.gram *ᵥ b.ζ))) = 1 ∧
      WShape (G i).q b.d b.o b.ζ Lm (fun j => ((((G i).S.ϖ : (G i).kˣ) : (G i).k) ^ (j.1 + 1))⁻¹)
        (fun j => ((((G i).S.ϖ : (G i).kˣ) : (G i).k) ^ (2 * D.R.rS - j.1 + 1))⁻¹)
        (((((G i).S.ϖ : (G i).kˣ) : (G i).k) ^ (D.R.rS + 1))⁻¹) 1 (c.x 0).L

theorem facts {c : Comm D} {v : VCom c} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ι : Type} (o : TDat c k ι) {n : ℕ} (G : Fin n → GLoc v) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m) (hc : c.Is) (hS : ShapeOff v o)
    (PP : Fin n → Formalism.L2.DIV.Pl D.host.E) (b : GA D (c.V 0)) (β : GL (Fin (c.V 0).rank) (Lev.EAf D))
    (hloc : ∀ i, LocAt (G i) (PP i) b β) (Λ Lm : Lat (c.V 0)) (hfr : Formalism.L2.DIV.IsFrame β Λ) (hmv : ∀ P, Moves (c.V 0) b Λ Lm P) :
    Facts o G Lm (c.bes 0 D.R.rS h0) :=
  ⟨o.M 0 _ h0, fun p => ⟨((hS.good p).bf 0 _ h0).sdV₀, ((hS.good p).bf 0 _ h0).monoV, ((hS.good p).bf 0 _ h0).prim,
      GlobalTheory.T.lastWittLine_of_besselJacobiLatticesGood D _ hc.std _ _ _ _ _ _ _ p ((hS.good p).bf 0 _ h0)⟩,
    fun p hp => (hS.split p hp).core 0 _ h0, fun i => ⟨_, (hS.glued 0 _ h0 i).sum, (hS.glued 0 _ h0 i).lat⟩,
    fun i => ⟨(G i).hz_unit 0 _ h0, GlobalTheory.LevZero.wShape_of_besFrame_loc (G i) _ h0 Lm
      (GlobalTheory.T.movedLattice_indexZero_normalFrame_component (G i) (PP i) b β (hloc i) ((G i).s + 1) (zero_add _) Λ Lm hfr (hmv _))⟩⟩

theorem sMoves_of_moves {S : HSp D} {t g : GA D S} {Λ L L' M : Lat S} {p : GlobalTheory.FinPl.Pl D} {c : AE D}
    (h : Moves S t Λ L (· = p)) (h' : Moves S t Λ L' (· = p)) (hs : SMoves S c g L M p) : SMoves S c g L' M p := by
  intro y hy
  have := moves_trans (moves_symm h') h y hy
  rw [mul_inv_cancel, mt_one', Matrix.one_mulVec] at this
  exact this.trans (hs y hy)

set_option maxHeartbeats 2000000 in

theorem stab_match : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ (u : D.what₂.Word) (f : FamCh W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), Placed f B → Framed B → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (W.S.tr u) a₀ → ∃ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) ∧ GlobalTheory.LevZero.StabAt f B a₀ a := by
  intro D L hT Gi Gl Kc Yd cX ex W hW u f B hPl hFr a₀ ha₀
  obtain ⟨k, _, _, _, _, ι, v, o, n, G, pl, hc, hv, hVT, hSh, hGP, hGR, hBT⟩ := hPl
  have hbot := GlobalTheory.LevZero.bot_of_placedBy W hW u f B k ι v o n G pl ⟨hc, hv, hVT, hSh, hGP, hGR, hBT⟩
  obtain ⟨μ, lam, hμ, hl, hz', he, he'⟩ := hFr
  have hF : B.FrameAt μ lam :=
    ⟨hμ, hl, funext fun r => funext fun a => he r a, funext fun r => funext fun a => he' r a, funext fun r => hz' r⟩
  have h0 : 0 + 2 * D.R.rS + 2 = D.R.m := by have := D.R.rS_two; omega
  have hm : 0 < D.R.m := by omega
  have hE : GlobalTheory.Core.Mi.IdE W.S.X := hW.bot.idE
  have hLM := hW.bot.hyp.2.1 u
  have hBa := hBT.adapted
  have hψ : IsStdChar D W.Q.Rl.ψ (-1) := hc.std
  have hb : @Eq (BesAt (f.c.V 0) (f.c.X 0) D.R.rS) (f.c.bes 0 D.R.rS h0) (toBes B) := eq_toBes B _ _ (hBT.lev h0)
  have hΛ : IsSelfDualC (Yc D 0) ((pk W).ΛY 0) := hbot.mem.selfDual
  have hfr : Formalism.L2.DIV.IsFrame ((pk W).βY 0) ((pk W).ΛY 0) := hbot.mem.frame
  obtain ⟨Lm, hLm, hmv⟩ := GlobalTheory.FinPl.GlobImage.image_moves (Yc D 0) ((pk W).ΛY 0) hΛ (f.g.b 0)
  have hloc : ∀ i, LocAt (G i) (pl i).1 (f.g.b 0) ((pk W).βY 0) := fun i => by
    have := hbot.loc (pl i)
    rwa [Equiv.symm_apply_apply] at this
  have hC := facts o G h0 hc hSh (fun i => (pl i).1) (f.g.b 0) ((pk W).βY 0) hloc ((pk W).ΛY 0) Lm hfr hmv
  rw [hb] at hC
  obtain ⟨M, c1, c2, c3, c4⟩ := hC
  obtain ⟨s1, s2, s3, -, -, s6⟩ := rows_shape hE hF
  obtain ⟨-, z2, -⟩ := GlobalTheory.T.besselLevelLineVector_primitive_rowLattice_norm D W.S.X W.Q.instEq u W.Q.Rl.ψ _ B μ lam hE hF
  have loc : ∀ p : GlobalTheory.FinPl.Pl D, ∃ (a : GA D (D.sp.X 0)) (c : AE D), CenAt (D.sp.X 0) p a ∧ NormOneAt p c ∧
      SMoves (D.sp.Y 0) c (embA B.d B.o (a₀ * a)) Lm (latS D) p := by
    intro p
    by_cases hpg : p ∈ v.gP
    · obtain ⟨i, rfl⟩ := (hGP.places p).1 hpg
      have hpT : (G i).q.v ∉ v.tP := Finset.disjoint_left.1 hv.disj hpg
      obtain ⟨q⟩ : Nonempty (GlobalTheory.LatPair.Unif (G i).k) := inferInstance
      have hϖ := (GlobalTheory.SeeSaw.LevelTest.val_eq_unif (G i).q (hloc i).idem q (hbot.typ.1 (pl i).1 (pl i).2)
        (GlobalTheory.SeeSaw.LevelTest.g_notMem_sq (pl i).1)).trans (GlobalTheory.SeeSaw.LevelTest.unif_val q (G i).S.unif)
      exact loc_level hE hF hLM hBa ha₀ (G i).q (G i).unit _ (by simpa using hϖ) (fun h => hpT ((hVT.tP _).2 h))
        (c4 i).1 hLm (hBT.lat _ hpT) (c4 i).2
    · have hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∉ p.asIdeal := by
        intro h
        obtain ⟨PP, ⟨h1, h2⟩, -⟩ := hbot.typ.2 p h
        exact hpg ((hVT.gP p).2 ⟨PP, h1, h2.symm⟩)
      have hpS : p ∉ (GlobalTheory.BaseChain.com W).S := by
        intro h
        obtain ⟨PP, h1, h2⟩ := Finset.mem_image.1 h
        exact hpg ((hVT.gP p).2 ⟨PP, h1, h2.symm⟩)
      have hN : Moves (Yc D 0) (f.g.b 0) ((pk W).ΛY 0) (v.N 0) (· = p) := hVT.moves 0 hm _ fun p' hp' => hp' ▸ hpg
      obtain ⟨d1, d2, d3, d4⟩ := c1 p
      suffices H : ∃ (a : GA D (D.sp.X 0)) (c : AE D), CenAt (D.sp.X 0) p a ∧ NormOneAt p c ∧
          SMoves (D.sp.Y 0) c (embA B.d B.o (a₀ * a)) (v.N 0) (latS D) p by
        obtain ⟨a, c, h1, h2, h3⟩ := H
        exact ⟨a, c, h1, h2, sMoves_of_moves (S := D.sp.Y 0) hN (hmv _) h3⟩
      refine loc_of_core hψ hE hF hg (hv.sd 0 hm) d1 d2 d3 d4 ?_
      by_cases hpT : p ∈ v.tP
      · have hTv := (hVT.tP p).1 hpT
        obtain ⟨i, rfl⟩ := (hSh.pre.tP p).1 hpT
        obtain ⟨β₀, e1, e2⟩ := c3 i
        have hr : 3 ≤ Fintype.card (Fin (D.sp.X 0).rank) := by
          have h1 := D.R.m_add_three_le_k
          rw [Fintype.card_fin, D.sp.X_rank 0 (Nat.zero_le _), Ranks.N]
          omega
        refine GlobalTheory.T.exists_central_element_homothetic_gluedCores D k (o.p i) _ _ _ B.o B.ζ _ (o.β 0 i) β₀ M _ μ _ o.q (o.Q 0 i) a₀ hr e1 d1 s2 e2 hF.ne (s6 _) z2
          (GlobalTheory.SeeSaw.LevelTest.unifT_of _ _ hTv) fun a ha => ?_
        obtain ⟨y, hy, hU⟩ := GlobalTheory.T.columnLevel_iff_rowLattice_kept_at_place D W.S.X W.Q.instEq u W.Q.Rl.ψ (F0 W u) (W.S.tr u) W.S.Y.hK B a₀ hE hLM hBa ha₀ _ hg a ha
        have c5 : (y : GL _ _) ∈ (F0 W u).cls0.lev.U ↔ Moves (D.sp.Y 0) (embA B.d B.o a) (v.N 0) (v.N 0) (· = (o.p i).v) :=
          (hBT.trace a (mem_GfC_of_grpAt ha) y hy).1.trans
            ((GlobalTheory.T.mem_chainLevel_iff_carriesLattice_offLevel D (GlobalTheory.BaseChain.com W) 0 (stZero W).st hbot.mem _ hpS _
              (conj_mem_grpAt (S := D.sp.Y 0) (embA_mem_grpAt _ _ ha) _)).trans (moves_conj (S := D.sp.Y 0) hN _))
        exact ((GlobalTheory.T.wittCoreEmbedding_stabilises_iff_core_stabilises D _ _ _ B.d _ _ _ _ d2).symm.trans (c5.symm.trans hU)).trans
          (GlobalTheory.T.wittCoreEmbedding_stabilises_iff_core_stabilises D _ _ _ B.d _ _ _ _ (s3 _))
      · obtain ⟨LL, e1, e2⟩ := c2 p hpT
        have hTv : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ p.asIdeal := fun h => hpT ((hVT.tP p).2 h)
        exact GlobalTheory.T.orthogonalSumCores_homothetic_off_level D _ _ _ B.o B.ζ M _ (f.g.x 0).L LL μ _ p a₀ B.line e1 e2
          (rows_trace hE hF hLM hBa ha₀ p (hBT.lat p hpT))
          (GlobalTheory.T.selfDualLattice_splitsOff_unitNormLine_at_place D _ _ _ B.o B.ζ _ μ _ p B.line s2 hF.ne (s6 p) z2 hTv) hF.ne (s6 p) z2 hTv
  obtain ⟨a, haf, hac, z, hz, hmvz⟩ := GlobalTheory.T.exists_central_glue_localHomotheties D (D.sp.Y 0) (D.sp.X 0) (embA B.d B.o) (embA B.d B.o a₀) Lm
    (latS D) hLm s1 (fun v a ha => embA_mem_grpAt _ _ ha) (fun v => by simpa only [map_mul] using loc v)
  rw [← map_mul] at hmvz
  exact ⟨a, haf, hac, stab_of_frame W.S.X W.Q.instEq u ((pk W).βY 0) _ _ z hz
    (GlobalTheory.T.isFrame_finitePart_mul_of_carries_lattice D (D.sp.Y 0) _ ((pk W).ΛY 0) (latS D) ((pk W).βY 0) (moves_trans (hmv _) hmvz) hfr)⟩

end GlobalTheory.LevZero.StabMatch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsSatisfyFlatLawsFinitePlacesStatement
section
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces : ∀ D : D7, GlobalTheory.FinPl.FlatLaws D := by
  first | exact @GlobalTheory.FinPl.flatLaws_all | exact GlobalTheory.FinPl.flatLaws_all | (intros; apply GlobalTheory.FinPl.flatLaws_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GlobalFormOfSiegelWeilStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_form_of_siegel_weil : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → GlobalTheory.Published.DoublingMethod → ∀ D : D7, GlobalForm D := by
  first | exact @GlobalTheory.Core.Rk.IP.globalForm_of_siegelWeil | exact GlobalTheory.Core.Rk.IP.globalForm_of_siegelWeil | (intros; apply GlobalTheory.Core.Rk.IP.globalForm_of_siegelWeil <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselUnfoldedIntegrandIntegrableStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobiToBessel_unfoldedIntegrand_integrable : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ), IsQuasiFam ψ J.W₀ B.L Y → RapidDec B.V G → IsThetaFunO ψ J.W B.V Φ → ∀ 𝓑 : Set (GA D B.V), IsFundamentalDomain (GQ B.V ⊓ besGrp B.d B.o : Subgroup (GA D B.V)) 𝓑 s.vW.μ → Integrable (Function.uncurry fun h₀ h => G h * tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ)) ((J.v0.μ.restrict J.v0.𝓕).prod (s.vW.μ.restrict 𝓑)) := by
  first | exact @GlobalTheory.Unf.FB.unfolded_integrable | exact GlobalTheory.Unf.FB.unfolded_integrable | (intros; apply GlobalTheory.Unf.FB.unfolded_integrable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KappaMapsBesselLineLatticeIffSplitStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kappa_maps_besselLineLattice_iff_split : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n' n'' : Type) [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (α : ∀ i, Frame (p i) B.A n') (α₀ : ∀ i, Frame (p i) B.V₀ (n' ⊕ Fin 1)) (γ : ∀ i, Frame (p i) B'.A n'') (γ₀ : ∀ i, Frame (p i) B'.V₀ (n'' ⊕ Fin 1)) (M : Lat B.V₀) (LS : Lat S) (M' : Lat B'.V₀) (Λ : ι → Submodule 𝒪[k] (n' → k)) (Λ' : ι → Submodule 𝒪[k] (n'' → k)), IsSelfDualC B.V₀ M → IsSelfDualC S LS → IsSelfDualC B'.V₀ M' → (∀ i, IsSumFrame B.o B.ζ (α i) (α₀ i) ∧ IsSumFrame B'.o B'.ζ (γ i) (γ₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i)) ∧ (γ₀ i).IsLat M' (lastKer (Λ' i))) → ∀ x : WO S B'.L, MxAt P x → ((B'.o.resT S).symm (0, x) ∈ latO S B'.V₀ (LS : Set _) (M' : Set _) P ↔ (B.o.resS S).symm (0, l.κ S x) ∈ latO B.V₀ S (M : Set _) (LS : Set _) P) := by
  first | exact @GlobalTheory.KappaLat.kappa_line_lat_iff | exact GlobalTheory.KappaLat.kappa_line_lat_iff | (intros; apply GlobalTheory.KappaLat.kappa_line_lat_iff <;> assumption)
end

