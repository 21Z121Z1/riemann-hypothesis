import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0587
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StepZeroTwistReferenceTupleEqId
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0264
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SplitOfFactorisation
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0448
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0449
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0513
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0392
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0197
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0502
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0394
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0381
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0368
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0354
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0352
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0555
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepAverageKillsThetaOfDenseFamily
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0213
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0450
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0036
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0458
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0467
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0483
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0522
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0585
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0582
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0037
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCommutationProperty
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0466

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AllTrueFamilyGeometryColumn
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevPrimeData

open GlobalTheory.FinPl GlobalTheory.FinPl.FrameLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_mem_of_fin_int (p : SplitPt D k) {a : AE D} (ha : finPart D a ∈ intAE D) : p.pr a ∈ 𝒪[k] := by
  rw [p.int_iff, p.sec_pr, RingHom.map_mul]
  exact mul_mem_intAE (e_mem_intAt p).2 ha

theorem splitPlace_valuation_cmImaginaryGenerator_eq_one (p : SplitPt D k) (hp : p.UnitAA) : valuation k (p.pr (incA D D.host.xi0)) = 1 := by
  obtain ⟨h1, h2⟩ := hp.1 _ (e_mem_intAt p)
  have he : p.pr p.e = 1 := by rw [← sec_one, p.pr_sec]
  have h3 := pr_mem_of_fin_int p h1.2
  have h4 := pr_mem_of_fin_int p h2.2
  rw [RingHom.map_mul, he, mul_one, Valuation.mem_integer_iff] at h3 h4
  have h5 : valuation k (p.pr (incA D D.host.xi0)) * valuation k (p.pr (incA D D.host.xi0⁻¹)) = 1 := by
    rw [← map_mul, ← RingHom.map_mul, ← RingHom.map_mul, mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), RingHom.map_one,
      RingHom.map_one, map_one]
  refine le_antisymm h3 ?_
  rw [← h5]
  exact mul_le_of_le_one_right' h4

theorem splitPlace_valuation_neg_cmGenerator_pow_eq_one (p : SplitPt D k) (hp : p.UnitAA) (n : ℕ) :
    valuation k (p.pr (incA D (-D.host.xi0 ^ n))) = 1 ∧ valuation k (p.pr (incA D (star (-D.host.xi0 ^ n)))) = 1 := by
  have h := splitPlace_valuation_cmImaginaryGenerator_eq_one p hp
  refine ⟨?_, ?_⟩
  · rw [RingHom.map_neg, RingHom.map_neg, RingHom.map_pow, RingHom.map_pow, Valuation.map_neg, map_pow, h, one_pow]
  · rw [star_neg, star_pow, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, RingHom.map_neg, RingHom.map_neg, RingHom.map_pow, RingHom.map_pow,
      RingHom.map_neg, RingHom.map_neg, Valuation.map_neg, map_pow, Valuation.map_neg, h, one_pow]

end GlobalTheory.LevPrimeData

theorem GlobalTheory.LevPrimeData.data_preT : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ : ℕ → ℂ) (v : VCom (commOf (pk W) u g)) (ζ₀ : Fin g.Lz.rank → (I.rec7 l Z).host.E), GlobalTheory.AdForm.PinX I l Z (pk W).ψ (pk W).θ g.x g.vac c₀ → v.NT = (pk W).ΛX → (∀ p, p ∈ v.tP ↔ ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ p.asIdeal) → IsLineVec g.Lz ζ₀ → (∀ r, vecB (g.oT B.R.m rfl) ζ₀ r = (show Fin (B.R.N B.R.m) → (I.rec7 l Z).host.E from TC.z0 X u) (Fin.cast (Formalism.L2.Forms.rankN (I.rec7 l Z) _ le_rfl) r)) → GlobalTheory.AdForm.IsEmbTop (D := I.rec7 l Z) (TC.z0 X u) ((g.oT B.R.m rfl).emb.comp (MonoidHom.inl _ _)) → (∀ x : GlobalTheory.FinPl.Pl (I.rec7 l Z), ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ x.asIdeal → ∃ LZ : GlobalTheory.FinPl.Lat g.Lz, GlobalTheory.FinPl.OrthAt (g.oT B.R.m rfl) (g.x B.R.m).L (pk W).ΛX LZ x) → (∀ j h, (v.τ j h)ᴴ * ((g.bes j 0 h).L.gram * v.τ j h) = (-((I.rec7 l Z).host.xi0 * star (I.rec7 l Z).host.xi0)) • g.Lz.gram ∧ v.τ j h *ᵥ ζ₀ = (-(I.rec7 l Z).host.xi0 ^ (B.R.m / 2)) • (g.bes j 0 h).ζ) → ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (ι : Type) (o : TDat (commOf (pk W) u g) k ι), PreT v o ∧ o.ζ₀ = ζ₀ ∧ GlobalTheory.AdForm.StdT I l Z u o.p o.β o.Q fun j => (g.x j).L := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u g c₀ v ζ₀ hPin hNT htP hline hz hemb hort htau
  obtain ⟨pins⟩ := hW.tr.pins
  obtain ⟨k, _, _, _, _, ι, p, J, q, χ, β, Q, hPl, hch, -, hval, hpl, hb, hStd⟩ :=
    GlobalTheory.T.standardPairs_exist_at_levelPrime I hW.tr.ok pins l Z u (pk W).ψ hPin.std (fun j => (g.x j).L) (fun j hj z => (hPin.xs j hj).2.2 z)
  have hG : ∀ j, ((I.rec7 l Z).sp.X j).gram = 1 := fun j => hW.tr.ok.gram_X j
  have hz' : ∀ r : Fin ((I.rec7 l Z).sp.X B.R.m).rank, vecB (g.oT B.R.m rfl) ζ₀ r =
      if r.1 + 1 = ((I.rec7 l Z).sp.X B.R.m).rank then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 0 := by
    intro r
    rw [hz r]
    have e : ((I.rec7 l Z).sp.X B.R.m).rank = B.R.N B.R.m := Formalism.L2.Forms.rankN (I.rec7 l Z) _ le_rfl
    show (if r.1 + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 0) = _
    rw [← e]
  have hpos : 0 < ((I.rec7 l Z).sp.X B.R.m).rank := by
    have h1 := (g.oT B.R.m rfl).rank_add
    have h2 : g.Lz.rank = 1 := hline.1
    omega
  have htop := fun i => GlobalTheory.StdPairTop.ker_stdPair _ k (p i) q _ _ _ (g.oT B.R.m rfl) (hG _) ζ₀ hline (X.piT u) _ hz' (hval i).1 (hval i).2
    (g.x B.R.m).L v.NT (fun z => (hPin.xs _ le_rfl).2.2 z)
    (by obtain ⟨LZ, h⟩ := hort (p i).v ((hpl _).1 ⟨i, rfl⟩); exact ⟨LZ, hNT ▸ h⟩)
    (β B.R.m i) (Q B.R.m i) (hb _ _) ((hStd.2 _ le_rfl).2 i).1 ((hStd.2 _ le_rfl).2 i).2
  choose γ γ₀ hγ using htop
  have hcore : ∀ j ρ h i, Nonempty (GlobalTheory.FinPl.Frame (p i) (g.bes j ρ h).V₀ (Fin ((I.rec7 l Z).sp.X j).rank ⊕ Fin 1)) := by
    intro j ρ h i
    obtain ⟨γ', -⟩ := ((GlobalTheory.T.exists_splitPoint_frame_character _).2 k (p i)).1 (g.bes j ρ h).V₀ (Fin (g.bes j ρ h).V₀.rank) 1 1
      (Matrix.mul_one _) (Matrix.mul_one _)
    obtain ⟨α, -⟩ := ((GlobalTheory.T.exists_splitPoint_frame_character _).2 k (p i)).1 ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank) 1 1
      (Matrix.mul_one _) (Matrix.mul_one _)
    obtain ⟨β₀, -⟩ := GlobalTheory.FinPl.DblInh.exists_sumFrame (g.bes j ρ h).o (g.bes j ρ h).line α γ'
    exact ⟨β₀⟩
  refine ⟨k, inferInstance, inferInstance, inferInstance, inferInstance, ι,
    ⟨p, J, q, χ, fun i => (hch i).1, β, Q, fun j ρ h i => (hcore j ρ h i).some, fun _ _ _ => ⊥, ζ₀, γ,
      fun n h i => h ▸ γ₀ i⟩, ?_, rfl, hStd⟩
  refine ⟨hPl.nodup, hPl.all, hPl.inj, fun x => (htP x).trans (hpl x).symm, fun i => ⟨(hch i).2, hPl.unit i⟩,
    fun j hj i => ((hStd.2 j hj).2 i).1, hline, fun j h => (htau j h).1,
    fun j h => ⟨_, (htau j h).2, fun i => GlobalTheory.LevPrimeData.splitPlace_valuation_neg_cmGenerator_pow_eq_one (p i) (hPl.unit i) _⟩,
    fun i => GlobalTheory.MiStar.normLast_valuation _ k (p i) q _ _ _ (g.oT B.R.m rfl) hpos (hG _) ζ₀ _ hz' (hval i).1 (hval i).2, fun n h i => ?_⟩
  subst h
  obtain ⟨h1, Λ, s, h2, h3, h4⟩ := hγ i
  exact ⟨h1, Λ, s, hNT ▸ h2, h3, h4⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseLatLineOffT
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

namespace GlobalTheory

theorem baseLat_line_offT : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ (hr : 1 ≤ D.R.rS) u (f : FamCh W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), GlobalTheory.MiTop.PlacedP f B → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ (pk W).Pg, PP.under (𝓞 D.host.F) ≠ v) → (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal → ∀ u'' : D.what₂.Word, (((D.mem u'').A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal → ∀ c ∈ GlobalTheory.FinPl.idAt D (· = v), (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹) ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) ∈ GlobalTheory.FinPl.latV (D.sp.Y 0) ((pk W).ΛY 0) (· = v) ↔ c ∈ GlobalTheory.FinPl.intAt D (· = v)) := by

  intro D L hT Gi Gl Kc Yd cX ex W hW hr u f B hP x hxg hxt u'' hxu c hc
  obtain ⟨k, _, _, _, _, ι, v', o, n, G, pl, hc0, hv0, hvt, hso, hgp, hgr, hbt, hpt⟩ := hP
  have hm : 0 < D.R.m := by unfold Ranks.rS at hr; omega
  have hxg' : x ∉ v'.gP := by
    intro h
    obtain ⟨PP, hPP, hPx⟩ := (hvt.gP x).1 h
    exact hxg PP hPP hPx.symm
  have hmv := hvt.moves 0 hm (· = x) (by rintro p rfl; exact hxg')
  set b : GA D (D.sp.Y 0) := f.g.b 0 with hb
  set w : Fin (D.sp.Y 0).rank → AE D := fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))) with hw
  have hy : ∀ i, (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) b⁻¹) w) i ∈ idAt D (· = x) := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    refine Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ ?_
    exact Ideal.mul_mem_right _ _ hc
  have key : (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) b⁻¹) w ∈ latV (D.sp.Y 0) ((pk W).ΛY 0) (· = x) ↔
      Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) b) (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) b⁻¹) w) ∈ latV (D.sp.Y 0) (v'.N 0) (· = x)) :=
    hmv _ hy
  have hinv : Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) b) (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) b⁻¹) w) = w := by
    rw [Matrix.mulVec_mulVec]
    simp only [Formalism.L2.Theta.mt, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec]
  rw [hinv] at key
  refine key.trans ?_

  exact GlobalTheory.T.bessel_local_component_data W hW hr u f B k ι v' o n G pl hc0 hv0 hvt hso hgp hgr hbt hpt x hxg'
    (fun h => hxt ((hvt.tP x).1 h)) u'' hxu c hc

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodDoubleStepUnfoldingOfDescentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselPeriod_double_step_unfolding_of_descent : ∀ D : D7, Descent D → DoubleStep D := by
  first | exact @GlobalTheory.Unf.doubleStep_of_descent | exact GlobalTheory.Unf.doubleStep_of_descent | (intros; apply GlobalTheory.Unf.doubleStep_of_descent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelPairActionFiniteDatumLaw
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.LevLaw

theorem latFr_stdLat (D : D7) (S : HSp D) (a : ℕ) (hS : S.rank = a) :
    latFr S hS (Formalism.L2.Col.stdLat D.host.E a) = intVec D S.rank := by
  subst hS
  rw [GlobalTheory.LatPairMove.latFr_rfl, coe_colStdLat]

theorem mem_stdHom_iff_actO (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (k : GA D S) (k' : GA D T)
    (h1 : Moves S hS 1 (Formalism.L2.Col.stdLat D.host.E a)) (h1' : Moves T hT 1 (Formalism.L2.Col.stdLat D.host.E b))
    (hk : Moves S hS k (Formalism.L2.Col.stdLat D.host.E a)) (hk' : Moves T hT k' (Formalism.L2.Col.stdLat D.host.E b)) :
    ∀ x, x ∈ stdHom S T ↔ actO S T k k' x ∈ stdHom S T := by
  have key := GlobalTheory.LatPairMove.latO_move D S T a b hS hT 1 k 1 k' _ _ _ _ h1 h1' (by rwa [mul_one]) (by rwa [mul_one])
  rw [latFr_stdLat, latFr_stdLat] at key
  intro x
  constructor
  · intro hx
    exact (key _).2 ⟨x, hx, rfl⟩
  · intro hx
    obtain ⟨u₀, hu₀, he⟩ := (key _).1 hx
    have hinv : ∀ v, actO S T k⁻¹ k'⁻¹ (actO S T k k' v) = v := fun v => by
      have := GlobalTheory.AdelicLatMove.actO_actO_inv S T k⁻¹ k'⁻¹ v
      rwa [inv_inv, inv_inv] at this
    have := congrArg (actO S T k⁻¹ k'⁻¹) he
    rw [hinv, hinv] at this
    rw [this]
    exact hu₀

theorem lev_law : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ Ch : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, Ch j → Ch₀ j) ψ θ x vac c₀ kom dd w Ram rd cK, PinX I l Z ψ θ x vac c₀ → PinColL A ι ψ θ x vac c₀ kom dd w Ram rd cK → ∀ j, j < B.R.m → ∀ α γ (κ : A.U j (ι j α)) (κ' : A.U (j + 1) (ι (j + 1) γ)), kom j (κ.1, κ'.1) (comb ψ _ _ (dd j α γ) (vac j)) = (((A.chi j _ κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (j + 1) _ κ' : ℂˣ) : ℂ)) • comb ψ _ _ (dd j α γ) (vac j) := by
  intro B X I hI hP l Z u a Ch₀ Ch A ι ψ θ x vac c₀ kom dd w Ram rd cK hX hC j hj α γ κ κ'
  have hj1 : j + 1 ≤ B.R.m := hj
  have hstd := GlobalTheory.T.trueColumnSteps_are_standardHermitianPairs I hI hP l Z ψ θ hX.std hX.inf
  have hSP := hstd.1 j hj1
  obtain ⟨xr, hxr⟩ := hstd.2.2.2.2 _ κ.1
  obtain ⟨yr, hyr⟩ := hstd.2.2.2.2 _ κ'.1
  have hU := hC.is.U j (Nat.le_of_succ_le hj1) (ι j α)
  have hU' := hC.is.U (j + 1) hj1 (ι (j + 1) γ)
  have hkG : κ.1 ∈ GfC _ := ((hU κ.1).1 κ.2).1
  have hkG' : κ'.1 ∈ GfC _ := ((hU' κ'.1).1 κ'.2).1
  have h1G : (1 : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) ∈ GfC _ := ((hU 1).1 (one_mem _)).1
  have h1G' : (1 : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X (j + 1))) ∈ GfC _ := ((hU' 1).1 (one_mem _)).1
  have hMk := GlobalTheory.T.chartLevels_keep_standardLattice I hI hP l Z u a Ch₀ A hC.is j (Nat.le_of_succ_le hj1) (ι j α) κ.1 κ.2
  have hMk' := GlobalTheory.T.chartLevels_keep_standardLattice I hI hP l Z u a Ch₀ A hC.is (j + 1) hj1 (ι (j + 1) γ) κ'.1 κ'.2
  have hM1 := GlobalTheory.T.chartLevels_keep_standardLattice I hI hP l Z u a Ch₀ A hC.is j (Nat.le_of_succ_le hj1) (ι j α) 1 (one_mem _)
  have hM1' := GlobalTheory.T.chartLevels_keep_standardLattice I hI hP l Z u a Ch₀ A hC.is (j + 1) hj1 (ι (j + 1) γ) 1 (one_mem _)
  have hom := hC.om j hj
  have hVT := (hX.mv j hj1).2 a (A.chr (j + 1)) (kom j) (hC.is.chr ⟨j, hj⟩) hom
  have e1 := hVT κ.1 hkG κ'.1 hkG' _ _ hMk hMk' xr yr hxr hyr
  have e0 := hVT 1 h1G 1 h1G' _ _ hM1 hM1' 1 1 (GlobalTheory.SmallFix.isDetRoot_one _) (GlobalTheory.SmallFix.isDetRoot_one _)
  have h11 : kom j ((1 : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)), (1 : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X (j + 1)))) = 1 :=
    map_one (kom j)
  set p : ℂ := ((A.chr (j + 1) xr : ℂ))⁻¹ * (A.chr (j + 1) yr : ℂ) with hpdef
  have hvth : IsThetaFunO ψ _ _ (vac j) := (hX.vc j hj).2.theta
  have hp : kom j (κ.1, κ'.1) (vac j) = p • vac j := by
    have hf : IsThetaFunO ψ _ _ (kom j (κ.1, κ'.1) (vac j) - p • vac j) :=
      GlobalTheory.AvgKill.theta_sub' (hom.om_pres _ _ hvth) (GlobalTheory.LocMod.LinSpace.isThetaFunO_smul p hvth)
    have hz : xiN θ _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj1)) (rankN (I.rec7 l Z) (j + 1) hj1) I.A.δ I.A.sc
        (kom j (κ.1, κ'.1) (vac j) - p • vac j) = 0 := by
      funext z
      have a1 := congrFun e1 z
      have a0 := congrFun e0 z
      rw [h11] at a0
      simp only [ColDat.xiS, xiN, Module.End.one_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply, map_one, Circle.coe_one, inv_one, mul_one] at a1 a0 ⊢
      rw [hpdef, mul_sub, show ∀ q r s : ℂ, q * (r * s) = r * (q * s) from fun q r s => by ring]
      erw [a1, a0]
      ring
    exact sub_eq_zero.1 ((GlobalTheory.T.gaussianTwistedRealReading_entire_and_injective _ ψ θ _ _ _ _ _ _ _ _ hSP).2 _ hf hz)
  obtain ⟨-, Φ, hΦ, hΞ, hth⟩ := hC.dat j hj1 α γ
  have hq : ∀ z, IsHalf A.e z → p * Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ z) =
      (((A.chi j _ κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (j + 1) _ κ' : ℂˣ) : ℂ)) * Φ z := fun z hz =>
    GlobalTheory.T.finite_datum_law_under_two_chart_levels I hI hP l Z u a Ch₀ A hC.is j hj1 (ι j α) (ι (j + 1) γ) Φ hΦ (w j α γ) (fun z => hΞ z) κ κ' xr yr hxr hyr z hz
  have hlat := mem_stdHom_iff_actO (I.rec7 l Z) _ _ _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj1))
    (rankN (I.rec7 l Z) (j + 1) hj1) κ.1 κ'.1 hM1 hM1' hMk hMk'
  exact GlobalTheory.T.weilAction_eq_smul_of_keeps_lattice (I.rec7 l Z) ψ θ _ _ _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj1)) (rankN (I.rec7 l Z) (j + 1) hj1)
    I.A.δ I.A.sc hSP (A.chr (j + 1)) (kom j) hom A.e _ hC.is.idem (vac j) Φ _ (hX.vc j hj) hΦ hth κ.1 hkG κ'.1 hkG' hlat p _ hp hq

end GlobalTheory.AdForm.LevLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemLevelOfThetaDatumNeZeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitePart_mem_level_of_thetaDatum_ne_zero : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank) (χ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (e : AE D), IsSelfDualC S ΛS → Formalism.L2.DIV.IsFrame βS ΛS → S.rank ≤ T.rank → L.Q = ∅ → IsIdemSum e (L.Pg ∪ ∅) → ∀ g : GA D S, (∀ v, (∀ PP ∈ L.Pg, PP.under (𝓞 D.host.F) ≠ v) → GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig S.gram ΛS v) → ∀ x, (fun x : WO S T => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ ∅ L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) x ≠ 0 → (fun x : WO S T => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ ∅ L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) (actO S T g 1 x) ≠ 0 → Lev.finE S g ∈ Formalism.L2.DIV.lev D.sp.cm S.gram βS L := by
  first | exact @GlobalTheory.SuppLevO.finE_mem_lev | exact GlobalTheory.SuppLevO.finE_mem_lev | (intros; apply GlobalTheory.SuppLevO.finE_mem_lev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPrimeOperatorsActRamifiedColumnsVanishing
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms NumberField Matrix GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.AdForm ValuativeRel IsLocalRing

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sOp_zero_fun {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : Frame p S n) (P : Pair k n) (q : Unif k)
    (χ : AddChar 𝓀[k] ℂ) (ε : 𝓀[k]ˣ) : sOp β P q χ ε 0 = 0 := by
  have h0 : formAt β P 0 = 0 := by
    funext P₁
    simp [formAt]
  simp [sOp, h0]

theorem foldr_sOp_zero_fun {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ι : Type} {p : ι → SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : ∀ i, Frame (p i) S n)
    (P : ι → Pair k n) (q : Unif k) (χ : ι → AddChar 𝓀[k] ℂ) (η : ι → 𝓀[k]ˣ) (J : List ι) :
    J.foldr (fun i f => sOp (β i) (P i) q (χ i) (η i) f) 0 = 0 := by
  induction J with
  | nil => rfl
  | cons i J ih => simp only [List.foldr_cons, ih]; exact sOp_zero_fun _ _ _ _ _

theorem infM_one_eq {D : D7} (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (τ : D.what₂.Tau) :
    infM θ V hn 1 τ = 1 := by
  simp [infM, Formalism.L2.Theta.mt, Datum.compAt]

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
  {Ch : ℕ → Type}

theorem TwDat.rd_eq_zero_of_vanish (A : TwDat I l Z u a Ch) (θ : InfFam (I.rec7 l Z)) (j : ℕ) (hj : j ≤ B.R.m) (b : Ch j)
    (φ : ColT I l u a j) (hφ : ∀ c, A.chOf j c = b → φ c = 0) (y : (I.chain l u a).Y j) : A.rd θ j hj b φ y = 0 := by
  funext g
  unfold TwDat.rd rdS
  split_ifs with h
  · simp [hφ _ h.choose.1.2, atFr]
    intro _
    rfl
  · rfl

theorem twS_ramL : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch₀ Ch : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ιc : ∀ j, Ch j → Ch₀ j), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, GlobalTheory.FinPl.Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank)) (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)), StdT I l Z u p β Q L → ∀ (J : List ι) (q : Unif k) (χ : ι → AddChar k Circle) (hχ : ∀ i, HasConductor (χ i) 1), ∃ S : ∀ j, (ι → 𝓀[k]ˣ) → ColT I l u a j → ColT I l u a j, ∀ j (hj : j ≤ B.R.m) φ, A.RamL ιc j φ → (∀ b y, IsContAut _ (A.rd θ j hj b φ y) ∧ ∀ i, GlobalTheory.FinPl.RamAt (β j i) (Q j i) (A.rd θ j hj b φ y)) ∧ ∀ η, A.RamL ιc j (S j η φ) ∧ ∀ b y, A.rd θ j hj b (S j η φ) y = J.foldr (fun i f => sOp (β j i) (Q j i) q (resChar (χ i) (hχ i) q) (η i) f) (A.rd θ j hj b φ y) := by
  intro B X I hOk hPins l Z u a Ch₀ Ch A ιc hA θ hθ k _ _ _ _ ι p β Q L hStd J q χ hχ
  obtain ⟨S, hS⟩ := GlobalTheory.T.levelPrime_operators_act_on_ramified_columns I hOk hPins l Z u a Ch₀ A hA θ hθ k ι p β Q L hStd J q χ hχ
  refine ⟨S, fun j hj φ hφ => ?_⟩
  obtain ⟨h1, h2⟩ := hS j hj φ hφ.1
  refine ⟨h1, fun η => ⟨⟨(h2 η).1, ?_⟩, (h2 η).2⟩⟩
  intro c hc
  have hrd0 : ∀ y, A.rd θ j hj (A.chOf j c) φ y = 0 := fun y =>
    TwDat.rd_eq_zero_of_vanish A θ j hj _ φ (fun c' hc' => hφ.2 c' (by rw [hc']; exact hc)) y
  have hrdS : ∀ y, A.rd θ j hj (A.chOf j c) (S j η φ) y = 0 := by
    intro y
    rw [(h2 η).2, hrd0]
    exact foldr_sOp_zero_fun _ _ _ _ _ _
  funext y'
  have hTr : IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) j hj) 1) ⟨y'.1, y'.2⟩ ⟨y'.1, y'.2⟩ := by
    intro τ
    rw [infM_one_eq]
    first
    | exact (Matrix.one_mul _).symm
    | exact (one_mul _).symm
    | exact (one_smul _ _).symm
    | (show _ = _; simp [Matrix.one_mul])
  have key := (GlobalTheory.T.scalarForms_on_charts_of_trueColumnTuple I hOk hPins l Z u a Ch₀ A hA θ hθ j hj (S j η φ) (h2 η).1.1).2 (A.chOf j c) y' 1 (one_mem _)
    ⟨c, rfl⟩ 1 (one_mem _) 1 y' hTr
  rw [hrdS] at key
  simpa using key.symm

end GlobalTheory.AdForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentPlacesCharacterized
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CommonVac

theorem latV_eq_of_moves {D : D7} {S : HSp D} {g : GA D S} {Λ M N : GlobalTheory.FinPl.Lat S} {P : GlobalTheory.FinPl.Pl D → Prop}
    (hM : GlobalTheory.FinPl.Moves S g Λ M P) (hN : GlobalTheory.FinPl.Moves S g Λ N P) :
    GlobalTheory.FinPl.latV S M P = GlobalTheory.FinPl.latV S N P := by
  have h1 : GlobalTheory.FinPl.Moves S (g * g⁻¹) M N P := GlobalTheory.StMoves.moves_mul (GlobalTheory.StMoves.moves_inv hM) hN
  rw [mul_inv_cancel] at h1
  have e1 : ∀ y : Fin S.rank → AE D, mt S (1 : GA D S) *ᵥ y = y := fun y => by
    rw [show mt S (1 : GA D S) = 1 from rfl, Matrix.one_mulVec]
  ext y
  constructor
  · intro hy
    have := (h1 y (GlobalTheory.FinPl.FrameLat.latV_supp hy)).1 hy
    rwa [e1] at this
  · intro hy
    have h2 := h1 y (fun i => by
      have := GlobalTheory.FinPl.FrameLat.latV_supp hy i
      exact this)
    rw [e1] at h2
    exact h2.2 hy

end GlobalTheory.CommonVac

namespace GlobalTheory.CommonVac

theorem exists_common_vacua : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b : ∀ j, GA D (Yc D j)) (v : VCom (commOf (pk W) u (mkGeo m b))), (commOf (pk W) u (mkGeo m b)).Is → v.τ = y.τ → v.NT = a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = PP.under (𝓞 D.host.F)) → GlobalTheory.Core.Mi.IsTypePlaces (pk W).Pg → (∀ j, b j ∈ GfC (Yc D j)) → a.bT ∈ GfC D.sp.X' → IsSelfDualC D.sp.X' a.LT → (∀ P, GlobalTheory.FinPl.Moves D.sp.X' a.bT (pk W).ΛX a.LT P) → (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (v.N j) ∧ ∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ p, P p → p ∉ v.gP) → GlobalTheory.FinPl.Moves (Yc D j) (b j) ((pk W).ΛY j) (v.N j) P) → v.b = b → v.bT = a.bT → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal) → ∃ (Ψ : ∀ j, PolF D (Yc D (j + 1)).rank (Yc D j).rank → GA D (Yc D j) → GA D (Yc D (j + 1)) → WO (Yc D j) (Yc D (j + 1)) → ℂ) (ΨT : ∀ j, j + 2 * 0 + 2 = D.R.m → PolF D D.sp.X'.rank (Yc D (j + 1)).rank → WO (Yc D (j + 1)) D.sp.X' → ℂ), (∀ j, j + 1 < D.R.m → ∀ P, ∀ x ∈ GinfC _, ∀ x' ∈ GinfC _, GlobalTheory.FinPl.Vac (pk W).ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) (Ψ j P x x')) ∧ (∀ j h P, GlobalTheory.FinPl.Vac (pk W).ψ _ _ (v.N (j + 1)) v.NT (fun _ => True) (ΨT j h P)) ∧ ∀ j row col, VTie (⟨mkGeo m b, j, row, col⟩ : FamCh W u) { v with Ψ := Ψ, ΨT := ΨT } := by
  intro D L hT Gi Gl Kc Yd cX ex W u hpk a y m b v hc hτ hNT hgP hTy hb hbT hLT hmT hN hvb hvbT htP

  have hQ : ∀ p ∈ v.gP, ((∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D p ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) ∧ (∀ a ∈ GlobalTheory.FinPl.intAt D (· = p), incA D D.host.xi0 * a ∈ GlobalTheory.FinPl.intAt D (· = p) ∧ incA D D.host.xi0⁻¹ * a ∈ GlobalTheory.FinPl.intAt D (· = p)) ∧ ∀ (V : HSp D) (Λ : GlobalTheory.FinPl.Lat V), GlobalTheory.FinPl.latA V Λ (· = p) = GlobalTheory.FinPl.latV V Λ (· = p)) := by
    intro p hp
    obtain ⟨PP, hPP, rfl⟩ := (hgP p).1 hp
    exact GlobalTheory.T.type_places_split_idempotents W hpk hTy PP hPP

  have hY : ∀ j, ∃ o : WO (Yc D j) (Yc D (j + 1)) →₀ ℂ, j + 1 < D.R.m →
      GlobalTheory.FinPl.CombAt (· ∈ v.gP) o ∧
      (∀ P, ∀ x ∈ GinfC (Yc D j), ∀ x' ∈ GinfC (Yc D (j + 1)), GlobalTheory.FinPl.Vac (pk W).ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True)
        (comb (pk W).ψ _ _ o ((pk W).ωY W.P.A3.A.μ0 j (x * b j, x' * b (j + 1)) (pureTensorO (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) ((pk W).vac j) P)))) ∧
      comb (pk W).ψ _ _ o ((pk W).ωY W.P.A3.A.μ0 j (b j, b (j + 1))
        (pureTensorO (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) ((pk W).vac j) 1)) ≠ 0 := by
    intro j
    by_cases hj : j + 1 < D.R.m
    · obtain ⟨M, hM, hMv⟩ := GlobalTheory.T.exists_self_dual_lattice_moves W hpk j (by omega) (b j)
      obtain ⟨M', hM', hM'v⟩ := GlobalTheory.T.exists_self_dual_lattice_moves W hpk (j + 1) hj (b (j + 1))
      obtain ⟨hvac, hnz⟩ := GlobalTheory.T.self_dual_lattices_consecutive_step W hpk j hj (b j) (b (j + 1)) (hb j) (hb (j + 1)) M M' hM hM' hMv hM'v
      obtain ⟨o, ho, hoV⟩ := GlobalTheory.T.exists_combination_rebase_vacuumLattices_injective D (pk W).ψ hc.std (Yc D j) (Yc D (j + 1)) M (v.N j) M' (v.N (j + 1)) v.gP hM
        (hN j (by omega)).1 hM' (hN (j + 1) hj).1 hQ (fun p hp =>
          ⟨latV_eq_of_moves (hMv (· = p)) ((hN j (by omega)).2 (· = p) (fun p' hp' => hp' ▸ hp)),
            latV_eq_of_moves (hM'v (· = p)) ((hN (j + 1) hj).2 (· = p) (fun p' hp' => hp' ▸ hp))⟩)
      have hv1 := hvac 1 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
      simp only [one_mul] at hv1
      exact ⟨o, fun _ => ⟨ho, fun P x hx x' hx' => (hoV _ (hvac P x hx x' hx')).1, (hoV _ hv1).2 hnz⟩⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose O hO using hY

  have hTs : ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∃ o : WO (Yc D (j + 1)) D.sp.X' →₀ ℂ, GlobalTheory.FinPl.CombAt (· ∈ v.gP) o ∧
      (∀ P, GlobalTheory.FinPl.Vac (pk W).ψ _ _ (v.N (j + 1)) v.NT (fun _ => True)
        (comb (pk W).ψ _ _ o (omT (pk W) W.P.A3.A.μ0 j h (b (j + 1), a.bT) (pureTensorO (pk W).ψ (pk W).θ (Yc D (j + 1)) D.sp.X' (cart ((pk W).MY (j + 1))) (cart (pk W).MX) (onb ((pk W).MY (j + 1))) (onb (pk W).MX) (vacT (pk W) j h) P)))) ∧
      comb (pk W).ψ _ _ o (omT (pk W) W.P.A3.A.μ0 j h (b (j + 1), a.bT) (pureTensorO (pk W).ψ (pk W).θ (Yc D (j + 1)) D.sp.X' (cart ((pk W).MY (j + 1))) (cart (pk W).MX) (onb ((pk W).MY (j + 1))) (onb (pk W).MX) (vacT (pk W) j h) 1)) ≠ 0 := by
    intro j h
    have hj : j + 1 < D.R.m := by omega
    obtain ⟨M', hM', hM'v⟩ := GlobalTheory.T.exists_self_dual_lattice_moves W hpk (j + 1) hj (b (j + 1))
    obtain ⟨hvac, hnz⟩ := GlobalTheory.T.self_dual_lattices_top_step W hpk j h (b (j + 1)) a.bT (hb (j + 1)) hbT M' a.LT hM' hLT hM'v hmT
    have hNT' : IsSelfDualC D.sp.X' v.NT := hNT ▸ hLT
    obtain ⟨o, ho, hoV⟩ := GlobalTheory.T.exists_combination_rebase_vacuumLattices_injective D (pk W).ψ hc.std (Yc D (j + 1)) D.sp.X' M' (v.N (j + 1)) a.LT v.NT v.gP hM'
      (hN (j + 1) hj).1 hLT hNT' hQ (fun p hp =>
        ⟨latV_eq_of_moves (hM'v (· = p)) ((hN (j + 1) hj).2 (· = p) (fun p' hp' => hp' ▸ hp)), by rw [hNT]⟩)
    exact ⟨o, ho, fun P => (hoV _ (hvac P)).1, (hoV _ (hvac 1)).2 hnz⟩
  choose OT hOT using hTs
  refine ⟨fun j P x x' => comb (pk W).ψ _ _ (O j) ((pk W).ωY W.P.A3.A.μ0 j (x * b j, x' * b (j + 1)) (pureTensorO (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) ((pk W).vac j) P)),
    fun j h P => comb (pk W).ψ _ _ (OT j h) (omT (pk W) W.P.A3.A.μ0 j h (b (j + 1), a.bT) (pureTensorO (pk W).ψ (pk W).θ (Yc D (j + 1)) D.sp.X' (cart ((pk W).MY (j + 1))) (cart (pk W).MX) (onb ((pk W).MY (j + 1))) (onb (pk W).MX) (vacT (pk W) j h) P)),
    fun j hj P x hx x' hx' => (hO j hj).2.1 P x hx x' hx', fun j h P => (hOT j h).2.1 P, ?_⟩
  intro j' row col
  exact {
    b := fun j => by rw [hvb]
    bT := ⟨hvbT, hNT⟩
    gP := hgP
    tP := htP
    moves := fun j hj P hP => (hN j hj).2 P hP
    movesT := hmT
    Ψ := fun j hj => ⟨O j, (hO j hj).1, fun P x x' => rfl⟩
    ΨT := fun j h => ⟨OT j h, (hOT j h).1, fun P => rfl⟩
    nz := ⟨fun j hj => ⟨1, by simpa only [one_mul] using (hO j hj).2.2⟩, fun j h => ⟨1, (hOT j h).2.2⟩⟩ }

end GlobalTheory.CommonVac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalDatumThetaFactorsPlaceByPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalDatum_theta_factors_placeByPlace : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → DenseRange p.pr → ∀ (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (PP : Formalism.L2.DIV.Pl D.host.E) (e : AE D), PP ∉ P → Formalism.L2.NTheta.IsIdemAt p.e PP → IsIdemSum e P → IsIdemSum (e + p.e) (@insert _ _ (@Finset.instInsert _ (Classical.decEq _)) PP P) → (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ↔ p.up FS FT x ∈ stdHom S T) → ∀ (Ξ Ξ' : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ) (Ξk : Matrix Y Y' k → ℂ), Ξk ∈ SB (Matrix Y Y' k) → (∀ γ, Ξ' γ = Ξ γ * Ξk (FT.γ * γ.map p.pr * FS.β)) → ∀ c, p.IsCombAt ψ FS FT c Ξk → ∀ f₀ f f', IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (stdHom S T) f₀ → IsRatDatum ψ S T e Ξ f₀ f → IsRatDatum ψ S T (e + p.e) Ξ' f₀ f' → f' = comb ψ S T c f := by
  first | exact @GlobalTheory.LocMod.ratDatum_factor | exact GlobalTheory.LocMod.ratDatum_factor | (intros; apply GlobalTheory.LocMod.ratDatum_factor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawTwistPlaceLawsOfRootOfUnityRescaling
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QTw

theorem laws_of_pin_resc : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → t.Is → v.Is → WeilOK (t := t) v → QPinU v w → QLaw v w ∧ QLast v w ∧ QFin v w :=
  fun D c v t w hc ht hv hW h =>
    GlobalTheory.QTw.RescTest.laws_of_qpinU v (fun w₀ h₀ =>
      ⟨GlobalTheory.T.seeSawIteratedIntegralLaw_at_twist_of_factorisation D c v t w₀ hc ht hv hW h₀, GlobalTheory.T.seeSawIteratedIntegralLawLastSteps_of_localFactorisation D c v t w₀ hc ht hv hW h₀, GlobalTheory.T.seeSawFiniteCells_at_twistPlaces_of_localFactorisation D c v t w₀ hc ht hv hW h₀⟩) w h

end GlobalTheory.QTw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCommutationPropertyStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_commutation_property : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → (commOf (pk W) u a.g).Is → ∀ t (J : QJ a t), J.ReadsStd → ∃ J' : QJ a t, J'.Reads := by
  first | exact @GlobalTheory.Fam.readsOfStd | exact GlobalTheory.Fam.readsOfStd | (intros; apply GlobalTheory.Fam.readsOfStd <;> assumption)
end

