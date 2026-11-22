import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0802
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0391
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0319
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0572
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0562
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0174
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0359
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaLiftLastStepsCouplingCosetOrbitInvari
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0515
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsRealFnNeZero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0501
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0195
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0234
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0545
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0803
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0558
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodNonvanishingOfArchimedeanInputs
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PeriodNePf

section General

variable {D : D7} {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar}

open Classical in

theorem real_translate (hθ : IsInfFam θ) {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} :
    ∀ a ∈ GinfC V, ∀ v : SmT M, ∃ v' : SmT M, ∀ T ∈ MultT θ M J χ, ∀ h, T v' h = T v (h * a) := by
  refine GlobalTheory.Core.Rk.TopOnto.real_induction hθ _ (fun v => ⟨v, fun T _ h => by rw [mul_one]⟩) (fun a b ha hb v => ?_)
    fun τ g hg v => ?_
  · obtain ⟨v₁, f1⟩ := hb v
    obtain ⟨v₂, f2⟩ := ha v₁
    exact ⟨v₂, fun T hT h => by rw [f2 T hT, f1 T hT, mul_assoc]⟩
  · induction v using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      let w : M.sm τ := ⟨M.rep τ g (v τ), GlobalTheory.Core.Rk.TopOnto.rep_mem_sm M τ hg _ (v τ).2⟩
      refine ⟨r • PiTensorProduct.tprod ℂ (Function.update v τ w), fun T hT h => ?_⟩
      rw [map_smul, map_smul, Pi.smul_apply, Pi.smul_apply,
        GlobalTheory.Core.Rk.TopOnto.multT_rel v (Function.update v τ w) (h * atTau θ V τ g) h 1 (fun m hm => by
          rw [one_mul]; exact congrFun (hm.equiv τ g hg v w rfl) h) hT, one_mul]
    | add a b ha hb =>
      obtain ⟨a', f1⟩ := ha
      obtain ⟨b', f2⟩ := hb
      exact ⟨a' + b', fun T hT h => by rw [T.map_add, T.map_add, Pi.add_apply, Pi.add_apply, f1 T hT, f2 T hT]⟩

end General

end GlobalTheory.PeriodNePf

namespace GlobalTheory.PeriodNePf

variable {D : D7}

theorem exists_kf {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (hM : M.IsRow)
    (hCR : GlobalTheory.Published.CuspRapidDecay) (hHC : GlobalTheory.Published.HarishChandraModules)
    (M₀ : DSModel (Yc D 0) (parB (Ptw D) 0)) (MP : DSModel (G.V (.core 0)) (Node.par D sc.cGap (.core 0)))
    {t : SmT M₀ →ₗ[ℂ] (GA D (Yc D 0) → ℂ)} (ht : t ∈ Rows L W.θ M₀)
    {y : SmT MP →ₗ[ℂ] (GA D (G.V (.core 0)) → ℂ)} (hy : y ∈ CoreForms G W.θ 0 MP) (v : SmT MP) (w' : SmT M₀)
    (h0 : per0 G M (y v) (t w') ≠ 0) (w : SmT M₀) (hw : w ≠ 0) :
    ∃ a ∈ KF MP, per0 G M (y a) (t w) ≠ 0 := by
  have hθ := W.θ_is
  obtain ⟨hμ, hfd⟩ := (hM.row 0 (Nat.zero_le _)).haar_fund
  let vY : GlobalTheory.Unf.Vol (Yc D 0) := ⟨M.ν (.grid 0 0), M.fd (.grid 0 0), hμ, hfd⟩
  have hyv : ∀ a, RapidDec (G.V (.core 0)) (y a) := fun a =>
    (GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hCR D _ _ MP W.θ hθ _ _ y hy a).2.2
  have htw : RapidDec (Yc D 0) (t w) :=
    (GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hCR D _ _ M₀ W.θ hθ _ _ t ht w).2.2
  have hF : GlobalTheory.Unf.IsContAut (Yc D 0) (fun g => y v (stabilizerEmbedding G.sp.dec0 g)) :=
    ⟨fun γ hγ g => by
      simp only [GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul]
      exact (hyv v).1 _ (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_rational _ γ hγ) _,
      (hyv v).2.1.comp (GlobalTheory.UnitaryEmbeddingProperties.continuous_unitaryEmbedding _)⟩
  have hB : ∃ C, ∀ g, ‖y v (stabilizerEmbedding G.sp.dec0 g)‖ ≤ C := by
    obtain ⟨C, hC⟩ := (hyv v).2.2 0
    exact ⟨C, fun g => by simpa using hC (stabilizerEmbedding G.sp.dec0 g)⟩
  obtain ⟨h, hh, hne⟩ : ∃ h ∈ GinfC (Yc D 0),
      ∫ g in vY.𝓕, y v (stabilizerEmbedding G.sp.dec0 g) * t w (g * h) ∂vY.μ ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact h0 (GlobalTheory.T.integral_eq_zero_of_orthogonal_real_translates hCR GlobalTheory.Mem.VolFin.finVol D W.θ hθ (Yc D 0) _ M₀ _ _ t ht vY _ hF hB w hw hn w')
  have e1 := GlobalTheory.QPl.LastOrb.setIntegral_mul_right vY
    (fun g => y v (stabilizerEmbedding G.sp.dec0 (g * h⁻¹)) * t w g) (fun γ hγ g => by
      simp only [mul_assoc, GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul]
      rw [(hyv v).1 _ (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_rational _ γ hγ), htw.1 γ hγ g]) h
  simp only [mul_inv_cancel_right] at e1
  have hinf : stabilizerEmbedding G.sp.dec0 h⁻¹ ∈ GinfC (G.V (.core 0)) := GlobalTheory.RealType.Emb_mem_inf G.sp.dec0 (inv_mem hh)
  obtain ⟨v', hv'⟩ := real_translate hθ (M := MP) (J := (lev G (.core 0) : Set _)) (χ := 1) _ hinf v
  have hp : per0 G M (y v') (t w) ≠ 0 := by
    unfold per0
    simp only [hv' y hy]
    rw [e1] at hne
    simp only [GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul] at hne
    exact hne
  by_contra hn
  push_neg at hn
  have key := GlobalTheory.T.period_eq_zero_of_vanishing_on_kFinite_values hCR hHC D W.θ hθ (G.V (.core 0)) _ MP _ _ y hy (GA D (Yc D 0)) (vY.μ.restrict vY.𝓕)
    (stabilizerEmbedding G.sp.dec0) (t w) (GlobalTheory.UnitaryEmbeddingProperties.continuous_unitaryEmbedding _).measurable
    (htw.integrableOn_fundamentalDomain hμ hfd) (fun a ha => hn a ha) v'
  exact hp key

end GlobalTheory.PeriodNePf

namespace GlobalTheory.PeriodNePf

end GlobalTheory.PeriodNePf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLevelIndexMulSchwartzNormFormula
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)

namespace GlobalTheory.LevelIndex

theorem levelIndexNormC : GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL.LocalIntegralSingleBlock → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → LevelIndexNormC R F := by
  intro hLoc D G _ _ Pl0 T A Ks _ _ _ R F hPM
  intro i t σ s P cμ cη m ω BW f₀ f c io hd
  classical
  have hC : Hk3.Core R F := hd.1
  obtain ⟨Hl, cl, hP⟩ := hd.2.2.2.1
  refine ⟨?_, fun μ 𝓧 hμ => ?_⟩
  · obtain ⟨c0, hc0⟩ := hC.lev.βV i
    rw [one_pow] at hc0
    exact GlobalTheory.T.level_le_stabilizer_selfDual_lattice_frame D (Vc D i) _ _ _ hc0
  · have hn := GlobalTheory.T.levelVector_squareNorm_eq_prod_localVolumes hLoc R F hPM i t σ s P cμ cη m ω BW f₀ f c io hd Hl cl hP μ 𝓧 hμ
    rw [GlobalTheory.T.relIndex_level_selfDual_stabilizer_eq_prod_local R F i t P m Hl cl hC hP, hn]
    obtain ⟨hdis, hinj, hsp⟩ := GlobalTheory.T.levelAndTwistPlaces_split_distinct R F hC t
    have hrank : (Vc D i).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
    have hrt : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
    have key : ∀ PP ∈ R.Pg ∪ R.Q t, (dLoc D (PP.under (𝓞 D.host.F)))⁻¹ =
        (Nat.card (GL (Fin (Vc D i).rank) (kP PP)) : ℝ) / ((Nat.card (GL (Fin D.R.t) (kP PP)) : ℝ) *
          (Nat.card (kP PP) : ℝ) ^ (D.R.r * D.R.t)) * ((Nat.card (kP PP) : ℝ) ^ (D.R.r ^ 2 + D.R.r * D.R.t))⁻¹ := by
      intro PP hPP
      obtain ⟨h2, hq⟩ := hsp PP hPP
      haveI : Fact PP.asIdeal.IsMaximal := ⟨PP.isMaximal⟩
      letI : Field (kP PP) := Ideal.Quotient.field _
      rw [GlobalTheory.T.card_GL_div_parabolic_index_finiteField (kP PP) _ D.R.r D.R.t hrt, hrank]
      unfold dLoc quadTerm quadSign
      rw [if_pos h2, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [inv_inv, hq]
      simp
    have hcard : ∀ PP : Pl D.host.E, ∀ n : ℕ, (Nat.card (GL (Fin n) (kP PP)) : ℝ) ≠ 0 := fun PP n => by
      have : Finite (GL (Fin n) (kP PP)) := inferInstance
      exact_mod_cast (Nat.card_pos (α := GL (Fin n) (kP PP))).ne'
    have hHl : ∀ PP, (Nat.card (Hl PP) : ℝ) ≠ 0 := fun PP => by
      exact_mod_cast (Nat.card_pos (α := Hl PP)).ne'
    have hq0 : ∀ PP : Pl D.host.E, (Nat.card (kP PP) : ℝ) ≠ 0 := fun PP => by
      exact_mod_cast (Nat.card_pos (α := kP PP)).ne'
    unfold finS
    rw [Finset.prod_image hinj, Finset.prod_union hdis, ← Finset.prod_attach R.Pg, mul_mul_mul_comm,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    congr 1
    · refine Finset.prod_congr rfl fun PP _ => ?_
      rw [key PP.1 (Finset.mem_union_left _ PP.2)]
      field_simp [hHl PP, hcard PP.1, hq0 PP.1]
    · refine Finset.prod_congr rfl fun PP hPP => ?_
      rw [key PP (Finset.mem_union_right _ hPP)]
      field_simp [hcard PP, hq0 PP]

end GlobalTheory.LevelIndex

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionSplitSupportStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_action_split_support : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T) (N : ℕ), 0 < N → ∀ g ∈ GfC A, ∀ g' ∈ GfC WW,
      GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N ((finHom A) g : Matrix (Fin A.rank) (Fin A.rank) _) →
      GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N ((finHom WW) g' : Matrix (Fin WW.rank) (Fin WW.rank) _) →
      ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → WO (GlobalTheory.Grid.neg A) WW), (∀ p, IsAlgebraic ℚ (c p)) ∧
        (∀ p, (w p).map (infPart D) = 0) ∧
        X.ω t (g, g') X.vac = ∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac := by
  first | exact @GlobalTheory.MovedAlg.suppSplit_algComb | exact GlobalTheory.MovedAlg.suppSplit_algComb | (intros; apply GlobalTheory.MovedAlg.suppSplit_algComb <;> assumption)
end

