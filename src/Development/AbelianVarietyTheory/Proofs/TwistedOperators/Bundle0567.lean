import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0091
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0174
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0217
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0328
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0325
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0314
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0546
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0544
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0421
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0549
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0550

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftVerticalCuspidalType
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.ThetaApproxX

theorem approx : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ F : (G.V i j).Maps, F ∈ (G.V i j).Cusp R.θ → ∀ v : SmT (G.V i j).M, (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * F v g) (G.meas t i j).fd (G.meas t i j).ν) → ∀ C : Set (GA D (G.V (i + 1) j).V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (f : Fin n → (WO (G.V (i + 1) j).V (G.V i j).V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol (G.V (i + 1) j) (G.V i j)), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f l)) ∧ ∀ h ∈ C, ‖(∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * F v g ∂(G.meas t i j).ν) - ∑ l, ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g (GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f l) (p l)) * F v g ∂(G.meas t i j).ν‖ < ε := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj Φ hΦ F hF v hint C hC ε hε
  have hw := (hG.arrows.X i j hi hj).weil
  have hθ : IsInfFam R.θ := hRB.inf
  have hψ : IsStdChar D R.ψ (-1) := hw.std
  let AF := GlobalTheory.PairLift.frSgn true (GlobalTheory.ChainFr.Fr.ofModel (G.V (i + 1) j).M)
  let BF := GlobalTheory.ChainFr.Fr.ofModel (G.V i j).M
  have hcart : ∀ τ, AF.cart τ = GlobalTheory.Grid.cartS true (G.V (i + 1) j) τ := fun τ => GlobalTheory.PairLift.cart_frSgn true _ τ
  have hpt : ∀ f P, GlobalTheory.ChainFr.ptF R.ψ R.θ AF BF f P = GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f P := by
    intro f P
    unfold GlobalTheory.ChainFr.ptF GlobalTheory.Grid.fock
    rw [show AF.cart = GlobalTheory.Grid.cartS true (G.V (i + 1) j) from funext hcart]
    rfl
  have hfin : ∀ f, GlobalTheory.ChainFr.IsVacF R.ψ R.θ AF BF f → GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f := by
    intro f hf
    refine ⟨hf.1, fun τ => ?_⟩
    have := hf.2 τ
    rwa [hcart τ] at this
  have hk : ∀ h g f, thetaKO (G.X i j).ω h g f =
      thetaKO ((G.X i j).ω.toSgn true) ((GlobalTheory.Grid.ofSgn true _).symm h) g f := by
    intro h g f
    simp only [thetaKO, GlobalTheory.Grid.WRep.toSgn, MonoidHom.comp_apply, MonoidHom.prodMap, MonoidHom.prod_apply,
      MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply, MonoidHom.id_apply]
  obtain ⟨μW, 𝓕W, hμW⟩ := GlobalTheory.Size.exists_isCovolOne (D := D) (V := GlobalTheory.Grid.neg (G.V (i + 1) j).V) (W := (G.V i j).V)
  obtain ⟨U, hU, hΦU, hdense⟩ := GlobalTheory.FockDensity.fockDense D _ _ AF BF R.θ R.ψ hψ hθ μW 𝓕W hμW Φ hΦ
  obtain ⟨Aexp, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D (GlobalTheory.Grid.neg (G.V (i + 1) j).V).rank (G.V i j).V.rank
  obtain ⟨Ck, hCk0, hCk⟩ := (H _ _ rfl rfl).real R.ψ hθ hU
  have hFr := GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hP.cuspRapidDecay D _ _ (G.V i j).M R.θ hθ ∅ 1 F hF v
  have hM := GlobalTheory.PairLift.haar_vert hRB hG t hi.le hj
  have : BorelSpace (GA D (G.V i j).V) := ⟨rfl⟩
  obtain ⟨Hh, hHh⟩ := hC.bddAbove_image
    ((GlobalTheory.Grow.continuous_height _).comp (GlobalTheory.Grid.continuous_ofSgn_symm true (G.V (i + 1) j).V)).continuousOn
  set Hq : ℝ := max Hh 1 with hHq
  have hHC : ∀ h ∈ C, GlobalTheory.Grow.height _ ((GlobalTheory.Grid.ofSgn true (G.V (i + 1) j).V).symm h) ≤ Hq :=
    fun h hh => (hHh ⟨h, hh, rfl⟩).trans (le_max_left _ _)
  have hq1 : (1 : ℝ) ≤ Hq := le_max_right _ _
  have hqm : AEStronglyMeasurable (fun g => ((GlobalTheory.Grow.quotHeight (G.V i j).V g ^ Aexp : ℝ) : ℂ))
      ((G.meas t i j).ν.restrict (G.meas t i j).fd) :=
    (Complex.continuous_ofReal.comp ((GlobalTheory.Grow.continuous_quotHeight _).pow Aexp)).aestronglyMeasurable
  have hQ : IntegrableOn ((fun g => ((GlobalTheory.Grow.quotHeight (G.V i j).V g ^ Aexp : ℝ) : ℂ)) * F v)
      (G.meas t i j).fd (G.meas t i j).ν :=
    hFr.2.2.integrableOn_mul_of_le hM.1 hM.2 hqm (C := 1) (A := Aexp) fun g => by
      rw [Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (GlobalTheory.Grow.quotHeight_pos _ g).le _), one_mul]
  set K0 : ℝ := ∫ g in (G.meas t i j).fd,
    ‖((fun g => ((GlobalTheory.Grow.quotHeight (G.V i j).V g ^ Aexp : ℝ) : ℂ)) * F v) g‖ ∂(G.meas t i j).ν with hK0def
  have hK0 : 0 ≤ K0 := integral_nonneg fun _ => norm_nonneg _
  set M : ℝ := Ck * 2 ^ Aexp * Hq ^ Aexp * K0 with hMdef
  have hM0 : 0 ≤ M := by positivity
  set δ : ℝ := ε / (M + 1) with hδdef
  have hδ : 0 < δ := div_pos hε (by linarith)
  obtain ⟨g0, hg0, hg0U, hsob⟩ := hdense d (ENNReal.ofReal δ) (ENNReal.ofReal_pos.2 hδ)
  obtain ⟨n, c, w, hsum⟩ := Submodule.mem_span_set'.1 hg0
  choose f₀ P hvac hlev heq using fun l => (w l).2
  refine ⟨n, f₀, fun l => c l • P l, fun l => hfin _ (hvac l), fun h hh => ?_⟩
  have hg0eq : g0 = ∑ l, GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f₀ l) (c l • P l) := by
    rw [← hsum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [heq l, hpt, map_smul]
  have hCA := (hL D hS G₀ Pl0 T A Ks R G hRB hG).X t i j hi hj
  have hintl : ∀ l, IntegrableOn (fun g => thetaKO (G.X i j).ω h g
      (GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f₀ l) (c l • P l)) * F v g)
      (G.meas t i j).fd (G.meas t i j).ν := fun l => by
    obtain ⟨F', -, hF'⟩ := hCA (f₀ l) (hfin _ (hvac l)) F hF
    exact (hF' (c l • P l) v h).1
  have hdiff : (∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * F v g ∂(G.meas t i j).ν) -
      ∑ l, ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g
        (GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f₀ l) (c l • P l)) * F v g ∂(G.meas t i j).ν =
      ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g (Φ - g0) * F v g ∂(G.meas t i j).ν := by
    rw [← integral_finset_sum _ (fun l _ => hintl l),
      ← integral_sub (hint h) (integrable_finset_sum _ fun l _ => hintl l)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [thetaKO, hg0eq, map_sub, map_sum, Pi.sub_apply, Finset.sum_apply, sub_mul, Finset.sum_mul]
  rw [hdiff]
  have hΞ : Φ - g0 ∈ GlobalTheory.Size.thetaLevel R.ψ _ _ U := sub_mem hΦU hg0U
  obtain ⟨hsT, hbd⟩ := hCk _ _ _ hw μW 𝓕W hμW (Φ - g0) hΞ
  set s : ℝ := (GlobalTheory.Size.sobO R.ψ R.θ μW 𝓕W d (Φ - g0)).toReal with hsdef
  have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
  have hs : s ≤ δ := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsob.le
    rwa [ENNReal.toReal_ofReal hδ.le] at this
  set h' := (GlobalTheory.Grid.ofSgn true (G.V (i + 1) j).V).symm h with hh'
  have hpt' : ∀ g, ‖thetaKO (G.X i j).ω h g (Φ - g0)‖ ≤
      Ck * s * Hq ^ Aexp * 2 ^ Aexp * GlobalTheory.Grow.quotHeight _ g ^ Aexp := by
    intro g
    have hinv : ∀ γ ∈ GQ (G.V i j).V, ∀ g, thetaKO (G.X i j).ω h (γ * g) (Φ - g0) = thetaKO (G.X i j).ω h g (Φ - g0) := by
      intro γ hγ g
      rw [hk, hk]
      exact GlobalTheory.Chain.LiftConv.thetaKO_left hw hΞ.1 h' γ hγ g
    have hb : ∀ g, ‖thetaKO (G.X i j).ω h g (Φ - g0)‖ ≤
        (Ck * s * GlobalTheory.Grow.height _ h' ^ Aexp) * GlobalTheory.Grow.height _ g ^ Aexp := by
      intro g
      have := hbd h' g
      rw [mul_pow, ← mul_assoc] at this
      rw [hk]
      exact this
    refine (GlobalTheory.Grow.norm_le_quotHeight_pow hinv hb g).trans ?_
    have h1 : GlobalTheory.Grow.height _ h' ^ Aexp ≤ Hq ^ Aexp :=
      pow_le_pow_left₀ (GlobalTheory.Grow.height_pos _ h').le (hHC h hh) _
    have h2 : 0 ≤ GlobalTheory.Grow.quotHeight (G.V i j).V g ^ Aexp := pow_nonneg (GlobalTheory.Grow.quotHeight_pos _ g).le _
    have h3 : 0 ≤ Ck * s := mul_nonneg hCk0 hs0
    have h4 : Ck * s * GlobalTheory.Grow.height _ h' ^ Aexp ≤ Ck * s * Hq ^ Aexp := mul_le_mul_of_nonneg_left h1 h3
    have h5 : (0 : ℝ) ≤ 2 ^ Aexp := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h4 (mul_nonneg h5 h2)]
  calc ‖∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g (Φ - g0) * F v g ∂(G.meas t i j).ν‖
      ≤ ∫ g in (G.meas t i j).fd, (Ck * s * Hq ^ Aexp * 2 ^ Aexp) *
          ‖((fun g => ((GlobalTheory.Grow.quotHeight (G.V i j).V g ^ Aexp : ℝ) : ℂ)) * F v) g‖ ∂(G.meas t i j).ν := by
        refine norm_integral_le_of_norm_le (hQ.norm.const_mul _) (Filter.Eventually.of_forall fun g => ?_)
        rw [norm_mul, Pi.mul_apply, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (pow_nonneg (GlobalTheory.Grow.quotHeight_pos _ g).le _)]
        calc ‖thetaKO (G.X i j).ω h g (Φ - g0)‖ * ‖F v g‖
            ≤ (Ck * s * Hq ^ Aexp * 2 ^ Aexp * GlobalTheory.Grow.quotHeight _ g ^ Aexp) * ‖F v g‖ :=
              mul_le_mul_of_nonneg_right (hpt' g) (norm_nonneg _)
          _ = _ := by ring
    _ = (Ck * s * Hq ^ Aexp * 2 ^ Aexp) * K0 := integral_const_mul _ _
    _ ≤ (Ck * δ * Hq ^ Aexp * 2 ^ Aexp) * K0 := by gcongr
    _ = δ * M := by rw [hMdef]; ring
    _ < ε := by
        rw [hδdef, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
        nlinarith

end GlobalTheory.ThetaApproxX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRowGridBottomSelfDualLattices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BottomGrid

theorem bottom : All fun {D} _ {L} _ {G} _ _ => IsSelfDualC (Yc D 0) (L.ΛY 0) ∧ IsSelfDualC (G.V (.core 0)) (G.Λ (.core 0)) ∧ G.Λ (.core 0) = G.sp.dec0.lat (L.ΛY 0) (fun _ => 1) ∧ zv G.sp.dec0 ∈ G.Λ (.core 0) ∧ (∀ k ∈ GfC (Yc D 0), Lev.finE (G.V (.core 0)) (stabilizerEmbedding G.sp.dec0 k) ∈ G.levCong (.core 0) → k ∈ levRow L) ∧ (Yc D 0).rank = D.R.r ∧ (G.V (.core 0)).rank = D.R.r + 1 ∧ ∀ (A : Fr (Yc D 0)) τ, (Finset.univ.filter fun a => A.ε τ a = false).card ≤ D.R.m := by
  intro D _ T L μ0 hL sc G W M _
  have hY : (⟨Yc D 0, L.ΛY 0⟩ : LSp D).IsV (Node.rank D (.grid 0 0)) (Node.neg D.R.m (.grid 0 0)) :=
    node_isV G hL (X := .grid 0 0) ⟨Nat.zero_le _, Nat.zero_le _⟩
  have hP := G.sp.P_is 0 (Nat.zero_le _)
  refine ⟨hY.sd, hP.sd, G.sp.lat0, ?_, ?_, ?_, ?_, ?_⟩
  · show zv G.sp.dec0 ∈ (G.sp.P 0).lat
    rw [G.sp.lat0]
    refine ⟨0, Submodule.zero_mem _, fun _ => 1, fun p => ?_, ?_⟩
    · exact (FractionalIdeal.mem_one_iff _).2 ⟨1, by simp⟩
    · funext i
      simp [zv, Matrix.mulVec, dotProduct]
  · intro k hk hfin
    have h1 : Lev.finE (Yc D 0) k ∈ congLev D.sp.cm (Yc D 0).gram (L.ΛY 0) G.modul := by
      refine GlobalTheory.T.congruence_level_of_embedding G.sp.dec0 (L.ΛY 0) (fun _ => 1) G.modul k ?_
      have e : G.Λ (.core 0) = G.sp.dec0.lat (L.ΛY 0) (fun _ => 1) := G.sp.lat0
      have := hfin
      unfold GridData.levCong at this
      rw [e] at this
      exact this
    have h2 := GlobalTheory.T.unitaryLatticeCongruence_mem_conjugateIdeal_inf (Yc D 0) (L.ΛY 0) hY.sd _ _ h1
    exact Subgroup.mem_inf.2 ⟨hk, congLev_mono (GlobalTheory.T.modulus_inf_conj_le_span_typePrimes_product G) h2⟩
  · simpa [Node.rank, rankV] using hY.rank
  · simpa [Node.rank, rankP, nRk] using hP.rank
  · intro A τ
    rw [GlobalTheory.T.card_negativeSigns_diagonalFrame_eq_signature _ hY.sigOK A τ, hY.sig]
    simp only [Node.neg, Nat.sub_zero]
    exact Nat.div_le_self _ _
end GlobalTheory.BottomGrid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ToPairMul
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries

namespace GlobalTheory.RowReal

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem toPair_mul (p : Pair T) (g k : GA D (G.V p.small)) (h k' : GA D (G.V p.big)) :
    G.toPair p (g * k) (h * k') = G.toPair p g h * G.toPair p k k' := by
  cases p <;> simp [GridData.toPair, map_mul]

theorem ker_mul (W : G.Weil) (p : Pair T) (f : WO (G.pS p) (G.pT p) → ℂ) (g k : GA D (G.V p.small))
    (h k' : GA D (G.V p.big)) : W.ker p f (g * k) (h * k') = W.ker p (W.om p (G.toPair p k k') f) g h := by
  simp only [GridData.Weil.ker, thetaKO, toPair_mul, Prod.fst_mul, Prod.snd_mul, ← Prod.mk_mul_mk, Prod.mk.eta, map_mul,
    Module.End.mul_apply]

end GlobalTheory.RowReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TotalTensorThetaLiftEqOfSchwartzEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped Pointwise

noncomputable section

namespace GlobalTheory.FlipRun

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}

theorem kerA_sum_of_grid {t : T} {a : Arrow T} (ha : IsGridArrow D.R.m t a) {ι : Type} (L : Finset ι) (w : ι → ℂ)
    (gs : ι → Sch G a) (g₀ : GA D (G.V a.src)) (h : GA D (G.V a.tgt)) :
    W.kerA a (∑ l ∈ L, w l • gs l) g₀ h = ∑ l ∈ L, w l * W.kerA a (gs l) g₀ h := by
  rcases ha with ⟨i, j, -, -, rfl⟩ | ⟨i, j, -, -, rfl⟩ <;>
    simp [GridData.Weil.kerA, GridData.Weil.ker, thetaKO, map_sum, map_smul, Finset.sum_apply]

theorem liftA_sum_datum (M : Vol G) {t : T} {a : Arrow T} (ha : IsGridArrow D.R.m t a) {ι : Type} (L : Finset ι)
    (w : ι → ℂ) (gs : ι → Sch G a) (F : Fn G a.src) (hc : ∀ l ∈ L, LiftConv W M a (gs l) F) :
    liftA W M a (∑ l ∈ L, w l • gs l) F = ∑ l ∈ L, w l • liftA W M a (gs l) F := by
  funext h
  simp only [liftA_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, kerA_sum_of_grid ha, Finset.sum_mul]
  rw [integral_finsetSum _ fun l hl => ?_]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun x => ?_)
    ring
  · have := (hc l hl h).const_mul (w l)
    refine this.congr (.of_forall fun x => ?_)
    simp only
    ring

theorem liftA_sum_form (M : Vol G) (a : Arrow T) (f : Sch G a) {ι : Type} (s : Finset ι) (w : ι → ℂ)
    (Fs : ι → Fn G a.src) (hc : ∀ k ∈ s, LiftConv W M a f (Fs k)) :
    liftA W M a f (∑ k ∈ s, w k • Fs k) = ∑ k ∈ s, w k • liftA W M a f (Fs k) := by
  funext h
  simp only [liftA_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [integral_finsetSum _ fun k hk => ?_]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun x => ?_)
    ring
  · have := (hc k hk h).const_mul (w k)
    refine this.congr (.of_forall fun x => ?_)
    simp only
    ring

theorem liftA_zero_form (M : Vol G) (a : Arrow T) (f : Sch G a) : liftA W M a f 0 = 0 := by
  have := liftA_smul W M a f 0 0
  rwa [zero_smul, zero_smul] at this

theorem sum_liftP_eq_zero {μ₀ : T} (hL : L.Is μ₀) (M : Vol G) (ρ : RealMatch W) (t : T) {e : AE D}
    (he : IsIdemSum e (locPl G t)) (hC : CuspStep W M ρ t) {X : Node} :
    ∀ {Y : Node} (p : Path T X Y), OnGrid D.R.m t p → ∀ {ι : Type} (s : Finset ι) (c : ι → ℂ) (φ d : ι → PureT G p),
      (∀ k ∈ s, VecAll ρ e p (φ k) (d k)) → (∀ x : ArgT G p, HalfAll e p x → ∑ k ∈ s, c k * famProd p (φ k) x = 0) →
      ∀ (P : PolT G p) (F : Fn G X), IsCuspListed W.θ X F →
      ∑ k ∈ s, c k • liftP W M p (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) (d k) P) F = 0
  | _, .nil, _, ι, s, c, φ, d, _, hsum, P, F, _ => by
    have h0 : ∑ k ∈ s, c k = 0 := by
      have := hsum () trivial
      simpa [famProd] using this
    show ∑ k ∈ s, c k • F = 0
    rw [← Finset.sum_smul, h0, zero_smul]
  | _, .snoc a p, hg, ι, s, c, φ, d, hv, hsum, P, F, hF => by
    classical
    obtain ⟨Tm, h1, -, h3⟩ := exists_arrowModel ρ hL he hg.last
    have hmem : ∀ k ∈ s, (φ k).2 ∈ LocTensor.sbSpace e (latA G a) := fun k hk => ((h1 _ _).1 (hv k hk).2).1
    have hd2 : ∀ k ∈ s, (d k).2 = Tm (φ k).2 := fun k hk => ((h1 _ _).1 (hv k hk).2).2
    let b := Module.Basis.ofVectorSpace ℂ (LocTensor.sbSpace e (latA G a))
    let v : ι → LocTensor.sbSpace e (latA G a) := fun k => if h : (φ k).2 ∈ LocTensor.sbSpace e (latA G a) then ⟨_, h⟩ else 0
    have hv' : ∀ k ∈ s, ((v k : LocTensor.sbSpace e (latA G a)) : Sch G a) = (φ k).2 := fun k hk => by
      simp only [v, dif_pos (hmem k hk)]
    let r : ι → Module.Basis.ofVectorSpaceIndex ℂ (LocTensor.sbSpace e (latA G a)) → ℂ := fun k l => b.repr (v k) l
    let Ls := s.biUnion fun k => (b.repr (v k)).support
    have hexp : ∀ k ∈ s, (φ k).2 = ∑ l ∈ Ls, r k l • ((b l : LocTensor.sbSpace e (latA G a)) : Sch G a) := by
      intro k hk
      rw [← hv' k hk]
      conv_lhs => rw [← b.linearCombination_repr (v k)]
      rw [Finsupp.linearCombination_apply,
        Finsupp.sum_of_support_subset _ (Finset.subset_biUnion_of_mem (fun k => (b.repr (v k)).support) hk)
          (fun i (x : ℂ) => x • b i) (fun _ _ => zero_smul _ _), Submodule.coe_sum]
      rfl
    let Fk : ι → Fn G a.src := fun k => liftP W M p (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) (d k).1 P.1) F
    have hFk : ∀ k ∈ s, IsCuspListed W.θ a.src (Fk k) := fun k hk =>
      (pathConv_zip_fock M ρ t he hC p hg.init (φ k).1 (d k).1 (hv k hk).1 P.1 F hF).2
    let g : Module.Basis.ofVectorSpaceIndex ℂ (LocTensor.sbSpace e (latA G a)) → Sch G a :=
      fun l => W.fock a.pair (Tm (b l)) P.2
    have hconv : ∀ l, ∀ k ∈ s, LiftConv W M a (g l) (Fk k) := fun l k hk =>
      (hC a hg.last e he (b l) (Tm (b l)) ((h1 _ _).2 ⟨(b l).2, rfl⟩) P.2 (Fk k) (hFk k hk)).1
    have hstep : ∀ k ∈ s, W.fock a.pair (d k).2 P.2 = ∑ l ∈ Ls, r k l • g l := by
      intro k hk
      rw [hd2 k hk, hexp k hk, map_sum]
      simp only [map_smul]
      exact GlobalTheory.SpecFac.pureTensorO_sum W.ψ_std W.θ_is _ _ _ _ Ls (r k) (fun l => Tm (b l))
        (fun l _ => h3 _ (b l).2) P.2
    have hIH : ∀ l, ∑ k ∈ s, (c k * r k l) • Fk k = 0 := by
      intro l
      refine sum_liftP_eq_zero hL M ρ t he hC p hg.init s (fun k => c k * r k l) (fun k => (φ k).1) (fun k => (d k).1)
        (fun k hk => (hv k hk).1) (fun x hx => ?_) P.1 F hF
      have hV : ∑ k ∈ s, (c k * famProd p (φ k).1 x) • v k = 0 := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        funext y
        rw [Finset.sum_apply]
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Submodule.coe_zero, Pi.zero_apply]
        rw [Finset.sum_congr rfl fun k hk => by rw [hv' k hk]]
        by_cases hy : IsHalf e y
        · have := hsum (x, y) ⟨hx, hy⟩
          rw [← this]
          refine Finset.sum_congr rfl fun k _ => ?_
          show _ = c k * (famProd p (φ k).1 x * (φ k).2 y)
          ring
        · refine Finset.sum_eq_zero fun k hk => ?_
          have : (φ k).2 y = 0 := by
            by_contra h0
            exact hy ((hmem k hk).1 y h0)
          rw [this, mul_zero]
      have := congrArg (fun z => b.repr z l) hV
      simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
        map_zero, Finsupp.coe_zero, Pi.zero_apply] at this
      rw [← this]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [r]
      ring
    show ∑ k ∈ s, c k • liftA W M a (W.fock a.pair (d k).2 P.2) (Fk k) = 0
    calc ∑ k ∈ s, c k • liftA W M a (W.fock a.pair (d k).2 P.2) (Fk k)
        = ∑ k ∈ s, ∑ l ∈ Ls, (c k * r k l) • liftA W M a (g l) (Fk k) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [hstep k hk, liftA_sum_datum M hg.last Ls (r k) g (Fk k) fun l _ => hconv l k hk, Finset.smul_sum]
          simp only [smul_smul]
      _ = ∑ l ∈ Ls, liftA W M a (g l) (∑ k ∈ s, (c k * r k l) • Fk k) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [liftA_sum_form M a (g l) s _ Fk fun k hk => hconv l k hk]
      _ = 0 := by
          refine Finset.sum_eq_zero fun l _ => ?_
          rw [hIH l, liftA_zero_form]

theorem liftT_tensE_expand (M : Vol G) {X Y : Node} (p : Path T X Y) (Q : PolE G →₀ ℂ) (τ : TotT G p) (F : Fn G X) :
    liftT W M p (tensE W p Q τ) F =
      ∑ P ∈ (Q.mapDomain fun P => restrictPol P p).support, (Q.mapDomain fun P => restrictPol P p) P •
        ∑ d ∈ τ.support, τ d • liftP W M p (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P) F := by
  unfold tensE tensT
  rw [Finsupp.sum, liftT_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [Finsupp.sum, liftT_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [liftT_single, mul_smul]

theorem liftT_tensE_eq_of_famProd : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ {W : G.Weil} (M : Vol G) (ρ : RealMatch W) (t : T) {e : AE D}, IsIdemSum e (locPl G t) → GlobalTheory.FlipRun.CuspStep W M ρ t → ∀ {X Y : Node} (p : Path T X Y), GlobalTheory.FlipRun.OnGrid D.R.m t p → ∀ (τ₁ τ₂ : TotT G p) (φ₁ φ₂ : PureT G p → PureT G p), (∀ d ∈ τ₁.support, GlobalTheory.FlipRun.VecAll ρ e p (φ₁ d) d) → (∀ d ∈ τ₂.support, GlobalTheory.FlipRun.VecAll ρ e p (φ₂ d) d) → (∀ x : GlobalTheory.FlipRun.ArgT G p, GlobalTheory.FlipRun.HalfAll e p x → (τ₁.sum fun d c => c * GlobalTheory.FlipRun.famProd p (φ₁ d) x) = τ₂.sum fun d c => c * GlobalTheory.FlipRun.famProd p (φ₂ d) x) → ∀ F : Fn G X, GlobalTheory.FlipRun.IsCuspListed W.θ X F → ∀ Q : GlobalTheory.FlipRun.PolE G →₀ ℂ, liftT W M p (GlobalTheory.FlipRun.tensE W p Q τ₁) F = liftT W M p (GlobalTheory.FlipRun.tensE W p Q τ₂) F := by
  intro D T L sc G μ₀ hL W M ρ t e he hC X Y p hg τ₁ τ₂ φ₁ φ₂ hv₁ hv₂ heq F hF Q
  classical
  rw [liftT_tensE_expand, liftT_tensE_expand]
  refine Finset.sum_congr rfl fun P _ => ?_
  congr 1
  have key := sum_liftP_eq_zero hL M ρ t he hC p hg (τ₁.support.disjSum τ₂.support)
    (Sum.elim (fun d => τ₁ d) fun d => -τ₂ d) (Sum.elim φ₁ φ₂) (Sum.elim id id)
    (by
      rintro (k | k) hk
      · exact hv₁ k (Finset.inl_mem_disjSum.1 hk)
      · exact hv₂ k (Finset.inr_mem_disjSum.1 hk))
    (fun x hx => by
      rw [Finset.sum_disjSum]
      have := heq x hx
      simp only [Finsupp.sum] at this
      simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib, this, add_neg_cancel])
    P F hF
  rw [Finset.sum_disjSum] at key
  simp only [Sum.elim_inl, Sum.elim_inr, id, neg_smul, Finset.sum_neg_distrib] at key
  exact sub_eq_zero.1 ((sub_eq_add_neg _ _).trans key)

end GlobalTheory.FlipRun

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransposeMemUnitary
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section

open scoped Matrix

namespace GlobalTheory.RealColAct

variable {D : D7}

theorem gramAt_of_gram_one {V : HSp D} (hV : HSpace.gram V = 1) (τ : D.what₂.Tau) : gramAt D V τ = 1 := by
  unfold gramAt
  rw [hV]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem compAt_mem_unitary {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} (hV : HSpace.gram V = 1) (g : GA D V)
    (τ : D.what₂.Tau) : compAt θ τ (Formalism.L2.Theta.mt V g) ∈ Matrix.unitaryGroup (Fin V.rank) ℂ := by
  have h := GlobalTheory.StdUnn.CartanMove.compAt_isom hθ V g τ
  rw [gramAt_of_gram_one hV, Matrix.mul_one] at h
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  exact h

theorem transpose_mem_unitary {n : ℕ} {K : Matrix (Fin n) (Fin n) ℂ} (hK : K ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Kᵀ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have h2 : K * star K = 1 := Matrix.mem_unitaryGroup_iff.1 hK
  rw [Matrix.mem_unitaryGroup_iff']
  have e : star Kᵀ = (star K)ᵀ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose]; rfl
  rw [e, ← Matrix.transpose_mul, h2, Matrix.transpose_one]

def realCol (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (hV : HSpace.gram V = 1) :
    GinfC V →* (D.what₂.Tau → Matrix.unitaryGroup (Fin V.rank) ℂ) where
  toFun g τ := ⟨(compAt θ τ (Formalism.L2.Theta.mt V ((g : GA D V)⁻¹)))ᵀ,
    transpose_mem_unitary (compAt_mem_unitary hθ hV _ τ)⟩
  map_one' := by
    funext τ
    apply Subtype.ext
    simp only [OneMemClass.coe_one, inv_one, GlobalTheory.StdUnn.CartanMove.compAt_mt_one, Matrix.transpose_one, Pi.one_apply]
  map_mul' g h := by
    funext τ
    apply Subtype.ext
    simp only [Subgroup.coe_mul, mul_inv_rev, GlobalTheory.StdUnn.CartanMove.compAt_mt_mul, Matrix.transpose_mul, Pi.mul_apply]
    rfl

theorem realCol_apply (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (hV : HSpace.gram V = 1) (g : GinfC V) (τ : D.what₂.Tau) :
    (realCol θ hθ V hV g τ : Matrix (Fin V.rank) (Fin V.rank) ℂ) = (compAt θ τ (Formalism.L2.Theta.mt V ((g : GA D V)⁻¹)))ᵀ := rfl

end GlobalTheory.RealColAct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedBaseTermEqFlatMapLineContractionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedBaseTerm_eq_flatMap_lineContraction : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B) (vb : VolM D (σ + 1) J.W₀.rank) (vL : VolM D B.L.rank J.W₀.rank) (y : WO J.W₀ B.L → ℂ) (Ψ : WO J.W B.V → ℂ), GlobalTheory.Unf.FB.Quasi ψ J.W₀ B.L y → IsThetaFunO ψ J.W B.V Ψ → fl ψ J.d B.V s.vS vb s.vU (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (xLast B.d (vecB B.o B.ζ)) Ψ = contractT B.o J.W₀ vL.μ vL.𝓕 (flFB s Ψ) y 0 ∧ ∀ M : ℝ, (∀ w, ‖y w‖ ≤ M) → ‖contractT B.o J.W₀ vL.μ vL.𝓕 (flFB s Ψ) y 0‖ₑ ≤ ENNReal.ofReal M * ∫⁻ u, ∫⁻ b in vb.𝓕, ‖J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 Ψ (xLast B.d (vecB B.o B.ζ) ⬝ u.1.1) (xLast B.d (vecB B.o B.ζ) ⬝ b)‖ₑ ∂vb.μ ∂s.vU.ν := by
  first | exact @GlobalTheory.Asc.FlatBaseL.fl_base_eq_contract | exact GlobalTheory.Asc.FlatBaseL.fl_base_eq_contract | (intros; apply GlobalTheory.Asc.FlatBaseL.fl_base_eq_contract <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VerticalThetaLevelFirstStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vertical_theta_level_first : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t j, j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.Xp j).V (G.Xp (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.Xp j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.col t j).ω g h Φ * φ g) (G.measX j).fd (G.measX j).ν) := by
  first | exact @GlobalTheory.ColConv.col_integrableOn | exact GlobalTheory.ColConv.col_integrableOn | (intros; apply GlobalTheory.ColConv.col_integrableOn <;> assumption)
end

