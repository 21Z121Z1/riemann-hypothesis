import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0217
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0195
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitProductRescaleDisjointFinsets
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0178
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0516
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOverBoth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0252
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0268
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0393
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0113
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0269
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0510
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumOfMemFockSpan
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FockApprox

section

open GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.Size GlobalTheory.ChainFr GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.FockDensity GlobalTheory.SquareComm
open scoped ENNReal

variable {D : D7}

theorem cart_frSgn (ε : Bool) (S : GlobalTheory.Grid.Node D) :
    (frSgn ε (Fr.ofModel S.M)).cart = GlobalTheory.Grid.cartS ε S := by
  funext τ
  cases ε
  · show (S.M.fr τ)⁻¹ * Formalism.REAL.Jm (fun a => xor false (S.M.ε τ a)) * S.M.fr τ = (S.M.fr τ)⁻¹ * Formalism.REAL.Jm (S.M.ε τ) * S.M.fr τ
    simp only [Bool.false_xor]
  · have e' : Formalism.REAL.Jm (fun a => xor true (S.M.ε τ a)) = -Formalism.REAL.Jm (S.M.ε τ) := by
      ext a b
      by_cases h : a = b
      · subst h; cases h' : S.M.ε τ a <;> simp [Formalism.REAL.Jm, h']
      · simp [Formalism.REAL.Jm, h]
    show (S.M.fr τ)⁻¹ * Formalism.REAL.Jm (fun a => xor true (S.M.ε τ a)) * S.M.fr τ = -((S.M.fr τ)⁻¹ * Formalism.REAL.Jm (S.M.ε τ) * S.M.fr τ)
    rw [e', Matrix.mul_neg, Matrix.neg_mul]

theorem ptF_eq_fock (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) (S T : GlobalTheory.Grid.Node D)
    (f : WO S.V T.V → ℂ) (P : GlobalTheory.Grid.Pol S T) :
    ptF ψ θ (frSgn ε (Fr.ofModel S.M)) (Fr.ofModel T.M) f P = GlobalTheory.Grid.fock ψ θ ε S T f P := by
  unfold ptF GlobalTheory.Grid.fock
  rw [cart_frSgn]
  rfl

theorem isVacF_iff (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) (S T : GlobalTheory.Grid.Node D)
    (f : WO S.V T.V → ℂ) :
    IsVacF ψ θ (frSgn ε (Fr.ofModel S.M)) (Fr.ofModel T.M) f ↔ GlobalTheory.Grid.IsFinVec ψ θ ε S T f := by
  unfold IsVacF GlobalTheory.Grid.IsFinVec
  rw [cart_frSgn]
  rfl

end

end GlobalTheory.FockApprox

namespace GlobalTheory.FockApprox

section

open GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.Size GlobalTheory.ChainFr GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.FockDensity GlobalTheory.SquareComm
open scoped ENNReal

theorem exists_sum_of_mem_fockSpan {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) (S T : GlobalTheory.Grid.Node D)
    (U : AddSubgroup (WO S.V T.V)) {g : WO S.V T.V → ℂ}
    (hg : g ∈ fockSpan ψ θ (frSgn ε (Fr.ofModel S.M)) (Fr.ofModel T.M) U) :
    ∃ (n : ℕ) (f : Fin n → (WO S.V T.V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol S T),
      (∀ l, GlobalTheory.Grid.IsFinVec ψ θ ε S T (f l)) ∧ g = ∑ l, GlobalTheory.Grid.fock ψ θ ε S T (f l) (p l) := by
  obtain ⟨n, c, x, hx⟩ := Submodule.mem_span_set'.1 hg
  choose f₀ P h1 _ h3 using fun l => (x l).2
  refine ⟨n, f₀, fun l => c l • P l, fun l => (isVacF_iff ψ θ ε S T _).1 (h1 l), ?_⟩
  rw [← hx]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [h3 l, map_smul, ptF_eq_fock]

end

end GlobalTheory.FockApprox

namespace GlobalTheory.FockApprox

section

open Formalism.IndefR.Mult GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.Size GlobalTheory.ChainFr GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.FockDensity
open scoped ENNReal

theorem dense_level {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} (A : Fr V) (B : Fr W)
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {μ : Measure (WO V W)} {𝓕 : Set (WO V W)}
    (hm : IsCovolOne (ratL W V) μ 𝓕) {U : AddSubgroup (WO V W)} (hU : IsOpen (U : Set (WO V W)))
    {f : WO V W → ℂ} (hf : f ∈ GlobalTheory.Size.thetaLevel ψ V W U) (d : ℕ) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ g ∈ fockSpan ψ θ A B U, g ∈ GlobalTheory.Size.thetaLevel ψ V W U ∧ sobO ψ θ μ 𝓕 d (f - g) < δ := by
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨-, i2, i3, i4, i5, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
  haveI : BorelSpace (WO V W) := ⟨rfl⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, hm.2.2]; exact ENNReal.one_lt_top⟩
  have e0 : coeL ψ V W (toB hψ f hf.1) = f := coe_toB hψ f hf.1
  have hF : toB hψ f hf.1 ∈ (GlobalTheory.Size.thetaLevel ψ V W U).comap (coeL ψ V W) := by
    rw [Submodule.mem_comap, e0]
    exact hf
  obtain ⟨g, h1, h2, h3⟩ := dense_vec h hψ A B hU (toL2 _ _ (μ.restrict 𝓕))
    (fun v G => by
      rw [← enorm_sq_inj, ← lintegral_norm_sq_eq_toL2, ← lintegral_norm_sq_eq_toL2]
      exact lintegral_rhoB hψ μ 𝓕 hm.1 hm.2.1 _ G)
    (fun a : D.what₂.Tau × Fin W.rank × Fin V.rank × Bool =>
      atPl a.1 (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1))) d hF hδ
  refine ⟨coeL ψ V W g, h1, h2, lt_of_eq_of_lt ?_ h3⟩
  have e1 : ∀ G : BB ψ V W, l2O μ 𝓕 (coeL ψ V W G) = ‖toL2 _ _ (μ.restrict 𝓕) G‖ₑ := fun G =>
    (eLpNorm_congr_ae (BoundedContinuousFunction.coeFn_toLp 2 (μ.restrict 𝓕) ℂ G.1)).symm.trans (Lp.enorm_def _).symm
  have e2 : f - coeL ψ V W g = coeL ψ V W (toB hψ f hf.1 - g) := by rw [LinearMap.map_sub, e0]
  simp only [sobO, wordSum, e2, coe_word h hψ hU _ (sub_mem hF h2), e1]

end

end GlobalTheory.FockApprox

open scoped ENNReal in

theorem GlobalTheory.FockApprox.theta_approx_fock : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → IsStdChar D ψ (-1) → ∀ (ε : Bool) (S T : GlobalTheory.Grid.Node D) (U : AddSubgroup (WO S.V T.V)), IsOpen (U : Set (WO S.V T.V)) → ∀ Φ, Φ ∈ GlobalTheory.Size.thetaLevel ψ (GlobalTheory.Grid.sgn ε S.V) T.V U → ∀ (μ : Measure (WO S.V T.V)) (𝓕 : Set (WO S.V T.V)), IsCovolOne (ratL T.V (GlobalTheory.Grid.sgn ε S.V)) μ 𝓕 → ∀ (d : ℕ) (δ : ℝ), 0 < δ → ∃ (n : ℕ) (f : Fin n → (WO S.V T.V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol S T), (∀ l, GlobalTheory.Grid.IsFinVec ψ θ ε S T (f l)) ∧ (Φ - ∑ l, GlobalTheory.Grid.fock ψ θ ε S T (f l) (p l)) ∈ GlobalTheory.Size.thetaLevel ψ (GlobalTheory.Grid.sgn ε S.V) T.V U ∧ @GlobalTheory.Size.sobO D ψ θ (GlobalTheory.Grid.sgn ε S.V) T.V μ 𝓕 d (Φ - ∑ l, GlobalTheory.Grid.fock ψ θ ε S T (f l) (p l)) < ENNReal.ofReal δ := by
  intro D ψ θ hθ hψ ε S T U hU Φ hΦ μ 𝓕 hm d δ hδ
  obtain ⟨g, h1, h2, h3⟩ := GlobalTheory.FockApprox.dense_level (ψ := ψ) (θ := θ) (V := GlobalTheory.Grid.sgn ε S.V) (W := T.V)
    (GlobalTheory.SquareComm.frSgn ε (GlobalTheory.ChainFr.Fr.ofModel S.M)) (GlobalTheory.ChainFr.Fr.ofModel T.M) hψ hθ hm hU hΦ d
    (ENNReal.ofReal_pos.2 hδ)
  obtain ⟨n, f, p, hf, hg⟩ := GlobalTheory.FockApprox.exists_sum_of_mem_fockSpan ψ θ ε S T U h1
  refine ⟨n, f, p, hf, ?_, ?_⟩
  · rw [← hg]
    exact sub_mem hΦ h2
  · rw [← hg]
    exact h3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePureDataOfCosetIndicatorExpansionsDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open GlobalTheory.FunObj

noncomputable section

namespace GlobalTheory.RowTest.CosetFin

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc}

theorem finDatum_eq {t : T} {p : Pair T} {k : ℕ} {a b : FinDatum G t p} (ha : IsCosetDatum k a) (hb : IsCosetDatum k b)
    (hP : a.P = b.P) (he : a.e = b.e) (hz : a.z = b.z) {u} (hu : a.fn u ≠ 0) (hu' : b.fn u ≠ 0) : a = b := by
  have hf := ha.fn_eq hb he hu hu'
  cases a
  cases b
  simp only at hP he hz hf
  subst hP he hz hf
  rfl

theorem pureDat_eq {t : T} {k : ℕ} {e : AE D} {d d' : PureDat G t}
    (hc : (∀ j, IsCosetDatum k (d.1 j)) ∧ ∀ i, IsCosetDatum k (d.2 i))
    (hc' : (∀ j, IsCosetDatum k (d'.1 j)) ∧ ∀ i, IsCosetDatum k (d'.2 i))
    (hp : (∀ j, (d.1 j).P = locPl G t ∧ (d.1 j).e = e ∧ (d.1 j).z = 1) ∧ ∀ i, (d.2 i).P = locPl G t ∧ (d.2 i).e = e ∧ (d.2 i).z = 1)
    (hp' : (∀ j, (d'.1 j).P = locPl G t ∧ (d'.1 j).e = e ∧ (d'.1 j).z = 1) ∧
      ∀ i, (d'.2 i).P = locPl G t ∧ (d'.2 i).e = e ∧ (d'.2 i).z = 1)
    (hx : ∀ j, ∃ u, (d.1 j).fn u ≠ 0 ∧ (d'.1 j).fn u ≠ 0) (hy : ∀ i, ∃ u, (d.2 i).fn u ≠ 0 ∧ (d'.2 i).fn u ≠ 0) : d = d' := by
  refine Prod.ext (funext fun j => ?_) (funext fun i => ?_)
  · obtain ⟨a1, a2, a3⟩ := hp.1 j
    obtain ⟨b1, b2, b3⟩ := hp'.1 j
    obtain ⟨u, hu, hu'⟩ := hx j
    exact finDatum_eq (hc.1 j) (hc'.1 j) (a1.trans b1.symm) (a2.trans b2.symm) (a3.trans b3.symm) hu hu'
  · obtain ⟨a1, a2, a3⟩ := hp.2 i
    obtain ⟨b1, b2, b3⟩ := hp'.2 i
    obtain ⟨u, hu, hu'⟩ := hy i
    exact finDatum_eq (hc.2 i) (hc'.2 i) (a1.trans b1.symm) (a2.trans b2.symm) (a3.trans b3.symm) hu hu'

end GlobalTheory.RowTest.CosetFin

namespace GlobalTheory.RowTest.CosetFin

section Sums

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
  {S : GridChoice W U} {t : T} {Φ : G.Datum} {β : CosFam G t}

theorem mem_support_of {k : ℕ} {τ₀ τ : PureDat G t →₀ ℂ} (h₀ : IsCosetExpansion S t Φ β k τ₀)
    (h : IsCosetExpansion S t Φ β k τ) {d : PureDat G t} (hd : d ∈ τ.support) : d ∈ τ₀.support := by
  obtain ⟨-, ⟨e, he, h1, h2⟩, h3⟩ := h
  obtain ⟨-, ⟨e₀, he₀, h1₀, h2₀⟩, h3₀⟩ := h₀
  have hee : e₀ = e := GlobalTheory.StepVecSum.idemSum_eq (G.V (.top 0)) he he₀
  subst hee
  choose x hx _ hx' using (h3 d hd).1
  choose y hy _ hy' using (h3 d hd).2
  have ex : ∀ j, (d.1 j).fn (x j) = 1 := fun j => by rw [hx', Set.indicator_of_mem (mem_halfCoset_self _ _ _ _)]; rfl
  have ey : ∀ i, (d.2 i).fn (y i) = 1 := fun i => by rw [hy', Set.indicator_of_mem (mem_halfCoset_self _ _ _ _)]; rfl
  have hs : (τ.sum fun d c => c * (∏ j, (d.1 j).fn (x j)) * ∏ i, (d.2 i).fn (y i)) = τ d := by
    rw [Finsupp.sum, Finset.sum_eq_single_of_mem d hd]
    · simp [ex, ey]
    · intro d' hd' hne
      by_contra h0
      obtain ⟨h4, h5⟩ := mul_ne_zero_iff.1 h0
      exact hne (pureDat_eq (h3 d' hd') (h3 d hd) (h1 d' hd') (h1 d hd)
        (fun j => ⟨x j, Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul h4) j (Finset.mem_univ _), by rw [ex]; exact one_ne_zero⟩)
        (fun i => ⟨y i, Finset.prod_ne_zero_iff.1 h5 i (Finset.mem_univ _), by rw [ey]; exact one_ne_zero⟩))
  have hxe := fun j => ((h1 d hd).1 j).2.1 ▸ hx j
  have hye := fun i => ((h1 d hd).2 i).2.1 ▸ hy i
  have hne : (τ₀.sum fun d c => c * (∏ j, (d.1 j).fn (x j)) * ∏ i, (d.2 i).fn (y i)) ≠ 0 := by
    rw [h2₀ x y hxe hye, ← h2 x y hxe hye, hs]
    exact Finsupp.mem_support_iff.1 hd
  obtain ⟨d', hd', h0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨h4, h5⟩ := mul_ne_zero_iff.1 h0
  have hdd : d' = d := pureDat_eq (h3₀ d' hd') (h3 d hd) (h1₀ d' hd') (h1 d hd)
    (fun j => ⟨x j, Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul h4) j (Finset.mem_univ _), by rw [ex]; exact one_ne_zero⟩)
    (fun i => ⟨y i, Finset.prod_ne_zero_iff.1 h5 i (Finset.mem_univ _), by rw [ey]; exact one_ne_zero⟩)
  exact hdd ▸ hd'

end Sums

theorem finite_pureDat_of_depth : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (k : ℕ), {d : PureDat G t | ∃ τ, IsCosetExpansion S t Φ β k τ ∧ d ∈ τ.support}.Finite := by
  intro D T L sc G W U S t Φ β k
  by_cases h : ∃ τ₀, IsCosetExpansion S t Φ β k τ₀
  · obtain ⟨τ₀, h₀⟩ := h
    exact τ₀.support.finite_toSet.subset fun d ⟨τ, hτ, hd⟩ => mem_support_of h₀ hτ hd
  · refine Set.finite_empty.subset ?_
    rintro d ⟨τ, hτ, -⟩
    exact h ⟨τ, hτ⟩

end GlobalTheory.RowTest.CosetFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstMemberParameterInvOfChainParameterInv
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainInv

variable {D : D7}

theorem conjP_eq_conjPl (P : HeightOneSpectrum (𝓞 D.host.E)) : Formalism.L2.Col.conjPrime₂ P = Formalism.DivisionValues.conjPl P := by
  apply HeightOneSpectrum.ext
  ext x
  show Formalism.L2.Col.cO _ x ∈ P.asIdeal ↔ x ∈ Ideal.map (Formalism.DivisionValues.cO D.host.E) P.asIdeal
  rw [← Ideal.comap_symm, Ideal.mem_comap]
  have : (Formalism.DivisionValues.cO D.host.E).symm x = Formalism.L2.Col.cO _ x := by
    apply RingOfIntegers.ext
    simp [Formalism.DivisionValues.cO, Formalism.L2.Col.cO]
    rfl
  rw [this]

theorem under_conjPl (w : HeightOneSpectrum (𝓞 D.host.E)) :
    (Formalism.DivisionValues.conjPl w).under (𝓞 D.host.F) = w.under (𝓞 D.host.F) := by
  rw [← conjP_eq_conjPl]
  exact GlobalTheory.GridPlaces.under_conjP w

theorem absNorm_conjPl (w : HeightOneSpectrum (𝓞 D.host.E)) :
    Ideal.absNorm (Formalism.DivisionValues.conjPl w).asIdeal = Ideal.absNorm w.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr
    (Ideal.quotientEquiv w.asIdeal (Formalism.DivisionValues.conjPl w).asIdeal (Formalism.DivisionValues.cO D.host.E) rfl).toEquiv).symm

theorem not_isSplit_of_conjPl_eq {w : HeightOneSpectrum (𝓞 D.host.E)} (hc : Formalism.DivisionValues.conjPl w = w) :
    ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) := by
  intro hs
  obtain ⟨P, Q, hPQ, hP, hQ⟩ := GlobalTheory.LFun.isSplit_iff.1 hs
  have key : ∀ R : HeightOneSpectrum (𝓞 D.host.E), R.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) → R = w :=
    fun R hR => (GlobalTheory.GridPlaces.eq_or_eq_conjP hR).elim id fun h => h.trans ((conjP_eq_conjPl w).trans hc)
  exact hPQ ((key P hP).trans (key Q hQ).symm)

theorem val_conjPl_of_resEta (χ : (AE D)ˣ →* Circle) (n : ℕ) (hr : Formalism.L2.Theta.ResEta D χ n)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hu : GlobalTheory.LFun.UnrAt χ w) (hu' : GlobalTheory.LFun.UnrAt χ (Formalism.DivisionValues.conjPl w)) :
    GlobalTheory.LFun.val (F := D.host.F) χ (Formalism.DivisionValues.conjPl w) = (GlobalTheory.LFun.val (F := D.host.F) χ w)⁻¹ := by
  have h2 := (GlobalTheory.AdelicU.isCMExt_host D).2.2.1
  by_cases hc : Formalism.DivisionValues.conjPl w = w
  · have hns := not_isSplit_of_conjPl_eq hc
    rcases GlobalTheory.LFun.InertChart.isSplit_or_isInertAt (GlobalTheory.VacCoef.isUnram_host D (w.under (𝓞 D.host.F))) with hs | ⟨w0, hw0⟩
    · exact absurd hs hns
    · obtain rfl : w0 = w := GlobalTheory.LFun.eq_of_not_isSplit hns (GlobalTheory.LFun.under_eq_of_isInertAt hw0) rfl
      have hv := GlobalTheory.LFun.ResEta.val_of_isInertAt h2 hr hw0 hu
      rw [hc, hv, ← inv_pow, inv_neg_one]
  · exact eq_inv_of_mul_eq_one_right (GlobalTheory.LFun.ResEta.val_mul_val h2 hr (Ne.symm hc) rfl (under_conjPl w) hu hu')

theorem val_step_conjPl (c : Com D) (hc : c.Is) (k : ℕ) (hk : k < D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) :
    GlobalTheory.LFun.val (F := D.host.F) (c.chS (k + 1)) (Formalism.DivisionValues.conjPl w) =
                 (GlobalTheory.LFun.val (F := D.host.F) (c.chS (k + 1)) w)⁻¹ ∧
      GlobalTheory.LFun.val (F := D.host.F) (c.chT (k + 1)) (Formalism.DivisionValues.conjPl w) =
        (GlobalTheory.LFun.val (F := D.host.F) (c.chT (k + 1)) w)⁻¹ := by
  have hw' : Formalism.DivisionValues.conjPl w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) := by
    intro h
    apply hw
    rw [GlobalTheory.LFun.above, Set.mem_setOf_eq] at h ⊢
    rwa [under_conjPl] at h
  have hμ : GlobalTheory.LFun.val (F := D.host.F) (c.μ (k + 1)) (Formalism.DivisionValues.conjPl w) =
      (GlobalTheory.LFun.val (F := D.host.F) (c.μ (k + 1)) w)⁻¹ :=
    val_conjPl_of_resEta _ 0 (hc.chars.2.2.2.2 (k + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)).2 w
      (hc.unr ⟨k, hk⟩ w hw) (hc.unr ⟨k, hk⟩ _ hw')
  have hη : GlobalTheory.LFun.val (F := D.host.F) c.η (Formalism.DivisionValues.conjPl w) = (GlobalTheory.LFun.val (F := D.host.F) c.η w)⁻¹ :=
    val_conjPl_of_resEta _ 1 hc.chars.2.2.1 w (GlobalTheory.LFun.unrAt_of_unramEverywhere hc.chars.2.1 w)
      (GlobalTheory.LFun.unrAt_of_unramEverywhere hc.chars.2.1 _)
  unfold Com.chS Com.chT Lift.chrStep
  split_ifs <;> simp only [GlobalTheory.LFun.val_mul, GlobalTheory.LFun.val_inv, hμ, hη, mul_inv, inv_inv, and_self]

theorem range_reflect (t : ℕ) : (Multiset.range t).map (fun i => t - 1 - i) = Multiset.range t := by
  refine (Multiset.Nodup.ext ?_ (Multiset.nodup_range t)).2 fun a => ?_
  · refine (Multiset.nodup_range t).map_on fun x hx y hy h => ?_
    rw [Multiset.mem_range] at hx hy
    omega
  · simp only [Multiset.mem_map, Multiset.mem_range]
    constructor
    · rintro ⟨b, hb, rfl⟩; omega
    · intro ha; exact ⟨t - 1 - a, by omega, by omega⟩

theorem seg_conjPl (w : HeightOneSpectrum (𝓞 D.host.E)) (z : ℂˣ) (t : ℕ) :
    GlobalTheory.LFun.seg (Formalism.DivisionValues.conjPl w) z⁻¹ t = (GlobalTheory.LFun.seg w z t).map (·⁻¹) := by
  have hN : ∀ y, GlobalTheory.LFun.npowU (Formalism.DivisionValues.conjPl w) y = GlobalTheory.LFun.npowU w y := fun y =>
    Units.ext (by simp only [GlobalTheory.LFun.coe_npowU, GlobalTheory.LFun.npow, absNorm_conjPl])
  simp only [GlobalTheory.LFun.seg, hN, Multiset.map_map, Finset.range_val]
  conv_rhs => rw [← range_reflect t, Multiset.map_map]
  refine Multiset.map_congr rfl fun i hi => ?_
  rw [Multiset.mem_range] at hi
  simp only [Function.comp_apply, mul_inv]
  congr 1
  refine Units.ext ?_
  simp only [GlobalTheory.LFun.coe_npowU, Units.val_inv_eq_inv_val, GlobalTheory.LFun.npow]
  rw [← Complex.cpow_neg]
  congr 1
  push_cast [Nat.cast_sub (show i ≤ t - 1 by omega), Nat.cast_sub (show 1 ≤ t by omega)]
  ring

theorem chainPar_conjPl (c : Com D) (hc : c.Is) (B B' : GlobalTheory.LFun.Fam D.host.E) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))))
    (hB : B' (Formalism.DivisionValues.conjPl w) = (B w).map (·⁻¹)) :
    ∀ k ≤ D.R.m, chainPar c B' k (Formalism.DivisionValues.conjPl w) = (chainPar c B k w).map (·⁻¹) := by
  intro k hk
  induction k with
  | zero => exact hB
  | succ k ih =>
    obtain ⟨hS, hT⟩ := val_step_conjPl c hc k (by omega) w hw
    rw [chainPar_succ, chainPar_succ]
    simp only [stepPar]
    rw [ih (by omega), hS, hT, seg_conjPl, Multiset.map_add, Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp_apply, mul_inv, inv_inv]

theorem conjPl_inv_of_chainPar : ∀ (D : D7) (c : Com D), c.Is → ∀ j ≤ D.R.m, ∀ (B : GlobalTheory.LFun.Fam D.host.E),
    ∀ w ∉ (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))),
    chainPar c B j (Formalism.DivisionValues.conjPl w) = (chainPar c B j w).map (·⁻¹) →
      B (Formalism.DivisionValues.conjPl w) = (B w).map (·⁻¹) := by
  intro D c hc j hj B w hw h
  classical
  let B' : GlobalTheory.LFun.Fam D.host.E := Function.update B (Formalism.DivisionValues.conjPl w) ((B w).map (·⁻¹))
  have hB : B' (Formalism.DivisionValues.conjPl w) = (B w).map (·⁻¹) := by simp [B']
  have h1 := chainPar_conjPl c hc B B' w hw hB j hj
  have h2 := chainPar_inj_at D c j B B' (Formalism.DivisionValues.conjPl w) (h.trans h1.symm)
  rw [h2, hB]

example : ∀ (D : D7) (c : Com D), c.Is → ∀ j ≤ D.R.m, ∀ (B : GlobalTheory.LFun.Fam D.host.E), ∀ w ∉ (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))), chainPar c B j (Formalism.DivisionValues.conjPl w) = (chainPar c B j w).map (·⁻¹) → B (Formalism.DivisionValues.conjPl w) = (B w).map (·⁻¹) :=
  conjPl_inv_of_chainPar

end GlobalTheory.ChainInv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrT
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

noncomputable section
namespace GlobalTheory.MovedDict
variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {U : Set T}

def frS (N : Std G U) : ∀ p : GlobalTheory.ChiGrid.Pair T, GL (Fin (G.pS p).rank) D.host.E
  | .chi i j => N.fr (.grid (i + 1) j)
  | .mu _ i j => N.fr (.grid i j)
  | .core i => N.fr (.core (i + 1))
  | .top _ j => N.fr (.top j)

def frT (N : Std G U) : ∀ p : GlobalTheory.ChiGrid.Pair T, GL (Fin (G.pT p).rank) D.host.E
  | .chi i j => N.fr (.grid i j)
  | .mu _ i j => N.fr (.grid i (j + 1))
  | .core i => N.fr (.core i)
  | .top _ j => N.fr (.top (j + 1))

def inV {n : ℕ} (B : GL (Fin n) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E) :=
  (B : Matrix (Fin n) (Fin n) D.host.E).mulVec '' (Λ : Set (Fin n → D.host.E))

end GlobalTheory.MovedDict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameCongruentSubOneMulVecMemIdealLatticeCompletStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameCongruent_sub_one_mulVec_mem_idealLatticeCompletion : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (n : Type) [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p S n),
  β.IsLat L (Submodule.pi Set.univ fun _ : n => (1 : Submodule 𝒪[k] k)) → ∀ (𝔪 : Ideal (𝓞 D.host.E)) (d : ℕ),
  (∃ m ∈ 𝔪, ∀ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ d, ∃ c ∈ 𝒪[k], (z : k) = c * p.pr (incA D ((m : 𝓞 D.host.E) : D.host.E))) →
  ∀ k₀ : GL n 𝒪[k], (∀ i j, (k₀.1 - 1) i j ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ d) →
  ∀ y : Fin S.rank → AE D, y ∈ latV S L (· = p.v) →
  (fun i => p.e * ((mt S (β.gl (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀)) - 1) *ᵥ y) i) ∈ latV S (𝔪 • L) (· = p.v) := by
  first | exact @GlobalTheory.FinPl.FrameCong.sub_one_mulVec_mem | exact GlobalTheory.FinPl.FrameCong.sub_one_mulVec_mem | (intros; apply GlobalTheory.FinPl.FrameCong.sub_one_mulVec_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodParOfSigOK
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.NodePar

theorem goodPar_of_sigOK {D : D7} (N : GlobalTheory.Grid.Node D) (h : N.V.SigOK) (τ : D.what₂.Tau) :
    GoodPar N.V.rank (N.V.sig (tauE D τ)).1 (N.V.sig (tauE D τ)).2 (N.S τ) := by
  have hm := GlobalTheory.TowerSplit.hasSignature_of_model N.M τ
  rw [GlobalTheory.TowerSplit.signCard_of_isEnum (N.M.enum τ), GlobalTheory.TowerSplit.signCard_of_isEnum (N.M.enum τ)] at hm
  have hs : Formalism.UG.HasSignature (gramAt D N.V τ) (N.V.sig (tauE D τ)).1 (N.V.sig (tauE D τ)).2 := h (tauE D τ)
  obtain ⟨e1, e2⟩ := Formalism.UG.P.signature_unique _ _ _ _ _ _ hm hs
  exact ⟨N.M.lam τ, N.M.ε τ, N.M.enum τ,
    GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (N.M.enum τ).1 (N.M.ds τ), e1, e2⟩

end GlobalTheory.NodePar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyGeneratorRatioLeTraceTermsStatement
section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeIsogeny_generatorRatio_le_traceTerms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (P : Ideal (𝓞 E)) (p i : ℕ) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (C : Subgroup (Over.mk (U.un k x).x ⟶ Xo.univ.t.G)) (z : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), admitted l P p → Xo.univ.t.HeckeKer (Over.mk (U.un k x).x) Dw P p i C → HkPtC p (U.un k x) C z → FrBor t (U.un k' x') z → IsUnitFr (U.X k) x.1 → IsUnitFr (U.X k') x'.1 → cabs (t none : CAt σ) ≤ (Ideal.absNorm P : ℝ) ^ i := by
  first | exact @GlobalTheory.HeckeEx.cabs_gen_le_of_hkPt | exact GlobalTheory.HeckeEx.cabs_gen_le_of_hkPt | (intros; apply GlobalTheory.HeckeEx.cabs_gen_le_of_hkPt <;> assumption)
end

