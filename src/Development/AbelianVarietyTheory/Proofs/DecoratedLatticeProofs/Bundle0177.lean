import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SchurOrthogonalitySquareIntegrable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.SharpRestriction.Bundle0001
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartW
import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.CarriesOfKilled
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0151
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0324
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1150
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0159

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TendstoSetIntegralUnramifiedOutsideOpenSubset
section
noncomputable section

namespace GlobalTheory.Core.Rk.IP

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem measurableSet_openOff {D : D7} (A : HSp D) (L : Lat A) (hL : IsSelfDualC A L) (S : Finset (FinPl D)) :
    MeasurableSet (openOff A L S) := by
  have : BorelSpace (GA D A) := ⟨rfl⟩
  have : Countable (FinPl D) := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum D.host.F
  have := hL.1
  have e : openOff A L S = ⋂ v, ⋂ (_ : v ∉ S),
      (proj D.sp.cm.sig A.gram v) ⁻¹' (stabLoc D.sp.cm.sig A.gram L v : Set _) := by
    ext g; simp [openOff]
  rw [e]
  exact MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ =>
    ((isOpen_stabLoc D.sp.cm.sig A.gram L v).preimage (continuous_proj D.sp.cm.sig A.gram v)).measurableSet

theorem monotone_openOff {D : D7} (A : HSp D) (L : Lat A) : Monotone (openOff A L) :=
  fun _ _ h _ hg v hv => hg v fun h' => hv (h h')

theorem iUnion_openOff {D : D7} (A : HSp D) (L : Lat A) (hL : IsSelfDualC A L) : ⋃ S, openOff A L S = Set.univ := by
  have := hL.1
  refine Set.eq_univ_of_forall fun g => ?_
  have h := Filter.eventually_cofinite.1 (eventually_proj_mem_stabLoc D.sp.cm.sig A.gram L g)
  exact Set.mem_iUnion.2 ⟨h.toFinset, fun v hv => by_contra fun h' => hv (h.mem_toFinset.2 h')⟩

theorem tendsto_setIntegral_openOff : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (m : Measure (GA D A)) (F : GA D A → ℂ), Integrable F m → Filter.Tendsto (fun S : Finset (FinPl D) => ∫ g in openOff A L S, F g ∂m) Filter.atTop (nhds (∫ g, F g ∂m)) := by
  intro D A L hL m F hF
  have : Countable (FinPl D) := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum D.host.F
  have h := tendsto_setIntegral_of_monotone (μ := m) (f := F) (measurableSet_openOff A L hL) (monotone_openOff A L)
    hF.integrableOn
  rwa [iUnion_openOff A L hL, Measure.restrict_univ] at h

end GlobalTheory.Core.Rk.IP

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaAdjointScalarTheoremOfScalarFormula
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.ThmAFromAForm

theorem pThmA_of_aForm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → AForm R.toRealDat R.SF → (∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c') → R.PThmA := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s _ hC _ hA h1
  exact GlobalTheory.LiftScalarTest.of_aForm R hA hC.scal.lam0 (fun i p c c' hc hc' => (h1 p c c' hc hc').2 i)

end GlobalTheory.ThmAFromAForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainCharQuotientLFunctionEntireNeZero
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.QuotL

theorem e_strictMono {R : Ranks} (P : HCParam R) : StrictMono P.e := by
  have ht : (0 : ℚ) ≤ R.t := by positivity
  have step : ∀ (a : ℕ) (h : a + 1 < R.m), P.e ⟨a, by omega⟩ < P.e ⟨a + 1, h⟩ := fun a h => by
    have g1 := P.gap_eb ⟨a, by omega⟩ h
    have g2 := P.gap_be ⟨a + 1, h⟩
    linarith
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  simp only [Fin.mk_lt_mk] at hab
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hab
  induction d with
  | zero => exact step a hb
  | succ d ih =>
    have h1 := ih (by omega) (by omega)
    have h2 := step (a + d + 1) (by omega)
    have e1 : (⟨a + (d + 1) + 1, hb⟩ : Fin R.m) = ⟨a + d + 1 + 1, by omega⟩ := Fin.ext (by simp; omega)
    rw [e1]
    exact h1.trans h2

variable {D : D7}

theorem trivialOnF {c : Com D} (hc : c.Is) {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ D.R.m) :
    GlobalTheory.IndefiniteRowSideFullHecke.PartialLFunctionCharacter.TrivialOnF (c.μ k) := fun a => by
  obtain ⟨⟨η, hη⟩, h⟩ := (hc.chars.2.2.2.2 k (Finset.mem_Icc.2 ⟨h1, h2⟩)).2
  exact (h η hη a).trans (pow_zero _)

theorem isHecke {c : Com D} (hc : c.Is) {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ D.R.m) : IsHeckeChar D (c.μ k) :=
  (hc.chars.2.2.2.2 k (Finset.mem_Icc.2 ⟨h1, h2⟩)).1

theorem quotL_entire_ne_zero : ∀ (D : D7) (c : Com D), c.Is → ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ D.R.m →
    ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
      (∀ z : ℂ, 1 < z.re → Λ z = GlobalTheory.LFun.eulerProd (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))))
        (fun w => {GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ j)⁻¹) w}) z) ∧
      ∀ n : ℕ, 1 ≤ n → n ≤ D.R.t → Λ n ≠ 0 := by
  intro D c hc i j hi hij hj
  obtain ⟨i', rfl⟩ : ∃ i' : ℕ, i = i' + 1 := ⟨i - 1, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j' : ℕ, j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  have hexp : ∃ (τ : D.what₂.Tau) (e e' : ℚ), HasInfExp D (c.μ (i' + 1)) τ (-e) ∧
      HasInfExp D (c.μ (j' + 1)) τ (-e') ∧ e ≠ e' :=
    ⟨τ, (D.hc τ).e ⟨i', by omega⟩, (D.hc τ).e ⟨j', by omega⟩, hc.exp ⟨i', by omega⟩ τ, hc.exp ⟨j', by omega⟩ τ,
      (e_strictMono (D.hc τ) (show (⟨i', by omega⟩ : Fin D.R.m) < ⟨j', by omega⟩ from
        Fin.mk_lt_mk.2 (by omega))).ne⟩
  obtain ⟨Λ, ⟨hd, hp⟩, hpos⟩ := (GlobalTheory.HeckeRatio.heckeRatioPos D (c.μ (i' + 1)) (c.μ (j' + 1))
    (isHecke hc (by omega) (by omega)) (isHecke hc (by omega) hj) (trivialOnF hc (by omega) (by omega))
    (trivialOnF hc (by omega) hj) hexp D.R.t).2 c.S
  refine ⟨Λ, hd, fun z hz => ?_, fun n h1 h2 h0 => ?_⟩
  · have hunr : ∀ w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))),
        GlobalTheory.LFun.UnrAt (c.μ (i' + 1) * (c.μ (j' + 1))⁻¹) w := fun w hw =>
      (hc.unr ⟨i', by omega⟩ w hw).mul (hc.unr ⟨j', by omega⟩ w hw).inv
    have hoff : ∀ P, OffS D c.S P ↔ P ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) :=
      fun P => (GlobalTheory.HeckeRatio.offS_iff c.S P).trans Iff.rfl
    let e := Equiv.subtypeEquivRight hoff
    have k := hp z hz
    rw [GlobalTheory.HeckeRatio.lfac_eq] at k
    have k2 : HasProd (fun w : {w // w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))} =>
        GlobalTheory.LFun.locL (fun w => {GlobalTheory.LFun.val (F := D.host.F) (c.μ (i' + 1) * (c.μ (j' + 1))⁻¹) w}) w.1 z) (Λ z) := by
      refine (e.hasProd_iff).1 (k.congr_fun fun P => ?_)
      have hu := hunr P.1 ((hoff P.1).1 P.2)
      rw [GlobalTheory.LFun.lfac_eq_locL (Formalism.IndefR.ThmB.InputsHecke.isCMExt D)]
      simp only [Function.comp_apply, e, Equiv.subtypeEquivRight_apply_coe, GlobalTheory.LFun.locL,
        GlobalTheory.LFun.charFam_of_unrAt hu]
    exact k2.tprod_eq.symm
  · have := (hpos n h1 h2).2
    rw [h0, Complex.zero_re] at this
    exact lt_irrefl _ this

end GlobalTheory.ChainOnto.QuotL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageConjugateValuesHeckeOperators
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjVal

variable {D : D7}

def Good (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ) (f : GA D V → ℂ) : Prop :=
  Continuous f ∧ (∃ C : ℝ, ∀ g, ‖f g‖ ≤ C) ∧ (∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) ∧ ∀ k ∈ J, ∀ g, f (g * k) = χ k * f g

theorem Good.add {V : HSp D} {J : Set (GA D V)} {χ : GA D V → ℂ} {f f' : GA D V → ℂ}
    (h : Good V J χ f) (h' : Good V J χ f') : Good V J χ (f + f') := by
  obtain ⟨c, ⟨C, hC⟩, l, r⟩ := h
  obtain ⟨c', ⟨C', hC'⟩, l', r'⟩ := h'
  refine ⟨c.add c', ⟨C + C', fun g => (norm_add_le _ _).trans (add_le_add (hC g) (hC' g))⟩,
    fun γ hγ g => by simp [l γ hγ g, l' γ hγ g], fun k hk g => by simp [r k hk g, r' k hk g, mul_add]⟩

theorem Good.smul {V : HSp D} {J : Set (GA D V)} {χ : GA D V → ℂ} {f : GA D V → ℂ} (a : ℂ)
    (h : Good V J χ f) : Good V J χ (a • f) := by
  obtain ⟨c, ⟨C, hC⟩, l, r⟩ := h
  refine ⟨continuous_const.mul c, ⟨‖a‖ * C, fun g => ?_⟩,
    fun γ hγ g => by simp [l γ hγ g], fun k hk g => by simp [r k hk g, mul_left_comm]⟩
  rw [Pi.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (hC g) (norm_nonneg a)

theorem good_val (hP : GlobalTheory.Published.CuspRapidDecay) {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D}
    {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ}
    (u : (⨂[ℂ] τ, M.sm τ) →ₗ[ℂ] (GA D V → ℂ)) (hu : u ∈ MultT θ M J χ) (v : ⨂[ℂ] τ, M.sm τ) :
    Good V J χ (u v) := by
  have hT := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT θ M J χ u).1 hu)
  have hu' : u = PiTensorProduct.lift (PiTensorProduct.lift.symm u) := (LinearEquiv.apply_symm_apply _ _).symm
  induction v using PiTensorProduct.induction_on with
  | smul_tprod a x =>
    rw [map_smul]
    refine Good.smul a ?_
    rw [hu', PiTensorProduct.lift.tprod]
    exact ⟨(hT.aut x).cont, GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ (hT.aut x) (hT.cusp x), (hT.aut x).left,
      hT.lev x⟩
  | add x y hx hy =>
    rw [map_add]
    exact hx.add hy

theorem conj_eq_one_iff' (z : ℂ) : conj z = 1 ↔ z = 1 := by
  constructor
  · intro h; simpa using congrArg conj h
  · intro h; simp [h]

theorem conj_values_hecke : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, ForStage D fun c _ s =>
    (∀ (u : s.CC c) v, Continuous (PiLocalization₂.val u v) ∧ (∃ C : ℝ, ∀ g, ‖PiLocalization₂.val u v g‖ ≤ C) ∧
      (∀ γ ∈ GQ s.V, ∀ g, PiLocalization₂.val u v (γ * g) = PiLocalization₂.val u v g) ∧
      ∀ k ∈ levS s.V s.β s.L, ∀ g, PiLocalization₂.val u v (g * k) = Lev.levChi s.V s.β s.L k * PiLocalization₂.val u v g) ∧
    (∀ P d R, Hecke₂ s.V (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S P d R ↔
      Hecke₂ s.V (levS s.V s.β s.L) (fun k => conj (Lev.levChi s.V s.β s.L k)) c.S P d R) ∧
    ∀ (R : Finset (GA D s.V)) (f : GA D s.V → ℂ),
      heckeLin s.V R (fun g => conj (f g)) = fun g => conj (heckeLin s.V R f g) := by
  intro hP D c hc j _ s _
  refine ⟨fun u v => good_val hP hc.inf (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) u.2 v, fun P d R => ?_, fun R f => ?_⟩
  · simp only [Hecke₂, conj_eq_one_iff']
  · funext g
    simp [heckeLin, map_sum]

end GlobalTheory.ConjVal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageCuspFormMapEqZeroOfValueZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem val_eq_zero_imp (D : D7) : MetEx D → ForStage D fun c _ s => ∀ (x : s.CC c) w, w ≠ 0 → PiLocalization₂.val x w = 0 → x = 0 := by
  intro hM c hc j hj s hs x w hw hx
  obtain ⟨ipD, ip, hm⟩ := hM c hc j hj s hs
  have h1 := hm.schur x x w w
  have h0 : Lift.pet s.ν s.fd ((x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w) ((x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w) = 0 := by
    have hx' : (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w = 0 := hx
    rw [hx']
    simp [Lift.pet]
  rw [h0] at h1
  have hD : ipD w w ≠ 0 := by
    intro h
    have := hm.posD w hw
    rw [h] at this
    simp at this
  have hip : ip x x = 0 := by
    rcases mul_eq_zero.mp h1.symm with h | h
    · exact h
    · exact absurd h hD
  by_contra hne
  have := hm.pos x hne
  rw [hip] at this
  simp at this

end GlobalTheory.ChainOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageLatticeStabilizerParamsOffSet
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatAgree

open GlobalTheory.AdelicU GlobalTheory.LFun Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem valued_natCast_eq_one {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {v : HeightOneSpectrum R} {N : ℕ} (hN : (N : R) ∉ v.asIdeal) :
    Valued.v (N : v.adicCompletion K) = 1 := by
  have e : (N : v.adicCompletion K) = ((algebraMap R K (N : R) : K) : v.adicCompletion K) := by
    rw [map_natCast]; exact (map_natCast (algebraMap K (v.adicCompletion K)) N).symm
  rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  exact le_antisymm (v.intValuation_le_one _) (not_lt.1 fun h => hN ((v.intValuation_lt_one_iff_mem _).1 h))

theorem natCast_ne_zero_of {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {v : HeightOneSpectrum R} {N : ℕ} (hN : (N : R) ∉ v.asIdeal) :
    (N : v.adicCompletion K) ≠ 0 := fun h => by
  have := valued_natCast_eq_one (K := K) hN
  rw [h, map_zero] at this
  exact zero_ne_one this

theorem inv_natCast_mem {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {v : HeightOneSpectrum R} {N : ℕ} (hN : (N : R) ∉ v.asIdeal) :
    (N : v.adicCompletion K)⁻¹ ∈ v.adicCompletionIntegers K := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, valued_natCast_eq_one hN, inv_one]

theorem latLoc_le {L L' : Submodule (𝓞 E) (Fin n → E)} {v : HeightOneSpectrum (𝓞 F)} {N : ℕ}
    (hN : (N : 𝓞 F) ∉ v.asIdeal) (h : ∀ x ∈ L, (N : E) • x ∈ L') : latLoc F L v ≤ latLoc F L' v := by
  intro y hy
  refine latLoc_induction (p := fun y => y ∈ latLoc F L' v) (fun a ha x hx => ?_) (zero_mem _)
    (fun _ _ => add_mem) (fun _ => neg_mem) hy
  have hN0 := natCast_ne_zero_of (K := F) hN
  have e : (fun i => a ⊗ₜ[F] x i) = fun i => (a * (N : Fv F v)⁻¹) ⊗ₜ[F] (((N : E) • x) i) := by
    funext i
    rw [Pi.smul_apply, show (N : E) • x i = (N : F) • x i by
      rw [Algebra.smul_def, Algebra.smul_def, map_natCast, map_natCast], TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', Algebra.smul_def, map_natCast]
    congr 1
    field_simp
  rw [e]
  exact tmul_mem_latLoc (mul_mem ha (inv_natCast_mem hN)) (h x hx)

theorem latAt_le {L L' : Submodule (𝓞 E) (Fin n → E)} {w : HeightOneSpectrum (𝓞 E)} {N : ℕ}
    (hN : (N : 𝓞 E) ∉ w.asIdeal) (h : ∀ x ∈ L, (N : E) • x ∈ L') : latAt w L ≤ latAt w L' := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  have hN0 := natCast_ne_zero_of (K := E) hN
  have hm : (⟨(N : w.adicCompletion E)⁻¹, inv_natCast_mem hN⟩ : Ov E w) •
      (fun i => algebraMap E (w.adicCompletion E) (((N : E) • x) i)) = fun i => algebraMap E (w.adicCompletion E) (x i) := by
    funext i
    change (N : w.adicCompletion E)⁻¹ * algebraMap E _ ((N : E) • x i) = _
    rw [smul_eq_mul, map_mul, map_natCast, inv_mul_cancel_left₀ hN0]
  change (fun i => algebraMap E (w.adicCompletion E) (x i)) ∈ latAt w L'
  rw [← hm]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h x hx, rfl⟩)

end GlobalTheory.LatAgree

namespace GlobalTheory.LatAgree

open GlobalTheory.AdelicU GlobalTheory.LFun Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem stabLoc_congr (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) {L L' : Submodule (𝓞 E) (Fin n → E)}
    {v : HeightOneSpectrum (𝓞 F)} (hs : latLoc F L v = latLoc F L' v) : stabLoc σ J L v = stabLoc σ J L' v := by
  simp only [stabLoc, hs]

theorem isParamVec_congr {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {L L' : Submodule (𝓞 E) (Fin n → E)}
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v)
    (hs : latLoc F L v = latLoc F L' v) (ha : latAt w L = latAt w L') {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GLoc σ J v) V) (x : V) (B : Multiset ℂˣ) :
    IsParamVec σ J L h ρ x B ↔ IsParamVec σ J L' h ρ x B := by
  have hst := stabLoc_congr σ J hs
  simp only [IsParamVec, IsSplitChart, IsInertChart, IsFrameAt, hst, ha]

theorem isParamFun_congr {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {L L' : Submodule (𝓞 E) (Fin n → E)}
    {S : Set (HeightOneSpectrum (𝓞 F))} (hs : ∀ v ∉ S, latLoc F L v = latLoc F L' v)
    (ha : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∉ S → latAt w L = latAt w L')
    {V : Type} [AddCommGroup V] [Module ℂ V] (f : GAd σ J → V) (c : Fam E) :
    IsParamFun σ J L S f c ↔ IsParamFun σ J L' S f c := by
  unfold IsParamFun IsParamVecOff
  refine forall₂_congr fun v hv => forall₂_congr fun w h => ?_
  exact isParamVec_congr h (hs v hv) (ha w (h ▸ hv)) _ _ _

theorem exists_under_eq (v : HeightOneSpectrum (𝓞 F)) : ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v := by
  have := v.isPrime
  obtain ⟨Q, hQ, hl⟩ := (Ideal.nonempty_primesOver v.asIdeal (S := 𝓞 E)).some
  exact ⟨⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩

theorem latLoc_latAt_eq {L L' : Submodule (𝓞 E) (Fin n → E)} {S : Set (HeightOneSpectrum (𝓞 F))} {N : ℕ}
    (h₁ : ∀ x ∈ L, (N : E) • x ∈ L') (h₂ : ∀ x ∈ L', (N : E) • x ∈ L)
    (hN : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∉ S → (N : 𝓞 E) ∉ w.asIdeal) :
    (∀ v ∉ S, latLoc F L v = latLoc F L' v) ∧
      ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∉ S → latAt w L = latAt w L' := by
  refine ⟨fun v hv => ?_, fun w hw => le_antisymm (latAt_le (hN w hw) h₁) (latAt_le (hN w hw) h₂)⟩
  obtain ⟨w, rfl⟩ := exists_under_eq (E := E) v
  have hv' : (N : 𝓞 F) ∉ (w.under (𝓞 F)).asIdeal := fun h => hN w hv (by
    rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at h
    exact h)
  exact le_antisymm (latLoc_le hv' h₁) (latLoc_le hv' h₂)

end GlobalTheory.LatAgree

namespace GlobalTheory.ChainOnto

theorem stabLoc_isParamFun_frameLat : ∀ D : D7, ForStage D fun c _ s =>
    (∀ v ∉ c.S, GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v =
      GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram (GlobalTheory.AdelicU.frameLat s.V) v) ∧
    ∀ (f : GA D s.V → ℂ) (B : GlobalTheory.LFun.Fam D.host.E),
      GlobalTheory.LFun.IsParamFun D.sp.cm.sig s.V.gram s.Λ (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) f B ↔
        GlobalTheory.LFun.IsParamFunV s.V c.S f B := by
  intro D c _ j _ s hs
  obtain ⟨N, ⟨-, -, -, h₁, h₂⟩, hN⟩ := hs.base
  have h₁' : ∀ x ∈ GlobalTheory.AdelicU.frameLat s.V, (N : D.host.E) • x ∈ s.Λ := fun x hx =>
    h₁ x (by rw [GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]; exact hx)
  have h₂' : ∀ x ∈ s.Λ, (N : D.host.E) • x ∈ GlobalTheory.AdelicU.frameLat s.V := fun x hx => by
    have := h₂ x hx
    rw [GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice] at this
    exact this
  obtain ⟨hloc, hat⟩ := GlobalTheory.LatAgree.latLoc_latAt_eq (S := (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) h₂' h₁'
    (fun w hw => hN w hw)
  exact ⟨fun v hv => GlobalTheory.LatAgree.stabLoc_congr _ _ (hloc v hv),
    fun f B => GlobalTheory.LatAgree.isParamFun_congr hloc hat f B⟩

end GlobalTheory.ChainOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageLevelSphericalOffSet
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOntoSph

variable {D : D7}

open Classical in

theorem sep_level {c : Com D} {j : ℕ} {s : PiLocalization₂ D} (hs : s.Is c j) {P : HeightOneSpectrum (𝓞 D.host.E)}
    (hP : OffS D c.S P) : ∀ PP, PP ∈ s.L.Pg ∨ PP ∈ s.L.Q → PP ≠ P ∧ ¬ Lev.IsConjPl PP P := by
  obtain ⟨hr, ξ, hL⟩ := hs.lev
  have hPg : s.L.Pg = c.Pg := by rw [hL]; rfl
  have hQ : s.L.Q = ∅ := by rw [hL]; rfl
  rintro PP (h | h)
  · rw [hPg] at h
    exact GlobalTheory.HeckeOffLevel.sep_of_offS hP (by unfold Com.S; exact Finset.mem_image.2 ⟨PP, h, rfl⟩)
  · rw [hQ] at h
    exact absurd h (Finset.notMem_empty _)

theorem exists_unif_of_F (P : HeightOneSpectrum (𝓞 D.host.E)) :
    ∃ x : 𝓞 D.host.F, ∃ y : 𝓞 D.host.E, (y : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F) ∧
      y ∈ P.asIdeal ∧ y ∉ P.asIdeal ^ 2 := by
  haveI := P.isPrime
  haveI : Algebra.IsUnramifiedAt (𝓞 D.host.F) P.asIdeal :=
    Algebra.unramified_iff_forall.1 (GlobalTheory.InertOfConj.unram D) ⟨P.asIdeal, P.isPrime⟩
  have hle : (P.asIdeal.under (𝓞 D.host.F)).map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ P.asIdeal :=
    Ideal.map_comap_le
  have h1 : Ideal.ramificationIdx' (P.asIdeal.under (𝓞 D.host.F)) P.asIdeal = 1 := by
    letI := Localization.AtPrime.algebraOfLiesOver (P.asIdeal.under (𝓞 D.host.F)) P.asIdeal
    exact (Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff P.ne_bot hle).2
      ((Algebra.isUnramifiedAt_iff_map_eq (𝓞 D.host.F) (P.asIdeal.under (𝓞 D.host.F)) P.asIdeal).1 ‹_›).2
  have h2 : ¬ (P.asIdeal.under (𝓞 D.host.F)).map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ P.asIdeal ^ 2 :=
    fun h => (Ideal.ramificationIdx'_ne_one_iff hle).2 h h1
  rw [Ideal.map_le_iff_le_comap] at h2
  obtain ⟨x, hx, hx2⟩ := SetLike.not_le_iff_exists.1 h2
  exact ⟨x, algebraMap _ _ x, rfl, Ideal.mem_comap.1 hx, fun h => hx2 (Ideal.mem_comap.2 h)⟩

theorem level_spherical_off_S : ∀ D : D7, ForStage D fun c _ s => SphOff (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S ∧
    SphOff (levS s.V s.β s.L) (fun k => conj (Lev.levChi s.V s.β s.L k)) c.S ∧
    (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, OffS D c.S P → IsPrimeIdem P e f → ∀ k ∈ Lev.levG s.V s.β s.L,
      ∃ k₁ ∈ Lev.levG s.V s.β s.L, ∃ k₂ ∈ Lev.levG s.V s.β s.L, SuppF s.V f k₁ ∧ SuppF s.V (1 - f) k₂ ∧ k = k₁ * k₂) ∧
    (∀ P : HeightOneSpectrum (𝓞 D.host.E), OffS D c.S P ↔ P.under (𝓞 D.host.F) ∉ c.S) ∧
    ∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ x : 𝓞 D.host.F, ∃ y : 𝓞 D.host.E,
      (y : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F) ∧ y ∈ P.asIdeal ∧ y ∉ P.asIdeal ^ 2 := by
  intro D c _ j _ s hs
  obtain ⟨N, hB, hNP⟩ := hs.base
  have hoff : ∀ P, OffS D c.S P ↔ P.under (𝓞 D.host.F) ∉ c.S := fun P => GlobalTheory.GoodPrimes.offS_iff _ P
  have key := fun P e f (hP : OffS D c.S P) (hi : IsPrimeIdem P e f) =>
    (GlobalTheory.LevSplit.lev_split s.V s.β s.Λ N s.L hB).2 P e f hi (hNP P ((hoff P).1 hP)) (sep_level hs hP)
  have hex := fun P => (GlobalTheory.IdemSupport.supported_group_and_prime_idempotents s.V).2.1 P
  refine ⟨fun P hP => ?_, fun P hP => ?_, fun P e f hP hi => (key P e f hP hi).2.2, hoff, exists_unif_of_F⟩
  · obtain ⟨e, f, hi⟩ := hex P
    obtain ⟨h1, h2, -⟩ := key P e f hP hi
    exact ⟨e, f, hi, h1, h2⟩
  · obtain ⟨e, f, hi⟩ := hex P
    obtain ⟨h1, h2, -⟩ := key P e f hP hi
    refine ⟨e, f, hi, h1, fun g hg hf => ?_⟩
    show conj (Lev.levChi s.V s.β s.L g) = 1
    rw [h2 g hg hf, map_one]

end GlobalTheory.ChainOntoSph

end
end

