import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0610
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0623
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1667
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1699
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0521
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0547
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0617
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0409
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0609
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0256
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0471
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRight
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0624
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelCharacterMatch
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0356
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0376
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationIntegralAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0603
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryArchimedeanLinePairOperatorsOneParameter
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

namespace GlobalTheory.LineGroupPair

theorem archOp_oneParam_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ γ ∈ Lines σ W, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (T t f)) →
        (∀ (s t : ℝ) (f : SInf F (Fin n × Fin d)), T (s + t) f = T s (T t f)) ∧ ∀ f : SInf F (Fin n × Fin d), T 0 f = f := by
  intro F E _ _ _ _ _ σ _ n d X W M ψ χX χW om _ _ _ _ _ _ _ _ _ _ γ _ T hA
  obtain ⟨r₀, hR, hinj⟩ := GlobalTheory.ArchUniq.exists_admissible_finite_factor (F := F) (Fin n × Fin d)
  refine ⟨fun s t f => hinj _ _ ?_, fun f => hinj _ _ ?_⟩
  · rw [← hA (s + t) f r₀ (hR f), ← hA s (T t f) r₀ (hR _), ← hA t f r₀ (hR f), ofAdd_add, map_mul,
      show ((1 : UA σ X.J), γ (Multiplicative.ofAdd s) * γ (Multiplicative.ofAdd t)) =
        ((1 : UA σ X.J), γ (Multiplicative.ofAdd s)) * (1, γ (Multiplicative.ofAdd t)) by
          simp [Prod.mk_mul_mk], map_mul, Module.End.mul_apply]
  · rw [← hA 0 f r₀ (hR f), ofAdd_zero, map_one, Prod.mk_one_one, map_one, Module.End.one_apply]

end GlobalTheory.LineGroupPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryInBasisIntegralAtConjugatePlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryInBasis_integral_at_conjugatePlace : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsFrame β Λ → Formalism.L2.Herm.dualL D.sp.cm V Λ = Λ → ∀ x ∈ UA D.sp.cm V.gram, ∀ w : Pl D.host.E, inBasis rfl β w x ∈ GlobalTheory.SplitWeil.KO (Kw w) (Fin V.rank) → inBasis rfl β (Formalism.DivisionValues.conjPl w) x ∈ GlobalTheory.SplitWeil.KO (Kw (Formalism.DivisionValues.conjPl w)) (Fin V.rank) := by
  first | exact @GlobalTheory.ConjPlaceUnitary.inBasis_conjPl_mem_KO | exact GlobalTheory.ConjPlaceUnitary.inBasis_conjPl_mem_KO | (intros; apply GlobalTheory.ConjPlaceUnitary.inBasis_conjPl_mem_KO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumVectorMovedPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

namespace GlobalTheory.MovedDict

theorem movedVac_isVacO : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    IsVacO ch.W.ψ ch.W.θ _ _ (ch.G.cartS ch.W.cart p) (ch.G.onT ch.W.cart p) (inV (frS ch.S.N p) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y)) (inV (frT ch.S.N p) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y))
      (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p)) := by
  intro hPr hInp D Γ _ _ Pl0 T A Ks _ _ _ R ch hIs p hp x y
  have hn := DefPair.nodes hp
  have hom := ch.W.om_is p (by cases p <;> simp only [DefPair, DefNode] at hp hn <;> simp only [Pair.InRange, Node.InRange] <;> omega)
  have negMem : ∀ (V : HSp D) {g : Formalism.L2.Theta.GA D V}, g ∈ GfC V → negGA V g ∈ GfC (negSp V) := by
    intro V g hg
    have e : matHom (negSp V) (negGA V g) = matHom V g := Units.ext (mt_negGA V g)
    simp only [GfC, MonoidHom.mem_ker, infHom, MonoidHom.comp_apply] at hg ⊢
    rw [e]
    exact hg
  set gh := ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small))
    ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big)) with hgh
  have mem : gh.1 ∈ GfC (ch.G.pS p) ∧ gh.2 ∈ GfC (ch.G.pT p) := by
    rw [hgh]
    cases p with
    | chi i j => exact ⟨negMem _ (y * ch.S.N.u _).2, (x * ch.S.N.u _).2⟩
    | mu t i j => exact ⟨(x * ch.S.N.u _).2, (y * ch.S.N.u _).2⟩
    | core i => exact ⟨negMem _ (y * ch.S.N.u _).2, (x * ch.S.N.u _).2⟩
    | top t j => exact ⟨(x * ch.S.N.u _).2, (y * ch.S.N.u _).2⟩
  obtain ⟨hstd, hv⟩ := ch.S.Z.vac_is p hp
  have hact := (GlobalTheory.T.lattice_orbit_vectors_moved_pair hPr hInp ch hIs p hp x y).2
  have hth' := hom.om_pres gh _ hv.theta
  have hgh' : gh = (gh.1, gh.2) := rfl
  refine ⟨hstd, { inf := hv.inf, theta := hth', lat := ⟨fun u' hu' => ?_, fun e he u' hu' hhalf => ?_⟩, fock := fun τ z => ?_, norm := ⟨hv.norm.1, fun q hq => ?_⟩ }⟩
  · obtain ⟨u, hu, rfl⟩ := hact u' hu'
    have h2 : actO _ _ gh.1 gh.2 u + actO _ _ gh.1 gh.2 u = actO _ _ gh.1 gh.2 (u + u) := by
      simp only [actO, Matrix.mul_add, Matrix.add_mul]
    have h3 := hv.lat.1 u hu
    rw [two_nsmul] at h3 ⊢
    rw [h2, hgh', ← hom.om_heis gh.1 gh.2 _ _ hv.theta, h3]
  · obtain ⟨u, hu, rfl⟩ := hact u' hu'
    rw [hgh', ← hom.om_heis gh.1 gh.2 u _ hv.theta, hv.lat.2 e he u hu (GlobalTheory.MovedVac.halfBack D _ _ gh.1 gh.2 e u hhalf)]
  · have hθ := ch.W.θ_is
    have e : ∀ z', Formalism.IndefR.Datum.dRho (heisO ch.W.ψ _ _) ch.W.θ τ z' (ch.W.om p gh (ch.S.Z.vac p)) =
        ch.W.om p gh (Formalism.IndefR.Datum.dRho (heisO ch.W.ψ _ _) ch.W.θ τ z' (ch.S.Z.vac p)) := by
      intro z'
      rw [hgh', GlobalTheory.OrientedHeis.om_dRho hom hθ gh.1 gh.2 τ z' hv.theta, GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC ch.W.θ _ mem.2,
        GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC ch.W.θ _ (inv_mem mem.1), Matrix.one_mul, Matrix.mul_one]
    have h0 := hv.fock τ z
    unfold annih at h0 ⊢
    rw [e, e, ← map_smul, ← map_add, h0, map_zero]
  · show nrm2 q.1 q.2 (ch.W.om p gh (ch.S.Z.vac p)) = 1
    have hU := hom.om_unit q.1 q.2 hq.1 hq.2.1 gh _ hv.theta
    haveI : OpensMeasurableSpace (WO (ch.G.pS p) (ch.G.pT p)) := ⟨le_rfl⟩
    have key : ∀ F : WO (ch.G.pS p) (ch.G.pT p) → ℂ, Continuous F → nrm2 q.1 q.2 F = (∫⁻ w in q.2, ‖F w‖ₑ ^ 2 ∂q.1).toReal := by
      intro F hF
      unfold nrm2
      have hc : Continuous fun w => ‖F w‖ ^ 2 := by fun_prop
      rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae (f := fun w => ‖F w‖ ^ 2)
        (Filter.Eventually.of_forall fun w => sq_nonneg ‖F w‖) hc.aestronglyMeasurable]
      congr 1
      refine MeasureTheory.lintegral_congr fun w => ?_
      rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [key _ hth'.cont, hU, ← key _ hv.theta.cont]
    exact hv.norm.2 q hq

end GlobalTheory.MovedDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilCompactRealPointFockVectorSubstitution
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RowReal

section FockAll

open Classical

variable {D : D7}

def fockSubOn {m n : ℕ} (s : Finset D.what₂.Tau) (pS pT : D.what₂.Tau → ℕ) (κS : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ)
    (κT : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) : MvPolynomial (FVar D m n) ℂ →ₐ[ℂ] MvPolynomial (FVar D m n) ℂ :=
  MvPolynomial.aeval fun y : FVar D m n =>
    if y.1 ∈ s then
      ∑ i, ∑ j, MvPolynomial.C (if (y.2.1.val < pT y.1 ↔ y.2.2.val < pS y.1) then κT y.1 i y.2.1 * (κS y.1)⁻¹ y.2.2 j
        else (starRingEnd ℂ) (κT y.1 i y.2.1 * (κS y.1)⁻¹ y.2.2 j)) * MvPolynomial.X (y.1, i, j)
    else MvPolynomial.X y

variable {m n : ℕ} (pS pT : D.what₂.Tau → ℕ) (κS : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ)
    (κT : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ)

theorem fockSubOn_empty (Q : MvPolynomial (FVar D m n) ℂ) : fockSubOn ∅ pS pT κS κT Q = Q := by
  have e : fockSubOn (∅ : Finset D.what₂.Tau) pS pT κS κT = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro y
    simp only [fockSubOn, MvPolynomial.aeval_X, Finset.notMem_empty, if_false, AlgHom.id_apply]
  rw [e, AlgHom.id_apply]

theorem fockSubOn_univ : fockSubOn Finset.univ pS pT κS κT = fockSubAll pS pT κS κT := by
  apply MvPolynomial.algHom_ext
  intro y
  simp only [fockSubOn, fockSubAll, MvPolynomial.aeval_X, Finset.mem_univ, if_true]

theorem fockSub_fockSubOn {τ : D.what₂.Tau} {s : Finset D.what₂.Tau} (hτ : τ ∉ s) (Q : MvPolynomial (FVar D m n) ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockSub τ (pS τ) (pT τ) (κS τ) (κT τ) (fockSubOn s pS pT κS κT Q) =
      fockSubOn (insert τ s) pS pT κS κT Q := by
  suffices e : (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockSub τ (pS τ) (pT τ) (κS τ) (κT τ)).comp (fockSubOn s pS pT κS κT) =
      fockSubOn (insert τ s) pS pT κS κT from DFunLike.congr_fun e Q
  apply MvPolynomial.algHom_ext
  intro y
  rw [AlgHom.comp_apply]
  by_cases hy : y.1 ∈ s
  · have hne : y.1 ≠ τ := fun h => hτ (h ▸ hy)
    simp only [fockSubOn, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockSub, MvPolynomial.aeval_X, Finset.mem_insert, hy, if_true, or_true,
      map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, hne, if_false]
  · by_cases h2 : y.1 = τ
    · obtain ⟨ρ, a, b⟩ := y
      simp only at h2 hy
      subst h2
      simp only [fockSubOn, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockSub, MvPolynomial.aeval_X, Finset.mem_insert, hy, if_false, true_or,
        if_true]
    · simp only [fockSubOn, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockSub, MvPolynomial.aeval_X, Finset.mem_insert, hy, h2, if_false,
        or_false]

theorem om_pureTensorO_compact_all (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (χS χT : (AE D)ˣ →* Circle) (om : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.OmT S T) (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ)
    (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (pS pT : D.what₂.Tau → ℕ) (hpS : ∀ ρ, pS ρ ≤ S.rank) (hpT : ∀ ρ, pT ρ ≤ T.rank)
    (hS : ∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) (hT : ∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ))
    (hBS : ∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) (hBT : ∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ))
    (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f) (hvac : ∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) f)
    (κS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (κT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hκS : ∀ ρ, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsKMat (pS ρ) (κS ρ)) (hκT : ∀ ρ, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsKMat (pT ρ) (κT ρ))
    (x : GA D S) (y : GA D T) (hx : x ∈ GinfC S) (hy : y ∈ GinfC T)
    (hxc : ∀ ρ, compAt θ ρ (mt S x) = BS ρ * κS ρ * (BS ρ)⁻¹)
    (hyc : ∀ ρ, compAt θ ρ (mt T y) = BT ρ * κT ρ * (BT ρ)⁻¹)
    (c : ℂ) (hc : om (x, y) f = c • f) (Q : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    om (x, y) (pureTensorO ψ θ S T sS sT BS BT f Q) =
      c • pureTensorO ψ θ S T sS sT BS BT f (fockSubAll pS pT κS κT Q) := by
  have hUS : ∀ ρ, compAt θ ρ (mt S x) ∈ Formalism.QuantumDeterminants.UH (gramAt D S ρ) := fun ρ =>
    GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ S x ρ
  have hUT : ∀ ρ, compAt θ ρ (mt T y) ∈ Formalism.QuantumDeterminants.UH (gramAt D T ρ) := fun ρ =>
    GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ T y ρ
  have hAS : ∀ τ, IsAtTau θ S τ (BS τ * κS τ * (BS τ)⁻¹) (atTau θ S τ (compAt θ τ (mt S x))) := fun τ => by
    rw [← hxc τ]; exact GlobalTheory.PointAtPlaceHom.atTau_spec hθ S τ (hUS τ)
  have hAT : ∀ τ, IsAtTau θ T τ (BT τ * κT τ * (BT τ)⁻¹) (atTau θ T τ (compAt θ τ (mt T y))) := fun τ => by
    rw [← hyc τ]; exact GlobalTheory.PointAtPlaceHom.atTau_spec hθ T τ (hUT τ)
  have hev : ∀ τ, ∃ e : ℂ, om (atTau θ S τ (compAt θ τ (mt S x)), atTau θ T τ (compAt θ τ (mt T y))) f = e • f :=
    fun τ => by
      obtain ⟨mS, mT, h⟩ := GlobalTheory.VacCharAtPlace.vacuum_char_at_place D ψ θ S T χS χT om hom hθ τ
      exact ⟨_, h sS BS sT BT pS pT hpS hpT hS hT hBS hBT f hf hvac (κS τ) (κT τ) (hκS τ) (hκT τ) _ _ (hAS τ) (hAT τ)⟩
  choose e he using hev
  let MSs : Finset D.what₂.Tau → D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ :=
    fun s ρ => if ρ ∈ s then compAt θ ρ (mt S x) else 1
  let MTs : Finset D.what₂.Tau → D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ :=
    fun s ρ => if ρ ∈ s then compAt θ ρ (mt T y) else 1
  have hUSs : ∀ s ρ, MSs s ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D S ρ) := fun s ρ => by
    by_cases h : ρ ∈ s
    · simp only [MSs, if_pos h]; exact hUS ρ
    · simp only [MSs, if_neg h]; exact GlobalTheory.PointAtPlaceHom.one_mem_UH _
  have hUTs : ∀ s ρ, MTs s ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D T ρ) := fun s ρ => by
    by_cases h : ρ ∈ s
    · simp only [MTs, if_pos h]; exact hUT ρ
    · simp only [MTs, if_neg h]; exact GlobalTheory.PointAtPlaceHom.one_mem_UH _
  have key : ∀ s : Finset D.what₂.Tau, ∀ Q, om (realAll θ S (MSs s), realAll θ T (MTs s)) (pureTensorO ψ θ S T sS sT BS BT f Q) =
      (∏ τ ∈ s, e τ) • pureTensorO ψ θ S T sS sT BS BT f (fockSubOn s pS pT κS κT Q) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro Q
      have h1 : MSs ∅ = 1 := by funext ρ; simp [MSs]
      have h2 : MTs ∅ = 1 := by funext ρ; simp [MTs]
      rw [h1, h2, realAll_one hθ, realAll_one hθ, Prod.mk_one_one, map_one, Module.End.one_apply, Finset.prod_empty,
        one_smul, fockSubOn_empty]
    · intro τ s hτ ih Q
      have eS : realAll θ S (MSs (insert τ s)) = atTau θ S τ (compAt θ τ (mt S x)) * realAll θ S (MSs s) := by
        rw [realAll_eq_atTau_mul hθ (hUSs (insert τ s)) τ]
        congr 2
        · simp [MSs]
        · funext ρ
          by_cases h : ρ = τ
          · subst h; simp [MSs, hτ]
          · simp [MSs, Function.update_of_ne h, h]
      have eT : realAll θ T (MTs (insert τ s)) = atTau θ T τ (compAt θ τ (mt T y)) * realAll θ T (MTs s) := by
        rw [realAll_eq_atTau_mul hθ (hUTs (insert τ s)) τ]
        congr 2
        · simp [MTs]
        · funext ρ
          by_cases h : ρ = τ
          · subst h; simp [MTs, hτ]
          · simp [MTs, Function.update_of_ne h, h]
      rw [eS, eT, ← Prod.mk_mul_mk, map_mul, Module.End.mul_apply, ih Q, map_smul,
        GlobalTheory.FockCompact.om_pureTensorO_compact D ψ θ S T χS χT om hom hθ sS BS sT BT pS pT hpS hpT hS hT hBS hBT f hf τ
          (κS τ) (κT τ) (hκS τ) (hκT τ) _ _ (hAS τ) (hAT τ) (e τ) (he τ),
        smul_smul, fockSub_fockSubOn pS pT κS κT hτ, Finset.prod_insert hτ, mul_comm (e τ)]
  have hxr : realAll θ S (MSs Finset.univ) = x :=
    realAll_eq hθ (hUSs _) ⟨hx, fun ρ => by simp only [MSs, Finset.mem_univ, if_true]; rfl⟩
  have hyr : realAll θ T (MTs Finset.univ) = y :=
    realAll_eq hθ (hUTs _) ⟨hy, fun ρ => by simp only [MTs, Finset.mem_univ, if_true]; rfl⟩
  have hall := key Finset.univ
  rw [hxr, hyr, fockSubOn_univ] at hall
  have hE : om (x, y) f = (∏ τ, e τ) • f := by
    have h1 := hall 1
    rw [map_one (fockSubAll pS pT κS κT)] at h1
    simpa only [GlobalTheory.FiniteFock.pureTensorO_one] using h1
  rw [hall Q]
  by_cases hf0 : f = 0
  · subst hf0
    have z : ∀ P, pureTensorO ψ θ S T sS sT BS BT 0 P = 0 := fun P => by
      have := GlobalTheory.FiniteFock.pureTensorO_smul ψ θ S T sS sT BS BT 0 0 P
      rwa [zero_smul, zero_smul] at this
    simp only [z, smul_zero]
  · have hce : c = ∏ τ, e τ := smul_left_injective ℂ hf0 (hc.symm.trans hE)
    rw [hce]

end FockAll

theorem om_fock_compact_all : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (p : Pair T), p.InRange D.R.m →
    ∀ (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ (G.pS p).rank) → (∀ ρ, pT ρ ≤ (G.pT p).rank) →
    (∀ ρ, IsCartanInv (gramAt D (G.pS p) ρ) (G.cartS W.cart p ρ)) →
    (∀ ρ, IsCartanInv (gramAt D (G.pT p) ρ) (G.onT W.cart p ρ)) →
    (∀ ρ, IsONBasis (gramAt D (G.pS p) ρ) (G.cartS W.cart p ρ) (G.onS W.onb p ρ) (pS ρ)) →
    (∀ ρ, IsONBasis (gramAt D (G.pT p) ρ) (G.onT W.cart p ρ) (G.onT W.onb p ρ) (pT ρ)) →
    ∀ f : WO (G.pS p) (G.pT p) → ℂ, IsThetaFunO W.ψ _ _ f →
    (∀ ρ, IsFockVacAt (heisO W.ψ _ _) W.θ ρ (cplxO (G.cartS W.cart p ρ) (G.onT W.cart p ρ)) f) →
    ∀ (κS : D.what₂.Tau → Matrix (Fin (G.pS p).rank) (Fin (G.pS p).rank) ℂ)
      (κT : D.what₂.Tau → Matrix (Fin (G.pT p).rank) (Fin (G.pT p).rank) ℂ),
    (∀ ρ, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsKMat (pS ρ) (κS ρ)) → (∀ ρ, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsKMat (pT ρ) (κT ρ)) →
    ∀ (x : GA D (G.pS p)) (y : GA D (G.pT p)), x ∈ GinfC (G.pS p) → y ∈ GinfC (G.pT p) →
    (∀ ρ, compAt W.θ ρ (mt _ x) = G.onS W.onb p ρ * κS ρ * (G.onS W.onb p ρ)⁻¹) →
    (∀ ρ, compAt W.θ ρ (mt _ y) = G.onT W.onb p ρ * κT ρ * (G.onT W.onb p ρ)⁻¹) →
    ∀ c : ℂ, W.om p (x, y) f = c • f → ∀ Q : PolF D (G.pT p).rank (G.pS p).rank,
    W.om p (x, y) (W.fock p f Q) = c • W.fock p f (GlobalTheory.RowReal.fockSubAll pS pT κS κT Q) := by
  intro D T L sc G W p hp pS pT hpS hpT hS hT hBS hBT f hf hvac κS κT hκS hκT x y hx hy hxc hyc c hc Q
  exact om_pureTensorO_compact_all D W.ψ W.θ (G.pS p) (G.pT p) (G.chrS p) (G.chrT p) (W.om p) (W.om_is p hp) W.θ_is
    (G.cartS W.cart p) (G.onS W.onb p) (G.onT W.cart p) (G.onT W.onb p) pS pT hpS hpT hS hT hBS hBT f hf hvac κS κT hκS hκT
    x y hx hy hxc hyc c hc Q

end GlobalTheory.RowReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineSchrodingerModelStatement
section
open scoped Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_line_schrodinger_model : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (χX χW : Chr F E) (om : Rep σ X W), IsCMExt F E σ → IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ Lines σ W, ∃ (l : Type) (_ : Fintype l) (_ : DecidableEq l)
      (Φ : SInf F (Fin n × Fin d) ≃L[ℂ] GlobalTheory.RealWeil.Sch l) (g : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ)
      (T : ℝ → GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l),
      Continuous g ∧ g 0 = 1 ∧ (∀ s t, g (s + t) = g s * g t) ∧ (∀ t, g t ∈ Matrix.symplecticGroup l ℝ) ∧
      T 0 = LinearMap.id ∧ (∀ s t, T (s + t) = T s ∘ₗ T t) ∧
      (∀ (t : ℝ) (w : l ⊕ l → ℝ) (h h₁ : GlobalTheory.RealWeil.Sch l), ⇑h₁ = GlobalTheory.RealWeil.rhoFun w ⇑h →
        ⇑(T t h₁) = GlobalTheory.RealWeil.rhoFun (g t *ᵥ w) ⇑(T t h)) ∧
      (∀ (t : ℝ) (h : GlobalTheory.RealWeil.Sch l), ∫⁻ x, ‖T t h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) ∧
      (∀ (h : GlobalTheory.RealWeil.Sch l) (x : EuclideanSpace ℝ l), Continuous fun t => T t h x) ∧
      ∀ (t : ℝ) (f : SInf F (Fin n × Fin d)),
        Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑(Φ.symm (T t (Φ f))) := by
  first | exact @GlobalTheory.ArchLine.realLine | exact GlobalTheory.ArchLine.realLine | (intros; apply GlobalTheory.ArchLine.realLine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelCharacterMatchStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_model_character_match : GlobalTheory.FunPr.Hypotheses₂ →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ → GlobalTheory.RealDict.IsPairReading ψ ε A B ω Xs Ws Mo ψ' om τ →
    ∀ Φ : PolF D X.rank M.rank →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
    Function.Injective Φ → LinearMap.range Φ = Mo.Pol ψ' τ → GlobalTheory.RealDict.IsFockMap ψ θ ε A B Mo Φ →
      ∀ N : Submodule ℂ (PolF D X.rank M.rank),
        GlobalTheory.RealQuot.IsStab (fun i : GlobalTheory.RealQuot.LieIx X => GlobalTheory.RealQuot.actT ε A B eS i.1.1 i.1.2) N →
        ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Ws τ, ∀ f ∈ N.map Φ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (om (1, k)) f f₁ → f₁ ∈ N.map Φ := by
  first | exact @GlobalTheory.CompactStable.kInf_stable | exact GlobalTheory.CompactStable.kInf_stable | (intros; apply GlobalTheory.CompactStable.kInf_stable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationIntegralActionStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representation_integral_action : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    M.IsWeil ψ χX χW om → ∀ (μ : Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F)), μ.IsAddHaarMeasure →
    ∀ (h : UA σ W.J) (f f₁ : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, h)) ⇑f ⇑f₁ →
      ∫ x, ‖f₁ x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  first | exact @GlobalTheory.ArchIsom.acts_norm_sq_eq | exact GlobalTheory.ArchIsom.acts_norm_sq_eq | (intros; apply GlobalTheory.ArchIsom.acts_norm_sq_eq <;> assumption)
end

