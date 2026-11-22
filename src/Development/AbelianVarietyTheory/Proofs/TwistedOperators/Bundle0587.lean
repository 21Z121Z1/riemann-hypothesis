import Mathlib
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0841
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0558
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurFiniteHeisenbergFockVacuumThetaFunctions
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelAlgebraicExpansion
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0568
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0521
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0547
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0010
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0379
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1873
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0556
import GroundTheory.GlobalFields.Adele.Compact
import GroundTheory.GlobalFields.Adele.Approximation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelArchimedeanExponent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0356
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0376

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSelfDualLattices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.AlgPair

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem alg_star {a : ℂ} (ha : a ∈ algebraicClosure ℚ ℂ) : star a ∈ algebraicClosure ℚ ℂ := by
  rw [mem_algebraicClosure_iff] at ha ⊢
  exact ha.algHom ((Complex.conjAe.restrictScalars ℚ).toAlgHom)

theorem fin_neg {x : WO S T} (hx : x.map (infPart D) = 0) : (-x).map (infPart D) = 0 := by
  ext i j
  have h := congrFun (congrFun hx i) j
  simp only [Matrix.map_apply, Matrix.neg_apply, Matrix.zero_apply] at h ⊢
  rw [RingHom.map_neg, h, neg_zero]

theorem fin_add {x y : WO S T} (hx : x.map (infPart D) = 0) (hy : y.map (infPart D) = 0) :
    (x + y).map (infPart D) = 0 := by
  ext i j
  have h := congrFun (congrFun hx i) j
  have h' := congrFun (congrFun hy i) j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.zero_apply] at h h' ⊢
  rw [RingHom.map_add, h, h', add_zero]

variable {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}

theorem thetaInner_zero_left (G : WO S T → ℂ) : GlobalTheory.RawLift.thetaIP μ 𝓕 0 G = 0 := by
  have h := GlobalTheory.RawLift.thetaInner_smul_left μ 𝓕 0 0 G
  simpa using h

theorem thetaInner_zero_right (G : WO S T → ℂ) : GlobalTheory.RawLift.thetaIP μ 𝓕 G 0 = 0 := by
  have h := GlobalTheory.RawLift.thetaInner_smul_right μ 𝓕 0 G 0
  simpa using h

theorem sum_left (hψ : IsStdChar D ψ (-1)) (hcv : IsCovolOne (ratL T S) μ 𝓕) {G : WO S T → ℂ}
    (hG : IsThetaFunO ψ S T G) : ∀ {n : ℕ} (c : Fin n → ℂ) (g : Fin n → WO S T → ℂ), (∀ p, IsThetaFunO ψ S T (g p)) →
    IsThetaFunO ψ S T (∑ p, c p • g p) ∧
      GlobalTheory.RawLift.thetaIP μ 𝓕 (∑ p, c p • g p) G = ∑ p, star (c p) * GlobalTheory.RawLift.thetaIP μ 𝓕 (g p) G
  | 0, c, g, _ => by
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact ⟨GlobalTheory.WeilVacMove.isTheta_zero, thetaInner_zero_left G⟩
  | n + 1, c, g, hg => by
    obtain ⟨ht, he⟩ := sum_left hψ hcv hG (fun p => c p.succ) (fun p => g p.succ) fun p => hg _
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    exact ⟨GlobalTheory.WeilVacMove.isTheta_add (GlobalTheory.WeilVacMove.isTheta_smul _ (hg 0)) ht,
      by rw [GlobalTheory.VacSchurFin.thetaInner_left hψ hcv _ (hg 0) ht hG, he]⟩

theorem sum_right (hψ : IsStdChar D ψ (-1)) (hcv : IsCovolOne (ratL T S) μ 𝓕) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : ∀ {n : ℕ} (c : Fin n → ℂ) (g : Fin n → WO S T → ℂ), (∀ p, IsThetaFunO ψ S T (g p)) →
    IsThetaFunO ψ S T (∑ p, c p • g p) ∧
      GlobalTheory.RawLift.thetaIP μ 𝓕 f (∑ p, c p • g p) = ∑ p, c p * GlobalTheory.RawLift.thetaIP μ 𝓕 f (g p)
  | 0, c, g, _ => by
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact ⟨GlobalTheory.WeilVacMove.isTheta_zero, thetaInner_zero_right f⟩
  | n + 1, c, g, hg => by
    obtain ⟨ht, he⟩ := sum_right hψ hcv hf (fun p => c p.succ) (fun p => g p.succ) fun p => hg _
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    exact ⟨GlobalTheory.WeilVacMove.isTheta_add (GlobalTheory.WeilVacMove.isTheta_smul _ (hg 0)) ht,
      by rw [GlobalTheory.VacSchurFin.thetaInner_right hψ hcv _ hf (hg 0) ht, he]⟩

variable {θ : InfFam D} {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
  {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {v : WO S T → ℂ}

theorem vac_translate (hv : IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v)
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (hcv : IsCovolOne (ratL T S) μ 𝓕) {u : WO S T}
    (hu : u.map (infPart D) = 0) : GlobalTheory.RawLift.thetaIP μ 𝓕 v (heisO ψ S T u v) ∈ algebraicClosure ℚ ℂ := by
  have hψ : IsStdChar D ψ (-1) := hv.1
  have hvt : IsThetaFunO ψ S T v := hv.2.theta
  have hlat := hv.2.lat
  have laws := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  obtain ⟨h1, -, h3⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT
  by_cases hmem : u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
  · obtain ⟨ε, hε, hεv⟩ := h3 v hlat u hmem
    have hself : GlobalTheory.RawLift.thetaIP μ 𝓕 v v = 1 := by
      rw [GlobalTheory.RawLift.thetaInner_self]
      have hn := hv.2.norm.2 (μ, 𝓕) hcv
      simp only [nrm2] at hn
      rw [hn, Complex.ofReal_one]
    rw [hεv v hlat, GlobalTheory.RawLift.thetaInner_smul_right, hself, mul_one]
    rcases hε with rfl | rfl
    · exact one_mem _
    · exact neg_mem (one_mem _)
  · have hne : ∃ u' ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
        ψ (symplO S T u u') ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      exact hmem ((h1 u hu).2 hcon)
    obtain ⟨u', hu', hψu⟩ := hne
    obtain ⟨ε, hε, hεv⟩ := h3 v hlat u' hu'
    have hεv' := hεv v hlat
    have comm := GlobalTheory.SplitScalar.heisO_comm ψ S T u u' v
    rw [hεv', GlobalTheory.VacSchurFin.heisO_smul'] at comm
    have inv := GlobalTheory.VacSchurFin.thetaInner_heisenberg hψ hcv hvt (laws.1 u v hvt) u'
    rw [hεv'] at inv
    have hεε : star ε * ε = 1 := by
      rcases hε with h | h <;> rw [h] <;> simp only [star_one, star_neg, one_mul, neg_mul_neg]
    have hfix : ψ (symplO S T u u') * GlobalTheory.RawLift.thetaIP μ 𝓕 v (heisO ψ S T u v) =
        GlobalTheory.RawLift.thetaIP μ 𝓕 v (heisO ψ S T u v) := by
      conv_lhs => rw [← inv, ← GlobalTheory.RawLift.thetaInner_smul_right, ← comm, GlobalTheory.RawLift.thetaInner_smul_left,
        GlobalTheory.RawLift.thetaInner_smul_right, ← mul_assoc, hεε, one_mul]
    have h0 : (ψ (symplO S T u u') - 1) * GlobalTheory.RawLift.thetaIP μ 𝓕 v (heisO ψ S T u v) = 0 := by
      rw [sub_mul, hfix, one_mul, sub_self]
    rw [(mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hψu)]
    exact zero_mem _

theorem translates (hv : IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v)
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (hcv : IsCovolOne (ratL T S) μ 𝓕) {x y : WO S T}
    (hx : x.map (infPart D) = 0) (hy : y.map (infPart D) = 0) :
    GlobalTheory.RawLift.thetaIP μ 𝓕 (heisO ψ S T x v) (heisO ψ S T y v) ∈ algebraicClosure ℚ ℂ := by
  have hψ : IsStdChar D ψ (-1) := hv.1
  have hvt : IsThetaFunO ψ S T v := hv.2.theta
  have laws := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  have e1 : heisO ψ S T (-x) (heisO ψ S T x v) = ψ (symplOH S T (-x) x) • v := by
    rw [GlobalTheory.SplitScalar.heisO_heisO, neg_add_cancel, GlobalTheory.SplitScalar.heisO_zero]
  have e2 : heisO ψ S T (-x) (heisO ψ S T y v) = ψ (symplOH S T (-x) y) • heisO ψ S T (-x + y) v :=
    GlobalTheory.SplitScalar.heisO_heisO ψ S T (-x) y v
  rw [← GlobalTheory.VacSchurFin.thetaInner_heisenberg hψ hcv (laws.1 x v hvt) (laws.1 y v hvt) (-x), e1, e2,
    GlobalTheory.RawLift.thetaInner_smul_left, GlobalTheory.RawLift.thetaInner_smul_right]
  refine mul_mem (alg_star (GlobalTheory.BotFourier.psiH_mem hψ hS hT (fin_neg hx) hx))
    (mul_mem (GlobalTheory.BotFourier.psiH_mem hψ hS hT (fin_neg hx) hy) ?_)
  exact vac_translate hv hS hT hcv (fin_add (fin_neg hx) hy)

theorem thetaIP_algComb : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {v : WO S T → ℂ}, IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v → IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ F F' : WO S T → ℂ,
    GlobalTheory.MovedAlg.IsAlgComb ψ S T v F → GlobalTheory.MovedAlg.IsAlgComb ψ S T v F' → IsAlgebraic ℚ (GlobalTheory.RawLift.thetaIP μ 𝓕 F F') := by
  intro D ψ θ S T sS sT ΛS ΛT v hv hS hT μ 𝓕 hcv F F' hF hF'
  obtain ⟨n, c, w, hc, hw, rfl⟩ := hF
  obtain ⟨m, c', w', hc', hw', rfl⟩ := hF'
  have hψ : IsStdChar D ψ (-1) := hv.1
  have hvt : IsThetaFunO ψ S T v := hv.2.theta
  have laws := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  have hth : ∀ x, IsThetaFunO ψ S T (heisO ψ S T x v) := fun x => laws.1 x v hvt
  have hR := (sum_right hψ hcv (hth 0) c' (fun q => heisO ψ S T (w' q) v) fun q => hth _).1
  rw [(sum_left hψ hcv hR c (fun p => heisO ψ S T (w p) v) fun p => hth _).2, ← mem_algebraicClosure_iff]
  refine Subalgebra.sum_mem _ fun p _ => mul_mem (alg_star (mem_algebraicClosure_iff.2 (hc p))) ?_
  rw [(sum_right hψ hcv (hth (w p)) c' (fun q => heisO ψ S T (w' q) v) fun q => hth _).2]
  exact Subalgebra.sum_mem _ fun q _ =>
    mul_mem (mem_algebraicClosure_iff.2 (hc' q)) (translates hv hS hT hcv (hw p) (hw' q))

end GlobalTheory.AlgPair

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionOMemLatticeOOfIntegralCombinationsStatement
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
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilActionO_mem_latticeO_of_integralCombinations : ∀ {D : D7} (S T : HSp D) (g : Formalism.L2.Theta.GA D S) (h : Formalism.L2.Theta.GA D T)
    (AS BS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (AT BT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    (∀ s ∈ AS, ∃ (m : ℕ) (β : Fin m → Formalism.L2.Theta.AE D) (b : Fin m → Fin S.rank → D.host.E),
      (∀ p, finPart D (β p) ∈ intAE D) ∧ (∀ p, b p ∈ BS) ∧
      ∀ i, finPart D ((mt S g *ᵥ fun k => incA D (s k)) i) =
        finPart D (∑ p, β p * incA D (b p i))) →
    (∀ t ∈ AT, ∃ (m : ℕ) (β : Fin m → Formalism.L2.Theta.AE D) (b : Fin m → Fin T.rank → D.host.E),
      (∀ p, finPart D (β p) ∈ intAE D) ∧ (∀ p, b p ∈ BT) ∧
      ∀ i, finPart D ((mt T h *ᵥ fun k => incA D (t k)) i) =
        finPart D (∑ p, β p * incA D (b p i))) →
    ∀ w ∈ latO S T (AS : Set (Fin S.rank → D.host.E)) (AT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      actO S T g h w ∈ latO S T (BS : Set (Fin S.rank → D.host.E)) (BT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  first | exact @GlobalTheory.LatMoveGen.actO_mem_latO | exact GlobalTheory.LatMoveGen.actO_mem_latO | (intros; apply GlobalTheory.LatMoveGen.actO_mem_latO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionUnitaryCompact
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

noncomputable section
namespace GlobalTheory.ArchLocality

theorem evI_add {F : Type} [Field F] [NumberField F] (a b : AF F) : evI F (a + b) = evI F a + evI F b :=
  map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_mul {F : Type} [Field F] [NumberField F] (a b : AF F) : evI F (a * b) = evI F a * evI F b :=
  map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_fin {F : Type} [Field F] [NumberField F] : evI F ((0, 1) : AF F) = 0 :=
  map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem fst_eq_zero {F : Type} [Field F] [NumberField F] {a : AF F} (h : evI F a = 0) : a.1 = 0 :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.mp h

theorem loc_chars : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ Φ ∈ schA F κ, ∀ y : κ → AF F, (∀ z, At (evI F) z → Φ (y + z) = 0) →
    ∃ (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ), (∀ q ∈ s, ∀ i, evI F (q i) = 0) ∧
      ∑ q ∈ s, c q * ψ (y ⬝ᵥ q) = 1 ∧ ∀ x, (∑ q ∈ s, c q * ψ (x ⬝ᵥ q)) * Φ x = 0 := GlobalTheory.T.exists_trigPolynomial_annihilating_adelicSchwartz

theorem snd_eq_zero_of_at {F : Type} [Field F] [NumberField F] {κ : Type} {z : κ → AF F} (hz : At (evI F) z) (i : κ) :
    (z i).2 = 0 := by
  have := congrArg Prod.snd (congrFun (hz (0, 1) evI_fin) i)
  change (((0, 1) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F).2 * (z i).2) = (0 : AF F).2 at this
  rw [one_mul] at this
  exact this

def intInd {F : Type} [Field F] [NumberField F] (κ : Type) : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  (Set.pi Set.univ fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))).indicator 1

theorem intInd_mem {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    intInd (F := F) κ ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  set B := Set.pi Set.univ fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) with hB
  have hO : IsOpen B := isOpen_set_pi Set.finite_univ fun _ _ => GroundTheory.Global.isOpen_integralFiniteAdeles
  have hK : IsCompact B := isCompact_univ_pi fun _ => GroundTheory.Global.isCompact_integralFiniteAdeles F
  have hC : IsClosed B := hK.isClosed
  refine ⟨?_, HasCompactSupport.intro hK fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ B
  · refine ⟨_, hO, hx, fun y hy => ?_⟩
    simp only [intInd, ← hB, Set.indicator_of_mem hy, Set.indicator_of_mem hx, Pi.one_apply]
  · refine ⟨_, hC.isOpen_compl, hx, fun y hy => ?_⟩
    simp only [intInd, ← hB, Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

theorem ref_fun : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∃ r₀ : (κ → AF F) → ℂ, (∀ x : κ → AF F, (∀ i, (x i).2 = 0) → r₀ x = 1) ∧
      ∀ f : SInf F κ, Rest (evI F) (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) r₀ := by
  intro F _ _ κ _
  refine ⟨fun x => intInd κ (fun i => (x i).2), fun x hx => ?_, fun f => ⟨fun x z hz => ?_, ?_⟩⟩
  · have : (fun i => (x i).2) = 0 := funext hx
    simp only [this, intInd]
    rw [Set.indicator_of_mem (show (0 : κ → FiniteAdeleRing (𝓞 F) F) ∈ Set.pi Set.univ
      fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) from
        fun i _ => zero_mem (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F))]
    rfl
  · have : (fun i => ((x + z) i).2) = fun i => (x i).2 := by
      funext i
      change (x i).2 + (z i).2 = (x i).2
      rw [snd_eq_zero_of_at hz i, add_zero]
    simp only [this]
  · exact Submodule.subset_span ⟨f, intInd κ, intInd_mem κ, rfl⟩

theorem res_arch : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ], ∀ Φ ∈ schA F κ,
    ∃ f : SInf F κ, ∀ t : κ → mixedEmbedding.mixedSpace F,
      Φ (fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t i), 0) : AF F)) = f t := by
  intro F _ _ κ _ Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, _, rfl⟩ := h
    refine ⟨g 0 • f, fun t => ?_⟩
    simp only [pureA, RingEquiv.apply_symm_apply, SchwartzMap.smul_apply, smul_eq_mul]
    rw [mul_comm]
    rfl
  | zero => exact ⟨0, fun t => rfl⟩
  | add Φ₁ Φ₂ _ _ h1 h2 =>
    obtain ⟨f₁, hf₁⟩ := h1
    obtain ⟨f₂, hf₂⟩ := h2
    exact ⟨f₁ + f₂, fun t => by
      show Φ₁ _ + Φ₂ _ = _
      rw [hf₁, hf₂, SchwartzMap.add_apply]⟩
  | smul a Φ _ h =>
    obtain ⟨f, hf⟩ := h
    exact ⟨a • f, fun t => by
      show a • Φ _ = _
      rw [hf, SchwartzMap.smul_apply]⟩

theorem comm_fin {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W)
    (hW : M.IsWeil ψ χX χW om) (h : UA σ W.J) (hh : h ∈ UAt σ W (evI F))
    (u : AF F) (hu : evI F u = 0) (p q : Fin n × Fin d → AF F)
    (Φ : (Fin n × Fin d → AF F) → ℂ) (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
      om (1, h) (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (om (1, h) Φ) := by
  have hS := IsUWeilPair.isUSplitting hW
  set w := M.co.e.symm (p, q) with hw
  have he : M.co.e (u • w) = (u • p, u • q) := by
    rw [LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]
  have h0 : u • (mat h - 1) = 0 := hh u hu
  have hact : actAB (cA σ) ((1, h) : UA σ X.J × UA σ W.J) (u • w) = u • w := by
    have h1 : (u • w) * (mat h)ᵀ - u • w = w * (u • (mat h - 1))ᵀ := by
      rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
        Matrix.mul_sub, Matrix.mul_one, smul_sub]
    rw [h0, Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at h1
    simp only [actAB]
    simpa [mat] using h1
  have h2 := hS.impl (1, h) (u • w) Φ hΦ
  simp only [Darboux.rho, he, hact] at h2
  exact h2

theorem fibre {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (T : Module.End ℂ ((κ → AF F) → ℂ))
    (hcomm : ∀ u : AF F, evI F u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ schA F κ,
      T (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (T Φ))
    (Φ : (κ → AF F) → ℂ) (hΦ : Φ ∈ schA F κ) (y : κ → AF F) (hy : ∀ z, At (evI F) z → Φ (y + z) = 0) :
    T Φ y = 0 := by
  obtain ⟨s, c, hs, h1, h0⟩ := loc_chars ψ hψ Φ hΦ y hy
  have hch : ∀ q ∈ s, T (fun x => ψ (x ⬝ᵥ q) * Φ x) = fun x => ψ (x ⬝ᵥ q) * T Φ x := by
    intro q hq
    set u : AF F := (0, 1) with hu
    have hu0 : evI F u = 0 := evI_fin
    have huq : u • q = q := by
      funext i
      have hi := hs q hq i
      have hq1 : (q i).1 = 0 := fst_eq_zero hi
      refine Prod.ext ?_ ?_
      · show (0 : InfiniteAdeleRing F) * (q i).1 = (q i).1
        rw [hq1, zero_mul]
      · show (1 : FiniteAdeleRing (𝓞 F) F) * (q i).2 = (q i).2
        rw [one_mul]
    have e := hcomm u hu0 0 q Φ hΦ
    have hs0 : ∀ G : (κ → AF F) → ℂ, schr ψ (u • (0 : κ → AF F), u • q) G = fun x => ψ (x ⬝ᵥ q) * G x := by
      intro G; funext x; simp [schr, huq]
    rw [hs0, hs0] at e
    exact e
  have hsum : ∀ G : (κ → AF F) → ℂ, (fun x => (∑ q ∈ s, c q * ψ (x ⬝ᵥ q)) * G x) =
      ∑ q ∈ s, c q • (fun x => ψ (x ⬝ᵥ q) * G x) := by
    intro G; funext x; simp [Finset.sum_mul, mul_assoc]
  have hT : T (fun x => (∑ q ∈ s, c q * ψ (x ⬝ᵥ q)) * Φ x) = fun x => (∑ q ∈ s, c q * ψ (x ⬝ᵥ q)) * T Φ x := by
    rw [hsum, hsum, map_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [map_smul, hch q hq]
  have hz : (fun x => (∑ q ∈ s, c q * ψ (x ⬝ᵥ q)) * Φ x) = 0 := funext h0
  rw [hz, map_zero] at hT
  have := congrFun hT y
  simp only [Pi.zero_apply, h1, one_mul] at this
  exact this.symm

theorem acts_arch : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsCMExt F E σ → IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ h ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, h)) f f₁ := by
  intro _ F E _ _ _ _ _ σ n d X W M ψ χX χW om _ hψ hW h hh f
  have hS := IsUWeilPair.isUSplitting hW
  set T := om (1, h) with hTdef
  have hpres : ∀ Φ ∈ schA F (Fin n × Fin d), T Φ ∈ schA F (Fin n × Fin d) := fun Φ hΦ => hS.pres (1, h) Φ hΦ
  have hcomm := comm_fin M ψ χX χW om hW h hh
  obtain ⟨r₀, hr₀1, hr₀⟩ := ref_fun (F := F) (Fin n × Fin d)
  set Φ₀ := tens (evI F) (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) r₀ with hΦ₀
  have hm₀ : Φ₀ ∈ schA F _ := (hr₀ f).2
  obtain ⟨f₁, hf₁⟩ := res_arch (T Φ₀) (hpres Φ₀ hm₀)
  refine ⟨f₁, fun r hr => ?_⟩
  funext y
  set u : AF F := (0, 1) with hu
  have hu0 : evI F u = 0 := evI_fin
  have htr : ∀ Ψ ∈ schA F (Fin n × Fin d), T (fun w => Ψ (w + u • (-y))) = fun w => T Ψ (w + u • (-y)) := by
    intro Ψ hΨ
    have e := hcomm u hu0 (-y) 0 Ψ hΨ
    have hs0 : ∀ G : (Fin n × Fin d → AF F) → ℂ, schr ψ (u • (-y), u • (0 : Fin n × Fin d → AF F)) G =
        fun w => G (w + u • (-y)) := by
      intro G; funext w; simp [schr]
    rw [hs0, hs0] at e
    exact e
  set Φ₁ := tens (evI F) (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) r with hΦ₁
  set Φ₂ : (Fin n × Fin d → AF F) → ℂ := r y • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
  have hm₂ : Φ₂ ∈ schA F _ := Submodule.smul_mem _ _ (GlobalTheory.SchwartzTranslation.schA_add_const _ _ hm₀)
  have hz2 : ∀ z : Fin n × Fin d → AF F, At (evI F) z → ∀ i, (z i).2 = 0 := by
    intro z hz i
    have := congrArg Prod.snd (congrFun (hz u hu0) i)
    change (u * z i).2 = (0 : AF F).2 at this
    have e : (u * z i).2 = (z i).2 := one_mul _
    rw [e] at this
    exact this
  have hvan : ∀ z, At (evI F) z → (Φ₁ - Φ₂) (y + z) = 0 := by
    intro z hz
    have e1 : r (y + z) = r y := hr.1 y z hz
    have e2 : (fun i => evI F ((y + z + u • (-y)) i)) = fun i => evI F ((y + z) i) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, evI_add, evI_mul, hu0, zero_mul, add_zero]
    have e3 : r₀ (y + z + u • (-y)) = 1 := by
      refine hr₀1 _ fun i => ?_
      change ((y i + z i) + u * -(y i)).2 = 0
      change (y i).2 + (z i).2 + 1 * -(y i).2 = 0
      rw [hz2 z hz i]
      ring
    simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, tens]
    rw [e2, e3, e1]
    ring
  have h0 := fibre ψ hψ T hcomm (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hvan
  rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
  have hy0 : y + u • (-y) = fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (evI F (y i)), 0) : AF F) := by
    funext i
    refine Prod.ext ?_ ?_
    · change (y i).1 + 0 * -(y i).1 = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
        (InfiniteAdeleRing.ringEquiv_mixedSpace F (y i).1)
      rw [RingEquiv.symm_apply_apply]
      ring
    · change (y i).2 + 1 * -(y i).2 = 0
      ring
  have h2 : T Φ₂ y = r y * f₁ (fun i => evI F (y i)) := by
    rw [hΦ₂, map_smul, htr Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hy0, hf₁]
  rw [h0, h2]
  simp only [tens]
  ring

end GlobalTheory.ArchLocality
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelArchimedeanExponentStatement
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
theorem _root_.GlobalTheory.T.weil_model_archimedean_exponent : GlobalTheory.FunPr.Hypotheses₂ →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ → GlobalTheory.RealDict.IsPairReading ψ ε A B ω Xs Ws Mo ψ' om τ →
    ∃ Φ : PolF D X.rank M.rank →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
      Function.Injective Φ ∧ LinearMap.range Φ = Mo.Pol ψ' τ ∧ GlobalTheory.RealDict.IsFockMap ψ θ ε A B Mo Φ := by
  first | exact @GlobalTheory.RealDict.FockMap.exists_fockMap | exact GlobalTheory.RealDict.FockMap.exists_fockMap | (intros; apply GlobalTheory.RealDict.FockMap.exists_fockMap <;> assumption)
end

