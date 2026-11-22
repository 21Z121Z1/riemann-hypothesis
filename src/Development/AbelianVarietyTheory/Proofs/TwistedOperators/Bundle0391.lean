import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1090
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0134
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0377
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0358
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0178
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0188
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearGKMapExtendsToSmoothVectors
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0275
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0318
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0378
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0379
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0380
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0174
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1051
import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaIsLatticeVacuumFockPureTensor
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FockLatVac

theorem infPart_latO_any {D : D7} {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : HeightOneSpectrum (𝓞 D.host.F) → Prop} {u : WO S T} (hu : u ∈ latO S T LS LT P) : u.map (infPart D) = 0 := by
  ext i j
  rw [Matrix.map_apply, Matrix.zero_apply]
  unfold latO at hu
  refine AddSubgroup.closure_induction (p := fun u _ => infPart D (u i j) = 0) ?_ ?_ ?_ ?_ hu
  · rintro w ⟨α, -, -, a, -, s, -, t, -, rfl⟩
    rw [Matrix.of_apply]
    exact (show infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) =
      (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) from rfl).trans (TensorProduct.zero_tmul _ _)
  · simp
  · intro x y _ _ hx hy; rw [Matrix.add_apply, RingHom.map_add, hx, hy, add_zero]
  · intro x _ hx; rw [Matrix.neg_apply, RingHom.map_neg, hx, neg_zero]

theorem theta_isLatVac_pureTensorO : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (g : WO S T → ℂ), IsThetaFunO ψ S T g → IsLatVac (heisO ψ S T) (latO S T LS LT P) g → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ), IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT g φ) ∧ IsLatVac (heisO ψ S T) (latO S T LS LT P) (pureTensorO ψ θ S T sS sT BS BT g φ) := by
  intro D ψ θ S T hψ hθ LS LT P g hg hvac sS BS sT BT φ
  have hth : ∀ φ, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT g φ) := fun φ =>
    GlobalTheory.GalLift.Vec.theta_pureTensorO hψ hθ sS BS sT BT hg φ
  refine ⟨hth φ, fun u hu => ?_, fun e he u hu hh => ?_⟩
  · exact GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite ψ θ S T hθ sS sT BS BT g hth (2 • u)
      (infPart_latO_any (AddSubgroup.nsmul_mem _ hu 2)) (hvac.1 u hu) φ
  · exact GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite ψ θ S T hθ sS sT BS BT g hth u
      (infPart_latO_any hu) (hvac.2 e he u hu hh) φ

end GlobalTheory.FockLatVac

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsWeilDatumCompGroupSwappingSymplecticEquivStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isWeilDatum_comp_group_swapping_symplectic_equiv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T S' T' : HSp D), S'.rank = T.rank → T'.rank = S.rank →
    ∀ (L : WO S' T' ≃ₗ[AE D] WO S T) (φ : GA D S' →* GA D T) (φ' : GA D T' →* GA D S),
    Continuous L → Continuous L.symm → (∀ x, L x ∈ ratL T S ↔ x ∈ ratL T' S') →
    (∀ x y, symplO S T (L x) (L y) = symplO S' T' x y) →
    (∀ x, (L x).map (infPart D) = 0 ↔ x.map (infPart D) = 0) → (∀ x, (L x).map (finPart D) = 0 ↔ x.map (finPart D) = 0) →
    Continuous φ → Continuous φ' → (∀ γ ∈ GQ S', φ γ ∈ GQ T) → (∀ γ ∈ GQ T', φ' γ ∈ GQ S) →
    (∀ g h x, L (actO S' T' g h x) = actO S T (φ' h) (φ g) (L x)) →
    (∀ e g, SuppAt e S' g → SuppAt e T (φ g)) → (∀ e h, SuppAt e T' h → SuppAt e S (φ' h)) →
    (∀ g, (Formalism.L2.Theta.mt T (φ g)).det = (Formalism.L2.Theta.mt S' g⁻¹).det) → (∀ h, (Formalism.L2.Theta.mt S (φ' h)).det = (Formalism.L2.Theta.mt T' h⁻¹).det) →
    ∀ (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT ω →
      ∃ ω' : GA D S' × GA D T' →* Module.End ℂ (WO S' T' → ℂ), IsWeilDatumO ψ S' T' χT χS ω' ∧
        ∀ g h (f : WO S T → ℂ), ω' (g, h) (fun u => f (L u)) = fun u => ω (φ' h, φ g) f (L u) := by
  first | exact @GlobalTheory.SwapWeil.isWeilDatumO_swap | exact GlobalTheory.SwapWeil.isWeilDatumO_swap | (intros; apply GlobalTheory.SwapWeil.isWeilDatumO_swap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeReductionEqOneOfCompletionCongruenceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_reduction_eq_one_of_completion_congruence : ∀ (D : D7) (V : HSp D) (L : Lt D.host.E V.rank) (β : GL (Fin V.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame β L → ∀ k : GA D V, Lev.finE V k ∈ Formalism.L2.DIV.St β → ∀ (PP : Formalism.L2.DIV.Pl D.host.E) (b : 𝓞 D.host.E), b ∉ PP.asIdeal → (∀ u ∈ hatV L, ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • (fmt V k *ᵥ u - u) ∈ hatV (PP.asIdeal • L)) → Formalism.L2.DIV.redFn β PP (Lev.finE V k) = 1 := by
  first | exact @GlobalTheory.LevRedTriv.redFn_eq_one_of_cong | exact GlobalTheory.LevRedTriv.redFn_eq_one_of_cong | (intros; apply GlobalTheory.LevRedTriv.redFn_eq_one_of_cong <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelTowerRapidDecayStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_tower_rapid_decay : GlobalTheory.FunPr.Hypotheses₂ → RowTower → RowRapid := by
  first | exact @GlobalTheory.SepRows.RowRapidPf.rowRapid | exact GlobalTheory.SepRows.RowRapidPf.rowRapid | (intros; apply GlobalTheory.SepRows.RowRapidPf.rowRapid <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalDecompositionSplitPlace
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.IwSplitFrame

section Frame

variable {D : D7} {V : HSp D} (Φ : WittFrame V)

def cols {r : ℕ} (x : Fin r → V.V) : Matrix (Fin V.rank) (Fin r) D.host.E := Matrix.of fun k i => V.frame.repr (x i) k

theorem gram_cols {r s : ℕ} (x : Fin r → V.V) (y : Fin s → V.V) (i : Fin r) (j : Fin s) :
    (((cols x).map D.sp.cm.sig).transpose * V.gram * cols y) i j = V.hT (x i) (y j) := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord V]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, cols, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem fe : ((cols Φ.f).map D.sp.cm.sig).transpose * V.gram * cols Φ.e = 1 := by
  ext j i
  rw [gram_cols, Matrix.one_apply, ← HSpace.hD, Φ.ef]
  simp only [eq_comm]

theorem ee : ((cols Φ.e).map D.sp.cm.sig).transpose * V.gram * cols Φ.e = 0 := by
  ext j i
  rw [gram_cols, Matrix.zero_apply, ← HSpace.hD, Φ.ee]

theorem ff : ((cols Φ.f).map D.sp.cm.sig).transpose * V.gram * cols Φ.f = 0 := by
  ext j i
  rw [gram_cols, Matrix.zero_apply, ← HSpace.hD, Φ.ff]

theorem ef : ((cols Φ.e).map D.sp.cm.sig).transpose * V.gram * cols Φ.f = 1 := by
  ext i j
  have h1 : V.hT (Φ.e i) (Φ.f j) = star (V.hT (Φ.f j) (Φ.e i)) := GlobalTheory.IndefiniteRowSideFullHecke.BesselData.hT_swap rfl
  rw [gram_cols, Matrix.one_apply, h1, ← HSpace.hD, Φ.ef]
  split_ifs <;> simp

theorem coordMat_eq (R : Type) [CommRing R] [Algebra D.host.F R] :
    (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V R (Φ.e i) x) =
      (cols Φ.e).map (inclR (F := D.host.F) R) := by
  ext; rfl

end Frame

theorem exists_compl {K : Type} [Field K] [CharZero K] {n r : ℕ} (e e' : Matrix (Fin n) (Fin r) K)
    (p a : Matrix (Fin r) (Fin n) K) (hpe : p * e = 1) (hpe' : p * e' = 0) (hae : a * e = 0) (hae' : a * e' = 1) :
    ∃ (k : ℕ) (i : Matrix (Fin n) (Fin k) K) (q : Matrix (Fin k) (Fin n) K), n = r + k + r ∧
      e * p + i * q + e' * a = 1 := by
  set π : Matrix (Fin n) (Fin n) K := 1 - e * p - e' * a with hπdef
  have hXX : e * p * (e * p) = e * p := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc p, hpe, Matrix.one_mul]
  have hXY : e * p * (e' * a) = 0 := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc p, hpe', Matrix.zero_mul, Matrix.mul_zero]
  have hYX : e' * a * (e * p) = 0 := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc a, hae, Matrix.zero_mul, Matrix.mul_zero]
  have hYY : e' * a * (e' * a) = e' * a := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc a, hae', Matrix.one_mul]
  have hπ : π * π = π := by
    simp only [hπdef, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hXX, hXY, hYX, hYY]
    abel
  have hid : IsIdempotentElem (Matrix.toLin' π) := by
    rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hπ]
  set W := LinearMap.range (Matrix.toLin' π)
  set b := Module.finBasis K W
  refine ⟨Module.finrank K W, LinearMap.toMatrix' (W.subtype ∘ₗ b.equivFun.symm.toLinearMap),
    LinearMap.toMatrix' (b.equivFun.toLinearMap ∘ₗ (Matrix.toLin' π).rangeRestrict), ?_, ?_⟩
  · have h1 := (LinearMap.IsIdempotentElem.isProj_range _ hid).trace
    rw [Matrix.trace_toLin'_eq, hπdef, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_mul_comm e,
      Matrix.trace_mul_comm e', hpe, hae', Matrix.trace_one, Matrix.trace_one] at h1
    simp only [Fintype.card_fin] at h1
    have h2 : ((r + Module.finrank K W + r : ℕ) : K) = n := by push_cast; rw [← h1]; ring
    exact (Nat.cast_injective h2).symm
  · rw [← LinearMap.toMatrix'_comp]
    have h3 : (W.subtype ∘ₗ b.equivFun.symm.toLinearMap) ∘ₗ (b.equivFun.toLinearMap ∘ₗ (Matrix.toLin' π).rangeRestrict) =
        Matrix.toLin' π := by
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, Submodule.subtype_apply,
        LinearMap.rangeRestrict, LinearMap.codRestrict_apply]
    rw [h3, LinearMap.toMatrix'_toLin', hπdef]
    abel

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n r : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}

theorem mat_mul (g h : GLoc σ J v) : (HA.mat (F := F) (Fv F v) σ J (g * h)).1 =
    (HA.mat (F := F) (Fv F v) σ J g).1 * (HA.mat (F := F) (Fv F v) σ J h).1 := by
  rw [← GlobalTheory.AdelicU.matHom_apply, ← GlobalTheory.AdelicU.matHom_apply, ← GlobalTheory.AdelicU.matHom_apply, map_mul, Units.val_mul]

theorem mat_one : (HA.mat (F := F) (Fv F v) σ J 1).1 = 1 := by
  rw [← GlobalTheory.AdelicU.matHom_apply, map_one, Units.val_one]

def keepGrp (j : Matrix (Fin n) (Fin r) (Fv F v ⊗[F] E)) : Subgroup (GLoc σ J v) where
  carrier := {q | ∃ β : GL (Fin r) (Fv F v ⊗[F] E), (HA.mat (F := F) (Fv F v) σ J q).1 * j = j * β.1}
  mul_mem' := by
    rintro a b ⟨β, hβ⟩ ⟨β', hβ'⟩
    refine ⟨β * β', ?_⟩
    rw [mat_mul, Matrix.mul_assoc, hβ', ← Matrix.mul_assoc, hβ, Units.val_mul, Matrix.mul_assoc]
  one_mem' := ⟨1, by rw [mat_one, Matrix.one_mul, Units.val_one, Matrix.mul_one]⟩
  inv_mem' := by
    rintro a ⟨β, hβ⟩
    refine ⟨β⁻¹, ?_⟩
    have h1 : (HA.mat (F := F) (Fv F v) σ J a⁻¹).1 * (HA.mat (F := F) (Fv F v) σ J a).1 = 1 := by
      rw [← mat_mul, inv_mul_cancel, mat_one]
    calc (HA.mat (F := F) (Fv F v) σ J a⁻¹).1 * j
        = (HA.mat (F := F) (Fv F v) σ J a⁻¹).1 * (j * β.1) * (β⁻¹).1 := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc j, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = j * (β⁻¹).1 := by rw [← hβ, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem keeps_of_split (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (g : GLoc σ J v) {e : Matrix (Fin n) (Fin r) E}
    {p : Matrix (Fin r) (Fin n) E} (hp : p * e = 1) {a a' : Matrix (Fin r) (Fin r) (Fv F v)}
    (h1 : (splitHom σ J τ g).1 * e.map τ = e.map τ * a)
    (h2 : (splitHom σ J (τ.comp σ) g).1 * e.map (τ.comp σ) = e.map (τ.comp σ) * a') :
    g ∈ keepGrp (σ := σ) (J := J) (v := v) (e.map (inclR (F := F) (Fv F v))) := by
  set j := e.map (inclR (F := F) (Fv F v))
  set P := p.map (inclR (F := F) (Fv F v))
  have hP : P * j = 1 := by
    rw [← Matrix.map_mul, hp, Matrix.map_one _ (map_zero _) (map_one _)]
  have key : ∀ (t : E →ₐ[F] Fv F v) {b : Matrix (Fin r) (Fin r) (Fv F v)},
      (splitHom σ J t g).1 * e.map t = e.map t * b →
      (HA.mat (F := F) (Fv F v) σ J g).1.map ((splitProj t).toRingHom) * j.map ((splitProj t).toRingHom) =
        j.map ((splitProj t).toRingHom) * b := fun t b hb => by
    have e2 : j.map ((splitProj t).toRingHom) = e.map t := by
      ext k l
      simp [j, splitProj_inclR]
    rw [e2]
    exact hb
  have hk : (HA.mat (F := F) (Fv F v) σ J g).1 * j = j * (P * ((HA.mat (F := F) (Fv F v) σ J g).1 * j)) := by
    ext k l
    exact split_ext h τ (congrFun (congrFun (GlobalTheory.Core.Rk.IwFlagSplit.map_keeps _ hP (key τ h1)) k) l)
      (congrFun (congrFun (GlobalTheory.Core.Rk.IwFlagSplit.map_keeps _ hP (key _ h2)) k) l)
  have hk' : (HA.mat (F := F) (Fv F v) σ J g⁻¹).1 * (HA.mat (F := F) (Fv F v) σ J g).1 = 1 := by
    rw [← mat_mul, inv_mul_cancel, mat_one]
  have h3 : (P * ((HA.mat (F := F) (Fv F v) σ J g⁻¹).1 * j)) * (P * ((HA.mat (F := F) (Fv F v) σ J g).1 * j)) = 1 := by
    rw [Matrix.mul_assoc P, Matrix.mul_assoc (HA.mat (F := F) (Fv F v) σ J g⁻¹).1, ← hk,
      ← Matrix.mul_assoc (HA.mat (F := F) (Fv F v) σ J g⁻¹).1, hk', Matrix.one_mul, hP]
  exact ⟨⟨_, _, mul_eq_one_comm.1 h3, h3⟩, hk⟩

end Local

theorem iwasawa_span_split : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (a : GL (Fin V.rank) (TensorProduct D.host.F (AF D.host.F) D.host.E)), Φ.IsGood D.sp.cm L a → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v → ∀ (g : GLoc D.sp.cm.sig V.gram v), ∃ q k : GLoc D.sp.cm.sig V.gram v, k ∈ stabLoc D.sp.cm.sig V.gram L v ∧ g = q * k ∧ ∃ β : GL (Fin (wittIndex V)) (TensorProduct D.host.F (Fv D.host.F v) D.host.E), (HA.mat (F := D.host.F) (Fv D.host.F v) D.sp.cm.sig V.gram q).1 * (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V (Fv D.host.F v) (Φ.e i) x) = (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V (Fv D.host.F v) (Φ.e i) x) * β.1 := by
  intro D V Φ L a hG v ⟨P, P', hne, hP, hP'⟩ g
  obtain ⟨τ, -⟩ := existsUnique_splitPrime_eq (isCMExt_host D) (v := v) hne (HeightOneSpectrum.ext hP)
    (HeightOneSpectrum.ext hP')
  haveI : Submodule.IsLattice D.host.E L := hG.1
  obtain ⟨k, i, qq, hn, hsum⟩ := exists_compl (cols Φ.e) (cols Φ.f)
    (((cols Φ.f).map D.sp.cm.sig).transpose * V.gram) (((cols Φ.e).map D.sp.cm.sig).transpose * V.gram)
    (fe Φ) (ff Φ) (ee Φ) (ef Φ)
  obtain ⟨B, lv, hB⟩ := GlobalTheory.Core.Rk.IwFlagSplit.exists_flag_basis (v := v) τ (GlobalTheory.Doubling.isHermND_gram V)
    (e := cols Φ.e) (e' := cols Φ.f) (i := i) (p := ((cols Φ.f).map D.sp.cm.sig).transpose * V.gram) (q := qq)
    (Fintype.equivOfCardEq (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)) hsum (ef Φ)
  have hQ : ∀ x : GLoc D.sp.cm.sig V.gram v, (B⁻¹ * splitHom D.sp.cm.sig V.gram τ x * B).1.BlockTriangular lv →
      x ∈ keepGrp (σ := D.sp.cm.sig) (J := V.gram) (v := v) ((cols Φ.e).map (inclR (F := D.host.F) (Fv D.host.F v))) :=
    fun x hx => by
      obtain ⟨⟨b, hb⟩, b', hb'⟩ := hB x hx
      exact keeps_of_split (isCMExt_host D) τ x (fe Φ) hb hb'
  obtain ⟨q, k', hq, hk, rfl⟩ := GlobalTheory.Core.Rk.IwFlagSplit.iwasawa_of_triangular (isCMExt_host D)
    (GlobalTheory.Doubling.isHermND_gram V) τ L (hG.2.1 v) _ B lv hQ g
  obtain ⟨β, hβ⟩ := hq
  refine ⟨q, k', hk, rfl, β, ?_⟩
  rw [coordMat_eq]
  exact hβ

end GlobalTheory.IwSplitFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearGKMapExtendsToSmoothVectorsStatement
section
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multilinear_gKMap_extends_to_smooth_vectors : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (E : Type) [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [T2Space E] (p : ℕ → Seminorm ℂ E) (π dπ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → (E →L[ℂ] E)), (∀ τ, GlobalTheory.SmoothGlob.IsSmoothModRep (M.ε τ) p (π τ) (dπ τ)) → (∀ τ τ', τ ≠ τ' → ∀ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ g' ∈ Formalism.MainNotions.S.UJset (M.ε τ'), (π τ g).comp (π τ' g') = (π τ' g').comp (π τ g)) → ∀ T₀ : MultilinearMap ℂ (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) E, (∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ), (w : M.H τ) = M.σ τ k (u τ) → T₀ (Function.update u τ w) = π τ k (T₀ u)) → (∀ τ, ∀ X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ), ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ), (w : M.H τ) = dRep (M.σ τ) X (u τ) → T₀ (Function.update u τ w) = dπ τ X (T₀ u)) → ∃ T : MultilinearMap ℂ (fun τ : D.what₂.Tau => M.sm τ) E, (∀ (v : M.Vec) (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M), (∀ τ, (v τ : M.H τ) = u τ) → T v = T₀ u) ∧ (∀ τ, ∀ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.σ τ g (v τ) → T (Function.update v τ w) = π τ g (T v)) ∧ ∀ τ (i : ℕ) (v : M.Vec), ∃ (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ), (∀ l ∈ L, ∀ X ∈ l, X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ)) ∧ ∀ w : M.sm τ, p i (T (Function.update v τ w)) ≤ C * GlobalTheory.SmoothGlob.sobNorm (M.σ τ) L w := by
  first | exact @GlobalTheory.FactorExtension.extend_positions | exact GlobalTheory.FactorExtension.extend_positions | (intros; apply GlobalTheory.FactorExtension.extend_positions <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityValuesContinuousBoundedHeckeConjStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicity_values_continuous_bounded_hecke_conj : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, ForStage D fun c _ s => (∀ (u : s.CC c) v, Continuous (PiLocalization₂.val u v) ∧ (∃ C : ℝ, ∀ g, ‖PiLocalization₂.val u v g‖ ≤ C) ∧ (∀ γ ∈ GQ s.V, ∀ g, PiLocalization₂.val u v (γ * g) = PiLocalization₂.val u v g) ∧ (∀ k ∈ s.J, ∀ g, PiLocalization₂.val u v (g * k) = PiLocalization₂.val u v g) ∧ GlobalTheory.Grow.RapidDec s.V (PiLocalization₂.val u v)) ∧ ∀ (R : Finset (GA D s.V)) (f : GA D s.V → ℂ), heckeLin s.V R (fun g => conj (f g)) = fun g => conj (heckeLin s.V R f g) := by
  first | exact @GlobalTheory.EvenOnto.ConjVal.values_conj_hecke | exact GlobalTheory.EvenOnto.ConjVal.values_conj_hecke | (intros; apply GlobalTheory.EvenOnto.ConjVal.values_conj_hecke <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityVanishingAndSameParamsSubspaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicity_vanishing_and_same_params_subspace : ∀ D : D7, MetEx D → (ForStage D fun c _ s => ∀ (x : s.CC c) w, w ≠ 0 → PiLocalization₂.val x w = 0 → x = 0) ∧ ∀ (c : Com D) (s : PiLocalization₂ D), (∀ (u u' : s.CC c) B B' (a : ℂ), IsPar u B → IsPar u' B' → (∀ w ∉ (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))), B w = B' w) → u + a • u' ≠ 0 → IsPar (u + a • u') B) ∧ ∀ (u : s.CC c) B (a : ℂ), IsPar u B → a ≠ 0 → IsPar (a • u) B := by
  first | exact @GlobalTheory.EvenOnto.vanish_and_parLin | exact GlobalTheory.EvenOnto.vanish_and_parLin | (intros; apply GlobalTheory.EvenOnto.vanish_and_parLin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyAlgHomCompletionOfSplitPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_algHom_completion_of_split_place : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
    ¬ GlobalTheory.WeilParts.NonSplitAt D v ε → Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F v) := by
  first | exact @GlobalTheory.SplitPlaceEmb.nonempty_algHom_of_not_nonSplitAt | exact GlobalTheory.SplitPlaceEmb.nonempty_algHom_of_not_nonSplitAt | (intros; apply GlobalTheory.SplitPlaceEmb.nonempty_algHom_of_not_nonSplitAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodEqZeroOfVanishingOnKFiniteValuesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_eq_zero_of_vanishing_on_kFinite_values : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ y ∈ MultT θ M J χ, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) (e : X → GA D V) (u : X → ℂ), Measurable e → Integrable u ν → (∀ a ∈ KF M, ∫ x, y a (e x) * u x ∂ν = 0) → ∀ a, ∫ x, y a (e x) * u x ∂ν = 0 := by
  first | exact @GlobalTheory.SepPer.KFinPer.per_eq_zero_of_kF | exact GlobalTheory.SepPer.KFinPer.per_eq_zero_of_kF | (intros; apply GlobalTheory.SepPer.KFinPer.per_eq_zero_of_kF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodIntegrableBoundedByProductOfNorms
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.PeriodBound

theorem period_bound : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ t ∈ MultT θ M J χ, ∀ (v : GlobalTheory.Unf.Vol V) (F : GA D V → ℂ), GlobalTheory.Unf.IsContAut V F → (∃ C, ∀ g, ‖F g‖ ≤ C) → (∀ x : SmT M, IntegrableOn (fun g => F g * t x g) v.𝓕 v.μ) ∧ ∃ K : ℝ, ∀ w : M.Vec, ‖∫ g in v.𝓕, F g * t (PiTensorProduct.tprod ℂ w) g ∂v.μ‖ ≤ K * ∏ τ, ‖(w τ : M.H τ)‖ := by
  intro hP hV D θ hθ V S M J χ t ht v F hF hFb
  obtain ⟨C0, hC0⟩ := hFb
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have hfin : v.μ v.𝓕 < ⊤ := GlobalTheory.CuspDecay.measure_lt_top hV V v.μ v.𝓕 v.haar v.fund
  have hval : ∀ x : SmT M, Continuous (t x) ∧ ∃ B : ℝ, ∀ g, ‖t x g‖ ≤ B := by
    intro x
    obtain ⟨ha, hc, -⟩ := GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hP D V S M θ hθ J χ t ht x
    exact ⟨ha.cont, GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ ha hc⟩
  have hint0 : ∀ x : SmT M, IntegrableOn (fun g => F g * t x g) v.𝓕 v.μ := by
    intro x
    obtain ⟨hcont, B, hB⟩ := hval x
    refine Measure.integrableOn_of_bounded (M := C0 * B) hfin.ne
      ((hF.2.mul hcont).measurable.aestronglyMeasurable) (.of_forall fun g => ?_)
    rw [norm_mul]
    exact mul_le_mul (hC0 g) (hB g) (norm_nonneg _) ((norm_nonneg _).trans (hC0 g))
  refine ⟨hint0, ?_⟩
  set T : MMap M := PiTensorProduct.lift.symm t with hTdef
  have hT : T ∈ Mult θ M J χ := (mem_multT θ M J χ t).1 ht
  obtain ⟨c, hc⟩ := GlobalTheory.SchurConst.schurMult_all hP D θ hθ V S M J χ v.μ v.𝓕 v.haar v.fund hθ v.haar v.fund T hT T hT
  have hTw : ∀ w : M.Vec, T w = t (PiTensorProduct.tprod ℂ w) := fun w => by
    rw [hTdef, PiTensorProduct.lift_symm]
    rfl
  set C' : ℝ := max C0 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hFC : ∀ g, ‖F g‖ ≤ C' := fun g => (hC0 g).trans (le_max_left _ _)
  refine ⟨C' * ((v.μ v.𝓕).toReal + ‖c‖) / 2, fun w => ?_⟩
  set s : ℝ := ∏ τ, ‖(w τ : M.H τ)‖ with hs
  have hs0 : 0 ≤ s := Finset.prod_nonneg fun τ _ => norm_nonneg _
  rcases hs0.eq_or_lt with h0 | hpos
  · obtain ⟨τ, -, hτ⟩ := Finset.prod_eq_zero_iff.1 h0.symm
    have hwτ : w τ = 0 := Subtype.ext (norm_eq_zero.1 hτ)
    have h1 : PiTensorProduct.tprod ℂ w = 0 := (PiTensorProduct.tprod ℂ).map_coord_zero τ hwτ
    rw [h1, map_zero, ← h0]
    simp
  · obtain ⟨hint, heq⟩ := hc w w
    have hnsq : ∀ g, ‖star (T w g) * T w g‖ = ‖T w g‖ ^ 2 := fun g => by
      rw [norm_mul, norm_star, sq]
    have hint2 : IntegrableOn (fun g => ‖T w g‖ ^ 2) v.𝓕 v.μ := by
      have h := funext fun g => (hnsq g).symm
      rw [h]
      exact hint.norm
    have hsq : ∫ g in v.𝓕, ‖T w g‖ ^ 2 ∂v.μ ≤ ‖c‖ * s ^ 2 := by
      have h1 : ((∫ g in v.𝓕, ‖T w g‖ ^ 2 ∂v.μ : ℝ) : ℂ) = ∫ g in v.𝓕, star (T w g) * T w g ∂v.μ := by
        rw [← integral_complex_ofReal]
        congr 1
        funext g
        rw [Complex.star_def, Complex.conj_mul']
        push_cast
        ring
      have hnn : 0 ≤ ∫ g in v.𝓕, ‖T w g‖ ^ 2 ∂v.μ := integral_nonneg fun g => sq_nonneg _
      have h2 : ∫ g in v.𝓕, ‖T w g‖ ^ 2 ∂v.μ = ‖∫ g in v.𝓕, star (T w g) * T w g ∂v.μ‖ := by
        rw [← h1, Complex.norm_of_nonneg hnn]
      rw [h2, heq, norm_mul, norm_prod, hs, ← Finset.prod_pow]
      refine le_of_eq ?_
      congr 1
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [inner_self_eq_norm_sq_to_K]
      simp
    have hpt : ∀ g, ‖F g * t (PiTensorProduct.tprod ℂ w) g‖ ≤ C' * s / 2 + C' / (2 * s) * ‖T w g‖ ^ 2 := by
      intro g
      rw [norm_mul, ← hTw]
      have h3 : ‖T w g‖ ≤ s / 2 + ‖T w g‖ ^ 2 / (2 * s) := by
        rw [div_add_div _ _ (by norm_num) (by positivity), le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (‖T w g‖ - s)]
      calc ‖F g‖ * ‖T w g‖ ≤ C' * ‖T w g‖ := mul_le_mul_of_nonneg_right (hFC g) (norm_nonneg _)
        _ ≤ C' * (s / 2 + ‖T w g‖ ^ 2 / (2 * s)) := mul_le_mul_of_nonneg_left h3 hC'0
        _ = C' * s / 2 + C' / (2 * s) * ‖T w g‖ ^ 2 := by ring
    have hintR : IntegrableOn (fun g => C' * s / 2 + C' / (2 * s) * ‖T w g‖ ^ 2) v.𝓕 v.μ :=
      (integrableOn_const hfin.ne).add (hint2.const_mul _)
    calc ‖∫ g in v.𝓕, F g * t (PiTensorProduct.tprod ℂ w) g ∂v.μ‖
        ≤ ∫ g in v.𝓕, ‖F g * t (PiTensorProduct.tprod ℂ w) g‖ ∂v.μ := norm_integral_le_integral_norm _
      _ ≤ ∫ g in v.𝓕, (C' * s / 2 + C' / (2 * s) * ‖T w g‖ ^ 2) ∂v.μ :=
          integral_mono (hint0 _).norm hintR hpt
      _ = (v.μ v.𝓕).toReal * (C' * s / 2) + C' / (2 * s) * ∫ g in v.𝓕, ‖T w g‖ ^ 2 ∂v.μ := by
          have hc1 : Integrable (fun _ : GA D V => C' * s / 2) (v.μ.restrict v.𝓕) := integrableOn_const hfin.ne
          have hc2 : Integrable (fun g => C' / (2 * s) * ‖T w g‖ ^ 2) (v.μ.restrict v.𝓕) := hint2.const_mul _
          rw [integral_add hc1 hc2, setIntegral_const,
            integral_const_mul, smul_eq_mul, Measure.real]
      _ ≤ (v.μ v.𝓕).toReal * (C' * s / 2) + C' / (2 * s) * (‖c‖ * s ^ 2) := by
          gcongr
      _ = C' * ((v.μ v.𝓕).toReal + ‖c‖) / 2 * s := by
          field_simp

end GlobalTheory.PeriodBound
end
end

