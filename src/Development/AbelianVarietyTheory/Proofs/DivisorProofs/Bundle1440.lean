import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1418
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1419
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDistributionAutomorphySourceGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1420
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0108
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1412
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1285
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1261
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1332
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1278
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1327
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1254
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1270
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1262
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPolynomialsToProductVariablesCompPderivStatement
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorPolynomialsToProductVariables_comp_pderiv : ∀ (W Λ : Type) [Fintype W] [DecidableEq W] (w : W) (l : Λ),
    GlobalTheory.CCRFock.polMap W Λ ∘ₗ GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial Λ ℂ) w
                 (MvPolynomial.pderiv l).toLinearMap =
      (MvPolynomial.pderiv (w, l)).toLinearMap ∘ₗ GlobalTheory.CCRFock.polMap W Λ := by
  first | exact @GlobalTheory.CCRFock.polMap_comp_atPl_pderiv | exact GlobalTheory.CCRFock.polMap_comp_atPl_pderiv | (intros; apply GlobalTheory.CCRFock.polMap_comp_atPl_pderiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPolynomialsToProductVariablesInjectiveStatement
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorPolynomialsToProductVariables_injective : ∀ (W Λ : Type) [Fintype W] [DecidableEq W], Function.Injective (GlobalTheory.CCRFock.polMap W Λ) := by
  first | exact @GlobalTheory.CCRFock.polMap_injective | exact GlobalTheory.CCRFock.polMap_injective | (intros; apply GlobalTheory.CCRFock.polMap_injective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestFunctionsTransportLocalLatticeIsometriesStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.testFunctions_transport_localLatticeIsometries : ∀ (D : D7) (V V' : HSp D), V'.rank = V.rank → ∀ j : ∀ v, GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v, (∀ v, IsLatticeConj (frameLat V) (frameLat V') (j v)) → (∀ v g, j v g ∈ Kv V' v ↔ g ∈ Kv V v) ∧ ∀ (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V), ∃ (T' : TypeDataG V') (U' : AuxiliaryPlaceHermitianSpace V'), (NoFixed T → NoFixed T') ∧ ∀ (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) ff, IsTestFin T U μf ff → IsTestFin T' U' (fun v => (μf v).map (j v)) (transfer j ff) := by
  first | exact @GlobalTheory.LatTransport.isTestFin_transport | exact GlobalTheory.LatTransport.isTestFin_transport | (intros; apply GlobalTheory.LatTransport.isTestFin_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDistributionAutomorphySourceGroupStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaDistribution_automorphy_source_group : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (θ : InfFam D), IsInfFam θ → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ η, IsEtaTilde D η → ∀ (of oi : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))), IsFinWeil ψ S T ΛS ΛT (η ^ S.rank) (η ^ T.rank) of → IsInfWeil ψ θ S T oi → ∀ γ ∈ GQ S, ∀ f, IsThetaFunO ψ S T f → of (γ, 1) (oi (γ, 1) f) 0 = f 0 := by
  first | exact @GlobalTheory.DualSwap.automorphy_source | exact GlobalTheory.DualSwap.automorphy_source | (intros; apply GlobalTheory.DualSwap.automorphy_source <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionPullbackEqZeroOfNotDominantStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topSelfIntersection_pullback_eq_zero_of_not_dominant : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsProjOver q → topologicalKrullDim X ≤ D → topologicalKrullDim Y ≤ D → ∀ (π : Y ⟶ X), π (genericPoint Y) ≠ genericPoint X → ∀ B : LB X, B.IsLB → letI := GlobalTheory.algebraΓOfHom q; topSelfIntersection k (B.pull π) D = 0 := by
  first | exact @GlobalTheory.PullVanish.topSelf_pull_eq_zero_of_not_dominant | exact GlobalTheory.PullVanish.topSelf_pull_eq_zero_of_not_dominant | (intros; apply GlobalTheory.PullVanish.topSelf_pull_eq_zero_of_not_dominant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodConstantPolynomialsNeZeroStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tprod_constant_polynomials_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (P Q R S : ℕ),
    (PiTensorProduct.tprod ℂ fun _ : InfinitePlace F => (1 : Formalism.BasicNotions.TH.Pol P Q R S)) ≠ 0 := by
  first | exact @GlobalTheory.tprod_one_pol_ne_zero | exact GlobalTheory.tprod_one_pol_ne_zero | (intros; apply GlobalTheory.tprod_one_pol_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceFormMapSurjective
section
open NumberField

noncomputable section

namespace GlobalTheory.TraceDual

def traceFormMap (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] Module.Dual ℝ (κ → mixedEmbedding.mixedSpace F) :=
  LinearMap.mk₂ ℝ (fun Y X => -(2 * Real.pi) *
      ∑ i, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (X i * Y i))
    (fun Y₁ Y₂ X => by simp [mul_add, Finset.sum_add_distrib]; ring)
    (fun c Y X => by simp [Finset.mul_sum, mul_left_comm])
    (fun Y X₁ X₂ => by simp [add_mul, Finset.sum_add_distrib, mul_add]; ring)
    (fun c Y X => by simp [Finset.mul_sum, mul_left_comm])

theorem traceFormMap_apply (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (Y X : κ → mixedEmbedding.mixedSpace F) :
    traceFormMap F κ Y X = -(2 * Real.pi) *
      ∑ i, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (X i * Y i) := rfl

theorem traceFormMap_injective (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    Function.Injective (traceFormMap F κ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro Y hY
  have h0 := LinearMap.congr_fun hY (fun i => GlobalTheory.VacLn.TrNondeg.conjM (Y i))
  rw [traceFormMap_apply, LinearMap.zero_apply] at h0
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have h1 : ∑ i, Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (GlobalTheory.VacLn.TrNondeg.conjM (Y i) * Y i) = 0 := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd (neg_eq_zero.1 h) hpi
    · exact h
  have hnn : ∀ i, 0 ≤ Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (GlobalTheory.VacLn.TrNondeg.conjM (Y i) * Y i) := by
    intro i
    rw [GlobalTheory.VacLn.TrNondeg.trace_conjM_mul]
    exact add_nonneg (Finset.sum_nonneg fun w _ => sq_nonneg _)
      (Finset.sum_nonneg fun w _ => mul_nonneg (by norm_num) (Complex.normSq_nonneg _))
  have e := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn i).1 h1
  funext i
  exact GlobalTheory.VacLn.TrNondeg.eq_zero_of_trace_conjM_mul _ (e i (Finset.mem_univ _))

theorem traceFormMap_surjective (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    Function.Surjective (traceFormMap F κ) := by
  have h := Subspace.dual_finrank_eq (K := ℝ) (V := κ → mixedEmbedding.mixedSpace F)
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h.symm).1
    (traceFormMap_injective F κ)

theorem exists_trace_rep : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (L : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ), ∃ Y : κ → mixedEmbedding.mixedSpace F,
      ∀ X, L X = -(2 * Real.pi) * ∑ i, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (X i * Y i) := by
  intro F _ _ κ _ L
  obtain ⟨Y, hY⟩ := traceFormMap_surjective F κ L.toLinearMap
  exact ⟨Y, fun X => by rw [← traceFormMap_apply, hY]; rfl⟩

end GlobalTheory.TraceDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerDecompositionStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_centralizer_decomposition : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r → ∀ γ : Gp G, regular₂ G γ → ∀ δ z : Gr G r, IsNrm G r γ δ z → ∀ E : Finset (Gr G r), ∃ D : Finset (Gr G r), ∀ t : Gr G r, t * nrmG (sigG G r) r δ = nrmG (sigG G r) r δ * t → (∃ e ∈ E, ∃ k ∈ KHT p G.m G.n r G.Fw, t⁻¹ * δ * sigG G r t = e * k) → ∃ u ∈ GlobalTheory.BCT.twCent (sigG G r) δ, ∃ d ∈ D, ∃ k ∈ KHT p G.m G.n r G.Fw, t = u * d * k := by
  first | (exact @GlobalTheory.TwFin.main) | (exact GlobalTheory.TwFin.main) | (intros; apply GlobalTheory.TwFin.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralLevelFunctionInertEqLattic
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.TwOrbLevel

open GlobalTheory.TwLat

theorem twOrb_level_eq_stSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → qV E w = K.q ^ 2 → ∀ (k : ℕ) (t : K.O), K.Small t → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ (m : ℕ) (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K), Q.Monic → Q.natDegree = m → Q.Separable → IsCsr w Q → Algebra.adjoin K.E {(1 + algebraMap K.O B.A t * B.g)} = ⊤ → aeval (1 + algebraMap K.O B.A t * B.g) (Q.map e.symm.toRingHom) = 0 → Module.finrank K.E B.A = Q.natDegree → (1 + algebraMap K.O B.A t * B.g) * B.σ (1 + algebraMap K.O B.A t * B.g) = 1 → stTw m w Q (fun y : GLw m w => if y ∈ GlobalTheory.LFun.KGL w m ∧ nrmL m w y ∈ {g : GLw m w | g ∈ GlobalTheory.LFun.KGL w m ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0) = ((B.stSum : ℚ) : ℂ) := by
  intro E _ _ _ hE w hw K e hc hint hval hq k t ht htk m Q B hQm hQd hQs hQc hadj hQu hfin huσ
  set u : B.A := 1 + algebraMap K.O B.A t * B.g with hu_def
  obtain ⟨-, -, hθK, hnrm, -, -, -, -, -, -⟩ := GlobalTheory.BCT.ThBasic.twist_basic E hE m w
  set cong : Set (GLw m w) := {g : GLw m w | g ∈ GlobalTheory.LFun.KGL w m ∧ ∀ i j, Valued.v (g.val i j -
    (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} with hcong
  set f : GLw m w → ℂ := fun y => if y ∈ GlobalTheory.LFun.KGL w m ∧ nrmL m w y ∈ cong then 1 else 0 with hf
  set S : Set (GLw m w) := {y | (nrmL m w y).val.charpoly = Q} with hS
  show clSum (thL m w) (GlobalTheory.LFun.KGL w m) S (fun _ => 1) f = _
  have hfK : ∀ c ∈ GlobalTheory.LFun.KGL w m, ∀ y, f (c⁻¹ * y * thL m w c) = f y := by
    intro c hcK y
    have h1 : c⁻¹ * y * thL m w c ∈ GlobalTheory.LFun.KGL w m ↔ y ∈ GlobalTheory.LFun.KGL w m := by
      constructor
      · intro h
        have := mul_mem (mul_mem hcK h) (inv_mem (hθK c hcK))
        simpa [mul_assoc] using this
      · intro h
        exact mul_mem (mul_mem (inv_mem hcK) h) (hθK c hcK)
    have h2 : nrmL m w (c⁻¹ * y * thL m w c) ∈ cong ↔ nrmL m w y ∈ cong := by
      rw [hnrm]; exact GlobalTheory.T.principalCongruenceGL_conj_maxCompact_iff E w m k c _ hcK
    simp only [hf, h1, h2]
  have hf01 : ∀ y, f y = 0 ∨ f y = 1 := by
    intro y; simp only [hf]; split_ifs <;> simp
  have hSinv : ∀ y g, g⁻¹ * y * thL m w g ∈ S ↔ y ∈ S := by
    intro y g
    simp only [hS, Set.mem_setOf_eq, hnrm, Units.val_mul]
    rw [Matrix.coe_units_inv, Matrix.charpoly_units_conj']
  have hrstab : ∀ (δ x : GLw m w), (rStab fun k : GlobalTheory.LFun.KGL w m => f ((x * k)⁻¹ * δ * thL m w (x * k))).index ≠ 0 := by
    intro δ x
    have : rStab (fun k : GlobalTheory.LFun.KGL w m => f ((x * k)⁻¹ * δ * thL m w (x * k))) = ⊤ := by
      refine eq_top_iff.2 fun k' _ z => ?_
      have := hfK (k' : GLw m w) k'.2 ((x * ↑z)⁻¹ * δ * thL m w (x * ↑z))
      show f ((x * ↑(z * k'))⁻¹ * δ * thL m w (x * ↑(z * k'))) = f ((x * ↑z)⁻¹ * δ * thL m w (x * ↑z))
      rw [← this]
      congr 1
      simp only [Subgroup.coe_mul, map_mul, _root_.mul_inv_rev, mul_assoc]
    rw [this, Subgroup.index_top]; exact one_ne_zero
  have htwinv : ∀ y g, twOrb (thL m w) (GlobalTheory.LFun.KGL w m) (g⁻¹ * y * thL m w g) f = twOrb (thL m w) (GlobalTheory.LFun.KGL w m) y f :=
    fun y g => GlobalTheory.TwOrbConj.twOrb_twConj _ _ _ y g f (hrstab y)
  have hrank : Module.finrank K.E B.A = m := hfin.trans hQd
  let b : Module.Basis (Fin m) K.E B.A := Module.finBasisOfFinrankEq K.E B.A hrank
  have hgu : ∀ L : Submodule K.O B.A, (∀ y ∈ L, B.g * y ∈ L) → ∀ y ∈ L, u * y ∈ L := by
    intro L hg y hy
    rw [hu_def, add_mul, one_mul, mul_assoc]
    refine L.add_mem hy ?_
    rw [← Algebra.smul_def]
    exact L.smul_mem t (hg y hy)
  by_cases hui : IsIntegral K.O u
  · let Bu : GlobalTheory.UnitLemma.InvAlg K := { B with g := u }
    have hP : (LinearMap.mulLeft K.E u).charpoly = Q.map e.symm.toRingHom :=
      GlobalTheory.T.charpoly_mulLeft_generator_eq_map_symm K B _ e u Q hQm hadj hQu hfin
    have hsep : (Q.map e.symm.toRingHom).Separable := hQs.map
    obtain ⟨β₀, hβ₀, hX⟩ := GlobalTheory.UnitLemma.TwistUnit.twisted_unit_eq_unit K Bu huσ
      (by show (LinearMap.mulLeft K.E u).charpoly.Separable; rw [hP]; exact hsep) hui ((-1) ^ (m - 1))
      (neg_one_pow_eq_or B.A (m - 1))
    have hβ₀' : B.σ (β₀ : B.A) = β₀ * ((-1) ^ (m - 1) * u) := hβ₀
    have hgram : ∀ x : B.Aˣ, IsUnit (gram e b ((β₀ : B.A) * x)) := fun x =>
      GlobalTheory.T.separable_element_basis_integral E hE w hw K e hc hint hval B m b u _ hsep hQu hadj _ (β₀.isUnit.mul x.isUnit)
    have hσβ : ∀ x : B.Aˣ, B.σ (x : B.A) = x → B.σ ((β₀ : B.A) * x) = (β₀ * x) * ((-1) ^ (m - 1) * u) := by
      intro x hx
      rw [map_mul, hβ₀', hx]; ring
    have hN : ∀ x : B.Aˣ, B.σ (x : B.A) = x → (nrmL m w (dlt e b ((β₀ : B.A) * x))).val = mulMat e b u :=
      fun x hx => GlobalTheory.T.inertPlace_norm_gramInverse_eq_mulMatrix E hE w hw K e hc hint hval B m b u _ (hgram x) (hσβ x hx)
    have hcp : (mulMat e b u).charpoly = Q := by
      have h1 := Matrix.charpoly_map (LinearMap.toMatrix b b (LinearMap.mulLeft K.E u)) (e : K.E →+* w.adicCompletion E)
      have h2 : mulMat e b u = (LinearMap.toMatrix b b (LinearMap.mulLeft K.E u)).map (e : K.E →+* w.adicCompletion E) := rfl
      rw [h2, h1, LinearMap.charpoly_toMatrix, hP, Polynomial.map_map]
      ext n
      simp [Polynomial.coeff_map]
    obtain ⟨hΛK, hlat⟩ := GlobalTheory.T.latticeSpannedByGLColumns_eq_iff_GLint_coset E hE w hw K e hc hint hval B m b
    have hOrb : ∀ x : B.Aˣ, B.σ (x : B.A) = x →
        twOrb (thL m w) (GlobalTheory.LFun.KGL w m) (dlt e b ((β₀ : B.A) * x)) f = ((B.N x : ℚ) : ℂ) := by
      intro x hx
      obtain ⟨φ, hφv, hφc⟩ := GlobalTheory.T.twistedCentralizer_equiv_normOneTorus_nonsplit E hE w hw K e hc hint hval B m b u _ (β₀.isUnit.mul x.isUnit)
        (hσβ x hx) hadj (hgram x)
      refine GlobalTheory.T.twistedOrbitalIntegral_indicator_eq_latticeCount K B x (GLw m w) (thL m w) (GlobalTheory.LFun.KGL w m) _ f φ (lat e b) hfK hf01 hφc hΛK ?_ ?_
        (fun L hL => GlobalTheory.T.exists_GL_completion_lattice_eq_columns E hE w hw K e hc hint hval B m b L hL.1)
      · intro t' q
        refine GlobalTheory.T.latticeSpannedByGLColumns_mulLeftMatrix_eq_mul E hE w hw K e hc hint hval B m b _ q _ ?_
        rw [Units.val_mul, hφv t']
      · intro q
        have hf1 : f (q⁻¹ * dlt e b ((β₀ : B.A) * x) * thL m w q) = 1 ↔
            (q⁻¹ * dlt e b ((β₀ : B.A) * x) * thL m w q ∈ GlobalTheory.LFun.KGL w m ∧
              nrmL m w (q⁻¹ * dlt e b ((β₀ : B.A) * x) * thL m w q) ∈ cong) := by
          simp only [hf]; split_ifs with h <;> simp [h]
        rw [hf1, hnrm, GlobalTheory.T.twistedNorm_integral_iff_lattice_unimodular E hE w hw K e hc hint hval B m b _ (hgram x) q]
        have hlev : q⁻¹ * nrmL m w (dlt e b ((β₀ : B.A) * x)) * q ∈ cong ↔
            ∀ y ∈ lat e b q, B.g * y ∈ lat e b q :=
          GlobalTheory.T.principalCongruenceLevel_iff_lattice_stable E hE w hw K e hc hint hval B m b t k ht htk q _ (hN x hx)
        rw [hlev]
        have hXiff : (GlobalTheory.UnitLemma.IsLat K.O K.E (lat e b q) ∧ ∀ z, z ∈ lat e b q ↔
            ∀ y ∈ lat e b q, B.herm ((β₀ : B.A) * x) y z ∈ (algebraMap K.O K.E).range) ↔ lat e b q ∈ Bu.X x := by
          rw [← hX x hx]; rfl
        constructor
        · rintro ⟨hL, hg, hsd⟩
          exact ⟨(hXiff.2 ⟨hL, hgu _ hg, hsd⟩).2, hg⟩
        · rintro ⟨hun, hg⟩
          obtain ⟨hL, -, hsd⟩ := hXiff.1 ⟨hlat q, hun⟩
          exact ⟨hL, hg, hsd⟩
    have hsum := GlobalTheory.T.sum_twistedOrbitalIntegrals_eq_finsum_parametrised (GLw m w) (thL m w) (GlobalTheory.LFun.KGL w m) S f B.Cl
      (fun c => dlt e b ((β₀ : B.A) * ((Quot.out c).1 : B.Aˣ))) (fun c => ((B.N c.rep : ℚ) : ℂ))
      (fun c => by show (nrmL m w _).val.charpoly = Q; rw [hN _ (Quot.out c).2]; exact hcp)
      (by
        intro y hy
        obtain ⟨x, hx, g, rfl⟩ := GlobalTheory.T.exists_twistedConj_delta_of_unit_mod_norms E hE w hw K e hc hint hval B m b u Q hQs hQu hadj β₀ hβ₀' hgram y hy
        let c : B.Cl := Quot.mk _ ⟨x, hx⟩
        obtain ⟨a, ha⟩ := GlobalTheory.T.exists_norm_of_classOfFixedUnits_eq K B ⟨x, hx⟩ (Quot.out c) (Quot.out_eq c).symm
        obtain ⟨g', hg'⟩ := (GlobalTheory.T.twistedConj_iff_mul_norm_invAlg E hE w hw K e hc hint hval B m b u hadj β₀ hβ₀' hgram x (Quot.out c).1 hx
          (Quot.out c).2).2 ⟨a, ha⟩
        refine ⟨c, g'⁻¹ * g, ?_⟩
        show _ = _ * dlt e b ((β₀ : B.A) * ((Quot.out c).1 : B.Aˣ)) * _
        rw [hg']
        simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left])
      (by
        intro c c' hcc
        obtain ⟨a, ha⟩ := (GlobalTheory.T.twistedConj_iff_mul_norm_invAlg E hE w hw K e hc hint hval B m b u hadj β₀ hβ₀' hgram (Quot.out c).1
          (Quot.out c').1 (Quot.out c).2 (Quot.out c').2).1 hcc
        rw [← Quot.out_eq c, ← Quot.out_eq c']
        exact Quot.sound ⟨a, ha⟩)
      hSinv htwinv (fun c => hOrb _ (Quot.out c).2)
    rw [hsum]
    show _ = ((∑ᶠ c : B.Cl, B.N c.rep : ℚ) : ℂ)
    by_cases hfs : (Function.support fun c : B.Cl => B.N c.rep).Finite
    · exact (map_finsum (Rat.castHom ℂ) hfs).symm
    · have hfs' : ¬ (Function.support fun c : B.Cl => ((B.N c.rep : ℚ) : ℂ)).Finite := by
        simpa [Function.support] using hfs
      rw [finsum_of_infinite_support hfs, finsum_of_infinite_support hfs']
      simp
  · have hX0 : ∀ x : B.A, B.X x = ∅ := by
      intro x
      ext L
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨hL, hg, -⟩
      exact hui (GlobalTheory.T.isIntegral_of_preserves_fullLattice K B u L hL (hgu L hg))
    have hN0 : ∀ x : B.A, B.N x = 0 := by
      intro x
      unfold GlobalTheory.UnitLemma.InvAlg.N GlobalTheory.UnitLemma.orbSum
      haveI : IsEmpty (GlobalTheory.UnitLemma.Orb K.O B.T (B.X x)) := by
        constructor
        intro o
        induction o using Quot.ind with
        | mk L =>
          have h := (hX0 x).subset L.2
          simp at h
      exact finsum_of_isEmpty _
    have hf0 : ∀ y ∈ S, ∀ q : GLw m w, f (q⁻¹ * y * thL m w q) = 0 := by
      intro y hy q
      simp only [hf]
      rw [if_neg]
      rintro ⟨-, hn, -⟩
      exact hui (GlobalTheory.T.isIntegral_of_integral_matrix_charpoly_root E hE w hw K e hc hint hval B m b u Q hQm hQu _ hn ((hSinv y q).2 hy))
    have hst : B.stSum = 0 := by
      unfold GlobalTheory.UnitLemma.InvAlg.stSum
      simp [hN0]
    rw [hst, Rat.cast_zero]
    unfold clSum
    refine (finsum_congr fun c => ?_).trans finsum_zero
    split_ifs with hc'
    · have h0 := hf0 _ hc'
      simp only [twOrb, avg, h0, finsum_zero, mul_zero]
    · rfl

end GlobalTheory.TwOrbLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralRestrictedProductFinprodStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedOrbitalIntegral_restrictedProduct_finprod : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] [∀ v, IsTopologicalGroup (Y v)] [∀ v, T2Space (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (θ : X →* X) (θv : ∀ v, Y v →* Y v), (∀ v x, pf v (θ x) = θv v (pf v x)) → (∀ v, ∀ k ∈ K v, θv v k ∈ K v) → ∀ (δ : X) (f : X → ℂ) (fv : ∀ v, Y v → ℂ), (∀ x, f x = ∏ᶠ v, fv v (pf v x)) → (∀ v, ∀ a ∈ twCent (θv v) (pf v δ), ∀ b ∈ twCent (θv v) (pf v δ), a * b = b * a) → (∀ v (y : Y v), (rStab fun k : K v => fv v ((y * k)⁻¹ * pf v δ * θv v (y * k))).index ≠ 0) → (∀ v, {q : DoubleCoset.Quotient (twCent (θv v) (pf v δ) : Set (Y v)) (K v : Set (Y v)) | ∃ k ∈ K v, fv v ((Quotient.out q * k)⁻¹ * pf v δ * θv v (Quotient.out q * k)) ≠ 0}.Finite) → (∀ v (y : Y v), twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj y).toMonoidHom ≤ cptPart (twCent (θv v) (pf v δ)) ∧ (twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj y).toMonoidHom).relIndex (cptPart (twCent (θv v) (pf v δ))) ≠ 0) → (∀ᶠ v in cofinite, fv v = (K v : Set (Y v)).indicator 1 ∧ pf v δ ∈ K v ∧ cptPart (twCent (θv v) (pf v δ)) ≤ K v ∧ ∀ y, y⁻¹ * pf v δ * θv v y ∈ K v → ∃ t ∈ twCent (θv v) (pf v δ), ∃ k ∈ K v, y = t * k) → twOrb θ (⨅ v, (K v).comap (pf v)) δ f = ∏ᶠ v, twOrb (θv v) (K v) (pf v δ) (fv v) := by
  first | exact @GlobalTheory.EulerAbs.twOrb_restr_eq_finprod | exact GlobalTheory.EulerAbs.twOrb_restr_eq_finprod | (intros; apply GlobalTheory.EulerAbs.twOrb_restr_eq_finprod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFromBlocksNegOfDiagBasisTransport
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

theorem GlobalTheory.fromBlocks_unitary_transfer : ∀ (A O : Type) [CommRing A] [CommRing O] (ι : O →ₙ+* A) (γ : A →+* A) (c : O →+* O) (n : ℕ)
    (P K : Matrix (Fin n) (Fin n) A) (JL : Matrix (Fin n) (Fin n) O),
    Function.Injective ι → (∀ x, γ (ι x) = ι (c x)) → Pᵀ * K * P.map γ = JL.map ι →
    ∀ (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O),
    Mᵀ * Matrix.fromBlocks K 0 0 (-K) * M.map γ = Matrix.fromBlocks K 0 0 (-K) →
    M * Matrix.fromBlocks P 0 0 P = Matrix.fromBlocks P 0 0 P * G.map ι →
    Gᵀ * Matrix.fromBlocks JL 0 0 (-JL) * G.map c = Matrix.fromBlocks JL 0 0 (-JL) := by
  intro A O _ _ ι γ c n P K JL hinj hγ hP M G hM hG
  have hmul : ∀ {m : Type} [Fintype m] (X Y : Matrix m m O), (X * Y).map ι = X.map ι * Y.map ι := by
    intro m _ X Y; ext i j; simp [Matrix.mul_apply, map_sum]
  have hneg : (-JL).map ι = -(JL.map ι) := by ext i j; simp
  have hD : (Matrix.fromBlocks P 0 0 P)ᵀ * Matrix.fromBlocks K 0 0 (-K) * (Matrix.fromBlocks P 0 0 P).map γ
      = (Matrix.fromBlocks JL 0 0 (-JL)).map ι := by
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_map,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_map, hneg, ← hP]
    simp [Matrix.mul_neg, Matrix.neg_mul]
  have hc : (G.map c).map ι = (G.map ι).map γ := by
    ext i j; simp [hγ]
  apply Matrix.map_injective hinj
  show (Gᵀ * Matrix.fromBlocks JL 0 0 (-JL) * G.map c).map ι = (Matrix.fromBlocks JL 0 0 (-JL)).map ι
  rw [hmul, hmul, Matrix.transpose_map, hc]
  conv_lhs => rw [← hD]
  have hG' : (Matrix.fromBlocks P 0 0 P * G.map ι).map γ = (Matrix.fromBlocks P 0 0 P).map γ * (G.map ι).map γ := by
    rw [Matrix.map_mul]
  calc (G.map ι)ᵀ * ((Matrix.fromBlocks P 0 0 P)ᵀ * Matrix.fromBlocks K 0 0 (-K) * (Matrix.fromBlocks P 0 0 P).map γ) * (G.map ι).map γ
      = (Matrix.fromBlocks P 0 0 P * G.map ι)ᵀ * Matrix.fromBlocks K 0 0 (-K) * (Matrix.fromBlocks P 0 0 P * G.map ι).map γ := by
        rw [hG', Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = (M * Matrix.fromBlocks P 0 0 P)ᵀ * Matrix.fromBlocks K 0 0 (-K) * (M * Matrix.fromBlocks P 0 0 P).map γ := by rw [hG]
    _ = (Matrix.fromBlocks P 0 0 P)ᵀ * (Mᵀ * Matrix.fromBlocks K 0 0 (-K) * M.map γ) * (Matrix.fromBlocks P 0 0 P).map γ := by
        rw [Matrix.map_mul, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hM, hD]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeOperatorCommuteWeightVectorFunctionE
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.BCT.TrKer

theorem finsum_comp_eq_comp_finsum {ι V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (T : V →ₗ[ℂ] W) (g : ι → W →ₗ[ℂ] W) (h : ι → V →ₗ[ℂ] V) (hc : ∀ i, g i ∘ₗ T = T ∘ₗ h i)
    (hs : ∀ i, g i = 0 ↔ h i = 0) : (∑ᶠ i, g i) ∘ₗ T = T ∘ₗ ∑ᶠ i, h i := by
  have hg : Function.support g = Function.support h := by
    ext i; simp only [Function.mem_support, ne_eq, hs]
  by_cases hfin : (Function.support h).Finite
  · rw [finsum_eq_sum_of_support_subset g (s := hfin.toFinset) (by rw [hg]; simp),
      finsum_eq_sum_of_support_subset h (s := hfin.toFinset) (by simp)]
    ext x
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ => LinearMap.congr_fun (hc i) x
  · rw [finsum_of_infinite_support hfin, finsum_of_infinite_support (by rwa [hg])]
    simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem RF_apply' (x : finU E n) (φ : UA E n → ℂ) (g : UA E n) : RF E n x φ g = φ (g * x.1) := rfl

theorem RF_ne_zero (x : finU E n) : RF E n x ≠ 0 := by
  intro h
  have := congrFun (LinearMap.congr_fun h (fun _ => (1 : ℂ))) 1
  simp at this
  exact one_ne_zero this

theorem rightReg_dual_ne_zero (lam : InfinitePlace E → DomWeight n) [Nontrivial (Wsp lam)] (x : finU E n) :
    rightReg ℂ (finU E n) (Module.Dual ℂ (Wsp lam)) x ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : Wsp lam)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (Wsp lam), φ v ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ v).1 hc)
  intro h
  have := congrFun (LinearMap.congr_fun h (fun _ => φ)) 1
  have h2 : φ = 0 := by simpa [rightReg, LinearMap.funLeft] using this
  exact hφ (by rw [h2]; rfl)

theorem hop_phiFun (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w))
    (f : ∀ w : Pl E, UL n w → ℂ) (F : finU E n → Module.Dual ℂ (Wsp lam)) (w : Wsp lam) :
    hop S K' f (phiFun lam F w) = phiFun lam (hopM S lam K' f F) w := by
  rcases subsingleton_or_nontrivial (Wsp lam) with hW | hW
  · rw [Subsingleton.elim w 0]; simp
  set T : (finU E n → Module.Dual ℂ (Wsp lam)) →ₗ[ℂ] (UA E n → ℂ) := (phiFun lam).flip w with hT
  have key : (∑ᶠ q : finU E n ⧸ globLev S K', globFn S f q.out • (RF E n q.out ∘ₗ LinearMap.id)) ∘ₗ T =
      T ∘ₗ ∑ᶠ q : finU E n ⧸ globLev S K', globFn S f q.out •
        (rightReg ℂ (finU E n) (Module.Dual ℂ (Wsp lam)) q.out ∘ₗ LinearMap.id) := by
    refine finsum_comp_eq_comp_finsum T _ _ (fun q => ?_) (fun q => ?_)
    · ext G g
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, hT, LinearMap.flip_apply,
        LinearMap.map_smul, Pi.smul_apply]
      rw [RF_apply', phiFun_mul_fin]
    · rw [smul_eq_zero, smul_eq_zero, LinearMap.comp_id, LinearMap.comp_id]
      simp only [RF_ne_zero, rightReg_dual_ne_zero, or_false]
  have := LinearMap.congr_fun key F
  simp only [LinearMap.comp_apply, hT, LinearMap.flip_apply] at this
  simp only [hop, hopM, levOp, LinearMap.smul_apply, this, LinearMap.map_smul]

theorem hop_phiFun_comm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ) (F : finU E n → Module.Dual ℂ (Wsp lam)) (w : Wsp lam), hop S K' f (phiFun lam F w) = phiFun lam (hopM S lam K' f F) w :=
  fun _ _ _ _ _ S lam K' f F w => hop_phiFun S lam K' f F w

end GlobalTheory.BCT.TrKer
end
end

