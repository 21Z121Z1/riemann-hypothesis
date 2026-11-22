import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1362
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0048
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1204
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1201
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1361
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0144
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1327
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1363
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfVectorMultiplicationsGlobalResidues
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

set_option autoImplicit false

namespace GlobalTheory.HSShort.GlobWord

theorem shift_single {K : Type} [Field K] [NumberField K] (G : Geo K) (j : ℕ) (u : Fin G.N → K) (m : G.Sec j) :
    shift G u (Pi.single j m) = Pi.single (j + 1) (G.mulW j u m) := by
  funext i
  cases i with
  | zero => rw [Pi.single_eq_of_ne (Nat.succ_ne_zero j).symm]; rfl
  | succ i =>
    show G.mulW i u ((Pi.single j m : Tot G) i) = _
    by_cases h : i = j
    · subst h; rw [Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne (fun h' => h (Nat.succ_injective h')), map_zero]

theorem word_global : ∀ (K : Type) [Field K] [NumberField K] (G : Geo K) (t j : ℕ) (u : Fin t → Fin G.N → K), ∀ x ∈ G.global j, ∃ x' ∈ G.global (j + t), word (shift G) u (Pi.single j x) = Pi.single (j + t) x' ∧ ∀ (s : Fin G.D → Fin G.N → K) (hs : G.IsGood s) (δ : ℕ) (Co : Coord G hs δ) (p : Fin δ), Co.ev (j + t) (hs.res (j + t) x') p = (∏ q, ∑ k, u q k * Co.y p k) * Co.ev j (hs.res j x) p := by
  intro K _ _ G t j
  induction t with
  | zero =>
    intro u x hx
    exact ⟨x, hx, by simp [word], fun s hs δ Co p => by simp⟩
  | succ t ih =>
    intro u x hx
    obtain ⟨x', hx', hw, hr⟩ := ih (fun q => u q.succ) x hx
    refine ⟨G.mulW (j + t) (u 0) x', GlobalTheory.HilbertSamuel.Model.mulW_mem_global G (j + t) _ hx', ?_, fun s hs δ Co p => ?_⟩
    · unfold word at hw ⊢
      rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply, hw]
      exact shift_single G (j + t) (u 0) x'
    · show Co.ev (j + t + 1) (hs.res (j + t + 1) (G.mulW (j + t) (u 0) x')) p = _
      rw [hs.res_mulW, Co.mul]
      beta_reduce
      rw [hr, Fin.prod_univ_succ, mul_assoc]

end GlobalTheory.HSShort.GlobWord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoCoefficientRegularCharacterStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pseudo_coefficient_regular_character : DiscreteSeriesCharacter → ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (ρ : D.what₂.Tau) (μ : Measure (GArch D.sp.cm.sig V.gram (placeOf D ρ))) [μ.IsHaarMeasure]
    (f : GArch D.sp.cm.sig V.gram (placeOf D ρ) → ℂ), Formalism.QuantumDeterminants.IsHCParam (M.lam ρ) →
    (haveI := (M.ds ρ).1; IsPseudoCoeff (matAt V ρ) μ (dsRep M ρ) f) →
    ∀ (s : GArch D.sp.cm.sig V.gram (placeOf D ρ)), IsRegSS (matAt V ρ s) →
    IsCompact (cent s : Set (GArch D.sp.cm.sig V.gram (placeOf D ρ))) →
    ∀ (y : GArch D.sp.cm.sig V.gram (placeOf D ρ)) (θ : Fin V.rank → ℝ),
    frameMat M ρ (y⁻¹ * s * y) = Matrix.diagonal (fun a => Complex.exp (θ a * Complex.I)) →
    ∀ (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant],
    HasOrbInt μ s dt f (conj (dsChar (M.ε ρ) (M.lam ρ) θ) / dt.real univ) := by
  first | exact @GlobalTheory.EllipticOrb.orbInt_elliptic | exact GlobalTheory.EllipticOrb.orbInt_elliptic | (intros; apply GlobalTheory.EllipticOrb.orbInt_elliptic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuantumDetCentralCoeffsConj
section
noncomputable section

open Matrix GlobalTheory.TorFin Formalism.REAL

namespace GlobalTheory.CapFrame

variable {n : ℕ} {A : Type} [Ring A] [Algebra ℂ A]

theorem single_mul_single_one (a b c d : Fin n) :
    (Matrix.single a b (1 : ℂ)) * Matrix.single c d 1 = if b = c then Matrix.single a d 1 else 0 := by
  split_ifs with h
  · subst h; simp
  · exact Matrix.single_mul_single_of_ne a b c h 1 (c := (1 : ℂ))

theorem frame_glRel (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A) (hρ : IsLieRep ρ) (P P' : Matrix (Fin n) (Fin n) ℂ)
    (h : P * P' = 1) : GlRel (fun a b => ρ (P * Matrix.single a b 1 * P')) := by
  have h' : P' * P = 1 := mul_eq_one_comm.mp h
  intro a b c d
  rw [← hρ]
  have e : ∀ a b c d : Fin n, P * Matrix.single a b 1 * P' * (P * Matrix.single c d 1 * P') =
      P * (Matrix.single a b 1 * Matrix.single c d 1) * P' := by
    intro a b c d
    calc P * Matrix.single a b 1 * P' * (P * Matrix.single c d 1 * P')
        = P * Matrix.single a b 1 * (P' * P) * Matrix.single c d 1 * P' := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h', Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [e, e, single_mul_single_one, single_mul_single_one]
  split_ifs <;> simp [eq_comm]

theorem conj_single (P0 Q0 : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    P0 * Matrix.single a b 1 * Q0 = ∑ c, ∑ d, (P0 c a * Q0 b d) • Matrix.single c d (1 : ℂ) := by
  ext i j
  simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem qdet_frame_mem_adjoin (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A) (P P' : Matrix (Fin n) (Fin n) ℂ) (u : ℂ) :
    qdet (fun a b => ρ (P * Matrix.single a b 1 * P')) u ∈ Algebra.adjoin ℂ (Set.range ρ) := by
  unfold qdet qminor
  refine Subalgebra.sum_mem _ fun σ _ => Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) ?_
  refine Subalgebra.list_prod_mem _ fun x hx => ?_
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
  unfold Tm
  refine Subalgebra.add_mem _ ?_ (Algebra.subset_adjoin ⟨_, rfl⟩)
  split_ifs
  · exact Subalgebra.algebraMap_mem _ _
  · exact Subalgebra.zero_mem _

theorem qdet_frame_mem_invAlg (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A) (hρ : IsLieRep ρ) (P P' : Matrix (Fin n) (Fin n) ℂ)
    (h : P * P' = 1) (u : ℂ) : qdet (fun a b => ρ (P * Matrix.single a b 1 * P')) u ∈ invAlg ρ := by
  have h' : P' * P = 1 := mul_eq_one_comm.mp h
  refine mem_invAlg.mpr ⟨qdet_frame_mem_adjoin ρ P P' u, fun r g g' hg hr => ?_⟩
  have hg' : g' * g = 1 := mul_eq_one_comm.mp hg
  rw [GlobalTheory.CapAdInv.qdet_semiconj _ (fun a b => ρ (g * (P * Matrix.single a b 1 * P') * g')) r (fun a b => hr _) u]
  congr 1
  have hQP : (P' * g' * P) * (P' * g * P) = 1 := by
    calc (P' * g' * P) * (P' * g * P) = P' * g' * (P * P') * g * P := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h, Matrix.mul_one, Matrix.mul_assoc P' g' g, hg', Matrix.mul_one, h']
  rw [← GlobalTheory.CapAdInv.qdet_ad _ (frame_glRel ρ hρ P P' h) (P' * g * P) (P' * g' * P) hQP u]
  congr 1
  funext a b
  have e : g * (P * Matrix.single a b 1 * P') * g' = P * ((P' * g * P) * Matrix.single a b 1 * (P' * g' * P)) * P' := by
    calc g * (P * Matrix.single a b 1 * P') * g'
        = (P * P') * g * P * Matrix.single a b 1 * P' * g' * (P * P') := by
          rw [h, Matrix.one_mul, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [e, conj_single, Matrix.mul_sum, Matrix.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.mul_sum, Matrix.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, map_smul]

end GlobalTheory.CapFrame

open GlobalTheory.CapFrame in

theorem GlobalTheory.qdet_frame_coeff_mem_invAlg : ∀ (n : ℕ) (A : Type) [Ring A] [Algebra ℂ A]
    (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A), IsLieRep ρ → ∀ P P' : Matrix (Fin n) (Fin n) ℂ, P * P' = 1 →
    ∃ c : ℕ → A, c n = 1 ∧ (∀ k ≤ n, c k ∈ invAlg ρ) ∧
      ∀ u : ℂ, Formalism.REAL.qdet (fun a b => ρ (P * Matrix.single a b 1 * P')) u =
        ∑ k ∈ Finset.range (n + 1), u ^ k • c k := by
  intro n A _ _ ρ hρ P P' h
  obtain ⟨c, hcn, hc⟩ := GlobalTheory.qdet_polyMap_monic A n (fun a b => ρ (P * Matrix.single a b 1 * P'))
  refine ⟨c, hcn, fun k hk => ?_, hc⟩
  have hS : ∀ u : ℂ, ∑ k ∈ Finset.range (n + 1), u ^ k • c k ∈ Subalgebra.toSubmodule (invAlg ρ) := by
    intro u
    rw [← hc u]
    exact qdet_frame_mem_invAlg ρ hρ P P' h u
  exact GlobalTheory.T.coeff_mem_submodule_of_complex_poly_values_mem A (Subalgebra.toSubmodule (invAlg ρ)) (n + 1) c hS k (Nat.lt_succ_of_le hk)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPointsRestrictionSmoothRightDerivEq
section
noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic NormedSpace
open scoped ContDiff

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace GlobalTheory.HCA

theorem glRes_smooth_rightDeriv : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ),
    ∀ φ : Sm E a, ∀ x, (glH E a).IsSmoothFun (glRes φ.1 x) ∧
      ∀ X : glL E a, (glH E a).rightDeriv X (glRes φ.1 x) = glRes (lie E a (toL X.1) φ).1 x := by
  intro E _ _ _ a φ x
  let T : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap
  have hT : ∀ M, T M = toL M := fun _ => rfl
  have key : ∀ (g : glG E a) (Y : glL E a), glRes φ.1 x (g * (glH E a).expG Y) =
      chart φ.1 x (T ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * exp (Y : Matrix (Fin a) (Fin a) (Cinf E)))) := by
    intro g Y
    rw [hT]
    exact (chart_val φ.1 x ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ) * ((glH E a).expG Y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ))).symm
  have hs : (glH E a).IsSmoothFun (glRes φ.1 x) := by
    rw [IsExpLieAlgebra.isSmoothFun_iff]
    intro g
    have e : (fun Y : glL E a => glRes φ.1 x (g * (glH E a).expG Y)) =
        chart φ.1 x ∘ fun Y : glL E a => T ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * exp (Y : Matrix (Fin a) (Fin a) (Cinf E))) :=
      funext (key g)
    rw [e]
    have h1 : ContDiff ℝ ∞ (fun Y : glL E a => T ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * exp (Y : Matrix (Fin a) (Fin a) (Cinf E)))) :=
      T.contDiff.comp (contDiff_const.mul ((contDiff_exp ℝ _).comp (glL E a).subtypeL.contDiff))
    exact (φ.2 x).comp_contDiff h1 fun Y =>
      ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ) * ((glH E a).expG Y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ)).isUnit
  refine ⟨hs, fun X => funext fun g => ?_⟩
  have h2 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (X : Matrix (Fin a) (Fin a) (Cinf E)) (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h2
  have hc : HasDerivAt (fun t : ℝ => toL (((glH E a).expG (t • X) : (Matrix (Fin a) (Fin a) (Cinf E))ˣ) : Matrix (Fin a) (Fin a) (Cinf E)))
      (toL X.1) 0 := T.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
  have h0 : (((glH E a).expG ((0 : ℝ) • X) : glG E a) : (Matrix (Fin a) (Fin a) (Cinf E))ˣ) = 1 := by
    ext : 1
    simp
  have h3 := hasDerivAt_curve φ (x * infGL E a (g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ))
    (fun t => ((glH E a).expG (t • X) : (Matrix (Fin a) (Fin a) (Cinf E))ˣ)) (toL X.1) h0 hc
  have ef : (fun t : ℝ => glRes φ.1 x (g * (glH E a).expG (t • X))) = fun t : ℝ =>
      φ.1 (x * infGL E a (g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ) *
        infGL E a ((glH E a).expG (t • X) : (Matrix (Fin a) (Fin a) (Cinf E))ˣ)) := by
    funext t
    simp only [glRes, Subgroup.coe_mul, map_mul, mul_assoc]
  have h4 := (glH E a).hasDerivAt_rightDeriv hs X g
  rw [ef] at h4
  exact h4.unique h3

end GlobalTheory.HCA

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealScalarArchimedeanAdeleSmulMatrixRealPlace
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section
namespace GlobalTheory.RealScalar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem ext_realAd (r : ℝ) (w : InfinitePlace F) :
    InfinitePlace.Completion.extensionEmbedding w (evInf F w (realAd F r)) = (r : ℂ) := by
  set y : mixedEmbedding.mixedSpace F := algebraMap ℝ _ r with hy
  set a := (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y with ha
  have hev : evInf F w (realAd F r) = a w := rfl
  have hay : InfiniteAdeleRing.ringEquiv_mixedSpace F a = y := by rw [ha]; exact RingEquiv.apply_symm_apply _ _
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at hay
  rw [hev]
  rcases w.isReal_or_isComplex with hw | hw
  · have h1 := congrFun (congrArg Prod.fst hay) ⟨w, hw⟩
    simp only [hy] at h1
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw]
    rw [show (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (a w)) = r from by simpa using h1]
  · have h1 := congrFun (congrArg Prod.snd hay) ⟨w, hw⟩
    simpa [hy] using h1

theorem piInf_algebraMap {w : InfinitePlace F} (τ : EmbOver E w) (x : AF F) :
    piInf τ (algebraMap (AF F) (AE F E) x) = InfinitePlace.Completion.extensionEmbedding w (evInf F w x) := by
  change infEmb τ (compInf F E w (x ⊗ₜ[F] (1 : E))) = _
  rw [compInf]
  change infEmb τ ((evInf F w x) ⊗ₜ[F] ((AlgHom.id F E) 1)) = _
  rw [infEmb_tmul]
  simp

theorem piInf_realAd_smul {w : InfinitePlace F} (τ : EmbOver E w) (r : ℝ) (z : AE F E) :
    piInf τ (realAd F r • z) = (r : ℂ) * piInf τ z := by
  rw [Algebra.smul_def, map_mul, piInf_algebraMap, ext_realAd]

theorem realAd_smul_map : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β : Type}
    (τ : ∀ w : InfinitePlace F, EmbOver E w), IsCMExt F E σ →
    ∀ (u : Matrix α β (AE F E)) (r : ℝ) (w : InfinitePlace F),
      (realAd F r • u).map (piInf (τ w)) = (r : ℂ) • u.map (piInf (τ w)) := by
  intro F E _ _ _ _ _ σ α β τ _ u r w
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  exact piInf_realAd_smul (τ w) r (u i j)

end GlobalTheory.RealScalar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOrbitConjCompactModCentralizerUnitary
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct Pointwise

noncomputable section
namespace GlobalTheory.OrbitU

theorem locCpt (E : Type) [Field E] [NumberField E] (w : Pl E) : LocallyCompactSpace (w.adicCompletion E) := by
  have h : (w.adicCompletionIntegers E : Set (w.adicCompletion E)) =
      ((Valued.v : Valuation (w.adicCompletion E) _).integer : Set (w.adicCompletion E)) := by
    ext x
    simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.mem_integer_iff]
  have ho : IsOpen (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := by
    rw [h]; exact Valued.isOpen_integer _
  exact (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers E w).locallyCompactSpace_of_mem_nhds_of_addGroup
    (ho.mem_nhds (zero_mem _))

theorem glTop (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n : ℕ) : LocallyCompactSpace (GLw n w) ∧ SigmaCompactSpace (GLw n w) := by
  haveI := locCpt E w
  haveI hM : LocallyCompactSpace (Matrix (Fin n) (Fin n) (w.adicCompletion E)) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → w.adicCompletion E))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
  haveI : ProperSpace (w.adicCompletion E) := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (w.adicCompletion E)) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → w.adicCompletion E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : LocallyCompactSpace (GLw n w) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (GLw n w) := Units.isClosedEmbedding_embedProduct.isEmbedding.secondCountableTopology
  exact ⟨inferInstance, sigmaCompactSpace_of_locallyCompact_secondCountable⟩

def starU {K : Type} [Field K] {n : ℕ} (σ : K →+* K) (g : GL (Fin n) K) : GL (Fin n) K where
  val := cT σ (g : Matrix (Fin n) (Fin n) K)
  inv := cT σ ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  val_inv := by rw [← cT_mul, Units.inv_mul, cT_one]
  inv_val := by rw [← cT_mul, Units.mul_inv, cT_one]

theorem orbit_cpt_U : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : UL n w), y.1.val.charpoly.Separable → ∀ C : Set (UL n w), IsCompact C → ∃ Ω : Set (UL n w), IsCompact Ω ∧ ∀ g : UL n w, g⁻¹ * y * g ∈ C → ∃ t ∈ twCent (MonoidHom.id (UL n w)) y, ∃ ω ∈ Ω, g = t * ω := by
  intro E _ _ _ hE n w y hy C hC
  have hCG : IsCompact (Subtype.val '' C : Set (GLw n w)) := hC.image continuous_subtype_val
  obtain ⟨D, hD, hDg⟩ := GlobalTheory.OrbitCptW.orbit_cpt_w E hE n w y.1 hy _ hCG
  have hcl := (GlobalTheory.LocFinU.isClosed_UL n w).isClosedEmbedding_subtypeVal
  have hgC : ∀ g : UL n w, g⁻¹ * y * g ∈ C → g.1⁻¹ * y.1 * g.1 ∈ (Subtype.val '' C : Set (GLw n w)) :=
    fun g hg => ⟨_, hg, rfl⟩
  by_cases hs : IsSplitAt w
  · have hUL : ∀ g : GLw n w, g ∈ UL n w := fun g => by unfold UL; rw [if_pos hs]; trivial
    refine ⟨Subtype.val ⁻¹' D, hcl.isCompact_preimage hD, fun g hg => ?_⟩
    obtain ⟨z, hz, d, hd, hgd⟩ := hDg g.1 (hgC g hg)
    exact ⟨⟨z, hUL z⟩, Subtype.ext hz, ⟨d, hUL d⟩, hd, Subtype.ext hgd⟩
  obtain ⟨hσc, hσi, -⟩ := GlobalTheory.ConjAtPlace.main E hE w
  set σ := cj w with hσ
  have hmemU : ∀ g : GLw n w, g ∈ UL n w ↔ cT σ g.val * g.val = 1 := by
    intro g; unfold UL; rw [if_neg hs]; show cT σ _ * 1 * _ = 1 ↔ _; rw [Matrix.mul_one]
  have hcTc : Continuous fun M : Matrix (Fin n) (Fin n) (w.adicCompletion E) => cT σ M :=
    (continuous_id.matrix_map hσc).matrix_transpose
  have hcc : ∀ M : Matrix (Fin n) (Fin n) (w.adicCompletion E), cT σ (cT σ M) = M := by
    intro M; ext i j; simp [cT, hσi]
  have hstarc : Continuous (starU σ : GLw n w → GLw n w) := by
    rw [Units.continuous_iff]
    exact ⟨hcTc.comp Units.continuous_val, hcTc.comp Units.continuous_coe_inv⟩
  obtain ⟨lc, sc⟩ := glTop E w n
  let Z : Subgroup (GLw n w) := Subgroup.centralizer {y.1}
  have hZ : ∀ z : GLw n w, z ∈ Z ↔ z.val * y.1.val = y.1.val * z.val := by
    intro z
    rw [Subgroup.mem_centralizer_singleton_iff, Units.ext_iff, Units.val_mul, Units.val_mul]
  have hZc : IsClosed (Z : Set (GLw n w)) := by
    have : (Z : Set (GLw n w)) = {z | z * y.1 = y.1 * z} := by
      ext z; exact Subgroup.mem_centralizer_singleton_iff
    rw [this]
    exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  haveI : LocallyCompactSpace Z := hZc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SigmaCompactSpace Z := hZc.isClosedEmbedding_subtypeVal.sigmaCompactSpace
  have hcomm : ∀ a b : Z, a * b = b * a := fun a b => Subtype.ext (Units.ext
    (GlobalTheory.commute_of_commute_separable_charpoly _ n y.1.val a.1.val b.1.val hy ((hZ _).1 a.2) ((hZ _).1 b.2)))
  have hyU : cT σ y.1.val * y.1.val = 1 := (hmemU _).1 y.2
  have hyU' : y.1.val * cT σ y.1.val = 1 := mul_eq_one_comm.1 hyU
  have hst : ∀ z ∈ Z, starU σ z ∈ Z := by
    intro z hz
    rw [hZ] at hz ⊢
    have h1 : cT σ y.1.val * cT σ z.val = cT σ z.val * cT σ y.1.val := by rw [← cT_mul, ← cT_mul, hz]
    show cT σ z.val * y.1.val = y.1.val * cT σ z.val
    calc cT σ z.val * y.1.val = (y.1.val * cT σ y.1.val) * cT σ z.val * y.1.val := by rw [hyU', Matrix.one_mul]
      _ = y.1.val * (cT σ y.1.val * cT σ z.val) * y.1.val := by simp only [Matrix.mul_assoc]
      _ = y.1.val * (cT σ z.val * cT σ y.1.val) * y.1.val := by rw [h1]
      _ = y.1.val * cT σ z.val * (cT σ y.1.val * y.1.val) := by simp only [Matrix.mul_assoc]
      _ = y.1.val * cT σ z.val := by rw [hyU, Matrix.mul_one]
  let τ : Z →* Z :=
    { toFun := fun z => ⟨starU σ z.1, hst _ z.2⟩
      map_one' := Subtype.ext (Units.ext (cT_one σ))
      map_mul' := fun a b => by
        have : (⟨starU σ (a * b).1, hst _ (a * b).2⟩ : Z) = ⟨starU σ b.1, hst _ b.2⟩ * ⟨starU σ a.1, hst _ a.2⟩ :=
          Subtype.ext (Units.ext (by show cT σ (a.1.val * b.1.val) = cT σ b.1.val * cT σ a.1.val; exact cT_mul σ _ _))
        rw [this, hcomm] }
  have hτ : ∀ z : Z, ((τ z : Z) : GLw n w) = starU σ z.1 := fun z => rfl
  have hτc : Continuous τ := continuous_induced_rng.2 (hstarc.comp continuous_subtype_val)
  have hτi : ∀ z, τ (τ z) = z := fun z => Subtype.ext (Units.ext (hcc _))
  have hsq : ∃ W ∈ nhds (1 : Z), ∀ s ∈ W, τ s = s → ∃ r : Z, τ r = r ∧ r * r = s := by
    obtain ⟨W, hW, hWs⟩ : ∃ W ∈ nhds (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)), ∀ s ∈ W, ∃ r : Matrix (Fin n) (Fin n) (w.adicCompletion E), r * r = s ∧ (∀ a : Matrix (Fin n) (Fin n) (w.adicCompletion E), a * s = s * a → a * r = r * a) ∧ ((s.map σ)ᵀ = s → (r.map σ)ᵀ = r) := by
      haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
      letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
      exact GlobalTheory.T.exists_matrix_sqrt_near_one_ultrametric (w.adicCompletion E) n σ hσc
    refine ⟨(fun z : Z => (z.1 : Matrix (Fin n) (Fin n) _)) ⁻¹' W,
      (Units.continuous_val.comp continuous_subtype_val).continuousAt.preimage_mem_nhds (by simpa using hW), ?_⟩
    intro s hs hτs
    obtain ⟨r, hrr, hrc, hrs⟩ := hWs _ hs
    have hsv : cT σ s.1.val = s.1.val := by
      have h := congrArg (fun u : Z => u.1.val) hτs
      exact h
    have hrr' : r * r = s.1.val := hrr
    have hu : IsUnit r := isUnit_of_mul_isUnit_left (hrr'.symm ▸ s.1.isUnit)
    have hrZ : hu.unit ∈ Z := (hZ _).2 (hrc _ ((hZ _).1 s.2).symm).symm
    refine ⟨⟨hu.unit, hrZ⟩, Subtype.ext (Units.ext (hrs hsv)), Subtype.ext (Units.ext hrr')⟩
  let DZ : Set Z := Subtype.val ⁻¹' ((fun d : GLw n w => starU σ d⁻¹ * d⁻¹) '' D)
  have hDZ : IsCompact DZ := hZc.isClosedEmbedding_subtypeVal.isCompact_preimage
    (hD.image ((hstarc.comp continuous_inv).mul continuous_inv))
  obtain ⟨B, hB, hBz⟩ := GlobalTheory.T.exists_compact_mod_normOneKernel_involution Z hcomm τ hτc hτi hsq DZ hDZ
  refine ⟨Subtype.val ⁻¹' ((Subtype.val '' B : Set (GLw n w)) * D),
    hcl.isCompact_preimage ((hB.image continuous_subtype_val).mul hD), fun g hg => ?_⟩
  obtain ⟨z, hz, d, hd, hgd⟩ := hDg g.1 (hgC g hg)
  have hzZ : z ∈ Z := (hZ z).2 (by simpa using congrArg Units.val hz)
  have hgU : cT σ g.1.val * g.1.val = 1 := (hmemU _).1 g.2
  have hN : τ ⟨z, hzZ⟩ * ⟨z, hzZ⟩ ∈ DZ := by
    refine ⟨d, hd, Units.ext ?_⟩
    have hg' : g.1.val = z.val * d.val := by rw [hgd, Units.val_mul]
    rw [hg', cT_mul] at hgU
    have e1 : cT σ ((d⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _) * cT σ d.val = 1 := by
      rw [← cT_mul, Units.mul_inv, cT_one]
    show cT σ ((d⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _) * ((d⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _) = cT σ z.val * z.val
    calc cT σ ((d⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _) * ((d⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _)
        = cT σ ((d⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _) * (cT σ d.val * cT σ z.val * (z.val * d.val)) * ((d⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _) := by
          rw [hgU, Matrix.mul_one]
      _ = (cT σ ((d⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _) * cT σ d.val) * (cT σ z.val * z.val) * (d.val * ((d⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _)) := by
          simp only [Matrix.mul_assoc]
      _ = cT σ z.val * z.val := by rw [e1, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨t, ht, b, hb, hzt⟩ := hBz _ hN
  have htU : t.1 ∈ UL n w := by
    have h := congrArg (fun u : Z => u.1.val) ht
    exact (hmemU _).2 h
  have hgt : g.1 = t.1 * (b.1 * d) := by
    rw [hgd, ← mul_assoc]; exact congrArg (· * d) (congrArg Subtype.val hzt)
  have hωU : b.1 * d ∈ UL n w := by
    have : b.1 * d = t.1⁻¹ * g.1 := by rw [hgt, inv_mul_cancel_left]
    rw [this]; exact (UL n w).mul_mem ((UL n w).inv_mem htU) g.2
  refine ⟨⟨t.1, htU⟩, Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 t.2), ⟨b.1 * d, hωU⟩,
    ⟨b.1, ⟨b, hb, rfl⟩, d, hd, rfl⟩, Subtype.ext hgt⟩

end GlobalTheory.OrbitU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexSupSpanSingletonEqAbsNormStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_sup_span_singleton_eq_absNorm_of_isMaximal : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (N₀ : Submodule (𝓞 F) V) (u : V) (p : Ideal (𝓞 F)), p.IsMaximal → u ∉ N₀ → (∀ π ∈ p, π • u ∈ N₀) → N₀.toAddSubgroup.relIndex (N₀ ⊔ Submodule.span (𝓞 F) {u}).toAddSubgroup = Ideal.absNorm p := by
  first | exact @GlobalTheory.relIndex_sup_span_singleton_eq_absNorm | exact GlobalTheory.relIndex_sup_span_singleton_eq_absNorm | (intros; apply GlobalTheory.relIndex_sup_span_singleton_eq_absNorm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightLieDerivativeRealEntryPolynomialFunctionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightLieDerivative_realEntryPolynomialFunction : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), RealPoints θ V → ∀ (τ : D.what₂.Tau) (X : LieAt V τ) (P : PolyE V), lieDer V (expInf θ V) (atPlace V τ X) (polyFun θ V P) = polyFun θ V (matDer τ X.1 P) := by
  first | exact @GlobalTheory.PolyRightDeriv.lieDer_polyFun | exact GlobalTheory.PolyRightDeriv.lieDer_polyFun | (intros; apply GlobalTheory.PolyRightDeriv.lieDer_polyFun <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowTypePartLeEigensystemPartStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTypePart_le_eigensystemPart : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, Core R F → SchurAll R → ∀ SF, IsSF R SF → ∀ {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (PY : principalLevelFrame.RowPsi (Yc D 0) n) (PW : ∀ i, principalLevelFrame.RowPsi (Wc D i) n), StdPsi hF PY → (∀ i, StdPsi hF (PW i)) → ∀ π i0 c, principalLevelFrame.IsEigOf (PW i0) (levS _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A)))) (levChi _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A)))) SF π c → ∀ b, ∀ U ∈ principalLevelFrame.isotE R.θ PY (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F b))) (levChi _ (R.βY 0) (R.dat0 (R.levR F b))) R.e0 π, ∃ x ∈ EEc R SF c, R.HE.e x = U := by
  first | exact @GlobalTheory.TypePart.isotE_sub_eigenpart | exact GlobalTheory.TypePart.isotE_sub_eigenpart | (intros; apply GlobalTheory.TypePart.isotE_sub_eigenpart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondKindCoordinatesInfiniteAdelicUnitaryPointsStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut Filter Topology
open scoped TensorProduct ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secondKindCoordinates_infiniteAdelicUnitaryPoints : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∃ (m : ℕ) (η : Fin m → ℝ → GAd σ J) (s : GAd σ J → Fin m → ℝ), (∀ i, IsRealLine σ J (η i)) ∧ Tendsto s (𝓝[(infPts σ J : Set (GAd σ J))] 1) (𝓝 0) ∧ ∀ᶠ x in 𝓝[(infPts σ J : Set (GAd σ J))] 1, x = (List.ofFn fun i => η i (s x i)).prod := by
  first | exact @GlobalTheory.infPts_secondKind_chart | exact GlobalTheory.infPts_secondKind_chart | (intros; apply GlobalTheory.infPts_secondKind_chart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfIntegralKrullDimEqStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_of_integral_krullDim_eq : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp F) (n : ℕ), Smooth q → topologicalKrullDim X = n → SmoothOfRelativeDimension n q := by
  first | exact @GlobalTheory.RelDimOfDim.smoothOfRelativeDimension_of_topologicalKrullDim_eq | exact GlobalTheory.RelDimOfDim.smoothOfRelativeDimension_of_topologicalKrullDim_eq | (intros; apply GlobalTheory.RelDimOfDim.smoothOfRelativeDimension_of_topologicalKrullDim_eq <;> assumption)
end

