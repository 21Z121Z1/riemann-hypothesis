import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeDegreeGrowthChowFormIntegrality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1550
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1325
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1478
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1612
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1614
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GoodFormsSpanInduced
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0110
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCentralIdempotentOfGoodSeriesIdempotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1615
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1606

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankGrowthLineBundleSectionsLeImageForms
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.CompHt
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open AlgebraicGeometry Filter GlobalTheory.Twist GlobalTheory.Points

namespace GlobalTheory.SecGrowth

section Ratio

variable {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]

def ratioSub (ev : V →ₗ[K] Ω) : Subfield Ω where
  carrier := {r | ∃ (e : ℕ) (h : Ω), h ∈ ((LinearMap.range ev) ^ e : Submodule K Ω) ∧ h ≠ 0 ∧
    r * h ∈ ((LinearMap.range ev) ^ e : Submodule K Ω)}
  mul_mem' := by
    rintro a c ⟨e1, h1, m1, n1, p1⟩ ⟨e2, h2, m2, n2, p2⟩
    refine ⟨e1 + e2, h1 * h2, ?_, mul_ne_zero n1 n2, ?_⟩
    · rw [pow_add]; exact Submodule.mul_mem_mul m1 m2
    · rw [pow_add, show a * c * (h1 * h2) = (a * h1) * (c * h2) by ring]; exact Submodule.mul_mem_mul p1 p2
  one_mem' := ⟨0, 1, by rw [pow_zero]; exact Submodule.mem_one.2 ⟨1, map_one _⟩, one_ne_zero,
    by rw [one_mul, pow_zero]; exact Submodule.mem_one.2 ⟨1, map_one _⟩⟩
  add_mem' := by
    rintro a c ⟨e1, h1, m1, n1, p1⟩ ⟨e2, h2, m2, n2, p2⟩
    refine ⟨e1 + e2, h1 * h2, ?_, mul_ne_zero n1 n2, ?_⟩
    · rw [pow_add]; exact Submodule.mul_mem_mul m1 m2
    · rw [pow_add, show (a + c) * (h1 * h2) = (a * h1) * h2 + h1 * (c * h2) by ring]
      exact add_mem (Submodule.mul_mem_mul p1 m2) (Submodule.mul_mem_mul m1 p2)
  zero_mem' := ⟨0, 1, by rw [pow_zero]; exact Submodule.mem_one.2 ⟨1, map_one _⟩, one_ne_zero,
    by rw [zero_mul]; exact zero_mem _⟩
  neg_mem' := by
    rintro a ⟨e, h, m, n, p⟩
    exact ⟨e, h, m, n, by rw [neg_mul]; exact neg_mem p⟩
  inv_mem' := by
    rintro a ⟨e, h, m, n, p⟩
    by_cases ha : a = 0
    · refine ⟨e, h, m, n, ?_⟩
      rw [ha, inv_zero, zero_mul]; exact zero_mem _
    · exact ⟨e, a * h, p, mul_ne_zero ha n, by rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]; exact m⟩

theorem algebraMap_mem_ratioSub (ev : V →ₗ[K] Ω) (c : K) : algebraMap K Ω c ∈ ratioSub ev :=
  ⟨0, 1, by rw [pow_zero]; exact Submodule.mem_one.2 ⟨1, map_one _⟩, one_ne_zero,
    by rw [mul_one, pow_zero]; exact Submodule.mem_one.2 ⟨c, rfl⟩⟩

theorem div_mem_ratioSub (ev : V →ₗ[K] Ω) (v w : V) : ev v / ev w ∈ ratioSub ev := by
  by_cases hw : ev w = 0
  · rw [hw, div_zero]; exact zero_mem _
  · refine ⟨1, ev w, by rw [pow_one]; exact LinearMap.mem_range_self ev w, hw, ?_⟩
    rw [div_mul_cancel₀ _ hw, pow_one]; exact LinearMap.mem_range_self ev v

theorem isRatio_of_mem {ev : V →ₗ[K] Ω} {τ : ℕ} {t w : Ω} (hw : w ∈ LinearMap.range ev) (hw0 : w ≠ 0)
    (ht : t / w ^ τ ∈ ratioSub ev) : DegCmp.IsRatio ev τ t := by
  obtain ⟨e, h, m, n, p⟩ := ht
  refine ⟨e, h, m, n, ?_⟩
  have : t * h = w ^ τ * (t / w ^ τ * h) := by field_simp
  rw [this, pow_add]
  exact Submodule.mul_mem_mul (Submodule.pow_mem_pow _ hw τ) p

end Ratio

section Integral

variable {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]

theorem eval₂_mem_coneAlg (ev : V →ₗ[K] Ω) {r : ℕ} (v : Fin r → V) (g : MvPolynomial (Fin r) K) :
    eval₂ (Polynomial.C.comp (algebraMap K Ω)) (fun i => Polynomial.C (ev (v i)) * Polynomial.X) g ∈
      DegCmp.coneAlg ev := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    rw [eval₂_C, RingHom.comp_apply, ← Polynomial.algebraMap_apply]
    exact Subalgebra.algebraMap_mem _ a
  | add p q hp hq => rw [eval₂_add]; exact add_mem hp hq
  | mul_X p i hp =>
    rw [eval₂_mul, eval₂_X]
    refine mul_mem hp ?_
    rw [mul_comm]
    exact Algebra.subset_adjoin ⟨v i, rfl⟩

theorem isIntDeg_of_eq {ev : V →ₗ[K] Ω} {r : ℕ} (v : Fin r → V) {τ : ℕ} {t : Ω} {n : ℕ}
    (c : Fin n → MvPolynomial (Fin r) K)
    (h : (Polynomial.C t * Polynomial.X ^ τ) ^ n + ∑ k, eval₂ (Polynomial.C.comp (algebraMap K Ω))
      (fun i => Polynomial.C (ev (v i)) * Polynomial.X) (c k) * (Polynomial.C t * Polynomial.X ^ τ) ^ (k : ℕ) = 0) :
    DegCmp.IsIntDeg ev τ t := by
  let c' : Fin n → DegCmp.coneAlg ev := fun k => ⟨_, eval₂_mem_coneAlg ev v (c k)⟩
  refine ⟨Polynomial.X ^ n + ∑ k : Fin n, Polynomial.C (c' k) * Polynomial.X ^ (k : ℕ),
    Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt c'), ?_⟩
  rw [mul_comm (Polynomial.X ^ τ)]
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_finset_sum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X_pow]
  exact h

end Integral

variable {k : Type} [Field k] (S : LinSys k)

theorem comb_single (i : Fin S.N) : S.comb (Pi.single i 1) = S.b i := by
  rw [LinSys.comb, Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, map_zero, zero_smul])
    (fun h => (h (Finset.mem_univ i)).elim), Pi.single_eq_same, map_one, one_smul]

theorem sec_eq_zero_of_generic [IsReduced S.Y] {η : S.Y} (hη : IsGenericPoint η Set.univ) {m : ℤ}
    (s : (lbZPow S.L m).Sec) (h : η ∉ nonzeroLocus s) : s = 0 := by
  refine zglobal_ext fun i => ?_
  rw [zfun_zero, ← basicOpen_eq_bot_iff, basicOpen_zfun, eq_bot_iff]
  intro y hy
  exact (h ((hη.mem_open_set_iff (nonzeroLocus s).isOpen).2 ⟨y, trivial, hy.2⟩)).elim

theorem growth_mono (D : ℕ) {r r' : ℕ → ℕ∞} (h : ∀ τ, r τ ≤ r' τ) : growth D r ≤ growth D r' :=
  limsup_le_limsup (Eventually.of_forall fun τ => by
    simp only
    gcongr
    exact h τ)

theorem finrank_le_toENat (R M : Type) [Field R] [AddCommGroup M] [Module R M] :
    (Module.finrank R M : ℕ∞) ≤ Cardinal.toENat (Module.rank R M) := by
  by_cases h : Module.Finite R M
  · rw [← Module.finrank_eq_rank]; simp
  · rw [Module.finrank_of_not_finite h]; simp

def powValLin {Ω : Type} [Field Ω] [Algebra k Ω] (x : S.Pt Ω) (m : ℕ) :
    letI : Module k (lbPow S.L m).Sec := Module.compHom _ (algebraMap k Γ(S.Y, ⊤))
    (lbPow S.L m).Sec →ₗ[k] Ω :=
  letI : Module k (lbPow S.L m).Sec := Module.compHom _ (algebraMap k Γ(S.Y, ⊤))
  { toFun := fun s => S.powVal (m := (m : ℤ)) x.1 s
    map_add' := fun s t => by
      change S.powVal x.1 (s + t) = S.powVal x.1 s + S.powVal x.1 t
      rw [LinSys.powVal, LinSys.powVal, LinSys.powVal, zfun_add]
      exact valR_add x.1 _ (S.le_chartAt x.1) _ _
    map_smul' := fun c s => by
      rw [RingHom.id_apply, Algebra.smul_def]
      have e : c • s = algebraMap k Γ(S.Y, ⊤) c • s := rfl
      change S.powVal x.1 (c • s) = _
      rw [e]
      rw [LinSys.powVal, LinSys.powVal, zfun_smul]
      exact (valR_mul x.1 _ (S.le_chartAt x.1) _ _).trans (congrArg (· * _)
        ((valR_res x.1 le_top (S.le_chartAt x.1) _).trans ((S.valR_algebraMap x.1 c).trans
          (congrFun (congrArg DFunLike.coe (LinSys.baseHom_ptOver x)) c)))) }

theorem rankGrowth_lineBundleSections_le_image_forms : ∀ (k : Type) [Field k] [CharZero k] (S : LinSys k), S.IsVariety → S.BasePointFree →
    S.Birational → growth S.D (fun m => (lbH0 k (lbPow S.L m) : ℕ∞)) ≤
      growth S.D (fun m => (Module.finrank k (quotPiece S.imageIdeal (m : ℤ)) : ℕ∞)) := by
  intro k _ _ S hS hb hbir
  obtain ⟨η, hη, hrat⟩ := hbir
  have : IsIntegral S.Y := HeightExists.isIntegral hS
  letI : Algebra k (S.Y.residueField η) := (S.baseHom (resPt η)).toAlgebra
  let x : S.Pt (S.Y.residueField η) := ⟨resPt η, S.comp_str _⟩
  have hx : IsGenericPoint (ptOf x.1) Set.univ := by rw [ptOf_resPt]; exact hη
  let b := Pi.basisFun k (Fin S.N)
  let ev := b.constr k (S.coords (resPt η))
  have hev : ∀ j, ev (b j) = S.coords (resPt η) j := fun j => b.constr_basis k _ j
  have hI : S.imageIdeal = imageIdeal ev b := by
    rw [imageIdeal_eq_coneIdeal_of_generic k _ S x hx 1 (S.coords (resPt η)) one_ne_zero (one_smul _ _).symm,
      CompHt.imageIdeal]
    exact congrArg _ (funext fun j => (hev j).symm)
  have hR : (fun m : ℕ => (Module.finrank k (quotPiece S.imageIdeal (m : ℤ)) : ℕ∞)) =
      fun m => DegCmp.hilb ev (1 * m) := by
    funext m
    rw [one_mul, hI, DegCmp.hilb_eq_finrank_quotPiece k _ _ ev S.N b m]
  rw [hR]
  letI (m : ℕ) : Module k (lbPow S.L m).Sec := Module.compHom _ (algebraMap k Γ(S.Y, ⊤))
  haveI (m : ℕ) : IsScalarTower k Γ(S.Y, ⊤) (lbPow S.L m).Sec := IsScalarTower.of_compHom _ _ _
  have hinj : ∀ m, Function.Injective (powValLin S x m) := fun m => by
    refine (injective_iff_map_eq_zero _).2 fun s hs => sec_eq_zero_of_generic S hη (m := (m : ℤ)) s fun hm => ?_
    rw [← ptOf_resPt η] at hm
    exact (S.powVal_ne_zero_iff (resPt η) s).2 hm hs
  refine le_trans (growth_mono S.D fun m => ?_)
    (ConeDeg.growth_rank_le ev S.D 1 le_rfl (fun m => LinearMap.range (powValLin S x m)) ?_)
  · rw [rank_range_of_injective _ (hinj m), lineBundleGlobalSectionsDim_eq_finrank]
    exact finrank_le_toENat _ _
  · intro m t ht
    obtain ⟨s, rfl⟩ := ht
    rw [one_mul]
    obtain ⟨j, hj⟩ := Function.ne_iff.1 (hb.coords_ne_zero (resPt η))
    have hyj : S.coords (resPt η) j ≠ 0 := hj
    refine ⟨?_, ?_⟩
    · obtain ⟨n, c, hc⟩ := isIntegral_coneRing_of_forall_valuationSubring k (S.Y.residueField η) (algebraMap k _)
        S.N m (S.coords (resPt η)) (powValLin S x m s) fun V hV => by
          obtain ⟨i, hi, hV'⟩ := LinSys.exists_ratio_mem_of_point S hS S.N m (fun i => Pi.single i 1) s
            (fun y => by
              obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hb.ge (Set.mem_univ y))
              exact ⟨i, by rw [comb_single]; exact hi⟩) (resPt η) V hV
          have e : S.val (resPt η) (S.comb (Pi.single i 1)) = S.coords (resPt η) i := by rw [comb_single]; rfl
          rw [e] at hi hV'
          exact ⟨i, hi, hV'⟩
      exact isIntDeg_of_eq b c (by simpa only [hev] using hc)
    · refine isRatio_of_mem ⟨b j, hev j⟩ hyj ?_
      have hle : S.ratioField (resPt η) ≤ ratioSub ev := Subfield.closure_le.2 (Set.union_subset
        (by rintro _ ⟨c, rfl⟩; exact algebraMap_mem_ratioSub ev c)
        (by rintro _ ⟨i, i', rfl⟩; rw [← hev i, ← hev i']; exact div_mem_ratioSub ev _ _))
      exact hle (hrat ▸ Subfield.mem_top _)

end GlobalTheory.SecGrowth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnipotentRadicalEqLeviMulUnipotentStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_unipotentRadical_eq_levi_mul_unipotent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ S T : Finset (Fin r), S ⊆ T → ∀ γ ∈ ratPts σ J, γ ∈ GlobalTheory.StdPar.unip σ J X T →
        ∃ m ∈ ratPts σ J, m ∈ GlobalTheory.StdPar.levi σ J X Y S ∧ ∃ ν ∈ GlobalTheory.StdPar.unip σ J X S, γ = m * ν := by
  first | exact @GlobalTheory.RatLevi.rat_unip_eq_levi_mul_unip | exact GlobalTheory.RatLevi.rat_unip_eq_levi_mul_unip | (intros; apply GlobalTheory.RatLevi.rat_unip_eq_levi_mul_unip <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelDimLeOfIsClosedImmersionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relDim_le_of_smooth_of_isClosedImmersion : ∀ (k : Type) [Field k] (N G : Over (Sp k)) (ν : N ⟶ G), IsClosedImmersion ν.left → Nonempty N.left → ∀ g g' : ℕ, SmoothOfRelativeDimension g G.hom → SmoothOfRelativeDimension g' N.hom → g' ≤ g := by
  first | exact @GlobalTheory.relDim_le_of_isClosedImmersion | exact GlobalTheory.relDim_le_of_isClosedImmersion | (intros; apply GlobalTheory.relDim_le_of_isClosedImmersion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeGenericPointNeZeroProjectiveSameDim
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DominantProjDegree

theorem residueDegree_ne_zero_of_map_genericPoint : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsProjOver p → IsProjOver q → topologicalKrullDim X = D → topologicalKrullDim Y = D → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 := by
  intro k _ X Y _ _ p q D hp hq hX hY π hπ hη
  obtain ⟨N, i, hi, hcomp⟩ := hp
  obtain ⟨M, j, hj, hcomp'⟩ := hq
  haveI : IsProper (PSpace.str k N) := isProper_str k N
  haveI : IsProper (PSpace.str k M) := isProper_str k M
  haveI : IsProper p := by rw [← hcomp]; infer_instance
  haveI : IsProper (π ≫ p) := by rw [hπ, ← hcomp']; infer_instance
  haveI : IsProper π := IsProper.of_comp π p
  have hcl : IsClosed (Set.range π) := π.isClosedMap.isClosed_range
  have hsurj : Surjective π := ⟨fun x => by
    have : genericPoint X ∈ Set.range π := ⟨_, hη⟩
    exact (genericPoint_specializes x).mem_closed hcl this⟩
  exact GlobalTheory.GenFinite.residueDegree_genericPoint_ne_zero k Y X p π D inferInstance inferInstance
    hsurj hY hX

end GlobalTheory.DominantProjDegree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldInertiaFixedIsAlgClosedStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueField_inertiaFixed_isAlgClosed_alt : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → IsAlgClosed (IsLocalRing.ResidueField (V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω))) := by
  first | exact @GlobalTheory.InertiaRes.residueField_inertiaFixed_isAlgClosed | exact GlobalTheory.InertiaRes.residueField_inertiaFixed_isAlgClosed | (intros; apply GlobalTheory.InertiaRes.residueField_inertiaFixed_isAlgClosed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResiduePerfectAndCharStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_perfect_and_char_alt : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [PerfectField (ResidueField R)] (L W : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Algebra W L] [IsFractionRing W L], IsAbove R K (algebraMap W L).range → PerfectField (ResidueField W) ∧ ∀ m : ℕ, (m : ResidueField R) ≠ 0 → (m : ResidueField W) ≠ 0 := by
  first | exact @GlobalTheory.AbVarRedRes.residue_perfect_and_char | exact GlobalTheory.AbVarRedRes.residue_perfect_and_char | (intros; apply GlobalTheory.AbVarRedRes.residue_perfect_and_char <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedBlockSelfApply
section
noncomputable section

namespace GlobalTheory.LevelSpanCompare

section Move

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

theorem reflects_half_of_move {ρ : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ} {gM gA : Dw.La →ₗ[𝓞 E] Dw.La}
    (h : IsLevMove ρ ν gM gA) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Xo.X) (b : KA l →+* k)
    (hx : x ≫ Xo.s = spMap b) (a : Dw.La) (ha : gM a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) :
    a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
  obtain ⟨hs, hM, -⟩ := h
  obtain ⟨-, J, -, -, hJM⟩ := Xo.univ.geom k (x ≫ ρ) b (by rw [Category.assoc, hs]; exact hx)
  have h1 : a ∈ (l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) • (⊤ : Submodule (𝓞 E) Dw.La) := by
    rw [l.coprime]; simp
  rw [Submodule.sup_smul] at h1
  obtain ⟨b, hb, a', ha', rfl⟩ := Submodule.mem_sup.1 h1
  have hgb : gM b ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
    have := Submodule.mem_map_of_mem (f := gM) hb
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this
  have hga : gM a' ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
    have := Submodule.sub_mem _ ha hgb
    simpa using this
  have e1 : ρ ≫ (Xo.univ.eta a').left = ρ ≫ (Xo.univ.eta 0).left := by
    rw [← hM a', ← hM 0, Xo.univ.eta_ker _ hga, Xo.univ.eta_ker (gM 0) (by simp)]
  have e5 : J.ev l.M a' = J.ev l.M 0 := by
    rw [← hJM _ ha', ← hJM _ (Submodule.zero_mem _)]
    ext
    simpa using congrArg (x ≫ ·) e1
  have hM0 : 0 < l.M := by have := l.three_le; omega
  have e6 : J.ev l.M 0 = 1 := (J.ker l.M hM0 0).2 ⟨0, by simp⟩
  obtain ⟨b', hb'⟩ := (J.ker l.M hM0 a').1 (e5.trans e6)
  refine Submodule.add_mem _ hb ?_
  rw [hb', ← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul (GlobalTheory.LevelGroupTest.natCast_mem_half l) trivial

theorem levR_unique (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (gM : Dw.La →ₗ[𝓞 E] Dw.La)
    {S : Type} [CommRing S] [Algebra c.F S] [Nontrivial S] {y y' y'' : FrPt Xo c S}
    (h' : levR (gM, LinearMap.id) y y') (h'' : levR (gM, LinearMap.id) y y'') : y' = y'' := by
  obtain ⟨ρ, ν, i, h, hm⟩ := h'
  obtain ⟨ρ', ν', i', g, gm⟩ := h''
  obtain ⟨m, hmax⟩ := Ideal.exists_maximal S
  letI : Field (S ⧸ m) := Ideal.Quotient.field m
  let φ : S →+* AlgebraicClosure (S ⧸ m) := (algebraMap (S ⧸ m) _).comp (Ideal.Quotient.mk m)
  have hinj := reflects_half_of_move h (AlgebraicClosure (S ⧸ m)) (spMap φ ≫ y.x)
    (φ.comp ((algebraMap c.F S).comp (IntermediateField.inclusion c.le).toRingHom)) (by
      rw [Category.assoc, y.x_over]
      unfold sOf spMap
      rw [← Spec.map_comp]; rfl)
  obtain ⟨rfl, e⟩ := GlobalTheory.T.levelMove_moduli_unique_universalTriple E H Dw l Xo c ρ ρ' ν ν' _ _ _ _ hpq (fun a => by simp) (fun a => ⟨0, by simp⟩) i i' h g
    (GlobalTheory.exists_sim_of_aut_mod E H Dw l l.A gM hpq l.A_pos hA hinj)
  exact (GlobalTheory.T.existsUnique_framedPoint_move_universalTriple E H Dw l Xo c ρ ν h.1 S y).2 y' y'' ν' e.symm hm gm

end Move

section Idem

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GoodLatCompare

def ofList {G L : Type} [Group G] [Finite G] [Field L] (eC : G → L) : MonoidAlgebra L G :=
  MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm eC)

end Idem

section Framed

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Herm Formalism.UG Matrix
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

variable {β : GL (Fin n) (E ⊗[F] Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}

end Framed

section Swap

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Herm Formalism.UG Matrix
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def sw (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] : Af F ⊗[F] E ≃+* E ⊗[F] Af F :=
  (Algebra.TensorProduct.comm F (Af F) E).toRingEquiv

def clos (F : Type) [Field F] [NumberField F] [Algebra F E] (Λ : Submodule (𝓞 E) (Fin n → E)) :
    AddSubgroup (Fin n → Af F ⊗[F] E) :=
  AddSubgroup.closure {z | ∃ a : Af F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ ∃ x ∈ Λ, z = fun i => a ⊗ₜ x i}

variable {β : GL (Fin n) (E ⊗[F] Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}

end Swap

section Half

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Lev Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}

end Half

end GlobalTheory.LevelSpanCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingAutFixingSmallFieldFixesDeltaValuesStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR.Links Formalism.L2.Host GlobalTheory.SeriesTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringAut_fixing_smallField_fixes_delta_values : ∀ {D : D7} (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (χ : HChar D.host.E),
    ChrEq (ρ.B i j b).de.chi χ → χ.ValuesIn 0 (embLL0 D) → ∀ τ : ℂ ≃+* ℂ, (∀ y, τ (embLL0 D y) = embLL0 D y) →
    ∀ σ, τ (ρ.eO i b (algebraMap (D.ntw.O0 i) (D.ntw.O i)
        ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i))) =
      ρ.eO i b (algebraMap (D.ntw.O0 i) (D.ntw.O i) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)) := by
  first | exact @GlobalTheory.DeltaFixed.aut_fixes_delta_values | exact GlobalTheory.DeltaFixed.aut_fixes_delta_values | (intros; apply GlobalTheory.DeltaFixed.aut_fixes_delta_values <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerDerivativeSliceDirectionalAddPhaseStatement
section
open IsDedekindDomain NumberField
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schroedingerDerivative_slice_directional_add_phase : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ),
    (∀ z, ψ (GlobalTheory.WeilL2Words.arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z)) →
    ∀ (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → FiniteAdeleRing (𝓞 F) F),
      Differentiable ℝ (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) →
      ∀ (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) (x : κ → mixedEmbedding.mixedSpace F),
        GlobalTheory.WeilL2Words.dS F ψ h Φ (GlobalTheory.WeilCont.adeleJoin F x y) =
          fderiv ℝ (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x h.1 +
            2 * Real.pi * Complex.I * (ℓ (∑ k, x k * h.2 k) : ℂ) * Φ (GlobalTheory.WeilCont.adeleJoin F x y) := by
  first | exact @GlobalTheory.WeilL2Words.dS_adeleJoin_eq | exact GlobalTheory.WeilL2Words.dS_adeleJoin_eq | (intros; apply GlobalTheory.WeilL2Words.dS_adeleJoin_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearModelFixesUnitSectionAbelian
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.SemilinearModel

theorem unit_section_semilinear : ∀ (W K' : Type) [CommRing W] [IsDomain W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ (σ : K' →+* K') (τ : W →+* W) (φ : G.left ⟶ G.left) (ρ : pullback G.hom (spMap (algebraMap W K')) ⟶ pullback G.hom (spMap (algebraMap W K'))), (∀ x : W, σ (algebraMap W K' x) = algebraMap W K' (τ x)) → φ ≫ G.hom = G.hom ≫ spMap τ → pullback.fst G.hom (spMap (algebraMap W K')) ≫ φ = ρ ≫ pullback.fst G.hom (spMap (algebraMap W K')) → ∀ (e₀ : Sp W ⟶ G.left), e₀ ≫ G.hom = 𝟙 _ → ∀ x : Sp K' ⟶ pullback G.hom (spMap (algebraMap W K')), x ≫ pullback.fst G.hom (spMap (algebraMap W K')) = spMap (algebraMap W K') ≫ e₀ → x ≫ ρ = spMap σ ≫ x → e₀ ≫ φ = spMap τ ≫ e₀ := by
  intro W K' _ _ _ _ _ G _ hG σ τ φ ρ hστ hφ hρ e₀ he x hx hxρ
  haveI := hG.proper
  have hj : spMap σ ≫ spMap (algebraMap W K') = spMap (algebraMap W K') ≫ spMap τ := by
    unfold spMap
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext y
    simp [hστ]
  haveI : IsDominant (spMap (algebraMap W K')) := by
    refine ⟨?_⟩
    have := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap W K')).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective W K')]; exact bot_le)
    exact this
  refine ext_of_isDominant_of_isSeparated G.hom ?_ (spMap (algebraMap W K')) ?_
  · rw [Category.assoc, hφ, ← Category.assoc, he, Category.assoc, he]; simp
  · rw [← Category.assoc, ← hx, Category.assoc, hρ, ← Category.assoc, hxρ, Category.assoc, hx, ← Category.assoc, hj, Category.assoc]
end GlobalTheory.SemilinearModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepClosureFiniteExtPowMemRangeStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sepClosure_exists_pow_mem_range_of_finiteDimensional : ∀ (K L Ω Ω' : Type) [Field K] [Field L] [Field Ω] [Field Ω'] [Algebra K L] [FiniteDimensional K L] [Algebra K Ω] [IsSepClosure K Ω] [Algebra L Ω'] [IsSepClosure L Ω'] [Algebra K Ω'] [IsScalarTower K L Ω'] (j : Ω →ₐ[K] Ω') (y : Ω'), ∃ (m : ℕ) (x : Ω), 0 < m ∧ y ^ m = j x ∧ ∀ a b : Ω', (a - b) ^ m = a ^ m - b ^ m := by
  first | exact @GlobalTheory.Published.AbVarRed.sepClosure_finiteExt_pow_mem_range | exact GlobalTheory.Published.AbVarRed.sepClosure_finiteExt_pow_mem_range | (intros; apply GlobalTheory.Published.AbVarRed.sepClosure_finiteExt_pow_mem_range <;> assumption)
end

