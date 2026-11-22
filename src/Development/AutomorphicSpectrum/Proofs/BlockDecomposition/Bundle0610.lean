import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0583
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.UnlinkedIrreducibility.StdIrrQuotGeneric
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0777
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0585
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0058
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteGlobalStability.GenStable
import GroundTheory.AutomorphicForms.GL2.FiniteAdeleDecomp
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.InterpolationL2Bound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0586
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0575
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0558
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0011
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.HasInfCharOfIsRegAlg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0544
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0033
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0564

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheetDensityLogNormFormula
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ.ArchEq

section Torus

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem eval_torus_of_homog {s : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a) (c : K → ℂ)
    (u : (Σ k, ι k) → ℂ) :
    eval (fun p => c p.1 * u p) (map (Int.castRingHom ℂ) s) =
      (∏ k, c k ^ a k) * eval u (map (Int.castRingHom ℂ) s) := by
  rw [MvPolynomial.eval_map, MvPolynomial.eval_map, MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hprod : ∏ p, (c p.1 * u p) ^ d p = (∏ k, c k ^ a k) * ∏ p, u p ^ d p := by
    simp only [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, c k ^ d ⟨k, i⟩ = c k ^ a k
    rw [Finset.prod_pow_eq_pow_sum, hs d hd k]
  rw [hprod]
  ring

private theorem ratio_cancel {a b F G H : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * F / (b * G) / (a / b * H) = F / G / H := by
  by_cases hG : G = 0
  · simp [hG]
  by_cases hH : H = 0
  · simp [hH]
  field_simp

theorem logNormRat_torus {P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)} {A : HermLine ι} {f g : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι}
    (h : IsRatSectionOn P A f g) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ) :
    logNormRat A f g (fun p => c p.1 * z p) = logNormRat A f g z := by
  obtain ⟨α, β, hf, hg, -, -, hd⟩ := h
  have hne : ∀ (a : K → ℕ), ‖∏ k, c k ^ a k‖ ≠ 0 := fun a =>
    norm_ne_zero_iff.2 (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k))
  have hab : ∏ k, ‖c k‖ ^ A.a k = ‖∏ k, c k ^ α k‖ / ‖∏ k, c k ^ β k‖ := by
    rw [norm_prod, norm_prod, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← hd k, zpow_sub₀ (norm_ne_zero_iff.2 (hc k)), norm_pow, norm_pow, zpow_natCast, zpow_natCast]
  unfold logNormRat
  rw [eval_torus_of_homog hf, eval_torus_of_homog hg, A.smul c z hc, norm_mul, norm_mul, hab,
    ratio_cancel (hne α) (hne β)]

end Torus

theorem sheetDensity_eq_of_isSheet : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (P : Ideal (Pol n)) (D : ℕ) (Ψ : GlobalTheory.CompanionTheory.MixZ.ArchEq.LinProj n D)
    (B A : HermLine (Bk n)) (f g : Pol n), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (D + 1) → IsGoodProj P Ψ → IsSmoothHerm B →
    IsRatSectionOn P A f g → ∀ᵐ v : Fin D → ℂ, ∀ w γ, IsSheet P Ψ v w γ →
      sheetDensity P Ψ (pot fun _ : Fin D => B) (logNormRat A f g) v w =
        logNormRat A f g (γ v) * maDensity (fun _ y' => Real.log (B.h (γ y'))) v := by
  intro m n P D Ψ B A f g hP hΨ hB hA
  let A' : HermLine (Bk n) := ReciprocityTheory.ChartRestriction.G.AI.I2.constLine 1
  have hA1 : ∀ z, ReciprocityTheory.ChartRestriction.G.Geo.logNorm A' 1 z = 1 := fun z => by
    simp [ReciprocityTheory.ChartRestriction.G.Geo.logNorm, A', ReciprocityTheory.ChartRestriction.G.AI.I2.constLine, HermLine.ofWeight, Real.exp_neg]
  have hAs : IsSmoothHerm A' := contDiffOn_const
  have hs : ReciprocityTheory.ChartRestriction.G.Geo.IsSectionOn P A' 1 := by
    refine ⟨0, fun k => by simp [A', ReciprocityTheory.ChartRestriction.G.AI.I2.constLine, HermLine.ofWeight], fun d hd k => ?_, fun h => ?_⟩
    · rw [MvPolynomial.support_one, Finset.mem_singleton] at hd
      subst hd
      simp
    · exact hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  filter_upwards [ReciprocityTheory.ChartRestriction.G.Geo.sheetIndep (Fin (m + 1)) (Bk n) P D Ψ (fun _ => B) A' 1 hP hΨ (fun _ => hB) hAs hs]
    with v hind w γ hγ
  have hex : ∃ γ, IsSheet P Ψ v w γ := ⟨γ, hγ⟩
  have hc := hex.choose_spec
  have h1 := hind w _ γ hc hγ
  simp only [hA1, one_mul] at h1
  have hval : logNormRat A f g (hex.choose v) = logNormRat A f g (γ v) := by
    obtain ⟨c, hcne, hcz⟩ := ReciprocityTheory.ChartRestriction.G.Geo.sameOrbit_of_segre hγ.2.self_of_nhds.2.1.1 1 one_ne_zero
      (by rw [one_smul, hc.1, hγ.1])
    rw [hcz]
    exact logNormRat_torus hA hcne _
  unfold sheetDensity
  rw [dif_pos hex, hval]
  exact congrArg (logNormRat A f g (γ v) * ·) h1

end GlobalTheory.CompanionTheory.MixZ.ArchEq
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothWeightPullbackChartFormulaStatement
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_weight_pullback_chart_formula : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {T : Type}
    [TopologicalSpace T] (A : FinHolAtlas D T) (F : T → GlobalTheory.CxPts q σ) (hF : Continuous F),
    (∀ (W : X.Opens) (f : Γ(X, W)), A.HoloOn (F ⁻¹' ptsIn q σ W) (ev q σ W f ∘ F)) →
    ∀ {B : LB X} (φ : GlobalTheory.Weight q σ B), φ.IsCInf → ∀ (c : GlobalTheory.AlgChart q σ D) (j : Fin A.n) (u : Fin D → ℂ),
      u ∈ (A.chart j).target → F ((A.chart j).symm u) ∈ c.e.source →
      AnalyticAt ℂ (c.finChart ∘ F ∘ (A.chart j).symm) u ∧
      locDens A (fun _ => φ.locPot.pullback F hF) j u =
        ‖LinearMap.det (fderiv ℂ (c.finChart ∘ F ∘ (A.chart j).symm) u :
          (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))‖ ^ 2 * c.chernDens φ (F ((A.chart j).symm u)) := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.PullDens.locDens_pullback_eq | exact GlobalTheory.CompanionTheory.MixZ.PullDens.locDens_pullback_eq | (intros; apply GlobalTheory.CompanionTheory.MixZ.PullDens.locDens_pullback_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothWeightPullbackIsPotentialStatement
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_weight_pullback_is_potential : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {T : Type}
    [TopologicalSpace T] (A : FinHolAtlas D T) (F : T → GlobalTheory.CxPts q σ) (hF : Continuous F),
    (∀ (W : X.Opens) (f : Γ(X, W)), A.HoloOn (F ⁻¹' ptsIn q σ W) (ev q σ W f ∘ F)) →
    ∀ {B : LB X} (φ : GlobalTheory.Weight q σ B), φ.IsCInf → IsPotential A (φ.locPot.pullback F hF) := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.isPotential_pullback_locPot | exact GlobalTheory.CompanionTheory.MixZ.isPotential_pullback_locPot | (intros; apply GlobalTheory.CompanionTheory.MixZ.isPotential_pullback_locPot <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardQuotientGenericOfIrreducible
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

noncomputable section

namespace GlobalTheory.CompanionTheory.BZSegQuot

theorem stdQuotGeneric_of_irr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.BZSeg.StdIrrQuotGeneric k → GlobalTheory.BZSeg.ProdIrrFiniteLength k →
    GlobalTheory.BZSeg.StdQuotGeneric k := by
  intro k _ _ _ _ hI hL h N Δ x hd hΔ ho W _ _ τ f hf hW
  have hs : IsSmooth τ := (IsSubquotient.of_surjective f hf).isSmooth (isSmooth_prodIrr x hd)
  have hl : HasFiniteLength τ := IsFiniteLength.of_surjective (hL h N x hd)
    (f := Representation.IntertwiningMap.equivLinearMapAsModule _ τ f) hf
  obtain ⟨Y, _, _, τ', -, hi, q, hq⟩ := GlobalTheory.SmGL.IrrQuot.exists_irreducible_smooth_quotient τ hs hl hW
  obtain ⟨ψ, hc, h1, hg⟩ := hI h N Δ x hd hΔ ho Y τ' (q.comp f) (hq.comp hf) hi
  refine ⟨ψ, hc, h1, nontrivial_twJacquet_of_surjective q.toLinearMap hq (fun u v => ?_) hg⟩
  refine Submodule.subset_span ⟨u, q v, ?_⟩
  rw [map_sub, map_smul]
  exact congrArg (· - _) (q.isIntertwining _ _ (u : GL (Fin N) k) v)

end GlobalTheory.CompanionTheory.BZSegQuot

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummablePeriodicBoundByDenominatorStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_periodic_bound_by_denominator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (Λ : AddSubgroup (hermE σ n)) (t : F), t ≠ 0 → ∀ τ : ℕ, 0 < τ →
    (∀ c ∈ hermO σ n, ((τ : F) / t) • c ∈ Λ) →
    ∀ g : hermE σ n → ℝ, (∀ c, 0 ≤ g c) → (∀ c, ∀ l ∈ Λ, g (c + l) = g c) →
    ∀ C s : ℝ, (∀ c, g c ≤ C * (delta (t • c).1 : ℝ) ^ (-s)) →
    Summable (fun x : hermE σ n ⧸ hermO σ n => (delta (Quotient.out x).1 : ℝ) ^ (-s)) →
    Summable (fun x : hermE σ n ⧸ Λ => g (Quotient.out x)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.summable_quot_of_le_delta_rpow | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.summable_quot_of_le_delta_rpow | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.summable_quot_of_le_delta_rpow <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TauL
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection
open scoped NumberField.AdeleRing ValuativeRel ENNReal
open Ad3 Ad3.K Ad3.K.GPK

namespace GlobalTheory.CompanionTheory.GPKIntB

variable {K : Type} [Field K] [NumberField K]

def cU (a : (InfiniteAdeleRing K)ˣ) : ℂˣ :=
  Units.map (InfinitePlace.Completion.extensionEmbedding (wC K)).toMonoidHom
    (Units.map (Pi.evalMonoidHom (fun w : InfinitePlace K => w.Completion) (wC K)) a)

def cA (u : InfiniteAdeleRing K) : ℂ := InfinitePlace.Completion.extensionEmbedding (wC K) (u (wC K))

def wF (Wf : ∀ v : PlK K, GL (Fin 3) (Kv K v) → ℂ) (b : (FiniteAdeleRing (𝓞 K) K)ˣ)
    (u : FiniteAdeleRing (𝓞 K) K) : ℂ :=
  ∏ᶠ v : PlK K, Wf v (mm (finUnitAt v b) (u v))

open scoped Classical in

def Qf (D : DatK K) (S : Finset (PlK K)) (b : (FiniteAdeleRing (𝓞 K) K)ˣ) : ℂ :=
  ∏ᶠ v : PlK K, if v ∈ S then 1 else sph D v (dg 1 1 (finUnitAt v b))

section Loc
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def tauL (W : GL (Fin 3) F → ℂ) (t : Fˣ) : ℝ≥0∞ :=
  (∫⁻ u, ‖W (mm t u)‖ₑ ∂haarIntegers F) * ENNReal.ofReal ((modulus (t : F) : ℝ) ^ (-(5 / 2 : ℝ)))

end Loc

end GlobalTheory.CompanionTheory.GPKIntB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceEopEqOfHasInfCharGL
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC MeasureTheory PositivityTheory.S2.Clozel

noncomputable section

namespace GlobalTheory.CompanionTheory.CentEig

theorem trace_Eop_eq_of_hasInfCharGL {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}
    {V : Submodule ℂ (Sm E N)} {τ : E →+* ℂ} {m : Multiset ℂ} (hm : HasInfCharGL V τ m) :
    ∀ φ ∈ V, (∑ i : Fin N, Eop τ i i) φ = m.sum • φ := by
  intro φ hφ
  obtain ⟨hc, hu⟩ := hm
  rcases N with _ | n
  · obtain rfl : m = 0 := Multiset.card_eq_zero.1 hc
    simp
  · obtain ⟨l, rfl⟩ := Quot.exists_rep m
    refine GlobalTheory.CompanionTheory.CapelliTrace.trace_of_qdet (Eop τ) l (by simpa using hc) φ fun v => ?_
    have := hu (v - (n : ℂ) / 2) φ hφ
    rw [cap, show v - (n : ℂ) / 2 + (((n + 1 : ℕ) : ℂ) - 1) / 2 = v by push_cast; ring] at this
    simpa using this

end GlobalTheory.CompanionTheory.CentEig

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceOperatorEigenvalueSumStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_operator_eigenvalue_sum : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (τ : E →+* ℂ) (m : Multiset ℂ), π.HasInfChar τ m → ∀ φ ∈ π.V, (∑ i : Fin a, Eop τ i i) φ = m.sum • φ := by
  first | exact @GlobalTheory.CompanionTheory.CapelliTrace.trace_Eop_eq | exact GlobalTheory.CompanionTheory.CapelliTrace.trace_Eop_eq | (intros; apply GlobalTheory.CompanionTheory.CapelliTrace.trace_Eop_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumCompBoundedFibresLe
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumFibre

theorem summable_comp_of_bounded_fibres :
    ∀ (A B : Type) (π : A → B) (k : ℕ), (∀ b, Finite {a // π a = b} ∧ Nat.card {a // π a = b} ≤ k) → ∀ (g : B → ℝ), (∀ b, 0 ≤ g b) → Summable g → Summable (fun a => g (π a)) ∧ ∑' a, g (π a) ≤ k * ∑' b, g b := by
  intro A B π k h g hg hs
  classical
  have hcard : ∀ (u : Finset A) (b : B), (u.filter (fun a => π a = b)).card ≤ k := by
    intro u b
    have hf : ({a | π a = b} : Set A).Finite := Set.finite_coe_iff.mp (h b).1
    calc (u.filter (fun a => π a = b)).card
        = ((u.filter (fun a => π a = b) : Finset A) : Set A).ncard := (Set.ncard_coe_finset _).symm
      _ ≤ ({a | π a = b} : Set A).ncard := by
          apply Set.ncard_le_ncard _ hf
          intro a ha
          simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha
          exact ha.2
      _ = Nat.card {a // π a = b} := (Nat.card_coe_set_eq _).symm
      _ ≤ k := (h b).2
  have hbound : ∀ u : Finset A, ∑ a ∈ u, g (π a) ≤ k * ∑' b, g b := by
    intro u
    rw [Finset.sum_comp]
    calc ∑ b ∈ u.image π, (u.filter (fun a => π a = b)).card • g b
        ≤ ∑ b ∈ u.image π, (k : ℝ) * g b := by
          apply Finset.sum_le_sum
          intro b _
          rw [nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard u b) (hg b)
      _ = k * ∑ b ∈ u.image π, g b := by rw [Finset.mul_sum]
      _ ≤ k * ∑' b, g b :=
          mul_le_mul_of_nonneg_left (hs.sum_le_tsum _ (fun b _ => hg b)) (Nat.cast_nonneg k)
  have hsum : Summable (fun a => g (π a)) := summable_of_sum_le (fun a => hg (π a)) hbound
  exact ⟨hsum, hsum.tsum_le_of_sum_le hbound⟩

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumFibre
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TupleArchimedeanComplexCoordinatesStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tuple_archimedean_complex_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (τ : InfinitePlace F → (E →+* ℂ))
  (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)), IsCoord σ e τ Θ →
  ∀ n M : ℕ, ∃ Φ : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (InfinitePlace F → Fin n → Fin M → ℂ),
    (∀ X, Φ X = tupC Θ X) ∧ Continuous Φ ∧ Continuous Φ.symm ∧
    ∀ μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E), μ.IsAddHaarMeasure →
      (μ.map Φ).IsAddHaarMeasure ∧ ∀ g : (InfinitePlace F → Fin n → Fin M → ℂ) → ℂ, ∫ X, g (Φ X) ∂μ = ∫ Y, g Y ∂(μ.map Φ) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.TupHaar.tup_coord_haar | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.TupHaar.tup_coord_haar | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.TupHaar.tup_coord_haar <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwCentRatFCommStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twCent_comm_of_charpoly_separable : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (δ : GL (Fin n) E),
  (δ * thE E n δ).val.charpoly.Separable →
  ∀ a ∈ twCent (thF E n) (ratF E n δ), ∀ b ∈ twCent (thF E n) (ratF E n δ), a * b = b * a := by
  first | exact @GlobalTheory.CompanionTheory.RatCentComm.twCent_ratF_comm | exact GlobalTheory.CompanionTheory.RatCentComm.twCent_ratF_comm | (intros; apply GlobalTheory.CompanionTheory.RatCentComm.twCent_ratF_comm <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwKerWhitCharReflect
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.PRep.WhitExact

theorem twKer_whitChar_reflect : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W), IsSmooth π → IsSmooth σ → ∀ f : V →ₗ[ℂ] W, Function.Injective f → (∀ g v, f (π g v) = σ g (f v)) → ∀ v : V, f v ∈ twKer σ (unipB k (Fin N)) (whitChar ψ N) → v ∈ twKer π (unipB k (Fin N)) (whitChar ψ N) := by
  intro k _ _ _ _ ψ hψ N V W _ _ _ _ π σ hπ hσ f hf hfg v hv
  exact GlobalTheory.CompanionTheory.PRep.JacExact.twKer_reflect π σ hπ hσ _ _
    (GlobalTheory.Whittaker.isSmoothChar_whitChar hψ)
    (fun s hs => GlobalTheory.CompanionTheory.UnipExhaust.exists_compact_subgroup_of_finset k N s hs) f hf hfg v hv

end GlobalTheory.CompanionTheory.PRep.WhitExact
end

