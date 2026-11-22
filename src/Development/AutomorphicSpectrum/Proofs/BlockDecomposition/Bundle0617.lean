import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0593
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0594
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0563
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0041
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityBoundFromBoxVolumeGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0607
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0128
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0668
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0376
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0599
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralKernelNeTop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockMahlerBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DisintegrationAlongContinuousQuotientMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0595
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.EisensteinGrowthForms.GrowForms
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0015
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0488

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaEqLatticeIndexStatement
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.delta_eq_lattice_index : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (c : Matrix (Fin m) (Fin m) K), delta c ≠ 0 ∧ delta c = (intVec K m).toAddSubgroup.relIndex (lam c).toAddSubgroup := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DeltaIndex.delta_index | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DeltaIndex.delta_index | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DeltaIndex.delta_index <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorIndexBoundStatement
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.denominator_index_bound : ∀ (K : Type) [Field K] [NumberField K] (𝔱 : Ideal (𝓞 K)), 𝔱 ≠ ⊥ → ∀ c : Submodule (𝓞 K) K, c.FG → (1 : Submodule (𝓞 K) K) ≤ c → (∀ b : K, (∀ a ∈ 𝔱, (a : K) * b ∈ (1 : Submodule (𝓞 K) K)) → b ∈ c) → ∀ (t : 𝓞 K) (w x : K), t ∈ 𝔱 → w ∈ c → (t : K) * w - x ∈ (1 : Submodule (𝓞 K) K) → Ideal.absNorm 𝔱 * Ideal.absNorm (den K x) ≤ idx K c := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.IdxGe.absNorm_mul_den_le_idx | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.IdxGe.absNorm_mul_den_le_idx | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.IdxGe.absNorm_mul_den_le_idx <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorNormQuadraticExtensionStatement
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.denominator_norm_quadratic_extension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∀ x : F, Ideal.absNorm (den E (algebraMap F E x)) = Ideal.absNorm (den F x) ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DenMap.absNorm_den_algebraMap | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DenMap.absNorm_den_algebraMap | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DenMap.absNorm_den_algebraMap <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityBoundByRecursionStatement
section
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.density_bound_by_recursion : ∀ (H ι : Type) [MeasurableSpace H] (ν : Measure H) (D : Set H → ℝ≥0∞) (Dtot : ℝ≥0∞), Dtot ≠ ⊤ → (∀ Y, MeasurableSet Y → D Y ≤ Dtot) → ∀ (I : Finset ι) (α β : ι → ℝ≥0) (C₀ : ℝ≥0), (∀ Y, MeasurableSet Y → ∃ Z : ι → Set H, (∀ i ∈ I, MeasurableSet (Z i) ∧ ν (Z i) = β i * ν Y) ∧ D Y ≤ C₀ * ν Y + ∑ i ∈ I, α i * D (Z i)) → ∑ i ∈ I, α i * β i < 1 → ∑ i ∈ I, α i < 1 → ∃ C : ℝ≥0, ∀ Y, MeasurableSet Y → D Y ≤ C * ν Y := by
  first | exact @GlobalTheory.CompanionTheory.DensityIter.bounded_density_of_iterated | exact GlobalTheory.CompanionTheory.DensityIter.bounded_density_of_iterated | (intros; apply GlobalTheory.CompanionTheory.DensityIter.bounded_density_of_iterated <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityBoundFromBoxVolumeGrowthStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.density_bound_from_box_volume_growth : ∀ (K W : Type) [CommRing K] [Fintype W] (κ : K ≃+* (W → ℂ)) (n M : ℕ), 0 < n → 2 * n < M → ∀ (H : Type) [MeasurableSpace H] [MeasurableSpace (Fin n → Fin M → K)] (μ : Measure (Fin n → Fin M → K)) (ν : Measure H) (q : (Fin n → Fin M → K) → H) (C₀ : ℝ≥0∞), C₀ ≠ ⊤ → (∀ r : Fin n → W → ℝ, (∀ a w, 0 < r a w) → GlobalTheory.CompanionTheory.WhitFree.AvgInf.DenLE μ ν q (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ r) (C₀ * ∏ a, ∏ w, ENNReal.ofReal (r a w) ^ (2 * (M - n)))) → (∀ (S : Set (Fin n → Fin M → K)) (C : ℝ≥0∞) (a : Fin n) (s : Fin n → K), s a = 0 → GlobalTheory.CompanionTheory.WhitFree.AvgInf.DenLE μ ν q S C → GlobalTheory.CompanionTheory.WhitFree.AvgInf.DenLE μ ν q (GlobalTheory.CompanionTheory.WhitFree.AvgInf.shearK a s '' S) C) → ∀ R : ℝ, 1 ≤ R → ∀ δ : ℝ≥0∞, δ ≠ 0 → ∃ ε : ℝ, 0 < ε ∧ GlobalTheory.CompanionTheory.WhitFree.AvgInf.DenLE μ ν q (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ (fun _ _ => R) \ GlobalTheory.CompanionTheory.WhitFree.AvgInf.goodK κ R ε) δ := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.AvgInf.Bad.bad_density | exact GlobalTheory.CompanionTheory.WhitFree.AvgInf.Bad.bad_density | (intros; apply GlobalTheory.CompanionTheory.WhitFree.AvgInf.Bad.bad_density <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityChartIntegralFormulaStatement
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.density_chart_integral_formula : ∀ {Y ι : Type} {D : ℕ} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [Countable ι]
    (μ : ℤˣ → Measure Y) (e : ι → OpenPartialHomeomorph Y (Fin D → ℂ)) (ρ : ι → (Fin D → ℂ) → ℝ),
    (∀ l, ContinuousOn (ρ l) (e l).target) →
    (∀ l (ε : ℤˣ), (μ ε).restrict (e l).source = ((volume.restrict (e l).target).withDensity fun v =>
      ENNReal.ofReal (((ε : ℤ) : ℝ) * ρ l v)).map (e l).symm) →
    ∀ (G : Set Y), MeasurableSet G → G ⊆ ⋃ l, (e l).source → ∀ F : Y → ℝ, (∀ ε, IntegrableOn F G (μ ε)) →
    ∃ S : ι → Set Y, (∀ l, MeasurableSet (S l)) ∧ (∀ l, S l ⊆ (e l).source) ∧ Pairwise (Function.onFun Disjoint S) ∧
      ⋃ l, S l = G ∧ ∫ y in G, F y ∂μ 1 - ∫ y in G, F y ∂μ (-1) =
        ∫ v, ∑' l, ((e l) '' S l).indicator (fun v => F ((e l).symm v) * ρ l v) v := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ArchEq.integral_pieces | exact GlobalTheory.CompanionTheory.MixZ.ArchEq.integral_pieces | (intros; apply GlobalTheory.CompanionTheory.MixZ.ArchEq.integral_pieces <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiscreteInfimum
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.EGlue

theorem discInf : DiscInf := by
  intro E _ _ _ M V hV τ
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ h0
  obtain ⟨m, hm, h⟩ := exists_multiset_qdet (Eop (a := M) τ) (((M : ℂ) - 1) / 2) φ f hf
  refine ⟨m, hm, fun u ψ hψ => ?_⟩
  obtain ⟨c, h1⟩ := GlobalTheory.DiscLocEx.exists_scalarD hV (z := cap τ u) (Algebra.subset_adjoin ⟨τ, u, rfl⟩)
    (GlobalTheory.SpehInfChar.cap_commute_act τ u)
  have h2 : f (cap τ u φ) = _ := h u
  rw [h1 φ hφ, map_smul, hf, smul_eq_mul, mul_one] at h2
  rw [h1 ψ hψ, h2]

end GlobalTheory.CompanionTheory.EGlue

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiscreteTopologyProdMap
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Function
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TwUnfold

theorem mk_eq_iff_twConjugate {R : Type*} [Group R] (θ : Monoid.End R) (c : Quot (TwConjugate θ)) (d : R) :
    Quot.mk _ d = c ↔ TwConjugate θ (Quot.out c) d := by
  have hr : ∀ x, TwConjugate θ x x := fun x => ⟨1, by simp [twConj]⟩
  have hs : ∀ {x y}, TwConjugate θ x y → TwConjugate θ y x := by
    rintro x y ⟨g, rfl⟩
    refine ⟨g⁻¹, ?_⟩
    simp only [twConj, map_inv, inv_inv]
    group
  have ht : ∀ {x y z}, TwConjugate θ x y → TwConjugate θ y z → TwConjugate θ x z := by
    rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
    refine ⟨g * h, ?_⟩
    simp only [twConj, map_mul]
    group
  have he : Equivalence (TwConjugate θ) := ⟨hr, hs, ht⟩
  constructor
  · intro h
    have h1 : Quot.mk (TwConjugate θ) (Quot.out c) = Quot.mk _ d := by rw [Quot.out_eq, h]
    exact he.eqvGen_iff.1 (Quot.eqvGen_exact h1)
  · intro h
    rw [← Quot.sound h, Quot.out_eq]

section Adelic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem thetaA_ratGL (n : ℕ) (d : GL (Fin n) E) : thetaA E n (ratGL E n d) = ratGL E n (thetaE E n d) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [thetaR_val, ← map_inv]
  exact conjAd_algebraMap _

theorem discreteTopology_prodMap : DiscreteTopology ((ratGL E a).prodMap (ratGL E b)).range := by
  haveI := GlobalTheory.CompanionTheory.KerTwFin.discreteTopology_range (E := E) (n := a)
  haveI := GlobalTheory.CompanionTheory.KerTwFin.discreteTopology_range (E := E) (n := b)
  let f : ((ratGL E a).prodMap (ratGL E b)).range → (ratGL E a).range × (ratGL E b).range := fun z =>
    (⟨z.1.1, by obtain ⟨w, hw⟩ := z.2; exact ⟨w.1, congrArg Prod.fst hw⟩⟩,
     ⟨z.1.2, by obtain ⟨w, hw⟩ := z.2; exact ⟨w.2, congrArg Prod.snd hw⟩⟩)
  have hf : Continuous f := by
    refine Continuous.prodMk ?_ ?_
    · exact (continuous_fst.comp continuous_subtype_val).subtype_mk _
    · exact (continuous_snd.comp continuous_subtype_val).subtype_mk _
  have hi : Injective f := by
    intro z w h
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact congrArg (fun p => (p.1 : GA E a)) h
    · exact congrArg (fun p => (p.2 : GA E b)) h
  exact DiscreteTopology.of_continuous_injective hf hi

theorem finite_pair {φ : GA E a × GA E b → ℂ} (hφ : HasCompactSupport φ) {L : Set (GA E a × GA E b)} (hL : IsCompact L) :
    {d : GL (Fin a) E × GL (Fin b) E | ∃ x ∈ L,
      φ (twConj (thetaA E a) x.1 (ratGL E a d.1), twConj (thetaA E b) x.2 (ratGL E b d.2)) ≠ 0}.Finite := by
  have hθ₁ := GlobalTheory.CompanionTheory.KerTwFin.continuous_thetaA (E := E) (n := a)
  have hθ₂ := GlobalTheory.CompanionTheory.KerTwFin.continuous_thetaA (E := E) (n := b)
  have hL₁ : IsCompact (Prod.fst '' L) := hL.image continuous_fst
  have hL₂ : IsCompact (Prod.snd '' L) := hL.image continuous_snd
  have hS₁ : IsCompact (Prod.fst '' tsupport φ) := IsCompact.image hφ continuous_fst
  have hS₂ : IsCompact (Prod.snd '' tsupport φ) := IsCompact.image hφ continuous_snd
  have hK₁ := (hL₁.mul hS₁).mul (hL₁.image hθ₁).inv
  have hK₂ := (hL₂.mul hS₂).mul (hL₂.image hθ₂).inv
  refine ((GlobalTheory.CompanionTheory.KerTwFin.finite_ratGL_mem hK₁).prod (GlobalTheory.CompanionTheory.KerTwFin.finite_ratGL_mem hK₂)).subset ?_
  rintro ⟨d₁, d₂⟩ ⟨x, hx, h⟩
  have hs := subset_tsupport _ h
  constructor
  · change ratGL E a d₁ ∈ Prod.fst '' L * Prod.fst '' tsupport φ * (thetaA E a '' (Prod.fst '' L))⁻¹
    have hd : ratGL E a d₁ = x.1 * twConj (thetaA E a) x.1 (ratGL E a d₁) * (thetaA E a x.1)⁻¹ := by
      simp only [twConj]
      group
    rw [hd]
    exact Set.mul_mem_mul (Set.mul_mem_mul ⟨x, hx, rfl⟩ ⟨_, hs, rfl⟩)
      (Set.inv_mem_inv.2 ⟨x.1, ⟨x, hx, rfl⟩, rfl⟩)
  · change ratGL E b d₂ ∈ Prod.snd '' L * Prod.snd '' tsupport φ * (thetaA E b '' (Prod.snd '' L))⁻¹
    have hd : ratGL E b d₂ = x.2 * twConj (thetaA E b) x.2 (ratGL E b d₂) * (thetaA E b x.2)⁻¹ := by
      simp only [twConj]
      group
    rw [hd]
    exact Set.mul_mem_mul (Set.mul_mem_mul ⟨x, hx, rfl⟩ ⟨_, hs, rfl⟩)
      (Set.inv_mem_inv.2 ⟨x.2, ⟨x, hx, rfl⟩, rfl⟩)

theorem chiT_norm_le (τ : ℝ) {n : ℕ} (x : GA E n) : ‖(chiT τ x : ℂ)‖ ≤ 1 := by
  by_cases h : x ∈ cutSet E n τ <;> simp [chiT, h]

theorem mem_cutSet_of_chiT_ne_zero {τ : ℝ} {n : ℕ} {x : GA E n} (h : (chiT τ x : ℂ) ≠ 0) : x ∈ cutSet E n τ := by
  by_contra hx
  exact h (by simp [chiT, hx])

end Adelic

theorem unfold2_of (hM : Mahler) : Unfold2 := by
  intro E _ _ _ a b _ _ _ _ μ₁ _ μ₂ _ F₁ F₂ τ r φ hF₁ hF₂ hφ
  haveI := CuspidalL2GL.locallyCompactSpace_GA E a
  haveI := CuspidalL2GL.locallyCompactSpace_GA E b
  haveI := CuspidalL2GL.secondCountableTopology_GA E a
  haveI := CuspidalL2GL.secondCountableTopology_GA E b
  haveI : SigmaFinite μ₁ := sigmaFinite_of_locallyFinite
  haveI : SigmaFinite μ₂ := sigmaFinite_of_locallyFinite
  obtain ⟨hc₁, hi₁, C₁, hC₁, hs₁⟩ := hM E a τ
  obtain ⟨hc₂, hi₂, C₂, hC₂, hs₂⟩ := hM E b τ
  let ι : GL (Fin a) E × GL (Fin b) E →* GA E a × GA E b := (ratGL E a).prodMap (ratGL E b)
  let θ : Monoid.End (GA E a × GA E b) := (thetaA E a).prodMap (thetaA E b)
  let θR : Monoid.End (GL (Fin a) E × GL (Fin b) E) := (thetaE E a).prodMap (thetaE E b)
  haveI : DiscreteTopology ι.range := discreteTopology_prodMap
  haveI : Countable ι.range := by
    haveI : SecondCountableTopology ι.range := inferInstance
    exact (TopologicalSpace.separableSpace_iff_countable).1 inferInstance
  have hι : Injective ι :=
    GlobalTheory.CompanionTheory.KerTwFin.injective_ratGL.prodMap GlobalTheory.CompanionTheory.KerTwFin.injective_ratGL
  haveI : Countable (GL (Fin a) E × GL (Fin b) E) :=
    Injective.countable (f := ι.rangeRestrict) (fun x y h => hι (congrArg Subtype.val h))
  have hθ : ∀ r, ι (θR r) = θ (ι r) := fun r => Prod.ext (thetaA_ratGL a r.1).symm (thetaA_ratGL b r.2).symm
  have hFd : IsFundamentalDomain ι.range (F₁ ×ˢ F₂) (μ₁.prod μ₂) :=
    GlobalTheory.CompanionTheory.PairDom.isFundamentalDomain_range_prodMap μ₁ μ₂ (ratGL E a) (ratGL E b) F₁ F₂ hF₁ hF₂
  let cls : GL (Fin a) E × GL (Fin b) E → TwClass E a × TwClass E b := fun d => (Quot.mk _ d.1, Quot.mk _ d.2)
  let rep : TwClass E a × TwClass E b → GL (Fin a) E × GL (Fin b) E := fun c => (Quot.out c.1, Quot.out c.2)
  have hcls : ∀ c d, cls d = c ↔ TwConjugate θR (rep c) d := by
    rintro ⟨c₁, c₂⟩ ⟨d₁, d₂⟩
    constructor
    · intro h
      obtain ⟨g₁, h₁⟩ := (mk_eq_iff_twConjugate _ c₁ d₁).1 (congrArg Prod.fst h)
      obtain ⟨g₂, h₂⟩ := (mk_eq_iff_twConjugate _ c₂ d₂).1 (congrArg Prod.snd h)
      exact ⟨(g₁, g₂), Prod.ext h₁ h₂⟩
    · rintro ⟨g, hg⟩
      exact Prod.ext ((mk_eq_iff_twConjugate _ c₁ d₁).2 ⟨g.1, congrArg Prod.fst hg⟩)
        ((mk_eq_iff_twConjugate _ c₂ d₂).2 ⟨g.2, congrArg Prod.snd hg⟩)
  let H : TwClass E a × TwClass E b → Subgroup (GA E a × GA E b) := fun c =>
    (ratCent (Quot.out c.1)).prod (ratCent (Quot.out c.2))
  have hH : ∀ c g, g ∈ H c ↔ ∃ t, ι t = g ∧ twConj θR t (rep c) = rep c := by
    rintro c ⟨g₁, g₂⟩
    constructor
    · rintro ⟨⟨t₁, h₁, rfl⟩, ⟨t₂, h₂, rfl⟩⟩
      exact ⟨(t₁, t₂), rfl, Prod.ext h₁ h₂⟩
    · rintro ⟨t, ht, hc⟩
      exact ⟨⟨t.1, congrArg Prod.fst hc, congrArg Prod.fst ht⟩, ⟨t.2, congrArg Prod.snd hc, congrArg Prod.snd ht⟩⟩
  have hmχ : ∀ (n : ℕ) [MeasurableSpace (GA E n)] [BorelSpace (GA E n)], IsClosed (cutSet E n τ) →
      Measurable (chiT τ : GA E n → ℂ) := fun n _ _ h => measurable_one.indicator h.measurableSet
  have hχm : Measurable fun x : GA E a × GA E b => (chiT τ x.1 * chiT τ x.2 : ℂ) :=
    ((hmχ a hc₁).comp measurable_fst).mul ((hmχ b hc₂).comp measurable_snd)
  have hχb : ∀ x : GA E a × GA E b, ‖(chiT τ x.1 * chiT τ x.2 : ℂ)‖ ≤ 1 := fun x => by
    rw [norm_mul]
    exact mul_le_one₀ (chiT_norm_le τ _) (norm_nonneg _) (chiT_norm_le τ _)
  have hinv : ∀ (n : ℕ), (∀ g x, ratGL E n g * x ∈ cutSet E n τ ↔ x ∈ cutSet E n τ) → ∀ g (x : GA E n),
      (chiT τ (ratGL E n g * x) : ℂ) = chiT τ x := fun n h g x => by
    by_cases hx : x ∈ cutSet E n τ
    · simp [chiT, hx, (h g x).2 hx]
    · simp [chiT, hx, mt (h g x).1 hx]
  have hχi : ∀ (r : GL (Fin a) E × GL (Fin b) E) (x : GA E a × GA E b),
      (chiT τ (ι r * x).1 * chiT τ (ι r * x).2 : ℂ) = chiT τ x.1 * chiT τ x.2 := fun r x => by
    change (chiT τ (ratGL E a r.1 * x.1) * chiT τ (ratGL E b r.2 * x.2) : ℂ) = _
    rw [hinv a hi₁, hinv b hi₂]
  have hχK : ∀ x : GA E a × GA E b, (chiT τ x.1 * chiT τ x.2 : ℂ) ≠ 0 → ∃ r, ∃ k ∈ C₁ ×ˢ C₂, x = ι r * k := by
    intro x hx
    obtain ⟨_, ⟨r₁, rfl⟩, k₁, hk₁, e₁⟩ := Set.mem_mul.1 (hs₁ (mem_cutSet_of_chiT_ne_zero (left_ne_zero_of_mul hx)))
    obtain ⟨_, ⟨r₂, rfl⟩, k₂, hk₂, e₂⟩ := Set.mem_mul.1 (hs₂ (mem_cutSet_of_chiT_ne_zero (right_ne_zero_of_mul hx)))
    exact ⟨(r₁, r₂), (k₁, k₂), ⟨hk₁, hk₂⟩, Prod.ext e₁.symm e₂.symm⟩
  have hθc : Continuous θ := (GlobalTheory.CompanionTheory.KerTwFin.continuous_thetaA.comp continuous_fst).prodMk
    (GlobalTheory.CompanionTheory.KerTwFin.continuous_thetaA.comp continuous_snd)
  have hφm : ∀ d, Measurable fun x => φ (twConj θ x (ι d)) := fun d =>
    (hφ.cont.comp ((continuous_inv.mul continuous_const).mul hθc)).measurable
  obtain ⟨B, hB⟩ := hφ.supp.exists_bound_of_continuous hφ.cont
  have key := unfold_abs (μ := μ₁.prod μ₂) (ι := ι) (θ := θ) (θR := θR) (cls := cls) (rep := rep) (H := H)
    (χ := fun x => chiT τ x.1 * chiT τ x.2) (φ := φ) hι hθ hFd hcls hH hχm hχb hχi (hC₁.prod hC₂) hχK hφm hB
    (fun L hL => finite_pair hφ.supp hL)
  exact key

theorem unfold2 : Unfold2 := unfold2_of GlobalTheory.CompanionTheory.MahlerAdelic.mahler

end GlobalTheory.CompanionTheory.TwUnfold

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DisintegrationAlongContinuousQuotientMapStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.disintegration_along_continuous_quotient_map : ∀ (V H Z : Type) [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace H] [T2Space H] [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H] (μ : Measure V) (ν : Measure H) [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] (f : V → Z) (ι : H → Z) (q : V → H) (U : Set V) (m : H → Measure V), IsOpen U → Continuous q → Function.Injective ι → (∀ X, ι (q X) = f X) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ m → ∀ φ : V → ℂ, Continuous φ → Integrable φ μ → (∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ A : Set V, IsCompact A ∧ A ⊆ U ∧ ∀ Y, MeasurableSet Y → ∫⁻ X in Aᶜ ∩ q ⁻¹' Y, ‖φ X‖ₑ ∂μ ≤ ε * ν Y) → ∀ c : H, Integrable φ (m c) ∧ ∀ r : ℕ → H → ℝ, (∀ k, Continuous (r k) ∧ HasCompactSupport (r k) ∧ (∀ y, 0 ≤ r k y) ∧ 0 < ∫ y, r k y ∂ν) → Filter.Tendsto (fun k => tsupport (r k)) Filter.atTop (nhds c).smallSets → Filter.Tendsto (fun k => (∫ X, φ X * (r k (q X) : ℂ) ∂μ) / ((∫ y, r k y ∂ν : ℝ) : ℂ)) Filter.atTop (nhds (∫ X, φ X ∂(m c))) := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.AvgInf.Lim.fibre_avg_tendsto | exact GlobalTheory.CompanionTheory.WhitFree.AvgInf.Lim.fibre_avg_tendsto | (intros; apply GlobalTheory.CompanionTheory.WhitFree.AvgInf.Lim.fibre_avg_tendsto <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DisintegrationParameterContinuous
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.FibParam

open Set Filter

theorem fibre_param_continuous : ∀ (V H Y P : Type) [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace H] [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] [TopologicalSpace P] [T2Space P] [LocallyCompactSpace P] (μ : Measure V) (ν : Measure H) (f : V → Y) (ι : H → Y) (q : V → H) (U : Set V) (fam : H → Measure V), IsOpen U → Continuous q → Function.Injective ι → (∀ v, f v = ι (q v)) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ fam → ∀ ψ : P × V → ℝ, Continuous ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, p.2 ∈ U) → Continuous (fun z : P × H => ∫ v, ψ (z.1, v) ∂(fam z.2)) ∧ HasCompactSupport (fun z : P × H => ∫ v, ψ (z.1, v) ∂(fam z.2)) ∧ ∀ z ∈ tsupport (fun z : P × H => ∫ v, ψ (z.1, v) ∂(fam z.2)), ∃ v, (z.1, v) ∈ tsupport ψ ∧ q v = z.2 := by
  intro V H Y P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ ν f ι q U fam hU hq hι hf h ψ hψ hψc hψU
  have hCc : IsCompact (tsupport ψ) := hψc
  have hC₂c : IsCompact (Prod.snd '' tsupport ψ) := hCc.image continuous_snd
  have hC₂U : Prod.snd '' tsupport ψ ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact hψU x hx
  obtain ⟨ρ, hρ1, hρc, hρs, hρ01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hC₂c hU hC₂U
  have hzero : ∀ p v, v ∉ Prod.snd '' tsupport ψ → ψ (p, v) = 0 := fun p v hv =>
    image_eq_zero_of_notMem_tsupport (fun hh => hv ⟨_, hh, rfl⟩)
  have hsec : ∀ p, (∀ b, Integrable (fun v => ψ (p, v)) (fam b)) ∧
      Continuous (fun b => ∫ v, ψ (p, v) ∂(fam b)) := by
    intro p
    have hgc : Continuous (fun v => ψ (p, v)) := hψ.comp (continuous_const.prodMk continuous_id)
    have hsub : Function.support (fun v => ψ (p, v)) ⊆ Prod.snd '' tsupport ψ :=
      fun v hv => by_contra fun hn => hv (hzero p v hn)
    have hts : tsupport (fun v => ψ (p, v)) ⊆ Prod.snd '' tsupport ψ :=
      closure_minimal hsub hC₂c.isClosed
    have hcs : HasCompactSupport (fun v => ψ (p, v)) :=
      hC₂c.of_isClosed_subset (isClosed_tsupport _) hts
    obtain ⟨i, c⟩ := h.2.2 _ hgc hcs (hts.trans hC₂U)
    exact ⟨fun b => i b (mem_univ b), continuousOn_univ.1 c⟩
  obtain ⟨iρ, cρ⟩ := h.2.2 ρ ρ.continuous hρc hρs
  have hRc : Continuous (fun b => ∫ v, ρ v ∂(fam b)) := continuousOn_univ.1 cρ
  have hR0 : ∀ b, 0 ≤ ∫ v, ρ v ∂(fam b) := fun b => integral_nonneg fun v => (hρ01 v).1
  have hdiff : ∀ (p p' : P) (e : ℝ) (b : H), 0 ≤ e →
      (∀ v ∈ Prod.snd '' tsupport ψ, |ψ (p, v) - ψ (p', v)| ≤ e) →
      |(∫ v, ψ (p, v) ∂(fam b)) - ∫ v, ψ (p', v) ∂(fam b)| ≤ e * ∫ v, ρ v ∂(fam b) := by
    intro p p' e b he hb
    rw [← integral_sub ((hsec p).1 b) ((hsec p').1 b), ← integral_const_mul, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le ((iρ b (mem_univ b)).const_mul e) (ae_of_all _ fun v => ?_)
    rw [Real.norm_eq_abs]
    by_cases hv : v ∈ Prod.snd '' tsupport ψ
    · rw [hρ1 hv]
      simpa using hb v hv
    · rw [hzero p v hv, hzero p' v hv]
      simpa using mul_nonneg he (hρ01 v).1
  have hcont : Continuous (fun z : P × H => ∫ v, ψ (z.1, v) ∂(fam z.2)) := by
    refine continuous_iff_continuousAt.2 ?_
    rintro ⟨p₀, b₀⟩
    refine Metric.continuousAt_iff'.2 fun ε hε => ?_
    set M : ℝ := (∫ v, ρ v ∂(fam b₀)) + 1 with hMdef
    have hM : 0 < M := by linarith [hR0 b₀]
    set e : ℝ := ε / (2 * M) with hedef
    have he : 0 < e := by positivity
    have ev1 : ∀ᶠ b in 𝓝 b₀, (∫ v, ρ v ∂(fam b)) < M :=
      (isOpen_lt hRc continuous_const).mem_nhds (by simp [hMdef])
    have ev2 : ∀ᶠ b in 𝓝 b₀,
        dist (∫ v, ψ (p₀, v) ∂(fam b)) (∫ v, ψ (p₀, v) ∂(fam b₀)) < ε / 2 :=
      Metric.continuousAt_iff'.1 (hsec p₀).2.continuousAt (ε / 2) (by positivity)
    have hK := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1
      ((ContinuousMap.curry (⟨ψ, hψ⟩ : C(P × V, ℝ))).continuous.tendsto p₀)) _ hC₂c
    have ev3 := Metric.tendstoUniformlyOn_iff.1 hK e he
    filter_upwards [ev3.prod_nhds (ev1.and ev2)] with z hz
    obtain ⟨hz3, hz1, hz2⟩ := hz
    have hd := hdiff z.1 p₀ e z.2 he.le fun v hv => by
      have := hz3 v hv
      have h' : dist (ψ (p₀, v)) (ψ (z.1, v)) < e := this
      rw [Real.dist_eq, abs_sub_comm] at h'
      exact h'.le
    have hbound : e * (∫ v, ρ v ∂(fam z.2)) ≤ ε / 2 := by
      have h1 : e * M = ε / 2 := by
        rw [hedef]
        field_simp
      calc e * (∫ v, ρ v ∂(fam z.2)) ≤ e * M := mul_le_mul_of_nonneg_left hz1.le he.le
        _ = ε / 2 := h1
    rw [Real.dist_eq] at hz2 ⊢
    calc |(∫ v, ψ (z.1, v) ∂(fam z.2)) - ∫ v, ψ (p₀, v) ∂(fam b₀)|
        = |((∫ v, ψ (z.1, v) ∂(fam z.2)) - ∫ v, ψ (p₀, v) ∂(fam z.2)) +
            ((∫ v, ψ (p₀, v) ∂(fam z.2)) - ∫ v, ψ (p₀, v) ∂(fam b₀))| := by
          congr 1
          ring
      _ ≤ _ := abs_add_le _ _
      _ < ε := by linarith
  have hsupp : ∀ z : P × H, (∫ v, ψ (z.1, v) ∂(fam z.2)) ≠ 0 →
      ∃ v, ψ (z.1, v) ≠ 0 ∧ q v = z.2 := by
    intro z hz
    by_contra hn
    push_neg at hn
    apply hz
    have h1 : f ⁻¹' {ι z.2} ∩ U ∈ ae (fam z.2) := mem_ae_iff.2 (h.1 z.2)
    have h2 : (fun v => ψ (z.1, v)) =ᵐ[fam z.2] 0 := by
      filter_upwards [h1] with v hv
      have hqv : q v = z.2 := hι ((hf v).symm.trans hv.1)
      by_contra h0
      exact hn v h0 hqv
    exact (integral_congr_ae h2).trans (by simp)
  have hSc : IsCompact ((fun x : P × V => (x.1, q x.2)) '' tsupport ψ) :=
    hCc.image (continuous_fst.prodMk (hq.comp continuous_snd))
  have hts : tsupport (fun z : P × H => ∫ v, ψ (z.1, v) ∂(fam z.2)) ⊆
      (fun x : P × V => (x.1, q x.2)) '' tsupport ψ := by
    refine closure_minimal (fun z hz => ?_) hSc.isClosed
    obtain ⟨v, hv, hqv⟩ := hsupp z hz
    exact ⟨(z.1, v), subset_tsupport _ hv, Prod.ext rfl hqv⟩
  refine ⟨hcont, hSc.of_isClosed_subset (isClosed_tsupport _) hts, fun z hz => ?_⟩
  obtain ⟨x, hx, rfl⟩ := hts hz
  exact ⟨x.2, hx, rfl⟩

end GlobalTheory.CompanionTheory.WeilSiegel.FibParam
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleContragredientOfInducedProductStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_contragredient_of_induced_product : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), Nonempty ((contra (contra (prodIrr x hd))).Equiv (prodIrr x hd)) := by
  first | exact @GlobalTheory.CompanionTheory.ContraProd.contra_contra_prodIrr | exact GlobalTheory.CompanionTheory.ContraProd.contra_contra_prodIrr | (intros; apply GlobalTheory.CompanionTheory.ContraProd.contra_contra_prodIrr <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHalfHolds
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl SiegelEisensteinSeries
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.CompanionTheory.SiegelEisHalf

theorem eisHalf : EisHalf := by
  unfold SiegelEisensteinSeries.EisHalf
  intro F E _ _ _ _ _ σ B n Y r s hB hn hY χ hχ c hc b K a hb hK ha s₁ f hf
  obtain ⟨Ê, t₁, hsum, hdiff⟩ := GlobalTheory.T.eisenstein_series_continuation F E σ B n Y r s hB hn hY b K a hb hK ha χ s₁ f hf
  obtain ⟨t₀, h23⟩ := GlobalTheory.T.eisenstein_vertical_bound F E σ B n Y r s hB hn hY b K a hb hK ha χ s₁ f hf
  obtain ⟨t, ht₀, ht₁⟩ : ∃ t : ℝ, t₀ ≤ t ∧ t₁ ≤ t := ⟨max t₀ t₁, le_max_left _ _, le_max_right _ _⟩
  have hsum' : ∀ z : ℂ, t < z.re → ∀ x : GlobalTheory.ThK.Dbl.G2 σ Y,
      HasSum (GlobalTheory.ThK.Dbl.eisTerm (GlobalTheory.ThK.Dbl.flat a f s₁ z) x) (Ê z x) :=
    fun z hz x => hsum z (lt_of_le_of_lt ht₁ hz) x
  obtain ⟨hmod, hcont, hbd⟩ := h23 t Ê ht₀ hsum'
  let v : ℂ → ↥(GlobalTheory.ThK.Dbl.modFun σ Y) := fun z =>
    if hz : t < z.re then ⟨fun x => Ê z x, hmod z hz⟩ else 0
  have hv : ∀ z : ℂ, t < z.re → ∀ x : GlobalTheory.ThK.Dbl.G2 σ Y,
      (↑(v z) : GlobalTheory.ThK.Dbl.G2 σ Y → ℂ) x = Ê z x := by
    intro z hz x
    simp only [v]
    rw [dif_pos hz]
  refine ⟨t, v, fun z hz x => by rw [hv z hz x]; exact hsum' z hz x, ?_⟩
  have hS : IsOpen {z : ℂ | t < z.re} := isOpen_lt continuous_const Complex.continuous_re
  apply GlobalTheory.CompanionTheory.WeakHolo.wholo_growForms v hS
  · intro x
    exact ((hdiff x).mono fun z hz => lt_of_le_of_lt ht₁ hz).congr fun z hz => hv z hz x
  · exact hcont.congr fun y hy => hv y.1 hy.1 y.2
  · intro Q hQS hQ
    rcases Q.eq_empty_or_nonempty with hQe | hne
    · exact ⟨0, 0, fun z hz => by simp [hQe] at hz⟩
    · obtain ⟨z₀, hz₀, hmin⟩ := hQ.exists_isMinOn hne Complex.continuous_re.continuousOn
      obtain ⟨z₁, _, hmax⟩ := hQ.exists_isMaxOn hne Complex.continuous_re.continuousOn
      obtain ⟨C, N, hC⟩ := hbd z₀.re z₁.re (hQS hz₀)
      refine ⟨C, N, fun z hz x => ?_⟩
      rw [hv z (hQS hz) x]
      exact hC z (isMinOn_iff.mp hmin z hz) (isMaxOn_iff.mp hmax z hz) x

end GlobalTheory.CompanionTheory.SiegelEisHalf

end
end

