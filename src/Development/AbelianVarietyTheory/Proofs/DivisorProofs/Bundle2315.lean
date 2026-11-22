import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0240
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliPartOneStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0063
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2263
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0137
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0143
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2264
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2288
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2277
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0936
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2219
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2265
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfGrowthOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1622
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2200
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1554
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2090
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FiniteAndFinrankLeOfPointwise
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2174
import Development.AbelianVarietyTheory.Definitions.Foundations.CanonicalExponents
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ClausesIffExistsUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2297
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2044
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2266
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2225

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverStatementHolds
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem coverSt_holds : CoverSt := by
  intro E _ _ _ H Dw l Xo c hpq hA hgood hfac Z la p n hp hpla
  classical
  let l' : Level H := { l with A := p ^ n, A_pos := pow_pos hp.pos n }
  have hdvd : l.Dvd l' := ⟨dvd_rfl, le_rfl, by rw [hA]; exact one_dvd _⟩
  let fam : ∀ l₀ : Level H, Moduli Dw l₀ := fun l₀ => Classical.choice (GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.1 E H Dw l₀ hpq)
  let Xo' := fam l'
  obtain ⟨c₁⟩ : Nonempty (Coeff l') := inferInstance
  let c₀ : Coeff l' :=
    { F := c.F ⊔ c₁.F
      fin := by
        have := c.fin
        have := c₁.fin
        exact IntermediateField.finiteDimensional_sup _ _
      conj := fun τ a => (le_sup_right : c₁.F ≤ c.F ⊔ c₁.F) (c₁.conj τ a)
      zeta_mem := (le_sup_right : c₁.F ≤ c.F ⊔ c₁.F) c₁.zeta_mem
      le := c₁.le.trans le_sup_right }
  obtain ⟨-, c', hc', hall⟩ := GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed E H Dw l' Xo' c₀ hpq
  have hfac' : FnAlgClosed Xo' c' := hall c' le_rfl
  have hle : c.F ≤ c'.F := le_sup_left.trans hc'
  have hpU : (p : c.F) ∈ (la.valuation c.F).valuationSubring.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff]
    have h1 : la.valuation c.F (algebraMap (𝓞 c.F) c.F (p : 𝓞 c.F)) < 1 :=
      (HeightOneSpectrum.valuation_lt_one_iff_mem la _).2 hpla
    rw [map_natCast] at h1
    exact ((Valuation.isEquiv_valuation_valuationSubring (la.valuation c.F)).lt_one_iff_lt_one).1 h1
  obtain ⟨W, hpW, hWU⟩ := GlobalTheory.exists_valuationSubring_complex_comap_val_eq c.F _ p hpU
  obtain ⟨Ysys, -⟩ := GlobalTheory.T.compactifiedModuli_partOne.2 E H Dw hpq fam
  let Y : Model Xo' c' (c'.V W).subtype := Ysys p W hp hpW ⟨l', c', hgood p hp⟩
  obtain ⟨r, hr, r₀, m, hr₀, hfin, het, hsurj⟩ := GlobalTheory.T.exists_level_change_map E H Dw l l' Xo Xo' c c' hle hpq hdvd
  obtain ⟨ν₀, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp m Y.m0.toSABMap
  obtain ⟨U, hUZ, hUirr, hUlift⟩ := GlobalTheory.T.component_surjects_of_open_closed GlobalTheory.T.exists_component_surjects_clopen GlobalTheory.T.exists_lift_algebraically_closed_point E H Dw l l' Xo Xo' c c' hle (GlobalTheory.T.component_geometrically_irreducible E H Dw l Xo c hfac)
    (GlobalTheory.T.component_geometrically_irreducible E H Dw l' Xo' c' hfac') r hr hfin het hsurj Z
  obtain ⟨Xw, hXj, hXp, hXU, hXg⟩ := GlobalTheory.T.integral_model_component_irreducible E H Dw l' Xo' c' W Y p hp hpW U hUirr
  refine ⟨l', Xo', c', W, Y, r, hr₀ ▸ ν₀, hle, Xw, rfl, hr, fun x => ?_, hpW, ?_, hXj, hXp,
    fun z hz => hUZ z ((hXU z).1 hz), hXg, ?_⟩
  · rw [← Valuation.mem_valuationSubring_iff, ← hWU, ValuationSubring.mem_comap]
    rfl
  · have h := hpW
    rw [ValuationSubring.mem_nonunits_iff_or] at h ⊢
    rcases h with h | h
    · exact absurd (by exact_mod_cast h) hp.ne_zero
    · exact Or.inr fun h' => h (by simpa [Coeff.V] using h')
  · intro k _ _ fK x hx hxZ
    obtain ⟨yy, h1, h2, h3⟩ := hUlift k fK x hx hxZ
    refine ⟨yy, h1, h2, ?_⟩
    rintro _ ⟨w, rfl⟩
    exact (hXU _).2 (h3 ⟨w, rfl⟩)

end GlobalTheory.FlatModel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeLocalUnitValueHolomorphicThirdStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.MBLow.Cl GlobalTheory.MBLow.Cl.CubHol
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubeLocalUnit_value_holomorphic_third : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ} (ν : NumOf D ℂ N) (d : AB N.toNumB g), Geo ν d → ∀ (x y : Fin g → ℂ) (j : thK → D.P.L.ι), IsOpen {z | ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j} ∧ DifferentiableOn ℂ (fun z => valF (pt3 ν d x y z) (cubW D j) (D.cub.t.s j).val) {z | ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j} := by
  first | exact @GlobalTheory.MBLow.Cl.CubHol.isOpen_and_differentiableOn_valF_pt3_cubW | exact GlobalTheory.MBLow.Cl.CubHol.isOpen_and_differentiableOn_valF_pt3_cubW | (intros; apply GlobalTheory.MBLow.Cl.CubHol.isOpen_and_differentiableOn_valF_pt3_cubW <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeValueComplexPointsEqFrameAlternatingProductStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubeValue_complexPoints_eq_frameAlternatingProduct : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}
    (ν : NumOf D ℂ N) (d : AB N.toNumB g), d.Cub → ∀ (G : Geo ν d) (x y z : Fin g → ℂ) (j : thK.{0} → D.P.L.ι),
    (∀ I : thK.{0}, ⊤ ≤ (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left ⁻¹ᵁ D.P.L.U (j I)) →
    valF (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j)
      (D.cub.t.s j).val = ∏ I : thK.{0}, G.frG (j I) (∑ i ∈ I.down, ![x, y, z] i) ^ thε I := by
  first | exact @GlobalTheory.MBLow.Cl.cube_val_frame | exact GlobalTheory.MBLow.Cl.cube_val_frame | (intros; apply GlobalTheory.MBLow.Cl.cube_val_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeValueEqFirstJetAlternatingProduct
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.CubeJet

theorem cube_jet : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}
    (ν : NumOf D ℂ N) (d : AB N.toNumB g) (G : Geo ν d),
    (∀ (x y z : Fin g → ℂ) (j : thK.{0} → D.P.L.ι),
      (∀ I : thK.{0}, ⊤ ≤ (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left ⁻¹ᵁ D.P.L.U (j I)) →
      valF (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j)
        (D.cub.t.s j).val = ∏ I : thK.{0}, G.frG (j I) (∑ i ∈ I.down, ![x, y, z] i) ^ thε I) →
    ∀ (W : Fin g → ℂ) (gm : GtPt D (TE R ℂ)), (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) →
    IsD ν d W gm.b → ∀ (χ χ' : D.X) (x y : Fin g → ℂ),
    ν.eA (d.ex x) = DegPre.cF D ℂ χ → ν.eA (d.ex y) = DegPre.cF D ℂ χ' →
    vE (DegPre.cubAtT D (TE R ℂ) (DegPre.cT D (TE R ℂ) χ) (DegPre.cT D (TE R ℂ) χ') gm.b) (𝟙 _) ν.J =
      1 + TrivSqZeroExt.inr
        (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex (x + y))).left)) (x + y) W / G.frG (ν.J (ν.eA (d.ex (x + y))).left) (x + y) +
          fderiv ℂ (G.frG (ν.J (ν.eA (d.ex 0)).left)) 0 W / G.frG (ν.J (ν.eA (d.ex 0)).left) 0 -
          fderiv ℂ (G.frG (ν.J (ν.eA (d.ex x)).left)) x W / G.frG (ν.J (ν.eA (d.ex x)).left) x -
          fderiv ℂ (G.frG (ν.J (ν.eA (d.ex y)).left)) y W / G.frG (ν.J (ν.eA (d.ex y)).left) y) := by
  intro R _ _ D _ N g ν d G hprod W gm h0 hD χ χ' x y hx hy
  obtain ⟨U, f, hv, hU0, hUz⟩ := GlobalTheory.T.cubeValue_constPoints_tangent_eq_dualFibreValue ν d gm h0 χ χ' x y hx hy
  rw [hv, hD U f hU0]
  have hO : IsOpen {z | ⊤ ≤ ptB ν d z ⁻¹ᵁ U} := (G.hol U f).1
  have hFeq : (fun z => valF (ptB ν d z) U f) =ᶠ[nhds 0] fun z => ∏ I : thK.{0},
      G.frG (ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left) (∑ i ∈ I.down, ![x, y, z] i) ^ thε I := by
    filter_upwards [hO.mem_nhds hU0] with z hz
    obtain ⟨hI, hval⟩ := hUz z hz
    rw [hval]
    exact hprod x y z _ hI
  have hopen : ∀ i, IsOpen {z | ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ D.P.L.U i} := fun i => by
    have e : ∀ z, (ν.eA (d.ex z)).left = ptB ν d z ≫ (DegPre.prB D ℂ).left := fun z => by
      rw [ptB, DegPre.prB, ← Over.comp_left, lift_snd]
    have := (G.hol ((DegPre.prB D ℂ).left ⁻¹ᵁ D.P.L.U i) 0).1
    simpa only [e, Scheme.Hom.comp_preimage] using this
  have hd : ∀ I : thK.{0}, DifferentiableAt ℂ (G.frG (ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left))
      (∑ i ∈ I.down, ![x, y, 0] i) := fun I =>
    (G.fr_hol _).differentiableAt ((hopen _).mem_nhds (ν.good _))
  have hn : ∀ I : thK.{0}, G.frG (ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left)
      (∑ i ∈ I.down, ![x, y, 0] i) ≠ 0 := fun I => by
    rw [← G.fr_eq]
    exact mul_ne_zero (Units.ne_zero _) (GlobalTheory.Ex.Arch.AbVal.rg_ne_zero ν)
  have hpair : ∀ I : thK.{0}, 2 ∉ I.down →
      G.frG (ν.J (ν.eA (d.ex (∑ i ∈ (insert 2 I.down), ![x, y, 0] i))).left) =
        G.frG (ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left) := fun I h2 => by
    rw [Finset.sum_insert h2]
    simp
  obtain ⟨h1, h2⟩ := GlobalTheory.T.alternatingCubeProduct_value_fderiv_at_zero x y W (fun I : thK.{0} => G.frG (ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left)) _
    hFeq hd hn hpair
  rw [h1, h2]
  simp [Finset.sum_insert]

end GlobalTheory.MBLow.Cl.CubeJet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeValueTimesThetaFramesChartGaugeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.MBLow.Cl GlobalTheory.MBLow.Cl.CubHol
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubeValueTimesThetaFrames_chartGauge : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ} (ν : NumOf D ℂ N) (d : AB N.toNumB g) (geo : Geo ν d) (x y z : Fin g → ℂ) (j : thK → D.P.L.ι), ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j → cubF d x y z * ∏ I : thK, geo.frG (j I) (wI x y z I) ^ thε I = valF (pt3 ν d x y z) (cubW D j) (D.cub.t.s j).val := by
  first | exact @GlobalTheory.MBLow.Cl.CubHol.cubF_mul_prod_frG | exact GlobalTheory.MBLow.Cl.CubHol.cubF_mul_prod_frG | (intros; apply GlobalTheory.MBLow.Cl.CubHol.cubF_mul_prod_frG <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormGrowthLeImageDegreeLowerWeight
section
set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

namespace GlobalTheory.DegVal

theorem growthOn_le_compDeg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), UnfAll U → ∀ (Z : Comp Xo c) (G G' : WTZ E), Even G.2 → Even G'.2 → growthOn U Z G ≠ ⊤ → BirOn U Z G → ValMult U Z G G' → growthOn U Z G' ≤ (compDeg U Z G : ℝ≥0∞) := by
  intro E _ _ _ H Dw l Xo c r U hU Z G G' hG hG' hfin hB hM
  rcases eq_or_ne (growthOn U Z G') 0 with h0 | h0
  · rw [h0]; exact bot_le
  obtain ⟨a, θ, ha, hθ, hmul⟩ := hM
  haveI := GlobalTheory.DegTop.finiteDimensional_of_growthOn (U := U) (Z := Z) hG hfin
  have hR := GlobalTheory.T.cuspFormsRatioOnComponent_of_birational E H Dw l Xo c r U Z G hB
  have hFG := GlobalTheory.T.flagSpaceComponent_functionField_fg E H Dw l Xo c r U hU Z
  set ev := genPoint Z (cuspOn U Z G) with hev
  let S : ℕ → Submodule c.F (Om Z) := fun k =>
    if k = 0 then ⊥ else (cuspOn U Z ((a * k) • G')).map ((genVal Z).toLinearMap ∘ₗ LinearMap.mulLeft c.F (θ ^ k))
  have h1 := GlobalTheory.T.cone_degree_growth_chowForm_integrality.2.2.1 c.F _ _ ev (dimFlag Dw) a ha S (by
    intro k t ht
    by_cases hk : k = 0
    · simp only [S, hk, if_true, Submodule.mem_bot] at ht
      subst ht
      refine ⟨?_, ⟨0, 1, by simp [Submodule.one_eq_span], one_ne_zero, by simp⟩⟩
      rw [IsIntDeg, map_zero, mul_zero]
      exact isIntegral_zero
    · simp only [S, hk, if_false] at ht
      obtain ⟨f, hf, rfl⟩ := ht
      have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk
      obtain ⟨hc, hv⟩ := hmul k hk1 f hf
      exact ⟨GlobalTheory.T.isIntegralInConeDegree_of_valuativeBound c.F _ _ ev inferInstance inferInstance hFG _ _ hv, hR _ _ hc⟩)
  have hθk : ∀ k : ℕ, genVal Z (θ ^ k) ≠ 0 := fun k => by rw [map_pow]; exact pow_ne_zero _ hθ
  have h2 : growth (dimFlag Dw) (fun k => Cardinal.toENat (Module.rank c.F (cuspOn U Z ((a * k) • G')))) ≤
      growth (dimFlag Dw) (fun k => Cardinal.toENat (Module.rank c.F (S k))) :=
    GlobalTheory.DegTop.growth_mono _ fun k hk => by
      have hk0 : k ≠ 0 := by omega
      show _ ≤ Cardinal.toENat (Module.rank c.F (S k))
      have hS : S k = (cuspOn U Z ((a * k) • G')).map ((genVal Z).toLinearMap ∘ₗ LinearMap.mulLeft c.F (θ ^ k)) := if_neg hk0
      rw [hS, GlobalTheory.DegTop.rank_map_mul (U := U) (G := (a * k) • G') (hθk k)]
  have hmulG : ∀ G₀ : WTZ E, growth (dimFlag Dw) (fun k => Cardinal.toENat (Module.rank c.F (cuspOn U Z ((a * k) • G₀)))) =
      growthOn U Z (a • G₀) := fun G₀ => by
    rw [growthOn]
    congr 1
    funext k
    rw [mul_nsmul]
  have h3 : growth (dimFlag Dw) (fun k => Cardinal.toENat (Module.rank c.F (cuspOn U Z ((a * k) • G')))) =
      (a : ℝ≥0∞) ^ dimFlag Dw * growthOn U Z G' := by
    rw [hmulG, GlobalTheory.T.cuspFormGrowthOnComponent_nsmul E H Dw l Xo c r U hU Z G' hG' a ha]
  have h4 : growth (dimFlag Dw) (fun k => hilb ev (a * k)) ≤ (a : ℝ≥0∞) ^ dimFlag Dw * growthOn U Z G := by
    rw [← GlobalTheory.T.cuspFormGrowthOnComponent_nsmul E H Dw l Xo c r U hU Z G hG a ha, ← hmulG]
    exact GlobalTheory.DegTop.growth_mono _ fun k hk => GlobalTheory.DegTop.hilb_le hG (Nat.mul_pos ha hk)
  have haD0 : (a : ℝ≥0∞) ^ dimFlag Dw ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
  have haDT : (a : ℝ≥0∞) ^ dimFlag Dw ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top a)
  have hlow : (a : ℝ≥0∞) ^ dimFlag Dw * growthOn U Z G' ≤ growth (dimFlag Dw) (fun k => hilb ev (a * k)) :=
    h3 ▸ h2.trans h1
  have hne0 : growth (dimFlag Dw) (fun k => hilb ev (a * k)) ≠ 0 :=
    ne_bot_of_le_ne_bot (mul_ne_zero haD0 h0) hlow
  have hneT : growth (dimFlag Dw) (fun k => hilb ev (a * k)) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top haDT hfin) h4
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.cone_degree_growth_chowForm_integrality.2.1 c.F _ _ ev (dimFlag Dw) a ha hne0 hneT
  rw [GlobalTheory.T.cone_degree_growth_chowForm_integrality.1 c.F _ _ ev (dimFlag Dw) a ha δ hδ] at hlow
  rw [compDeg, ← hev, hδ.imageDeg_eq]
  first | exact (ENNReal.mul_le_mul_iff_right haD0 haDT).1 hlow | exact (ENNReal.mul_le_mul_iff_left haD0 haDT).1 hlow

end GlobalTheory.DegVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormRankLeBergmanBoundGoodCover
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.RankBergman

open MeasureTheory ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.AllWt (ptN petE muOn muPart framesOn bergE bergOn modelWt mem_cuspW cuspW_le_secZ cuspOn_le classesOver
  isProbabilityMeasure_muPart muPart_univ_le petE_ne_top bergE_le_iff)
open scoped ENNReal

set_option maxHeartbeats 1000000 in

theorem rkC_le_of_bergLe : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o →
    ∀ (la : AllWt.Weight (T.Q.Dw j)) (Z : Comp Y.d.Xo₂ Y.d.c₂) (β : ℝ), 0 ≤ β →
    BergLe Z Y.U (fun _ => D.sp.W j) Y.dict la β → (Y.rkC la Z : ℝ) ≤ β := by
  intro D T j Y e o hY la Z β hβ hB
  classical
  obtain ⟨G, hG⟩ : ∃ G : WTZ D.host.E, G = wtOf (T.Q.Dw j) la 0 := ⟨_, rfl⟩
  set σ : Y.d.c₂.F →+* ℂ := goodOf Y.d.c₂ Y.d.c₂.F.val.toRingHom with hσdef
  have hσ : GoodEmb Y.d.c₂ σ := goodEmb_goodOf _ _
  obtain ⟨th, hr, hth, hdU⟩ := hY.dictU σ hσ
  have hd : ∀ g, (Y.dict σ g).2 ∈ ((Y.U σ).X (Y.dict σ g).1).dom := hdU.2.2.2.1
  have hu := hY.unit σ hσ
  set Cw := cuspOn Y.U Z G with hCw
  set S : Submodule ℂ (FDSec (Y.U σ).X) := Submodule.span ℂ (rdU (Y.U σ) '' (Cw : Set (Rul Y.d.Xo₂ Y.d.c₂))) with hS
  set μ := muOn (Y.U σ) (D.sp.W j) (Y.dict σ) Z with hμdef
  set lw := modelWt (Y.U σ) G with hlw
  have hSsub : S ≤ holSub (Y.U σ).X lw :=
    Submodule.span_le.2 (by rintro _ ⟨f, hf, rfl⟩; exact (mem_cuspW.1 hf.1).2 σ hσ)
  have hoff : ∀ P ∈ S, ∀ z, z ∉ framesOn (Y.U σ) Z → P z.1 z.2 = 0 := fun P hP z hz =>
    eq_zero_of_mem_span_cuspOn hP hz
  have hμ1 : μ Set.univ ≤ 1 := muPart_univ_le _ _ _
  have hfin : ∀ P ∈ holSub (Y.U σ).X lw, petE (D.sp.W j) (Y.dict σ) μ lw P ≠ ⊤ := fun P hP =>
    petE_ne_top _ _ μ hμ1 hd hP

  have hpt : ∀ P ∈ S, ∀ z, ptN lw P z ^ 2 ≤ β * (petE (D.sp.W j) (Y.dict σ) μ lw P).toReal ^ 2 := by
    intro P hP z
    by_cases hz : z ∈ framesOn (Y.U σ) Z
    · have hzd := hz.1
      have hb := hB σ hσ ⟨z.1, z.2, hzd⟩ hz
      have hb' : bergE (D.sp.W j) (Y.dict σ) μ lw ⟨z.1, z.2, hzd⟩ ≤ ENNReal.ofReal β := by
        rw [hlw, hG]; exact hb
      have h := (bergE_le_iff (D.sp.W j) (Y.dict σ) μ hfin ⟨z.1, z.2, hzd⟩ ENNReal.ofReal_ne_top).1 hb' P (hSsub hP)
      have hf := hfin P (hSsub hP)
      have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hf)) h
      rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (GlobalTheory.AllWt.ptN_nonneg _ _ _), ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hβ, ENNReal.toReal_pow] at h2
      exact h2
    · have h0 : ptN lw P z = 0 := by
        simp only [ptN, Data.pnorm, hoff P hP z hz, norm_zero, zero_mul]
      rw [h0]
      nlinarith [sq_nonneg (petE (D.sp.W j) (Y.dict σ) μ lw P).toReal]
  have hzero : ∀ P ∈ S, petE (D.sp.W j) (Y.dict σ) μ lw P = 0 → P = 0 := by
    intro P hP h0
    funext k x
    by_cases hz : (⟨k, x⟩ : Σ k, Frame ((Y.U σ).X k).Ψ D.R.r) ∈ framesOn (Y.U σ) Z
    · have h1 := hpt P hP ⟨k, x⟩
      rw [h0, ENNReal.toReal_zero] at h1
      have h2 : ptN lw P ⟨k, x⟩ = 0 := by nlinarith [GlobalTheory.AllWt.ptN_nonneg lw P ⟨k, x⟩]
      have h3 := GlobalTheory.LevGeo.RankBd.pnorm_fac_pos ((Y.U σ).X k) (lw k) hz.1
      have h4 : ‖P k x‖ * _ = 0 := h2
      rcases mul_eq_zero.1 h4 with h5 | h5
      · simpa using h5
      · exact absurd h5 h3.ne'
    · exact hoff P hP ⟨k, x⟩ hz
  have hptd : ∀ (P : FDSec (Y.U σ).X) g, ptN lw P (Y.dict σ g) = ‖P (Y.dict σ g).1 (Y.dict σ g).2‖ := fun P g =>
    pnorm_eq_of_unit _ _ _ _ (hu g)
  have hmeasQ : ∀ P ∈ S, AEStronglyMeasurable
      (fun q : AutQ (D.sp.W j) => ‖P (Y.dict σ q.out).1 (Y.dict σ q.out).2‖) (muQ1 (D.sp.W j)) := by
    intro P hP
    have h := aesm_of_holSub (adelMeas_of_aut Y.d.Xo₂ Y.d.c₂ (U := Y.U) (σ := σ) (GlobalTheory.PetDef.adelAut_good Y hY σ hσ))
      _ (hSsub hP)
    have e : (fun q : AutQ (D.sp.W j) => ‖P (Y.dict σ q.out).1 (Y.dict σ q.out).2‖) =
        fun q => ‖onQ (D.sp.W j) (adel (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) P) q‖ := by
      funext q
      simp [onQ, adel]
    rw [e]
    exact h.norm
  have hmeas : ∀ P ∈ S, AEStronglyMeasurable
      (fun q : AutQ (D.sp.W j) => ‖P (Y.dict σ q.out).1 (Y.dict σ q.out).2‖) μ := by
    intro P hP
    rw [hμdef]
    unfold GlobalTheory.AllWt.muOn GlobalTheory.AllWt.muPart ProbabilityTheory.cond
    exact ((hmeasQ P hP).restrict).smul_measure _

  have hSfin : FiniteDimensional ℂ S ∧ (Module.finrank ℂ S : ℝ) ≤ β := by
    by_cases hA : muQ1 (D.sp.W j) (classesOver (D.sp.W j) (Y.dict σ) (framesOn (Y.U σ) Z)) = 0
    · have hμ0 : μ = 0 := ProbabilityTheory.cond_eq_zero_of_meas_eq_zero hA
      have hsub : Subsingleton S := ⟨fun a b => by
        have ha := hzero a a.2 (by rw [hμ0]; unfold GlobalTheory.AllWt.petE; exact eLpNorm_measure_zero)
        have hb := hzero b b.2 (by rw [hμ0]; unfold GlobalTheory.AllWt.petE; exact eLpNorm_measure_zero)
        exact Subtype.ext (ha.trans hb.symm)⟩
      refine ⟨inferInstance, ?_⟩
      rw [Module.finrank_zero_of_subsingleton]
      simpa using hβ
    · haveI : IsProbabilityMeasure μ := isProbabilityMeasure_muPart _ _ hA
      have hpet : ∀ P ∈ S, (petE (D.sp.W j) (Y.dict σ) μ lw P).toReal ^ 2 =
          ∫ q, ‖P (Y.dict σ q.out).1 (Y.dict σ q.out).2‖ ^ 2 ∂μ := by
        intro P hP
        obtain ⟨M, -, hM⟩ := exists_ptN_le (hSsub hP)
        have e : petE (D.sp.W j) (Y.dict σ) μ lw P =
            eLpNorm (fun q : AutQ (D.sp.W j) => ‖P (Y.dict σ q.out).1 (Y.dict σ q.out).2‖) 2 μ := by
          unfold GlobalTheory.AllWt.petE
          congr 1
          funext q
          exact hptd P _
        have h2 := GlobalTheory.LevGeo.RankBd.eLpNorm_sq_eq (μ := μ) (fun _ => norm_nonneg _) (hmeas P hP) (B := M)
          fun q => by rw [← hptd]; exact hM ⟨_, _, hd q.out⟩
        rw [← e] at h2
        rw [← ENNReal.toReal_pow, h2, ENNReal.toReal_ofReal (integral_nonneg fun _ => by positivity)]
      refine GlobalTheory.Bergman.finite_and_finrank_le_of_pointwise (μ := μ)
        (fun q (P : S) => ‖(P : FDSec (Y.U σ).X) (Y.dict σ q.out).1 (Y.dict σ q.out).2‖)
        (fun q => ⟨(LinearMap.proj (R := ℂ) (φ := fun _ : Frame ((Y.U σ).X (Y.dict σ q.out).1).Ψ D.R.r => ℂ)
          (Y.dict σ q.out).2 ∘ₗ LinearMap.proj (R := ℂ) (φ := fun k => Frame ((Y.U σ).X k).Ψ D.R.r → ℂ)
          (Y.dict σ q.out).1) ∘ₗ S.subtype, fun P => rfl⟩)
        (fun P => hmeas P P.2) ?_ hβ ?_
      · intro P hP0
        refine Subtype.ext (hzero P P.2 ?_)
        unfold GlobalTheory.AllWt.petE
        have e : (fun q : AutQ (D.sp.W j) => ptN lw (P : FDSec (Y.U σ).X) (Y.dict σ q.out)) = fun _ => 0 := by
          funext q
          rw [hptd]
          exact hP0 q
        rw [e]
        exact eLpNorm_zero
      · intro P q
        have h1 := hpt P P.2 (Y.dict σ q.out)
        rw [hptd, hpet P P.2] at h1
        exact h1

  obtain ⟨hSf, hSle⟩ := hSfin
  have hcard : ∀ s : Finset Cw, LinearIndependent Y.d.c₂.F (fun i : s => (i : Cw)) → s.card ≤ Module.finrank ℂ S := by
    intro s hs
    let eq : Fin s.card ≃ s := s.equivFin.symm
    let b : Fin s.card → Rul Y.d.Xo₂ Y.d.c₂ := fun i => ((eq i : Cw) : Rul Y.d.Xo₂ Y.d.c₂)
    have hb : LinearIndependent Y.d.c₂.F b := (hs.comp eq eq.injective).map' Cw.subtype (Submodule.ker_subtype _)
    have hrd := GlobalTheory.reading_linearIndependent_secZ GlobalTheory.abelianSchemeLaws_all.1.secBaseChange (Y.U σ) (hY.unf σ hσ)
      (exZ _ G) s.card b (fun i => cuspW_le_secZ G (cuspOn_le Y.U Z G (eq i : Cw).2)) hb
    let v : Fin s.card → S := fun i => ⟨rdU (Y.U σ) (b i), Submodule.subset_span ⟨b i, (eq i : Cw).2, rfl⟩⟩
    have hv : LinearIndependent ℂ v := LinearIndependent.of_comp S.subtype hrd
    simpa using hv.fintype_card_le_finrank
  haveI : Module.Free Y.d.c₂.F Cw := Module.Free.of_divisionRing Y.d.c₂.F Cw
  have hrank : Module.rank Y.d.c₂.F Cw ≤ ((Module.finrank ℂ S : ℕ) : Cardinal) := rank_le hcard
  haveI hCf : FiniteDimensional Y.d.c₂.F Cw :=
    Module.rank_lt_aleph0_iff.1 (lt_of_le_of_lt hrank (Cardinal.nat_lt_aleph0 _))
  have h2 : Module.finrank Y.d.c₂.F Cw ≤ Module.finrank ℂ S := Module.finrank_le_of_rank_le hrank
  have h3 : GlobalTheory.AllWt.rankOn Y.U Z G ≤ Module.finrank Y.d.c₂.F Cw := by
    unfold GlobalTheory.AllWt.rankOn Formalism.HN.rkK
    exact Submodule.finrank_le _
  show (GlobalTheory.AllWt.rankOn Y.U Z (wtOf (T.Q.Dw j) la 0) : ℝ) ≤ β
  rw [← hG]
  exact le_trans (Nat.cast_le.2 (h3.trans h2)) hSle

end GlobalTheory.RankBergman
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspSectionAnnihilatorStatement
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_section_annihilator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (G : WTZ E) (e' : Ix Dw → ℤ) (f s : Rul Xo c), f ∈ cuspOn U Z G → f ≠ 0 → s ∈ secZ Xo c e' → (s * f = 0 → idem Z * s = 0) ∧ (e' none = 0 → ∀ σ, GoodEmb c σ → ∀ (q : FDSec (U σ).X), (∀ k, ContinuousOn (q k) ((U σ).X k).dom) → (∀ z ∈ framesOn (U σ) Z, rdU (U σ) (s * f) z.1 z.2 = q z.1 z.2 * rdU (U σ) f z.1 z.2) → ∀ z ∈ framesOn (U σ) Z, rdU (U σ) s z.1 z.2 = q z.1 z.2) := by
  first | exact @GlobalTheory.FlatCore.cuspOn_cancel | exact GlobalTheory.FlatCore.cuspOn_cancel | (intros; apply GlobalTheory.FlatCore.cuspOn_cancel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepExistenceStatementStatement
section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deep_existence_statement : Hypotheses2 → DeepEx := by
  first | exact @GlobalTheory.CovTop.DeepExist.deepEx | exact GlobalTheory.CovTop.DeepExist.deepEx | (intros; apply GlobalTheory.CovTop.DeepExist.deepEx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseFlagBundlePreimageModuliStatement
section
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_flagBundle_preimage_moduli : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ), Dense (genMap π ⁻¹' Set.range Y.jQ) := by
  first | exact @GlobalTheory.FlagMod.FieldFlag.dense_genMap_preimage | exact GlobalTheory.FlagMod.FieldFlag.dense_genMap_preimage | (intros; apply GlobalTheory.FlagMod.FieldFlag.dense_genMap_preimage <;> assumption)
end

