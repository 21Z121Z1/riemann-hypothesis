import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3459
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2409
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantHeatOperatorOfSymmetricRelat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3384
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3460
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2819
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3465
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallinePeriodEqCechDeRhamPeriod
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0638
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThickId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2510
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3447
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3450
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2871
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0898
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0893
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0905
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0895
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2584
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2680
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasRepresentingSchemePinchedBase
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3461
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3401
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3376
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerField

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaugeUnitHasGeneratorWeightOnPreimagesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gauge_unit_has_generator_weight_on_preimages : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (dd : Fin n → Fld Y.H.left) (D : R → R) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (h₁ : Heat Y.H ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) Q.P.L dd D) (e : LB.Gen (LB.LinComb Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1])) (β : Q.X), (∀ (j : Fin 2 → Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ LB.wchart Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j → IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V))) → ∀ (p : h₁.J × (Fin 2 → Q.P.L.ι)) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ GlobalTheory.Heat.Gauge.W Y.q.left h₁ p → IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (GlobalTheory.Heat.Gauge.gU Y.q.left h₁ e p).val (Y.q.left ⁻¹ᵁ V)) := by
  first | exact @GlobalTheory.Heat.Gauge.gU_isWt | exact GlobalTheory.Heat.Gauge.gU_isWt | (intros; apply GlobalTheory.Heat.Gauge.gU_isWt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaugeUnitsTransitionRelationOnOverlapsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gauge_units_transition_relation_on_overlaps : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (X : Scheme.{0}) (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D) (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1])), L.IsLB → e.IsGen → ∀ (p p' : h₁.J × (Fin 2 → L.ι)) (O : G.left.Opens), O ≤ GlobalTheory.Heat.Gauge.W m h₁ p ⊓ GlobalTheory.Heat.Gauge.W m h₁ p' → pbT m (L.g (p.2 0) (p'.2 0)).val O * rsT (GlobalTheory.Heat.Gauge.gU m h₁ e p').val O = rsT (GlobalTheory.Heat.Gauge.gU m h₁ e p).val O * pbT m₁ (L.g (h₁.j p.1) (h₁.j p'.1)).val O := by
  first | exact @GlobalTheory.Heat.Gauge.gU_transition | exact GlobalTheory.Heat.Gauge.gU_transition | (intros; apply GlobalTheory.Heat.Gauge.gU_transition <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaugedChartFunctionEqGaugePowerMulStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gauged_chart_function_eq_gauge_power_mul : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (X : Scheme.{0}) (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D) (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1])), L.IsLB → e.IsGen → ∀ (k : ℕ) (σ : SecM m₁ L k) (ρ : SecM m L k), (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J → sval ρ r z J = sval σ r z J * ((val e r z J) ^ k).val) → ∀ (p : h₁.J × (Fin 2 → L.ι)), rsT (ρ.f fun _ => p.2 0) (GlobalTheory.Heat.Gauge.W m h₁ p) = (GlobalTheory.Heat.Gauge.gU m h₁ e p).val ^ k * rsT (σ.f fun _ => h₁.j p.1) (GlobalTheory.Heat.Gauge.W m h₁ p) := by
  first | exact @GlobalTheory.Heat.Gauge.chart_fn_mul_gen_pow | exact GlobalTheory.Heat.Gauge.chart_fn_mul_gen_pow | (intros; apply GlobalTheory.Heat.Gauge.chart_fn_mul_gen_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaugedLocalHeatOperatorPowerMulStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gauged_local_heat_operator_power_mul : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (X : Scheme.{0}) (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D) (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1])), (∀ a, IsField ⊤ (dd a)) → ∀ (c : R), 2 * c = 1 → ∀ (p : h₁.J × (Fin 2 → L.ι)) (k : ℕ) (O : G.left.Opens), O ≤ GlobalTheory.Heat.Gauge.W m h₁ p → ∀ (f : Γ(G.left, O)), op G dd h₁.Θ h₁.u (GlobalTheory.Heat.Gauge.gD m h₁ e p) (GlobalTheory.Heat.Gauge.gP m h₁ e c p) (GlobalTheory.Heat.Gauge.gP' m h₁ e c p) k O (rsT (GlobalTheory.Heat.Gauge.gU m h₁ e p).val O ^ k * f) = rsT (GlobalTheory.Heat.Gauge.gU m h₁ e p).val O ^ k * op G dd h₁.Θ h₁.u (h₁.d p.1) (h₁.p p.1) (h₁.p' p.1) k O f := by
  first | exact @GlobalTheory.Heat.Gauge.op_gauged | exact GlobalTheory.Heat.Gauge.op_gauged | (intros; apply GlobalTheory.Heat.Gauge.op_gauged <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussManinPeriodsHolds
section
open GlobalTheory.AnPer

namespace GlobalTheory.PeriodFamily

theorem gaussManinPeriods_holds : GlobalTheory.Published.GaussManinPeriods := by
  refine gaussManinPeriods_of_span_taylor ?_ GlobalTheory.AnPer.TaylorClause.pTaylor0
  intro A _ g hA _ L u P hP
  refine GlobalTheory.CechPer.span_periods_eq_top_and_finrank A g L u hA P fun c => ?_
  exact GlobalTheory.PerLink.main A g L u c.1
    { toFun := fun l => P l c, map_zero' := by simp, map_add' := fun x y => by simp }
    _ (fun _ => rfl) (hP c)

end GlobalTheory.PeriodFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreIsGrpPullbackOfUniversalTriple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

theorem genOf_isGrpPullback : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] (y : Sp (FractionRing R) ⟶ Xo.XF c) (t : SAB H (Sp R)) (tF : SAB H (Xo.XF c)), GlobalTheory.UPoinc.GenOf Xo c y t → SABMap tF Xo.univ.t (pullback.fst _ _) → ∃ α : pullback t.G.hom (jK R) ⟶ tF.G.left, IsGrpPullback ((Over.pullback (jK R)).obj t.G) tF.G y α := by
  intro E _ _ _ H Dw l Xo c R _ _ y t tF hy mF
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := hy
  obtain ⟨b⟩ := GlobalTheory.TraitOrder.cancel rfl mF m₂
  obtain ⟨e, he, -⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.grpPullback_iso (isGrpPullback_pullback t.G (jK R)) m₁.cart
  haveI := he
  exact ⟨e.hom.left ≫ b.φ,
    ((ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_of_iso e).comp b.cart).congr (Category.id_comp _) rfl⟩

end GlobalTheory.UPoinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodAtOfAntitoneGapWeightStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_at_of_antitone_gap_weight : Hypotheses2 → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (s : ℤ), Even n → (∀ τ, Antitone ((laOf (T.Q.Dw j) a n + s • hodgeWt (T.Q.Dw j)) τ)) → (∀ τ, 1 ≤ gap ((laOf (T.Q.Dw j) a n + s • hodgeWt (T.Q.Dw j)) τ) ((T.Q.Dw j).p - 1)) → Y.GoodAt (shiftG (T.Q.Dw j) a n s) := by
  first | exact @GlobalTheory.CovTop.ShiftGood.goodAt_shiftG | exact GlobalTheory.CovTop.ShiftGood.goodAt_shiftG | (intros; apply GlobalTheory.CovTop.ShiftGood.goodAt_shiftG <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeOfSqZero
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBLift

section
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.Obs

theorem abLift_of_prim (hP : PrimitiveExtendedDegTwoVanish) : AbLift := by
  intro R _ I hI A _ g hA hg X₀ Y₀ i i' ψ₀ ψ₁ ψ₂ hi hi' e₀ e₁ e₂ c hc
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  obtain ⟨hB, ⟨u, hu⟩, hall⟩ := GlobalTheory.T.small_affine_basis_and_transition_units_lift R I hI _ _ A.hom i L hi hL
  obtain ⟨hun, hdef, hnear⟩ := hall u hu
  obtain ⟨T, _, _, H, K₀, K₁, K₂, le₀, le₁, le₂, v, hH, hv, hrel⟩ := GlobalTheory.T.multiplicative_relation_of_pullback_iso_thickening R I hI _ _ _ _ A.hom (A ⊗ A).hom i i'
    _ _ _ (overW μ[A]) (overW (fst A A)) (overW (snd A A)) ψ₀ ψ₁ ψ₂ L hL u hi' hB hu e₀ e₁ e₂ hc
  obtain ⟨R₁, _, _, q, hq, hprim⟩ := GlobalTheory.T.flat_coefficient_extension_H2_class R I
  haveI : Smooth A.hom := SmoothOfRelativeDimension.smooth g _
  haveI : Smooth (A ⊗ A).hom := by
    rw [← Over.w (fst A A)]
    haveI : Smooth (fst A A).left := inferInstanceAs (Smooth (pullback.fst A.hom A.hom))
    infer_instance
  have hpi := hprim _ _ _ _ (pullMap (overW μ[A]) _ H K₀ le₀) (pullMap (overW (fst A A)) _ H K₁ le₁)
    (pullMap (overW (snd A A)) _ H K₂ le₂)
    (fun t ↦ haveI := GlobalTheory.LiftSys.smooth_sec_affine A.hom ((smallG i L).obj t).unop
      inferInstanceAs (Module.Flat R (Sec A.hom ((smallG i L).obj t).unop.1)))
    (fun t ↦ haveI := GlobalTheory.LiftSys.smooth_sec_affine (A ⊗ A).hom (H.obj t).unop
      inferInstanceAs (Module.Flat R (Sec (A ⊗ A).hom (H.obj t).unop.1)))
    (GlobalTheory.T.additiveClassDegreeTwo_vanish_affineBases_alt hP R R₁ q hq A g hA hg _ T _ H K₀ K₁ K₂ le₀ le₁ le₂ hB hH)
  obtain ⟨u', h1, h2⟩ := GlobalTheory.T.exists_cocycle_correction_square_zero_ideal R I hI _ _ _ _ _ _ _ hpi u v hun hdef hv hrel
  exact GlobalTheory.T.exists_lineBundle_lift_of_strict_cocycle R _ _ A.hom i L hL u' hB (hnear u' h1) (hall u' (hnear u' h1)).1 h2

theorem abLift : AbLift :=
  abLift_of_prim (GlobalTheory.T.primitive_degree_two_extension (GlobalTheory.T.additiveClassDegreeTwo_structureSheaf_vanish fun R _ A _ g hA hg ↦
    ⟨(GlobalTheory.T.abelian_structure_cohomology_statement R A g hA hg).1, (GlobalTheory.T.abelian_structure_cohomology_statement R A g hA hg).2.1⟩))

end

theorem exists_fac_quot {R K : Type} [CommRing R] [Field K] (J : Ideal R) (hJ : J ^ 2 = ⊥) (s : Sp K ⟶ Sp R) :
    ∃ s' : Sp K ⟶ Sp (R ⧸ J), s' ≫ spMap (Ideal.Quotient.mk J) = s := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective s
  have h : ∀ a ∈ J, φ.hom a = 0 := fun a ha ↦ by
    have h2 : a ^ 2 = 0 := by simpa [hJ] using Ideal.pow_mem_pow ha 2
    have := congrArg φ.hom h2
    rw [map_pow, map_zero] at this
    exact pow_eq_zero_iff two_ne_zero |>.1 this
  refine ⟨spMap (Ideal.Quotient.lift J φ.hom h), ?_⟩
  rw [← Spec.map_comp]
  rfl

theorem exists_fam {S : Scheme.{0}} {A U T : Over S} [GrpObj A] [IsLocallyNoetherian U.left] (hA : IsAbelianScheme A)
    (p : T ⟶ U) (hp : ∀ (K : Type) [Field K] (s : Sp K ⟶ S) (t : Over.mk s ⟶ U), ∃ t' : Over.mk s ⟶ T, t' ≫ p = t)
    {N : LB (A ⊗ T).left} (hN : N.IsLB) (ha : IsAdditive N) (c : Pic (A ⊗ U).left)
    (hc : CechPic.pull (A ◁ p).left c = cls N hN) :
    ∃ (M : LB (A ⊗ U).left) (hM : M.IsLB), IsAdditive M ∧
      ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ T), evc hM a (t ≫ p) = evc hN a t := by
  obtain ⟨M, hM, e⟩ := cls_surj (c - CechPic.pull (lift 1 (snd A U)).left c)
  have k : ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ U), evc hM a t =
      CechPic.pull (lift a t).left c - CechPic.pull (lift (1 : Y ⟶ A) t).left c := fun Y a t ↦ by
    rw [evc, e, map_sub, ← CechPic.pull_comp, ← Over.comp_left, comp_lift, MonObj.comp_one, lift_snd]
  have k' : ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ T), CechPic.pull (lift a (t ≫ p)).left c = evc hN a t :=
    fun Y a t ↦ by
    rw [evc, ← hc, ← CechPic.pull_comp, ← Over.comp_left, lift_whiskerLeft]
  have key : ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ T), evc hM a (t ≫ p) = evc hN a t := fun Y a t ↦ by
    rw [k, k', k', ha.evc_one hN, sub_zero]
  refine ⟨M, hM, GlobalTheory.T.isAdditive_lineBundleFamily_of_geometricFibres S A U hA M hM ((triv_ev_iff hM _ _).2 (by rw [k, sub_self])) fun K _ _ s t ↦ ?_, key⟩
  obtain ⟨t', rfl⟩ := hp K s t
  refine (isAdditive_iff (pull_isLB hM _)).2 fun Y a a' y ↦ ?_
  simp only [evc_ev hM, lift_fst, lift_snd_assoc]
  simp only [← Category.assoc, key]
  exact (isAdditive_iff hN).1 ha Y a a' _

theorem hasRep_of_sqZero : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ J : Ideal R, J ^ 2 = ⊥ → HasRep A g (Over.mk (spMap (Ideal.Quotient.mk J))) → HasRep A g (𝟙_ _) := by
  intro R _ _ A _ g hA hg J hJ ⟨B, b, P, hP, hb⟩
  refine GlobalTheory.T.representingScheme_of_finite_surjective_lift R A g hA hg B _ b P ?_ ?_ hP hb fun x ↦ ?_
  · haveI : IsClosedImmersion (spMap (Ideal.Quotient.mk J)) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    exact inferInstanceAs (IsFinite (spMap (Ideal.Quotient.mk J)))
  · exact GlobalTheory.LiftSys.surjective_spMap_sqZero _ Ideal.Quotient.mk_surjective hJ
      fun _ h ↦ Ideal.Quotient.eq_zero_iff_mem.1 h
  obtain ⟨C, _, σ, j, hs, hj, ho, hx⟩ := GlobalTheory.T.exists_affine_chart_smooth_lift_sqZero R J hJ g B b hb.smooth x
  have hN : (ev P (fst A _) (snd A _ ≫ j)).IsLB := pull_isLB hP.fam.isLB _
  have ha : IsAdditive (ev P (fst A _) (snd A _ ≫ j)) := (isAdditive_iff hN).2 fun Y a a' y ↦ by
    simp only [evc_ev hP.fam.isLB, lift_fst, lift_snd_assoc]
    exact (isAdditive_iff hP.fam.isLB).1 hP.fam.add Y a a' _
  obtain ⟨c, hc⟩ := GlobalTheory.T.additiveFamily_reduction_lifts_lineBundle abLift R J hJ A g hA hg C σ _ hN ha
  haveI : Smooth (spMap σ) := SmoothOfRelativeDimension.smooth g _
  haveI : IsLocallyNoetherian (Over.mk (spMap σ)).left :=
    LocallyOfFiniteType.isLocallyNoetherian (spMap σ)
  obtain ⟨M, hM, hMa, key⟩ := exists_fam hA (fst (Over.mk (spMap σ)) (Over.mk (spMap (Ideal.Quotient.mk J))))
    (fun K _ s t ↦ by
      obtain ⟨s', hs'⟩ := exists_fac_quot J hJ s
      exact ⟨lift t (Over.homMk s' hs'), lift_fst _ _⟩) hN ha c hc
  refine ⟨_, M, j, ⟨hM, hMa⟩, hs, hj, ho, hx, (same_iff hM hP.fam.isLB _ _).2 ?_⟩
  rw [key, evc_ev hP.fam.isLB, lift_fst, lift_snd_assoc]

end GlobalTheory.LBLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasRepresentingSchemePinchedBaseStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasRepresentingScheme_pinchedBase : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → HasRepAF A g (Over.mk (spMap (algebraMap R R'))) → HasRep A g (Over.mk (spMap (Ideal.Quotient.mk c))) → HasRep A g (𝟙_ _) := by
  first | exact @GlobalTheory.Pinch.hasRep_pinched | exact GlobalTheory.Pinch.hasRep_pinched | (intros; apply GlobalTheory.Pinch.hasRep_pinched <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorConstMulDerivationTerm
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatOpConst

open GlobalTheory.HeatGlue

section General

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {n : ℕ}

theorem op_constFn_mul {vv : Fin n → TanM (𝟙 (Sp R)) G} {dd : Fin n → Fld G.left} (hinv : ∀ a, IsInv G (vv a) (dd a))
    {D : R → R} (Θ : Matrix (Fin n) (Fin n) R) (u : Fin n → R) {d : Fld G.left} {W : G.left.Opens}
    (hd : IsLift G D W d) (p p' : Γ(G.left, W)) (k : ℕ) {O : G.left.Opens} (hO : O ≤ W) (c : R) (f : Γ(G.left, O)) :
    op G dd Θ u d p p' k O (constFn G.hom O c * f) =
      constFn G.hom O c * op G dd Θ u d p p' k O f + constFn G.hom O (2 * (k : R) * D c) * f := by
  have e1 : ∀ a (g : Γ(G.left, O)), dd a O (constFn G.hom O c * g) = constFn G.hom O c * dd a O g := fun a g => by
    rw [(isDer_of_isField (hinv a).1 le_top).2, IsInv.apply_constFn G (vv a) (dd a) (hinv a) O c, mul_zero, add_zero]
  have e2 : d O (constFn G.hom O c * f) = constFn G.hom O c * d O f + f * constFn G.hom O (D c) := by
    rw [(isDer_of_isField hd.1 hO).2, hd.2 O hO c]
  have e3 : constFn G.hom O (k : R) = (k : Γ(G.left, O)) := by simp [constFn]
  have e4 : ∀ a b : Γ(G.left, O), a * (constFn G.hom O c * b) = constFn G.hom O c * (a * b) := fun a b => by ring
  unfold op
  rw [e2, constFn_mul, constFn_mul, constFn_two, e3]
  simp only [e1, e4, ← Finset.mul_sum]
  ring

variable {X Y Z : Scheme.{0}}

theorem gs_rsT (r : Z ⟶ Y) (z : Z) {U V : Y.Opens} (hle : V ≤ U) (h : r z ∈ V) (a : Γ(Y, U)) :
    gs r z V (rsT a V) = gs r z U a := by
  rw [GlobalTheory.KS.rsT_of_le hle]
  exact gs_res r z hle h a

theorem gs_constFn_of_mem (p : Y ⟶ Sp R) (r : Z ⟶ Y) (z : Z) {V : Y.Opens} (h : r z ∈ V) (e : R) :
    gs r z V (constFn p V e) = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom e) := by
  rw [← GlobalTheory.HeatTermLin.gs_constFn, ← resG_constFn p (le_top : V ≤ ⊤)]
  exact gs_res r z le_top h _

theorem le_wchart {m : Y ⟶ X} {L : LB X} {V : Y.Opens} {j : L.ι} (h : V ≤ m ⁻¹ᵁ L.U j) :
    V ≤ LB.wchart L (K := Fin 1) (fun _ => m) (fun _ => j) := fun _ hy => Set.mem_iInter.2 fun _ => h hy

end General

theorem heat_const_mul : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (vv : Fin n → TanM (𝟙 (Sp R)) Y.H) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vv a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left Q.P.L dd ⇑D) (k : ℕ) (c : R) (τ τ' τu τu' : SecM Y.q.left Q.P.L k), h.Acts k τ τ' → h.Acts k τu τu' → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval τ r z J = gs (r ≫ Y.H.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * sval τu r z J) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval τ' r z J = gs (r ≫ Y.H.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * sval τu' r z J + gs (r ≫ Y.H.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (2 * (k : R) * D c)) * sval τu r z J := by
  intro R _ _ Q O _ _ _ oa Y n vv dd hinv D h k c τ τ' τu τu' a₁ a₂ hτ Z r z J hJ
  have hle : ∀ i, h.W i ≤ LB.wchart Q.P.L (K := Fin 1) (fun _ => Y.q.left) (fun _ => h.j i) := fun i =>
    le_wchart (h.le i)
  have s₁ : ∀ i, rsT (τ.f fun _ => h.j i) (h.W i) = constFn Y.H.hom (h.W i) c * rsT (τu.f fun _ => h.j i) (h.W i) := by
    intro i
    refine fn_ext fun y hy => ?_
    obtain ⟨I, hI, eI⟩ := exists_good Q.P.L Q.P.isLB y (K := Unit) (fun _ => 𝟙 _ ≫ Y.q.left) (fun _ => h.j i)
      (fun _ _ _ => rfl) (fun _ => h.le i hy)
    have e := hτ _ (𝟙 _) y I hI
    rw [sval_of τ _ y I (fun _ => h.j i) (fun _ => eI ()), sval_of τu _ y I (fun _ => h.j i) (fun _ => eI ())] at e
    refine (gs_rsT (𝟙 _) y (hle i) hy _).trans (e.trans (Eq.symm ?_))
    exact (gs_mul (𝟙 _) y _ hy _ _).trans (congrArg₂ (· * ·) (gs_constFn_of_mem _ _ y hy c)
      (gs_rsT (𝟙 _) y (hle i) hy _))
  have s₂ : ∀ i, rsT (τ'.f fun _ => h.j i) (h.W i) = constFn Y.H.hom (h.W i) c * rsT (τu'.f fun _ => h.j i) (h.W i) +
      constFn Y.H.hom (h.W i) (2 * (k : R) * D c) * rsT (τu.f fun _ => h.j i) (h.W i) := by
    intro i
    rw [a₁ i, a₂ i, s₁ i]
    exact op_constFn_mul hinv h.Θ h.u (h.lift i) (h.p i) (h.p' i) k le_rfl c _
  obtain ⟨i, hi⟩ : ∃ i, r z ∈ h.W i := TopologicalSpace.Opens.mem_iSup.1 (h.cover.ge trivial)
  have t : ∀ s : SecM Y.q.left Q.P.L k, sval s r z J =
      (trF (K := Fin 1) (fun _ => Y.q.left) (fun _ => (k : ℤ)) r z (fun _ => J (r ≫ Y.q.left)) (fun _ => h.j i)).val *
        gs r z (h.W i) (rsT (s.f fun _ => h.j i) (h.W i)) := fun s =>
    (sec_trans s r z (hJ.mem _ r) (hle i hi)).trans (congrArg _ (gs_rsT r z (hle i) hi _).symm)
  rw [t τ', t τu', t τu, s₂ i, gs_add r z _ hi, gs_mul r z _ hi, gs_mul r z _ hi, gs_constFn_of_mem _ r z hi,
    gs_constFn_of_mem _ r z hi]
  ring

end GlobalTheory.HeatOpConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorFourierTermAlongFibreConnectionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heat_operator_fourier_term_along_fibre_connection : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] (φ : R →+* K) (e : ℕ) (ν : R) (A₀ : Over (Sp K)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsFibre Y h φ e ν A₀ m₀ → ∀ (V : h.J → Q.P.A.left.Opens) (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), IsConnK Q.P.A Q.P.L A₀ m₀ (fun r => φ (D r)) V h.j ed pb → IsDesc Y h ν m₀ V ed pb → ∀ (α : Q.X) (c : K), CoordEq Y h ν m₀ V pb α c → ∀ (σ σ' : Q.SecB e α), TActs Y h e α σ σ' → ∀ (i : Fin 4 → h.J) (T : Fin 4 → (A₀.left ⟶ A₀.left)), (∀ j, T j ≫ m₀ = m₀ ≫ Q.famφB α j) → (∀ j, T j ≫ A₀.hom = A₀.hom) → ∀ U : A₀.left.Opens, U ≤ m₀ ⁻¹ᵁ LB.wchart Q.P.L (Q.famφB α) (fun j => h.j (i j)) → (∀ j, U ≤ T j ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i j))) → pbT m₀ (σ'.f (fun j => h.j (i j))) U = 2 * (e : Γ(A₀.left, U)) * (rsT (ed _ (σ.f (fun j => h.j (i j)))) U + pbT m₀ (σ.f (fun j => h.j (i j))) U * (∑ j, ((DegPre.famε e j : ℤ) : Γ(A₀.left, U)) * pbT (T j) (pb (i j)) U + constFn A₀.hom U c)) := by
  first | exact @GlobalTheory.HeatConn.heat_term_fibre | exact GlobalTheory.HeatConn.heat_term_fibre | (intros; apply GlobalTheory.HeatConn.heat_term_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorPeriodDefectIsCocycleStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heatOperator_period_defect_isCocycle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D) (c : ℕ → Dd.toPre.X → Dd.toPre.X → R), IsBasic Y h → HasDefect Y h c → ∀ (k : ℕ), 1 ≤ k → ∀ mu mu' α, c k (mu + mu') α = c k mu α + c k mu' (α + k • mu) := by
  first | exact @GlobalTheory.HeatDefect.defect_cocycle | exact GlobalTheory.HeatDefect.defect_cocycle | (intros; apply GlobalTheory.HeatDefect.defect_cocycle <;> assumption)
end

