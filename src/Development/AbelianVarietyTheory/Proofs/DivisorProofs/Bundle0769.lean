import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0756
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0757
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0663
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0708
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0734
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0698
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0689
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0039
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0758
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0347
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0730
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0762
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0753

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsMonHomLiftStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_isMonHom_lift_of_grpPullback_abelian : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (i : A₀.left ⟶ A.left) (j : B₀.left ⟶ B.left),
    IsGrpPullback A₀ A (spMap π) i → IsGrpPullback B₀ B (spMap π) j → IsAbelianScheme A → IsAbelianScheme B →
    ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀] (φ : A ⟶ B), i ≫ φ.left = f₀.left ≫ j → ∃! f : A ⟶ B, IsMonHom f ∧ i ≫ f.left = f₀.left ≫ j := by
  first | exact @GlobalTheory.HomLift.existsUnique_isMonHom_lift | exact GlobalTheory.HomLift.existsUnique_isMonHom_lift | (intros; apply GlobalTheory.HomLift.existsUnique_isMonHom_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitKummerEqOfPicardTorsionFreeStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_kummer_eq_of_picard_torsionFree : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) → (∀ c : CommRing.Pic A, c ^ q = 1 → c = 1) → ∀ x : Ht q (sp A) 1 1, ∃ u : (Γ(Spec (CommRingCat.of A), ⊤))ˣ, kum q u = x := by
  first | (exact @GlobalTheory.EtC.kum_surjective) | (exact GlobalTheory.EtC.kum_surjective) | (intros; apply GlobalTheory.EtC.kum_surjective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClosureThetaRatiosOfIsClStatement
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_closure_theta_ratios_of_isCl' : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (J : Type) (t : J → Ω), M.IsCl t → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j : S.Gam × J, x = S.th j.1 * t j.2 / (S.th i.1 * t i.2)})) Ω := by
  first | exact @GlobalTheory.ZH.finite_closure_theta_ratios_of_isCl | exact GlobalTheory.ZH.finite_closure_theta_ratios_of_isCl | (intros; apply GlobalTheory.ZH.finite_closure_theta_ratios_of_isCl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalSpanCompactOrbitLieDerivativeStatement
section
open NumberField GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_span_compact_orbit_lieDerivative : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (X : GlobalTheory.CuspRep.Lie E a) (φ : GlobalTheory.CuspRep.Sm E a), FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => GlobalTheory.CuspRep.cptRep E a k φ)) → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => GlobalTheory.CuspRep.cptRep E a k (GlobalTheory.CuspRep.lie E a X φ))) := by
  first | exact @GlobalTheory.CuspRep.KFin.kfin_lie | exact GlobalTheory.CuspRep.KFin.kfin_lie | (intros; apply GlobalTheory.CuspRep.KFin.kfin_lie <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockLoweringPartEqSubFockOperatorsStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockLoweringPart_eq_sub_fockOperators : ∀ (p q r s : ℕ) (Z : Mat p q), IsPC Z → ∀ P : Pol p q r s, omAct p q r s (Matrix.kroneckerMap (· * ·) Z (1 : Mat r s)) P - omAct p q r s (Matrix.kroneckerMap (· * ·) (Jm p q * Z) (Jm r s)) P = (2 : ℂ) • minusPart (fockAct1 p q r s Z) P := by
  first | exact @GlobalTheory.FockLowDiff.lowering_eq_diff | exact GlobalTheory.FockLowDiff.lowering_eq_diff | (intros; apply GlobalTheory.FockLowDiff.lowering_eq_diff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryMultiplicationDefectMulStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupLawCoboundary_multiplicationDefect_mul : ∀ (O E : Type) [CommRing O] [CommRing E] [Algebra O E] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ (f : MvPowerSeries (Fin d) E) (m n : ℕ), cob1 (up E μ) (defect μ n f) = (n : E) • cob1 (up E μ) f - pull2 (up E (nmul μ n)) (cob1 (up E μ) f) ∧ defect μ (m * n) f = (m : E) • defect μ n f + subst (up E (nmul μ n)) (defect μ m f) := by
  first | exact @GlobalTheory.QLog.cob1_defect_and_defect_mul_of_isLaw | exact GlobalTheory.QLog.cob1_defect_and_defect_mul_of_isLaw | (intros; apply GlobalTheory.QLog.cob1_defect_and_defect_mul_of_isLaw <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundarySymmCocycleModStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupLawCoboundary_symmCocycle_mod : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (N : Ideal B) (f : MvPowerSeries (Fin d) Q), DIn N f → In (RingHom.ker θ * N) (cob2 (up Q μ) (cob1 (up Q μ) f)) ∧ swap (cob1 (up Q μ) f) = cob1 (up Q μ) f := by
  first | exact @GlobalTheory.cob_symCoc_mod | exact GlobalTheory.cob_symCoc_mod | (intros; apply GlobalTheory.cob_symCoc_mod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameWeightSingularWeightSmoothLeviNonnegStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameWeight_singularWeight_smooth_leviNonneg : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → ∀ δ : ℝ, (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), ∀ i y, y ∈ (A.chart i).source → y ∉ A.zeroSet s → ∀ ξ : Fin n → ℂ, 0 ≤ A.leviAt i (fun x => A.ph E i x + α * psi A L s x) y ξ) → ∀ (U : Set Y) (z : Y → V n) (β : ι → Y → ℂ), Etale A U z → A.IsFrameOn (A.kap + E) U β → (∀ y ∈ U, y ∉ A.zeroSet s) → SmoothR n (fun y : U => z y) (fun y : U => GlobalTheory.OTY.TwEst.wt A E β z y) ∧ SmoothR n (fun y : U => z y) (fun y : U => psi A L s y) ∧ ∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), LeviNonneg n (fun y : U => z y) (fun y : U => GlobalTheory.OTY.TwEst.wt A E β z y + α * psi A L s y) := by
  first | exact @GlobalTheory.OTY.TwEst.wt_psi_smooth_leviNonneg | exact GlobalTheory.OTY.TwEst.wt_psi_smooth_leviNonneg | (intros; apply GlobalTheory.OTY.TwEst.wt_psi_smooth_leviNonneg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramChartSubFormEntryLe
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates

namespace GlobalTheory.GramChartNear

open scoped Matrix ComplexConjugate

theorem gw_sub_jd_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (w : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (τ : X.Ψ) (a b : Fin r), (r : ℝ) * ‖w‖ ≤ 1 → ‖ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.Gw X w τ a b - ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.Jd X a b‖ ≤ 3 * ‖w‖ := by
  intro E _ _ _ r X w τ a b hrw
  set L : Matrix (Fin r) (Fin r) ℂ := mat (nmat X w) τ - 1 with hLdef
  have hL : ∀ i j, ‖L i j‖ ≤ ‖w‖ := fun i j => PoinPf.nmat_entry X w τ i j
  have hs : ∀ c : Fin r, ‖((sgn X.p0 (c : ℕ) : ℝ) : ℂ)‖ = 1 := fun c => by
    rw [Complex.norm_real, Real.norm_eq_abs, PoinPf.abs_sgn]
  have h1 : mat (nmat X w) τ = 1 + L := by rw [hLdef]; abel
  have key : PoinPf.Gw X w τ - PoinPf.Jd X =
      Lᵀ * PoinPf.Jd X + PoinPf.Jd X * L.map (starRingEnd ℂ) + Lᵀ * PoinPf.Jd X * L.map (starRingEnd ℂ) := by
    rw [PoinPf.Gw, h1, Matrix.transpose_add, Matrix.transpose_one,
      Matrix.map_add _ (map_add (starRingEnd ℂ)), Matrix.map_one _ (map_zero _) (map_one _)]
    noncomm_ring
  rw [← Matrix.sub_apply, key, Matrix.add_apply, Matrix.add_apply, PoinPf.Jd, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.mul_apply]
  simp_rw [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply]
  have t1 : ‖L b a * ((sgn X.p0 (b : ℕ) : ℝ) : ℂ)‖ ≤ ‖w‖ := by
    rw [norm_mul, hs, mul_one]; exact hL b a
  have t2 : ‖((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * (starRingEnd ℂ) (L a b)‖ ≤ ‖w‖ := by
    rw [norm_mul, hs, one_mul, Complex.norm_conj]; exact hL a b
  have t3 : ‖∑ c, L c a * ((sgn X.p0 (c : ℕ) : ℝ) : ℂ) * (starRingEnd ℂ) (L c b)‖ ≤ ‖w‖ := by
    calc _ ≤ ∑ c : Fin r, ‖L c a * ((sgn X.p0 (c : ℕ) : ℝ) : ℂ) * (starRingEnd ℂ) (L c b)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _c : Fin r, ‖w‖ * ‖w‖ := by
          refine Finset.sum_le_sum fun c _ => ?_
          rw [norm_mul, norm_mul, hs, mul_one, Complex.norm_conj]
          exact mul_le_mul (hL c a) (hL c b) (norm_nonneg _) (norm_nonneg _)
      _ = ‖w‖ * ((r : ℝ) * ‖w‖) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ ‖w‖ * 1 := mul_le_mul_of_nonneg_left hrw (norm_nonneg _)
      _ = ‖w‖ := mul_one _
  calc _ ≤ _ := norm_add₃_le
    _ ≤ ‖w‖ + ‖w‖ + ‖w‖ := add_le_add (add_le_add t1 t2) t3
    _ = 3 * ‖w‖ := by ring

end GlobalTheory.GramChartNear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInvOfDirectedUnionStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hInv_of_directed_union_subalgebras : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (S : ι → Subalgebra ℤ A), Monotone S → (∀ a, ∃ i, a ∈ S i) → (∀ i, IsUnit (q : S i)) → (∀ i, HInv q (S i)) → HInv q A := by
  first | (exact @GlobalTheory.EtC.hInv_of_directed_union) | (exact GlobalTheory.EtC.hInv_of_directed_union) | (intros; apply GlobalTheory.EtC.hInv_of_directed_union  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCechDeRhamPeriodsOfAffineBasis
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem isPer_of_basis : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (c : cechDeRhamTotalCocyclesOne (OAff (str A))) (K : Type) (W : K → A.left.affineOpens) (k : K → (Fin g → ℂ) → ℂ) (q : u.Λ → ℂ), (∀ i j, ∀ z ∈ pre u.ex (W i).1, z ∈ pre u.ex (W j).1 → ∃ l, W l ≤ W i ∧ W l ≤ W j ∧ z ∈ pre u.ex (W l).1 ∧ (∀ a : Opposite.op (W i) ⟶ Opposite.op (W l), k l z = k i z + val u.ex (W l).1 (c.1.1 _ _ a) z) ∧ ∀ a : Opposite.op (W j) ⟶ Opposite.op (W l), k l z = k j z + val u.ex (W l).1 (c.1.1 _ _ a) z) → (∀ (U : A.left.affineOpens), ∀ z ∈ pre u.ex U.1, ∃ i, W i ≤ U ∧ z ∈ pre u.ex (W i).1) → (∀ i, DifferentiableOn ℂ (k i) (pre u.ex (W i).1)) → (∀ i, ∀ z ∈ pre u.ex (W i).1, fderiv ℂ (k i) z = evForm u.ex (W i).1 z (c.1.2 (Opposite.op (W i)))) → (∀ i (l : u.Λ), ∀ z ∈ pre u.ex (W i).1, k i (z + l) = k i z + q l) → IsPer u.ex u.Λ (Hyp1.mk _ c) q := by
  intro A _ g L u c K W k q hcomp hbasis hdiff hder hper
  classical
  obtain ⟨hopen, hvd, hpp, hvp, -, hmono, -, -, hres, halg, -, -⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u
  have hev := GlobalTheory.T.uniformisedOneFormEvaluation_rules A g L u
  have hevres := GlobalTheory.T.evForm_restriction_eq A g L u
  let f : ∀ (U V : A.left.affineOpens), V ≤ U → Sec (str A) V.1 := fun U V h ↦
    c.1.1 (Opposite.op U) (Opposite.op V) (homOfLE h).op
  have hf : ∀ (U V T : A.left.affineOpens) (h : V ≤ U) (h' : T ≤ V), ∀ z ∈ pre u.ex T.1,
      val u.ex T.1 (f U T (h'.trans h)) z = val u.ex V.1 (f U V h) z + val u.ex T.1 (f V T h') z := by
    intro U V T h h' z hz
    have e : f U T (h'.trans h) = Sec.res (str A) h' (f U V h) + f V T h' :=
      cechDeRhamTotalCocyclesOne.comp c (homOfLE h).op (homOfLE h').op
    obtain ⟨ev, hev⟩ := halg T.1 z hz
    rw [← hres V.1 T.1 h' _ z hz, e]
    exact (hev _).trans ((map_add ev _ _).trans (congrArg₂ _ (hev _).symm (hev _).symm))
  let h : A.left.affineOpens → (Fin g → ℂ) → ℂ := fun U z ↦
    if hz : z ∈ pre u.ex U.1 then
      k (hbasis U z hz).choose z - val u.ex _ (f U _ (hbasis U z hz).choose_spec.1) z else 0
  have hh : ∀ (U : A.left.affineOpens) i (hi : W i ≤ U), ∀ z ∈ pre u.ex (W i).1,
      h U z = k i z - val u.ex _ (f U _ hi) z := by
    intro U i hi z hz
    have hzU : z ∈ pre u.ex U.1 := hmono _ _ hi hz
    obtain ⟨hj, hzj⟩ := (hbasis U z hzU).choose_spec
    simp only [h, dif_pos hzU]
    generalize_proofs p1 p2
    generalize p1.choose = j at *
    obtain ⟨l, hli, hlj, hzl, e1, e2⟩ := hcomp i j z hz hzj
    have a1 := hf U _ _ hi hli z hzl
    have a2 := hf U _ _ hj hlj z hzl
    have b1 : k l z = k i z + val u.ex _ (f _ _ hli) z := e1 _
    have b2 : k l z = k j z + val u.ex _ (f _ _ hlj) z := e2 _
    linear_combination b1 - b2 - a1 + a2
  have hnhds : ∀ (U : A.left.affineOpens) i (hi : W i ≤ U), ∀ z ∈ pre u.ex (W i).1,
      h U =ᶠ[nhds z] fun y ↦ k i y - val u.ex _ (f U _ hi) y := fun U i hi z hz ↦
    Filter.eventually_of_mem ((hopen _).mem_nhds hz) fun y hy ↦ hh U i hi y hy
  refine ⟨c, h, rfl, ⟨fun U z hz ↦ ?_, fun U V a z hz ↦ ?_, fun U z hz ↦ ?_⟩, fun U l z hz ↦ ?_⟩
  · obtain ⟨i, hi, hzi⟩ := hbasis U z hz
    have n := (hopen _).mem_nhds hzi
    exact ((((hdiff i).differentiableAt n).sub ((hvd _ _).differentiableAt n)).congr_of_eventuallyEq
      (hnhds U i hi z hzi)).differentiableWithinAt
  · obtain ⟨i, hi, hzi⟩ := hbasis V z hz
    have hVU : V ≤ U := leOfHom a.unop
    have a1 := hf U V _ hVU hi z hzi
    change _ = _ + val u.ex V.1 (f U V hVU) z
    rw [hh V i hi z hzi, hh U i (hi.trans hVU) z hzi, a1]
    ring
  · obtain ⟨i, hi, hzi⟩ := hbasis U z hz
    have n := (hopen _).mem_nhds hzi
    refine (hnhds U i hi z hzi).fderiv_eq.trans ((fderiv_fun_sub ((hdiff i).differentiableAt n)
      ((hvd _ (f U _ hi)).differentiableAt n)).trans ?_)
    rw [hder i z hzi, sub_eq_iff_eq_add]
    refine (congrArg _ (cechDeRhamTotalCocyclesOne.conn c (homOfLE hi).op)).trans ((map_add _ _ _).trans ?_)
    exact congrArg₂ _ (hevres U (W i) (homOfLE hi).op _ z hzi) ((hev _ z hzi).2.2 _)
  · obtain ⟨i, hi, hzi⟩ := hbasis U z hz
    rw [hh U i hi z hzi, hh U i hi _ ((hpp _ l z).2 hzi), hper i l z hzi, hvp _ (f U _ hi)]
    ring

end GlobalTheory.CechPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCechDeRhamPeriodsZeroClassEqZero
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem zero_periods_eq_zero : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ q, IsPer u.ex u.Λ 0 q → q = 0 := by
  intro A _ g L u q hq
  obtain ⟨hopen, -, hadd, -, hinf, -, -, hbasis, -, -, -, htop⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u
  obtain ⟨h, ⟨hdiff, hres0, hder0⟩, hper⟩ := GlobalTheory.T.exists_holomorphic_primitive_of_cechDeRham_periods A g L u 0 q hq 0 (map_zero _)
  have hres : ∀ (U V : A.left.affineOpens), V.1 ≤ U.1 → ∀ z ∈ pre u.ex V.1, h V z = h U z := by
    intro U V hVU z hz
    have := hres0 U V (homOfLE hVU).op z hz
    rw [this]
    change h U z + valAt' _ _ (0 : Γ(A.left, V.1)) = h U z
    unfold valAt' valAt
    split_ifs <;> simp
  have hder : ∀ (U : A.left.affineOpens), ∀ z ∈ pre u.ex U.1, fderiv ℂ (h U) z = 0 := by
    intro U z hz
    rw [hder0 U z hz]
    change evForm u.ex U.1 z 0 = 0
    simp
  have hex : ∀ z, ∃ U : A.left.affineOpens, z ∈ pre u.ex U.1 := fun z ↦ by
    obtain ⟨W, -, hW⟩ := hbasis ⊤ z (htop z)
    exact ⟨W, hW⟩
  choose Uz hUz using hex
  let G : (Fin g → ℂ) → ℂ := fun z ↦ h (Uz z) z
  have hG : ∀ (U : A.left.affineOpens), ∀ z ∈ pre u.ex U.1, G z = h U z := by
    intro U z hz
    obtain ⟨W, hWle, hW⟩ := hbasis (U.1 ⊓ (Uz z).1) z (by rw [hinf]; exact ⟨hz, hUz z⟩)
    have h1 := hres U W (hWle.trans inf_le_left) z hW
    have h2 := hres (Uz z) W (hWle.trans inf_le_right) z hW
    simp only [G]
    rw [← h1, ← h2]
  have hloc : ∀ z, G =ᶠ[nhds z] h (Uz z) := fun z ↦ by
    filter_upwards [(hopen _).mem_nhds (hUz z)] with w hw
    exact hG _ w hw
  have hGd : Differentiable ℂ G := fun z ↦
    (((hdiff (Uz z)).differentiableAt ((hopen _).mem_nhds (hUz z)))).congr_of_eventuallyEq (hloc z)
  have hGf : ∀ z, fderiv ℂ G z = 0 := fun z ↦ by
    rw [(hloc z).fderiv_eq]; exact hder _ z (hUz z)
  funext l
  have hl : (0 : Fin g → ℂ) + l ∈ pre u.ex (Uz 0).1 := (hadd _ l 0).2 (hUz 0)
  have e1 := hper (Uz 0) l 0 (hUz 0)
  have e2 := hG (Uz 0) _ hl
  have e3 := is_const_of_fderiv_eq_zero hGd hGf ((0 : Fin g → ℂ) + l) 0
  have e4 := hG (Uz 0) 0 (hUz 0)
  simp only [Pi.zero_apply]
  linear_combination -e1 - e2 + e3 + e4

end GlobalTheory.CechPer
end

