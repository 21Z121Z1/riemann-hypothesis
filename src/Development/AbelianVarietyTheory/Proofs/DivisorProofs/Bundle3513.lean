import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivativesCoboundaryCoeffsMemMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3482
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0579
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3201
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3485
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0184
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3210
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3328
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3208
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2496
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0062
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0160
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2749
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1133
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2531
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0773
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0663
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0934
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0750
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0862
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0640
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2619
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0090
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3486
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3487
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0026
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorEqZeroOfLogDerivCoboundary
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

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LieRigid

open GlobalTheory.ZH.CrdCalc (valR_res valR_spMap valR_eq valHom)

theorem dlg_sub {A : Type} [CommRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (L : LB B.left)
    (δ : Fld B.left) (hδ : IsField ⊤ δ) (i j : L.ι) {O T : B.left.Opens} (hO : O ≤ L.U i ⊓ L.U j) (hT : T ≤ O) :
    rsT (dlg B (𝟙 _) L δ i j O) T = rsT (dlg B (𝟙 _) L δ i j (L.U i ⊓ L.U j)) T := by
  rw [GlobalTheory.CoverRefinementPullback.dlg_res' B L δ hδ i j (hT.trans hO)]
  unfold dlg
  rw [GlobalTheory.KS.rsT_of_le hT, map_mul, GlobalTheory.CoverRefinementPullback.pbT_id' _ hO, GlobalTheory.CoverRefinementPullback.pbT_id' _ hO, ← hδ.2.2 _ _ hT le_top,
    GlobalTheory.CoverRefinementPullback.resG_resG', GlobalTheory.CoverRefinementPullback.resG_resG']
  rfl

theorem lie_inj : ∀ (R : Type) [CommRing R] [IsLocalRing R] (P : PolAV (Sp R)) (w : TanM (𝟙 (Sp R)) P.A) (δ : Fld P.A.left), IsInv P.A w δ → ∀ (K : Type) (V : K → P.A.left.Opens) (jk : K → P.L.ι), ⨆ k, V k = ⊤ → (∀ k, V k ≤ P.L.U (jk k)) → ∀ (b : ∀ k, Γ(P.A.left, V k)), (∀ k k', rsT (b k') (V k ⊓ V k') - rsT (b k) (V k ⊓ V k') = dlg P.A (𝟙 _) P.L δ (jk k) (jk k') (V k ⊓ V k')) → w = 0 := by
  intro R _ _ P w δ hδ K V jk hV hVj b hb
  have hδ1 : IsField ⊤ δ := hδ.1
  have hcob : IsCob P.L.U (fun j j' => dlg P.A (𝟙 _) P.L δ j j' (P.L.U j ⊓ P.L.U j')) := by
    refine GlobalTheory.T.isCechOneCoboundary_of_mixed_overlaps P.A.left P.L.ι K P.L.U V hV _
      (fun k k' => dlg P.A (𝟙 _) P.L δ (jk k) (jk k') (V k ⊓ V k'))
      (fun j k => rsT (dlg P.A (𝟙 _) P.L δ j (jk k) (P.L.U j ⊓ P.L.U (jk k))) (P.L.U j ⊓ V k))
      (fun j j' k => ?_) (fun j k k' => ?_) ⟨b, fun k k' => (hb k k').symm⟩
    · have t1 : P.L.U j ⊓ P.L.U j' ⊓ V k ≤ P.L.U j ⊓ P.L.U j' := inf_le_left
      have t2 : P.L.U j ⊓ P.L.U j' ⊓ V k ≤ P.L.U j ⊓ V k := le_inf (inf_le_left.trans inf_le_left) inf_le_right
      have t3 : P.L.U j ⊓ P.L.U j' ⊓ V k ≤ P.L.U j' ⊓ V k := le_inf (inf_le_left.trans inf_le_right) inf_le_right
      rw [GlobalTheory.KS.rsT_rsT (inf_le_inf le_rfl (hVj k)) t2, GlobalTheory.KS.rsT_rsT (inf_le_inf le_rfl (hVj k)) t3,
        ← GlobalTheory.CoverRefinementPullback.dlg_tri _ _ P.isLB δ hδ1 j j' (jk k) t1 (t3.trans (inf_le_inf le_rfl (hVj k)))
          (t2.trans (inf_le_inf le_rfl (hVj k)))]
      abel
    · have t1 : P.L.U j ⊓ V k ⊓ V k' ≤ V k ⊓ V k' := le_inf (inf_le_left.trans inf_le_right) inf_le_right
      have t2 : P.L.U j ⊓ V k ⊓ V k' ≤ P.L.U j ⊓ V k := inf_le_left
      have t3 : P.L.U j ⊓ V k ⊓ V k' ≤ P.L.U j ⊓ V k' := le_inf (inf_le_left.trans inf_le_left) inf_le_right
      rw [dlg_sub _ _ δ hδ1 (jk k) (jk k') (inf_le_inf (hVj k) (hVj k')) t1,
        GlobalTheory.KS.rsT_rsT (inf_le_inf le_rfl (hVj k)) t2, GlobalTheory.KS.rsT_rsT (inf_le_inf le_rfl (hVj k')) t3,
        ← GlobalTheory.CoverRefinementPullback.dlg_tri _ _ P.isLB δ hδ1 j (jk k) (jk k')
          (t2.trans (inf_le_inf le_rfl (hVj k))) (t1.trans (inf_le_inf (hVj k) (hVj k')))
          (t3.trans (inf_le_inf le_rfl (hVj k')))]
      abel
  obtain ⟨H, hH⟩ := hcob

  have hgp := GlobalTheory.Heat.DlogIndep.isGrpPullback_self P.A
  obtain ⟨u, hu⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.push_surj hgp (tv w)
  have hul : u.left = (tv w).left := (Category.comp_id _).symm.trans (congrArg (fun q => q.left) hu)
  have hut : IsTangent u :=
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.isTangent_iff hgp _).2 (by rw [hu]; exact ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem _)
  have hee : ∀ (S : Type) [CommRing S] [Algebra R S] (φ : DualNumber R →ₐ[R] S),
      φ DualNumber.eps * φ DualNumber.eps = 0 := fun S _ _ φ => by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  have hφ : ∀ (S : Type) [CommRing S] [Algebra R S] (φ : DualNumber R →ₐ[R] S),
      (algOverHom φ ≫ u : algOver R S ⟶ P.A) = (Chart.spMap (SqZero.epsTo R (φ DualNumber.eps) (hee S φ)) ≫ u) := by
    intro S _ _ φ
    have e : φ = SqZero.epsTo R (φ DualNumber.eps) (hee S φ) := DualNumber.algHom_ext (by simp [SqZero.epsTo, SqZero.dualTo_apply])
    conv_lhs => rw [e]
    rfl
  have h1 : u = 1 := GlobalTheory.Heat.DlogIndep.eq_one_of_coboundary P.isLB P.ktriv (DualNumber.eps : DualNumber R)
    DualNumber.eps_mul_eps u (fun j => -H j)
    (fun S _ _ φ y U hU => by
      rw [hφ S φ]; exact (GlobalTheory.Heat.DlogIndep.valR_translate hul hut hδ _ (hee S φ) y U hU).1)
    (fun S _ _ φ y j j' hj hj' => by
      rw [hφ S φ]
      have hU : ⊤ ≤ y.left ⁻¹ᵁ (P.L.U j ⊓ P.L.U j') := fun p hp => ⟨hj hp, hj' hp⟩
      have e₁ := congrArg (valHom (R := S) y.left _ hU) (hH j j')
      have r₁ : valHom (R := S) y.left _ hU (rsT (H j) _) = valHom (R := S) y.left _ hj (H j) := by
        rw [rsT, dif_pos inf_le_left, ← valR_eq, ← valR_eq]
        exact valR_res _ _ hU _
      have r₂ : valHom (R := S) y.left _ hU (rsT (H j') _) = valHom (R := S) y.left _ hj' (H j') := by
        rw [rsT, dif_pos inf_le_right, ← valR_eq, ← valR_eq]
        exact valR_res _ _ hU _
      simp only [dlg, GlobalTheory.Heat.DlogIndep.pbT_id, map_sub, map_mul, r₁, r₂] at e₁
      have e₂ : valHom (R := S) y.left _ hU (P.L.g j j').val * valHom (R := S) y.left _ hU (P.L.g j j')⁻¹.val = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      refine ((GlobalTheory.Heat.DlogIndep.valR_translate hul hut hδ _ (hee S φ) y _ hU).2 _).trans ?_
      simp only [valR_eq (R := S) _ _ hU, valR_eq (R := S) _ _ hj, valR_eq (R := S) _ _ hj', map_neg]
      linear_combination (φ DualNumber.eps * valHom (R := S) y.left _ hU (P.L.g j j').val) * e₁ +
        (-(φ DualNumber.eps * valHom (R := S) y.left _ hU (δ _ (P.L.g j j').val))) * e₂)
  have h2 : tv w = tv (0 : TanM (𝟙 (Sp R)) P.A) := by
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_zero, ← hu, h1, map_one]
  exact ReciprocityTheory.ChartRestriction.G.PullbackSections.tanM_ext h2

end GlobalTheory.LieRigid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoLogDetGramChangeSemiPositiveMetric
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSAmpDet

theorem chInt_smul {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (L : HermLB p) (D : ℕ) (c : ℝ) (u : SmFn p) :
    chInt L D (u.smul c).u = c * chInt L D u.u := by
  simp only [chInt, SmFn.smul, Weight.chernInt_const_mul, mul_finsum]

section
variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem vals_smul (P : Pair p) (u : SmFn p) (t : ℝ) (a b : ℤ) {ι : Type} (g : ι → X.functionField) :
    vals (upperParabolic P (u.smul t)) a b g = fun σ y i => vals P a b g σ y i * (Real.exp (-(a * (t * u.u σ y)) / 2) : ℝ) := by
  funext σ y i
  exact ((GlobalTheory.T.raiseFirstWeight_sections_loci_values_norms k X p P (u.smul t) a b).2.2 σ y (g i)).1

theorem vals_zero (P : Pair p) (u : SmFn p) (a b : ℤ) {ι : Type} (g : ι → X.functionField) :
    vals (upperParabolic P (u.smul 0)) a b g = vals P a b g := by
  rw [vals_smul]
  funext σ y i
  simp

theorem vals_one (P : Pair p) (u : SmFn p) (a b : ℤ) {ι : Type} (g : ι → X.functionField) :
    vals (upperParabolic P (u.smul 1)) a b g = vals (upperParabolic P u) a b g := by
  rw [vals_smul]
  funext σ y i
  rw [one_mul]
  exact ((GlobalTheory.T.raiseFirstWeight_sections_loci_values_norms k X p P u a b).2.2 σ y (g i)).1.symm

theorem vals_two (P : Pair p) (u : SmFn p) (t t' : ℝ) (a b : ℤ) {ι : Type} (g : ι → X.functionField) :
    vals (upperParabolic (upperParabolic P (u.smul t)) (u.smul (t' - t))) a b g = vals (upperParabolic P (u.smul t')) a b g := by
  rw [vals_smul, vals_smul, vals_smul]
  funext σ y i
  rw [mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 3
  ring

end

theorem tendsto_logDet_gram_sub : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p), P.L.SemiPos D → ∀ (ω : ∀ σ, VolDens p σ D) (r : ℕ → ℕ) (f : ∀ m, Fin (r m) → X.functionField), (∀ (m : ℕ) i, f m i ∈ P.H m 1) → (∀ m, LinearIndependent ℤ (f m)) → Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 (gdeg P.L D / D.factorial)) → ∀ (u : SmFn p) (a a' : ℝ), (up P.L u).SemiPos D → P.L.IsSelfInter a → (up P.L u).IsSelfInter a' → Tendsto (fun m : ℕ => (Real.log (gram (fun σ => (ω σ).meas) (vals P m 1 (f m))).det.re - Real.log (gram (fun σ => (ω σ).meas) (vals (upperParabolic P u) m 1 (f m))).det.re) / (m : ℝ) ^ (D + 1)) atTop (𝓝 (2 * (a' - a) / (D + 1).factorial)) := by
  intro hA k _ X _ p D hX hG P hP ω r f hf hli hr u a a' hsp ha ha'
  obtain ⟨s, hs0, hs1, hsd⟩ := GlobalTheory.T.self_intersection_metric_segment_polynomial hA k X p D hX P.L u a a' ha ha'
  set c : ℝ := 2 / ((D + 1).factorial : ℝ) with hc
  let ℓ : ℚ → ℕ → ℝ := fun t m =>
    Real.log (gram (fun σ => (ω σ).meas) (vals (upperParabolic P (u.smul (t : ℝ))) m 1 (f m))).det.re / (m : ℝ) ^ (D + 1)
  have hR := GlobalTheory.T.tendsto_sub_of_one_sided_increment_bound_derivative (Polynomial.C c * s) ℓ ?_
  · have hfun : (fun m => ℓ 0 m - ℓ 1 m) = fun m : ℕ => (Real.log (gram (fun σ => (ω σ).meas) (vals P m 1 (f m))).det.re - Real.log (gram (fun σ => (ω σ).meas) (vals (upperParabolic P u) m 1 (f m))).det.re) / (m : ℝ) ^ (D + 1) := by
      funext m
      simp only [ℓ, Rat.cast_zero, Rat.cast_one, vals_zero, vals_one, sub_div]
    have hval : (Polynomial.C c * s).eval 1 - (Polynomial.C c * s).eval 0 = 2 * (a' - a) / (D + 1).factorial := by
      simp only [Polynomial.eval_mul, Polynomial.eval_C, hs0, hs1, hc]
      ring
    rw [hfun, hval] at hR
    exact hR
  · intro t t' ht0 ht1 ht0' ht1' ε hε
    have hsemi : (upperParabolic P (u.smul (t : ℝ))).L.SemiPos D :=
      GlobalTheory.T.semiPos_raiseWeight_segment_smul k X p D P.L u t (by exact_mod_cast ht0) (by exact_mod_cast ht1) hP hsp
    have hH : ∀ (m : ℕ) i, f m i ∈ (upperParabolic P (u.smul (t : ℝ))).H m 1 := fun m i => by
      rw [(GlobalTheory.T.raiseFirstWeight_sections_loci_values_norms k X p P (u.smul (t : ℝ)) m 1).1]
      exact hf m i
    have hrk : Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop
        (𝓝 (gdeg (upperParabolic P (u.smul (t : ℝ))).L D / D.factorial)) := by
      rw [show (upperParabolic P (u.smul (t : ℝ))).L = up P.L (u.smul (t : ℝ)) from rfl,
        GlobalTheory.T.hermLineBundleGeometricDegree_raiseWeight hA k X p D hX P.L (u.smul (t : ℝ))]
      exact hr
    have hstep := GlobalTheory.T.gramDeterminant_weightShift_asymptotic_le k X p D hX hG (upperParabolic P (u.smul (t : ℝ))) hsemi ω r f hH hli hrk
      (u.smul ((t' : ℝ) - t)) ε hε
    have hch : chInt (upperParabolic P (u.smul (t : ℝ))).L D (u.smul ((t' : ℝ) - t)).u / D.factorial =
        ((t' : ℝ) - t) * (Polynomial.C c * s).derivative.eval (t : ℝ) := by
      rw [chInt_smul, Polynomial.derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C, ← hsd t, hc,
        Nat.factorial_succ]
      have hf0 : (D.factorial : ℝ) ≠ 0 := by positivity
      show ((t' : ℝ) - t) * chInt (up P.L (u.smul (t : ℝ))) D u.u / D.factorial = _
      push_cast
      field_simp
    filter_upwards [hstep, eventually_ge_atTop 1] with m hm hm1
    have hpos : (0 : ℝ) < (m : ℝ) ^ (D + 1) := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      positivity
    rw [vals_two, hch] at hm
    simp only [ℓ]
    rw [← sub_div, div_le_iff₀ hpos]
    linarith

end GlobalTheory.HSAmpDet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFamilyCoefficientIntegralTorusPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

noncomputable section

namespace GlobalTheory.UT.CoefInt

theorem coef_int : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V)
    (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (lam : FractionRing V) (th : Fam D (FractionRing V) 1),
    famProj D (FractionRing V) 1 0 th = lam • termF D (FractionRing V) 1 0 θ →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ (TK V).left) (z : Z) J, Good D.P.L z J →
      val (D.psi 0) r z J * val D.rigK r z J = 1) →
    ∀ (χ : D.X) (g : GtPtF D (FractionRing V)) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A), g.b = toUnit _ ≫ b →
    ∀ (w : Frm D (FractionRing V) 1 g.b) (x : FractionRing V), IsCoef 1 g w χ (th.s χ) x →
    ∀ z J, Good D.P.L z J →
      cst (FractionRing V) z x = cst (FractionRing V) z lam *
        (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (D.psi χ) (jFK (R := V) (FractionRing V)) z J)).val *
        sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
          ((toUnit (TF (R := V) (FractionRing V))).left ≫ (b * D.c χ).left) z J *
        (val (g.s χ) (𝟙 _) z J).val * (val w (𝟙 _) z J).val := by
  intro V _ _ D θ lam th hlam hrig χ g b hb w x hx z J hJ
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have h1 := hx z J hJ
  rw [pow_one] at h1
  obtain ⟨u, hu, hc, hrel⟩ := fe_from_zero hG D (FractionRing V) th χ
  have e1 := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 hrel _ (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left z J hJ
  have e2 := (gen_fe (D := D) (F := FractionRing V) hG 1 χ 0).2 u hu hc _ (lift (𝟙 (TF (R := V) (FractionRing V))) g.b) z J hJ
  rw [GlobalTheory.UU.uVal_one D _ _ _ _ hJ, _root_.one_mul, lift_fst, Over.id_left] at e2
  have e3 := GlobalTheory.UU.val_famMult_one D (FractionRing V) (𝟙 (TF (R := V) (FractionRing V))) hJ χ 0
  have hps : val (D.psi (χ + 0)) (jFK (R := V) (FractionRing V)) z J = val (D.psi χ) (jFK (R := V) (FractionRing V)) z J := by
    rw [add_zero]
  rw [Over.id_left, Category.id_comp, hps] at e3
  have e4 := hrig _ (jFK (R := V) (FractionRing V)) z J hJ
  have hrK : val D.rigK (jFK (R := V) (FractionRing V)) z J = rigV D (TF (R := V) (FractionRing V)).hom z J := by
    rw [DegPre.rigK, val_pull hJ]
    rfl

  have hfm : val (DegPre.famMult D (FractionRing V) 1 χ 0) (𝟙 (TF (R := V) (FractionRing V)).left) z J =
      val (D.psi χ) (jFK (R := V) (FractionRing V)) z J * val D.rigK (jFK (R := V) (FractionRing V)) z J := by
    have h0 : val (D.psi 0) (jFK (R := V) (FractionRing V)) z J = (val D.rigK (jFK (R := V) (FractionRing V)) z J)⁻¹ :=
      eq_inv_of_mul_eq_one_left e4
    rw [h0] at e3
    exact eq_mul_of_mul_inv_eq e3
  have hsχ : sval (th.s χ) (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left z J =
      sval (th.s (0 + 1 • χ)) (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left z J := by
    rw [zero_add, one_smul]
  have hfst : ((lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left ≫ (DegPre.trF D (FractionRing V) χ).left) ≫
      famBase D (FractionRing V) = 𝟙 _ := by
    show _ ≫ (fst (TF (R := V) (FractionRing V)) D.P.A).left = _
    rw [Category.assoc, ← Over.comp_left, ← Over.comp_left, DegPre.trF, lift_fst, lift_fst]; rfl
  have hsndO : lift (𝟙 (TF (R := V) (FractionRing V))) g.b ≫ DegPre.trF D (FractionRing V) χ ≫ DegPre.prB D (FractionRing V) =
      toUnit _ ≫ (b * D.c χ) := by
    rw [ReciprocityTheory.ChartRestriction.G.DVR.trF_eq, ReciprocityTheory.ChartRestriction.G.DVR.tr_pr, MonObj.comp_mul, ← Category.assoc, lift_fst, Category.id_comp,
      lift_snd, hb, MonObj.comp_mul]
    rfl
  have hsnd : ((lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left ≫ (DegPre.trF D (FractionRing V) χ).left) ≫
      (DegPre.prB D (FractionRing V)).left = (toUnit (TF (R := V) (FractionRing V))).left ≫ (b * D.c χ).left := by
    rw [Category.assoc, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left, hsndO]
  have hs0 : sval (th.s 0) ((lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left ≫ (DegPre.trF D (FractionRing V) χ).left) z J =
      sval (famProj D (FractionRing V) 1 0 th) ((lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left ≫
        (DegPre.trF D (FractionRing V) χ).left) z J := rfl
  have t1 := sval_smul' (π := famBase D (FractionRing V)) hJ
    ((lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left ≫ (DegPre.trF D (FractionRing V) χ).left) lam
    (termF D (FractionRing V) 1 0 θ)
  have t2 := sval_pullOver (L := D.P.L) (ε := DegPre.famε 1) (prB_hom' D (FractionRing V)) (famφ_prB D (FractionRing V) 0) θ
    ((lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left ≫ (DegPre.trF D (FractionRing V) χ).left) hJ
  have hc0 : constVal (𝟙 (TF (R := V) (FractionRing V)).left) z lam = cst (FractionRing V) z lam := rfl
  rw [hs0, hlam, t1, hfst, hc0] at e1
  erw [t2] at e1
  rw [hsnd] at e1
  rw [hsχ, e1, e2, hfm, hrK] at h1
  refine (Units.mul_left_inj (rigV D (TF (R := V) (FractionRing V)).hom z J)).1 (h1.trans ?_)
  simp only [Units.val_mul, id]
  ring

end GlobalTheory.UT.CoefInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFamilyTermZeroIntegralTorusPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

noncomputable section

namespace GlobalTheory.UT.CoefZeroInt

theorem coef_zero_int : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))), (∀ (R' : Type) [CommRing R'] (f : V →+* R') θ', IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' → ThetaOne.OneBasisAt D f θ') → ∀ (th : Fam D (FractionRing V) 1), ∃ lam : FractionRing V, ∀ (g : GtPtF D (FractionRing V)) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A), g.b = toUnit _ ≫ b → ∀ (w : Frm D (FractionRing V) 1 g.b) (x : FractionRing V), IsCoef 1 g w 0 (th.s 0) x → ∀ z J, Good D.P.L z J → cst (FractionRing V) z x * (rigV D (TF (R := V) (FractionRing V)).hom z J).val = cst (FractionRing V) z lam * sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) ((toUnit (TF (R := V) (FractionRing V))).left ≫ b.left) z J * (val w (𝟙 _) z J).val := by
  intro V _ _ D θ hθ th
  obtain ⟨lam, hlam, -⟩ := existsUnique_scalar D θ hθ (FractionRing V) th
  refine ⟨lam, fun g b hb w x hx z J hJ => ?_⟩
  have h1 := hx z J hJ
  rw [pow_one] at h1
  rw [h1]
  have hs : sval (th.s 0) (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left z J =
      sval (famProj D (FractionRing V) 1 0 th) (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left z J := rfl
  have hfst : (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left ≫ famBase D (FractionRing V) = 𝟙 _ := by
    show (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left ≫ (fst (TF (R := V) (FractionRing V)) D.P.A).left = _
    rw [← Over.comp_left, lift_fst]; rfl
  have hsnd : (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left ≫ (DegPre.prB D (FractionRing V)).left =
      (toUnit (TF (R := V) (FractionRing V))).left ≫ b.left := by
    show (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left ≫ (snd (TF (R := V) (FractionRing V)) D.P.A).left = _
    rw [← Over.comp_left, lift_snd, hb, Over.comp_left]
  have hv : (Geo.Tor.val (g.s 0) (𝟙 (TF (R := V) (FractionRing V)).left) z J).val = 1 := by
    rw [val_corr hJ g.s_zero, val_one]; rfl
  have e1 := sval_smul' (π := famBase D (FractionRing V)) hJ (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left lam (termF D (FractionRing V) 1 0 θ)
  have e2 := sval_pullOver (L := D.P.L) (ε := DegPre.famε 1) (prB_hom' D (FractionRing V)) (famφ_prB D (FractionRing V) 0) θ (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left hJ
  have hc : constVal (𝟙 (TF (R := V) (FractionRing V)).left) z lam = cst (FractionRing V) z lam := rfl
  rw [hs, hlam, e1, hfst]
  erw [e2]
  rw [hsnd, hv, _root_.mul_one, hc]

end GlobalTheory.UT.CoefZeroInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFibreSectionEqScalarMulIntegralTheta
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT

noncomputable section

namespace GlobalTheory.ThetaFibreScalar

theorem famφB_zero {V₁ : Type} [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) :
    D.famφB 0 = ![𝟙 _, 𝟙 _, (toUnit D.P.A ≫ η[D.P.A]).left, (toUnit D.P.A ≫ η[D.P.A]).left] := by
  have h0 := GlobalTheory.Mum.degPre_c_zero D
  have e1 : toUnit D.P.A ≫ D.c 0 = toUnit D.P.A ≫ η[D.P.A] := by
    rw [h0, comp_one, Hom.one_def]
  have e2 : padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c 0) = 𝟙 D.P.A := by
    rw [h0, comp_one, padd, ← Hom.mul_def, _root_.mul_one]
  have e2' : padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ η[D.P.A]) = 𝟙 D.P.A := by rw [← e1]; exact e2
  funext i
  fin_cases i <;> simp [DegPre.famφB, e1, e2']

theorem thetaFibre_scalar : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))), (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ', IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' → ThetaOne.OneBasisAt D f θ') → ∀ (K : Type) [Field K] (ev : V₁ →+* K) (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))), ∃ Λ : K, ∀ (Z : Scheme) (r : Z ⟶ (Over.mk (spMap ev) ⊗ D.P.A).left) (z : Z) J, Good D.P.L z J → sval th r z J = gs (r ≫ (fst (Over.mk (spMap ev)) D.P.A).left) z ⊤ (GlobalTheory.Ex.fnOf Λ) * sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (snd (Over.mk (spMap ev)) D.P.A).left) z J := by
  intro V₁ _ _ D θ hθ K _ ev th
  have hF : FormEq (fun _ : Fin 1 => (snd (Over.mk (spMap ev)) D.P.A).left) (fun _ => ((1 : ℕ) : ℤ))
      (fun i => (snd (Over.mk (spMap ev)) D.P.A).left ≫ D.famφB 0 i) (DegPre.famε 1) := by
    intro U _ h
    rw [famφB_zero]
    simp [Fin.prod_univ_four, DegPre.famε]
  obtain ⟨th', hth'⟩ := exists_sec D.P.isLB hF th
  obtain ⟨r, hr, -⟩ := hθ K ev (pullTo D ev θ) (isPullSecLC_pullTo D ev θ) th'
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (r 0), fun Z rr z J hJ => ?_⟩
  refine (hth' Z rr z J hJ).symm.trans ?_
  have hm := hJ.mem (fun i => (snd (Over.mk (spMap ev)) D.P.A).left ≫ D.famφB 0 i) rr
  have h2 := sval_of (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (rr ≫ (snd (Over.mk (spMap ev)) D.P.A).left) z J
      (fun k => J (rr ≫ (snd (Over.mk (spMap ev)) D.P.A).left ≫ D.famφB 0 k)) (fun k => by rw [Category.assoc])
  erw [h2]
  rw [sval]
  erw [hr]
  rw [Fin.sum_univ_one]
  erw [gs_mul _ _ _ hm]
  congr 1
  · erw [gs_res rr z le_top hm]
    have := gs_pull rr (fst (Over.mk (spMap ev)) D.P.A).left z ⊤ trivial (r 0)
    refine this.trans ?_
    congr 1
    simp [GlobalTheory.Ex.fnOf]
  · have hle := wchart_comp_le D.P.L (D.famφB 0) (snd (Over.mk (spMap ev)) D.P.A).left
      (fun k => J (rr ≫ (snd (Over.mk (spMap ev)) D.P.A).left ≫ D.famφB 0 k))
    erw [isPullSecLC_pullTo D ev θ, gs_res rr z hle hm]
    exact gs_pull rr (snd (Over.mk (spMap ev)) D.P.A).left z
      (LB.wchart D.P.L (D.famφB 0) (fun k => J (rr ≫ (snd (Over.mk (spMap ev)) D.P.A).left ≫ D.famφB 0 k))) (hle hm)
      (θ.f (fun k => J (rr ≫ (snd (Over.mk (spMap ev)) D.P.A).left ≫ D.famφB 0 k)))

end GlobalTheory.ThetaFibreScalar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricPeriodZetaOfJetIntegralityAlgebra
section
theorem GlobalTheory.JoinFun.joinOut_of_jetInt : GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.LatJet.JetInt → GlobalTheory.LatVal.LatAlg → GlobalTheory.LatVal.LatConj → GlobalTheory.Mem.LiteralAutomorphy.JoinOut := by
  intro hEM hHCF hSKDR hPZ hHT hJetInt hLatAlg hLatConj
  have hS44 := GlobalTheory.T.cmLattice_derivClassInvariance_of_hecke (GlobalTheory.T.heckeWeightTwoContinuation_of_functionalEquation hPZ)
  exact GlobalTheory.T.toricPeriodZeta_of_latticeValue_statements hEM hHCF hSKDR hHT (GlobalTheory.T.latticeValueIntegrality_ramified_of_expansion hS44 (GlobalTheory.JetExp.expansion_of_jetInt hJetInt))
    (GlobalTheory.T.latticeValueIntegrality_unramified_of_jetIntegrality hS44 hJetInt) hLatAlg hLatConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalIntegralWeightSectionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toroidal_integral_weight_section : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), FnAlgClosed Xo c → 1 ≤ dimFlag Dw → ∀ la : AllWt.Weight Dw, GapGe (((dimFlag Dw + 1).choose 2 + 1 : ℕ) : ℤ) (la - FlagTan.kap Dw) → CuspIso TF.X Z U la → FreeOnOpen TF.X Z U la := by
  first | exact @GlobalTheory.HSApp.freeOnOpen_of_gapGe | exact GlobalTheory.HSApp.freeOnOpen_of_gapGe | (intros; apply GlobalTheory.HSApp.freeOnOpen_of_gapGe <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantLiftsSubEqSumInvariantFieldsStatement
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
theorem _root_.GlobalTheory.T.torusInvariant_lifts_sub_eq_sum_invariantFields : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (V : Q.P.A.left.Opens) (D : Derivation ℤ R R) (d d' : Fld Y.H.left), IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V) d → IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V) d' → (∀ (α : Q.X) (V' : Q.P.A.left.Opens), V' ≤ V → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d _ f)) → (∀ (α : Q.X) (V' : Q.P.A.left.Opens), V' ≤ V → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d' _ f)) → ∃ h : Fin n → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V), (∀ a, IsWt Y 0 _ (h a)) ∧ ∀ (O' : Y.H.left.Opens), O' ≤ Y.q.left ⁻¹ᵁ V → ∀ f, d O' f - d' O' f = ∑ a, rsT (h a) O' * dd a O' f := by
  first | exact @GlobalTheory.VertCoeff.lifts_sub_eq_sum_invFields | exact GlobalTheory.VertCoeff.lifts_sub_eq_sum_invFields | (intros; apply GlobalTheory.VertCoeff.lifts_sub_eq_sum_invFields <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitsOfModuliPointHaveIsomorphicProportionalLatStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traitsOfModuliPoint_have_isomorphic_proportional_lattices : UTraitUniqSt := by
  first | exact @GlobalTheory.UPoinc.uTraitUniqSt_holds | exact GlobalTheory.UPoinc.uTraitUniqSt_holds | (intros; apply GlobalTheory.UPoinc.uTraitUniqSt_holds <;> assumption)
end

