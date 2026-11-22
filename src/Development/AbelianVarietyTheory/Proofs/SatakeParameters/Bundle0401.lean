import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IwahoriAdmissibleSet
import GroundTheory.AutomorphicForms.AffineBruhat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0399
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0043
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0088
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0395
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0108
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0005
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0027
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0278
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0398
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0387
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IwahoriSubgroupDefinitionsAgree
section
open GlobalTheory.IwFn GlobalTheory.SmGL GlobalTheory.TfJl ValuativeRel Matrix

namespace GlobalTheory.IwEq

theorem iwahori_eq_glnLocal_iwahori : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a : ℕ),
    iwahori k (Fin a) = GroundTheory.Automorphic.GLnLocal.iwahori k a := by
  intro k _ _ _ _ a
  ext g
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, mem_borel] at hu
    refine ⟨u, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap, GroundTheory.Automorphic.mem_borel_iff]
      intro i j hij
      rw [GroundTheory.Automorphic.GLnLocal.residueReduction_apply]
      exact hu i j hij
    · ext i j
      rfl
  · rintro ⟨u, hu, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, GroundTheory.Automorphic.mem_borel_iff] at hu
    refine ⟨u, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap, mem_borel]
      intro i j hij
      have h := hu i j hij
      rw [GroundTheory.Automorphic.GLnLocal.residueReduction_apply] at h
      exact h
    · ext i j
      rfl

end GlobalTheory.IwEq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerEvalComplexPointLeSpanJacobianStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_evalComplexPoint_le_span_jacobian : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p] (U : X.Opens), IsAffineOpen U →
    ∀ (ch : GlobalTheory.AlgChart p (RingHom.id ℂ) d) (φ : Fin d → Γ(X, U)) (z : GlobalTheory.CxPts p (RingHom.id ℂ))
      (_hzc : z ∈ ch.e.source) (hz : z ∈ GlobalTheory.CxPts.ptsIn p (RingHom.id ℂ) U), (ch.jacMat φ z).det ≠ 0 →
      RingHom.ker (GlobalTheory.CxPts.evHom hz) ≤
        Ideal.span (Set.range fun j => φ j - ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U (GlobalTheory.CxPts.evHom hz (φ j))) ⊔
          RingHom.ker (GlobalTheory.CxPts.evHom hz) ^ 2 := by
  first | (exact @GlobalTheory.JacSpan.ker_le_span_jac) | (exact GlobalTheory.JacSpan.ker_le_span_jac) | (intros; apply GlobalTheory.JacSpan.ker_le_span_jac  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NullNegEvalOfJacobianDetEqZeroStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.null_negEval_of_jacobian_det_eq_zero : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (d : ℕ) (U : X.Opens) (ch : GlobalTheory.AlgChart p (RingHom.id ℂ) d)
    (φ : Fin d → Γ(X, U)), ∃ E : Set (Fin d → ℂ), MeasureTheory.volume E = 0 ∧
      ∀ z ∈ ch.e.source, ∀ hz : z ∈ GlobalTheory.CxPts.ptsIn p (RingHom.id ℂ) U,
        (ch.jacMat φ z).det = 0 → (fun j => -GlobalTheory.CxPts.evHom hz (φ j)) ∈ E := by
  first | (exact @GlobalTheory.ChartSard.null_negEv_of_det_eq_zero) | (exact GlobalTheory.ChartSard.null_negEv_of_det_eq_zero) | (intros; apply GlobalTheory.ChartSard.null_negEv_of_det_eq_zero  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairwiseDisjointTriangularCells
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD.XCover

attribute [local instance] MvPolynomial.gradedAlgebra

open MvPolynomial

theorem mem_span_X_of_pos {d n : ℕ} (hn : 0 < n) {f : MvPolynomial (Fin (d + 1)) ℂ}
    (hf : f.IsHomogeneous n) : f ∈ Ideal.span (Set.range (X : Fin (d + 1) → MvPolynomial _ ℂ)) := by
  rw [← Set.image_univ, mem_ideal_span_X_image]
  intro m hm
  by_contra! H
  obtain rfl : m = 0 := Finsupp.ext fun i => H i (Set.mem_univ i)
  have := hf (mem_support_iff.1 hm)
  simp only [map_zero] at this
  omega

theorem iSup_chart_eq_top (d : ℕ) : ⨆ i, chart d i = ⊤ :=
  Proj.iSup_basicOpen_eq_top _ _
    ((HomogeneousIdeal.toIdeal_irrelevant_le _).2 fun _ hn _ hf => mem_span_X_of_pos hn hf)

theorem inf_chart_eq (d : ℕ) (I : Finset (Fin (d + 1))) :
    I.inf (fun i => chart d i) = Proj.basicOpen (homogeneousSubmodule (Fin (d + 1)) ℂ) (∏ i ∈ I, X i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.inf_insert, Finset.prod_insert ha, Proj.basicOpen_mul, ih]

theorem preimage_chart_cover : ∀ (d : ℕ) (Z : Scheme.{0}) (φ : Z ⟶ PSpace ℂ d) [IsAffineHom φ],
    (⨆ i, φ ⁻¹ᵁ chart d i) = ⊤ ∧
      ∀ I : Finset (Fin (d + 1)), I.Nonempty → IsAffineOpen (I.inf fun i => φ ⁻¹ᵁ chart d i) := by
  intro d Z φ _
  constructor
  · rw [← Scheme.Hom.preimage_iSup, iSup_chart_eq_top, Scheme.Hom.preimage_top]
  · intro I hI
    have key : (I.inf fun i => φ ⁻¹ᵁ chart d i) = φ ⁻¹ᵁ (I.inf fun i => chart d i) := by
      classical
      clear hI
      induction I using Finset.induction_on with
      | empty => simp
      | insert a s ha ih => rw [Finset.inf_insert, Finset.inf_insert, ih, Scheme.Hom.preimage_inf]
    rw [key, inf_chart_eq]
    have hdeg : (∏ i ∈ I, X i : MvPolynomial (Fin (d + 1)) ℂ) ∈ homogeneousSubmodule (Fin (d + 1)) ℂ I.card := by
      have := SetLike.prod_mem_graded (homogeneousSubmodule (Fin (d + 1)) ℂ) (fun _ => 1) (fun i => X i)
        (F := I) (fun i _ => X_mem_one d i)
      simpa using this
    exact (Proj.isAffineOpen_basicOpen _ _ hdeg (Finset.card_pos.2 hI)).preimage φ

end GlobalTheory.PD.XCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PulledBackProjCoordinateRatioOverlapDiv
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover
open MvPolynomial HomogeneousLocalization

namespace GlobalTheory.PD.XCover

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Overlap

variable {d : ℕ}

def awayRatio (i j : Fin (d + 1)) : Away (homogeneousSubmodule (Fin (d + 1)) ℂ) (X i) :=
  Away.mk (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d i) 1 (X j) (by simpa using X_mem_one d j)

theorem ratioSec_eq (i j : Fin (d + 1)) :
    ratioSec d i j = Proj.awayToSection (homogeneousSubmodule (Fin (d + 1)) ℂ) (X i) (awayRatio i j) := rfl

theorem germ_awayToSection_mul (a b : Fin (d + 1)) {x : MvPolynomial (Fin (d + 1)) ℂ} (hx : x = X a * X b)
    (y : PSpace ℂ d) (hya : y ∈ chart d a)
    (hy : y ∈ Proj.basicOpen (homogeneousSubmodule (Fin (d + 1)) ℂ) x)
    (s : Away (homogeneousSubmodule (Fin (d + 1)) ℂ) (X a)) :
    (PSpace ℂ d).presheaf.germ (chart d a) y hya
        (Proj.awayToSection (homogeneousSubmodule (Fin (d + 1)) ℂ) (X a) s) =
      (PSpace ℂ d).presheaf.germ _ y hy (Proj.awayToSection (homogeneousSubmodule (Fin (d + 1)) ℂ) x
        (HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d b) hx s)) := by
  have e := ConcreteCategory.congr_hom (Proj.awayMap_awayToSection (homogeneousSubmodule (Fin (d + 1)) ℂ)
    (X_mem_one d b) hx) s
  simp only [ConcreteCategory.comp_apply] at e
  have e' : Proj.awayToSection (homogeneousSubmodule (Fin (d + 1)) ℂ) x
      (HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d b) hx s) =
      (PSpace ℂ d).presheaf.map (homOfLE (Proj.basicOpen_mono _ _ _ ⟨_, hx⟩)).op
        (Proj.awayToSection (homogeneousSubmodule (Fin (d + 1)) ℂ) (X a) s) := e
  rw [e', TopCat.Presheaf.germ_res_apply]

theorem awayRatio_mul_awayRatio (a i : Fin (d + 1)) :
    HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d i)
        (rfl : X a * X i = X a * X i) (awayRatio a i) *
      HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d a)
        (mul_comm (X a) (X i)) (awayRatio i a) = 1 := by
  apply val_injective
  rw [HomogeneousLocalization.val_mul, awayRatio, awayRatio, Away.mk, Away.mk, val_awayMap_mk, val_awayMap_mk,
    HomogeneousLocalization.val_one, Localization.mk_mul]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp
  ring

theorem awayRatio_change (a i j : Fin (d + 1)) :
    HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d a)
        (mul_comm (X a) (X i)) (awayRatio i j) =
      HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d i)
          (rfl : X a * X i = X a * X i) (awayRatio a j) *
        HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d a)
          (mul_comm (X a) (X i)) (awayRatio i a) := by
  apply val_injective
  rw [HomogeneousLocalization.val_mul, awayRatio, awayRatio, awayRatio, Away.mk, Away.mk, Away.mk, val_awayMap_mk,
    val_awayMap_mk, val_awayMap_mk, Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp
  ring

theorem rat_eq_germ {Z : Scheme.{0}} [IsIntegral Z] (φ : Z ⟶ PSpace ℂ d) (k l : Fin (d + 1))
    (hk : genericPoint Z ∈ φ ⁻¹ᵁ chart d k) :
    rat φ k l = φ.stalkMap (genericPoint Z) ((PSpace ℂ d).presheaf.germ (chart d k) _ hk (ratioSec d k l)) := by
  unfold rat
  rw [dif_pos hk]
  exact (Scheme.Hom.germ_stalkMap_apply φ _ _ hk _).symm

end Overlap

open Overlap in

theorem rat_overlap : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (φ : Z ⟶ PSpace ℂ d) (a i j : Fin (d + 1)),
    genericPoint Z ∈ φ ⁻¹ᵁ chart d a → genericPoint Z ∈ φ ⁻¹ᵁ chart d i →
      rat φ a i ≠ 0 ∧ rat φ i j = rat φ a j / rat φ a i := by
  intro d Z _ φ a i j ha hi
  have hW : φ (genericPoint Z) ∈ Proj.basicOpen (homogeneousSubmodule (Fin (d + 1)) ℂ) (X a * X i) := by
    rw [Proj.basicOpen_mul]; exact ⟨ha, hi⟩
  let F := ((Proj.awayToSection (homogeneousSubmodule (Fin (d + 1)) ℂ) (X a * X i) ≫
    (PSpace ℂ d).presheaf.germ _ _ hW) ≫ φ.stalkMap (genericPoint Z)).hom
  have hA : ∀ l, rat φ a l = F (HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (d + 1)) ℂ)
      (X_mem_one d i) (rfl : X a * X i = X a * X i) (awayRatio a l)) := by
    intro l
    rw [rat_eq_germ φ a l ha, ratioSec_eq, germ_awayToSection_mul a i rfl _ ha hW]
    rfl
  have hI : ∀ l, rat φ i l = F (HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (d + 1)) ℂ)
      (X_mem_one d a) (mul_comm (X a) (X i)) (awayRatio i l)) := by
    intro l
    rw [rat_eq_germ φ i l hi, ratioSec_eq, germ_awayToSection_mul i a (mul_comm (X a) (X i)) _ hi hW]
    rfl
  have h1 : rat φ a i * rat φ i a = 1 := by
    rw [hA, hI, ← map_mul, awayRatio_mul_awayRatio, map_one]
  refine ⟨left_ne_zero_of_mul_eq_one h1, ?_⟩
  rw [div_eq_mul_inv, ← eq_inv_of_mul_eq_one_right h1, hI, hA, hI, ← map_mul, awayRatio_change]
end GlobalTheory.PD.XCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SeriesLocationOfMembershipStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.series_location_of_membership : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ _ _ _ _ => GlobalTheory.TypeLeaf.SerLoc (w.D Z) := by
  first | exact @GlobalTheory.SerFinished.main | exact GlobalTheory.SerFinished.main | (intros; apply GlobalTheory.SerFinished.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceFibreRingEqFinsumFibrePointsStatement
section
open GlobalTheory GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_fibreRing_eq_finsum_fibrePoints : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → IsAlgClosed k → IsReduced ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) → ∀ h : (rB k K x {0}), Algebra.trace k ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) (Ideal.Quotient.mk _ h) = ∑ᶠ e : fib k K x, e.1 h := by
  first | (exact @GlobalTheory.PD.FibTrace.trace_quot_eq_finsum_fib) | (exact GlobalTheory.PD.FibTrace.trace_quot_eq_finsum_fib) | (intros; apply GlobalTheory.PD.FibTrace.trace_quot_eq_finsum_fib  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TuplesHaveLocalModelsOfStandardColumnObjects
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Svd

theorem modelsAt_of_part : GlobalTheory.TwV.Lt.AdmAtEnt2 → GlobalTheory.TwV.Lt.CurveEx → ∀ (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (O : Obj (w.D Z)), Part w Z (ofObj O) → ModelsAt (w.D Z) O := by
  intro hA hC B f T w Z O hP hL hk
  obtain ⟨⟨t, hJ⟩, he⟩ := GlobalTheory.Svd.jointsAt_all_std B f T w Z O hP hL
  have hS : OrbitPlaces.Stab0 (w.D Z) := GlobalTheory.Pdv.stepZero_trivial_stabilisers_trueColumns w.I w.ok w.pins w.l Z O.ex.lev
  exact GlobalTheory.T.thetaLocalModels_of_splitUnramified_joints hA hC t (fun μ _ => hJ μ) he hS hk

end GlobalTheory.Svd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilIntegralParahoricEquivariance
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover

noncomputable section

namespace GlobalTheory.PD.XCover

theorem finiteDimensional_of_finite {A B F K : Type} [CommRing A] [CommRing B] [Field F] [Field K] [Algebra F K]
    (ψ : B →+* A) (hψ : ψ.Finite) (g : A →+* K) (hB : ∀ b, g (ψ b) ∈ Set.range (algebraMap F K))
    (hfr : ∀ x : K, ∃ a b : A, g b ≠ 0 ∧ x * g b = g a) : FiniteDimensional F K := by
  letI := ψ.toAlgebra
  haveI : Module.Finite B A := hψ
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := B) (M := A)
  let M : Submodule F K := Submodule.span F (g '' (s : Set A))
  have hMfg : M.FG := Submodule.fg_span (s.finite_toSet.image g)
  have hM : ∀ a : A, g a ∈ M := by
    intro a
    have ha : a ∈ Submodule.span B (s : Set A) := hs ▸ Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact M.add_mem hx hy
    | smul b x _ hx =>
      obtain ⟨c, hc⟩ := hB b
      rw [Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra, ← hc, ← Algebra.smul_def]
      exact M.smul_mem c hx
  let R := Algebra.adjoin F (Set.range g)
  have hRM : Subalgebra.toSubmodule R ≤ M := by
    rw [Algebra.adjoin_eq_span]
    refine Submodule.span_le.2 fun x hx => ?_
    have hx' : x ∈ g.range.toSubmonoid := (Submonoid.closure_le.2 (fun y hy => hy)) hx
    obtain ⟨a, rfl⟩ := hx'
    exact hM a
  have hRfg : (Subalgebra.toSubmodule R).FG := by
    haveI : FiniteDimensional F M := Module.Finite.iff_fg.2 hMfg
    exact isNoetherian_submodule.1 inferInstance _ hRM
  have htop : ∀ z : K, z ∈ M := by
    intro z
    obtain ⟨a, b, hb, e⟩ := hfr z
    have hbR : g b ∈ R := Algebra.subset_adjoin ⟨b, rfl⟩
    have hint : IsIntegral F (g b) := IsIntegral.of_mem_of_fg R hRfg _ hbR
    have hinv : (g b)⁻¹ ∈ R := Subalgebra.inv_mem_of_algebraic R (x := ⟨g b, hbR⟩) hint.isAlgebraic
    have hz : z = g a * (g b)⁻¹ := by rw [← e, mul_assoc, mul_inv_cancel₀ hb, mul_one]
    rw [hz]
    exact hRM (R.mul_mem (Algebra.subset_adjoin ⟨a, rfl⟩) hinv)
  have : M = ⊤ := eq_top_iff.2 fun z _ => htop z
  exact ⟨this ▸ hMfg⟩

variable {d : ℕ}

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ratioSec_eq (i j : Fin (d + 1)) : ratioSec d i j = GlobalTheory.ProjSpace.ratio ℂ d i j := by
  refine (GlobalTheory.ProjFrac.awayToSection_mk (𝒜 := MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d i) 1 _).trans ?_
  exact GlobalTheory.ProjFrac.frac_eq (by ring)

theorem exists_frac_germ (Z : Scheme.{0}) [IsIntegral Z] (U : Z.Opens) (hU : IsAffineOpen U) (h : genericPoint Z ∈ U)
    (x : Z.functionField) : ∃ a b : Γ(Z, U), (Z.presheaf.germ U _ h).hom b ≠ 0 ∧
      x * (Z.presheaf.germ U _ h).hom b = (Z.presheaf.germ U _ h).hom a := by
  haveI : Nonempty U := ⟨⟨_, h⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen Z U hU
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Γ(Z, U)) x
  have hb' : algebraMap Γ(Z, U) Z.functionField b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  exact ⟨a, b, hb', div_mul_cancel₀ _ hb'⟩

theorem germ_app_mem (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) (φ : Z ⟶ PSpace ℂ d)
    (hp : φ ≫ PSpace.str ℂ d = p) (h : genericPoint Z ∈ φ ⁻¹ᵁ chart d 0) (b : Γ(PSpace ℂ d, chart d 0)) :
    letI := ffAlg p
    (Z.presheaf.germ _ _ h).hom ((φ.app (chart d 0)).hom b) ∈ fld φ := by
  letI := ffAlg p
  obtain ⟨P, rfl⟩ := GlobalTheory.ProjSpace.aeval_ratio_surjective ℂ d 0 b
  have e := congrArg (fun t => t P) (GlobalTheory.ProjSpace.appLE_comp_aeval_ratio (φ := φ) (W := φ ⁻¹ᵁ chart d 0) (i := 0) (hi := le_rfl))
  simp only [RingHom.comp_apply, RingHom.coe_coe] at e
  rw [← Scheme.Hom.appLE_eq_app, e, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left]
  refine MvPolynomial.eval₂_mem (fun _ _ => ?_) (fun j => ?_)
  · rw [RingHom.comp_apply, hp]
    have hc : ∀ c : ℂ, (Z.presheaf.germ _ _ h).hom ((GlobalTheory.QCoh.Qcqs.baseRingHom p (φ ⁻¹ᵁ chart d 0)).hom c) =
        algebraMap ℂ Z.functionField c := by
      intro c
      rw [← GlobalTheory.QCoh.Qcqs.baseRingHom_res p (le_top : φ ⁻¹ᵁ chart d 0 ≤ ⊤), Z.presheaf.germ_res_apply,
        GlobalTheory.QCoh.Qcqs.baseRingHom_top]
      rfl
    rw [hc]
    exact IntermediateField.algebraMap_mem _ _
  · have hr : (Z.presheaf.germ _ _ h).hom (GlobalTheory.ProjSpace.pullRatio φ (φ ⁻¹ᵁ chart d 0) 0 le_rfl j) = rat φ 0 j := by
      rw [rat, dif_pos h, ratioSec_eq, ← Scheme.Hom.appLE_eq_app]
      rfl
    simp only [Function.comp_apply]
    rw [hr]
    exact IntermediateField.subset_adjoin ℂ _ ⟨j, rfl⟩

theorem finiteDimensional_fld : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p]
    [inst : Algebra ℂ Z.functionField], inst = ffAlg p → ∀ (φ : Z ⟶ PSpace ℂ d) [IsFinite φ], φ ≫ PSpace.str ℂ d = p →
    (∀ i, genericPoint Z ∈ φ ⁻¹ᵁ chart d i) → FiniteDimensional (fld φ) Z.functionField := by
  intro d Z _ p _ inst hinst φ _ hp hgen
  subst hinst
  have hC : IsAffineOpen (chart d 0) := GlobalTheory.ProjSpace.isAffineOpen_chart ℂ d 0
  have hU : IsAffineOpen (φ ⁻¹ᵁ chart d 0) := hC.preimage φ
  exact finiteDimensional_of_finite (φ.app (chart d 0)).hom (φ.finite_app _ hC) (Z.presheaf.germ _ _ (hgen 0)).hom
    (fun b => ⟨⟨_, germ_app_mem Z p φ hp (hgen 0) b⟩, rfl⟩) (exists_frac_germ Z _ hU (hgen 0))

end GlobalTheory.PD.XCover
end
end

