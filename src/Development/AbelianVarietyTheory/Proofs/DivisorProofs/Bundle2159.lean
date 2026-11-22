import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TwoRunDatumBoundUnitAtIndefinitePoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThreeLeScaleOfPowBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2138
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2140
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2097
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2144
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTateIsoOfLevel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2110
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2146
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2149
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2147
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2142
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2123
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0364
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0070
import Formalism.LocalRingCardinality.Bundle0006
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PageEstimateStatement
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn

namespace GlobalTheory.BigOn.PageNumbers

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {Pm : ParameterChoice' D L}

theorem le_sup_fin (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (k : ℕ) (hk : k < D.R.m) :
    WeightAlgebra.DF (Formalism.MainNotions.DIV.Cons.lR Tp hK (k + 1)) ≤
      Finset.univ.sup fun j : Fin D.R.m => WeightAlgebra.DF (Formalism.MainNotions.DIV.Cons.lR Tp hK ((j : ℕ) + 1)) := by
  have h := Finset.le_sup (f := fun j : Fin D.R.m => WeightAlgebra.DF (Formalism.MainNotions.DIV.Cons.lR Tp hK ((j : ℕ) + 1)))
    (Finset.mem_univ (⟨k, hk⟩ : Fin D.R.m))
  exact h

theorem sup_fin_eq_topDeg (Tp : ParamsT D L Pm) (hK : DV.KapDef D) :
    (Finset.univ.sup fun j : Fin D.R.m => WeightAlgebra.DF (Formalism.MainNotions.DIV.Cons.lR Tp hK ((j : ℕ) + 1))) = GlobalTheory.IndexAssembly.topDeg Tp hK := by
  apply le_antisymm
  · exact Finset.sup_le fun j _ => GlobalTheory.IndexAssembly.le_topDeg Tp hK ⟨by omega, by omega⟩
  · refine Finset.sup_le fun j hj => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    exact le_sup_fin Tp hK k (by omega)

end GlobalTheory.BigOn.PageNumbers

namespace GlobalTheory.BigOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pageSt : PageSt := by
  refine (GlobalTheory.T.indexBoundParameterRequirements_eventually_family.and GlobalTheory.T.leaf_level_square_bound).imp fun Fm CH _ H => ?_
  obtain ⟨⟨xs, hxs⟩, ⟨c1, hc1⟩⟩ := H
  refine ⟨max c1 1, fun c hc hB => ?_⟩
  obtain ⟨x2, hx2⟩ := hc1 c ((le_max_left _ _).trans hc) hB
  refine ⟨max (max xs x2) (3 * c.C), fun x hx hle i p hp hm r O hr => ?_⟩
  have hxs' : xs ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hle)
  have hx2' : x2 ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hle)
  have hxC : 3 * c.C ≤ x := (le_max_right _ _).trans hle
  have hR := hxs x hx hxs' i
  obtain ⟨hSq, hY⟩ := hx2 x hx hx2' i p hp hm r O hr
  have hE : ∀ C CH', ErrorConstantMatchesDefinition ((R2 p).num (F2 p) C CH') O C := fun C CH' => (GlobalTheory.BigOn.Check.twoRunDatum_boundUnit_at_indefinitePoint p (Fm.parT x hx i) r O hr C CH').1
  have hb : O.b = (Fm.L x i).sc.b := (GlobalTheory.BigOn.Check.twoRunDatum_boundUnit_at_indefinitePoint p (Fm.parT x hx i) r O hr 0 0).2
  obtain ⟨st, hd⟩ := hr.1.depth
  letI := st
  letI := hostAlg (Fm.D x i)
  have hd' : GlobalTheory.RunDepth.RunTie p.T.toCore (Fm.ex x hx i).errX (Fm.parT x hx i) (Fm.ex x hx i).kap_def ({ O with de2 := (Fm.L x i).de2 } : Obj p c)
      (fun j : Fin (Fm.D x i).R.m => (j : ℕ) + 1) := { hd with }
  have hN : GlobalTheory.IndexAssembly.NumTie (Fm.parT x hx i) (Fm.ex x hx i).kap_def ({ O with de2 := (Fm.L x i).de2 } : Obj p c) :=
    ⟨hr.1.rr_eq, hr.1.realisedChain_torus_eq, hr.1.Nc_eq,
      hr.1.DF_eq.trans (congrArg (fun n : ℕ => (n : ℝ)) (PageNumbers.sup_fin_eq_topDeg _ _)), rfl, hr.1.pde_eq⟩
  have hx3 : 3 * c.C ≤ (Fm.L x i).sc.x := by rw [Fm.L_x x i hx]; exact hxC
  have hC : Formalism.L2.Indef.Tree.OnPage.ConstC c := (le_max_right _ _).trans hc
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.IndexAssembly.numericLeaves hd' hN hR hC hB hx3
  refine ⟨h1, h2, h3, h4, hSq, hY, hb, ?_, hE⟩
  have hx0 : 0 < (Fm.L x i).sc.x := by linarith [(Fm.L x i).sc.one_lt_alt]
  have e1 := Real.rpow_pos_of_pos hx0 (Fm.L x i).sc.eps
  have e2 := Real.rpow_pos_of_pos hx0 (-(Fm.L x i).sc.eps)
  change 0 ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps * (((Fm.D x i).R.f : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b *
    (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps + (Fm.L x i).Nc)
  have hb0 : 0 < (Fm.L x i).sc.b := Real.exp_pos _
  unfold SizeData₂.Nc budgetNc rankBudget bSize
  positivity

end GlobalTheory.BigOn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairFrameBlockEigenRelation
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

noncomputable section
namespace GlobalTheory.ThKTorus.Scale
variable {F : Type} [Field F] [NumberField F]

theorem realAd_add (u v : ℝ) : realAd F u + realAd F v = realAd F (u + v) := by
  simp only [realAd, map_add]
  rfl

theorem realAd_mul (u v : ℝ) : realAd F u * realAd F v = realAd F (u * v) := by
  simp only [realAd, map_mul]
  exact Prod.ext rfl (mul_zero _)

theorem realAd_zero : realAd F 0 = 0 := by
  simp only [realAd, map_zero]
  rfl

theorem tAd_mul (u v : ℝ) : tAd F u * tAd F v = tAd F (u * v) := by
  simp only [tAd]
  have : realAd F (u * v - 1) = realAd F (u - 1) + realAd F (v - 1) + realAd F (u - 1) * realAd F (v - 1) := by
    rw [realAd_mul, realAd_add, realAd_add]; congr 1; ring
  rw [this]; ring

theorem tAd_one : tAd F 1 = 1 := by
  simp [tAd, realAd_zero]

theorem tAd_inv_mul {s : ℝ} (hs : s ≠ 0) : tAd F s⁻¹ * tAd F s = 1 := by
  rw [tAd_mul, inv_mul_cancel₀ hs, tAd_one]

section GlobalTheory
variable {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ} (blk : Fin q → Finset κ)

theorem prod_inv_mul (t : Fin q → ℝ) (ht : ∀ i, t i ≠ 0) (j : κ) :
    (∏ i, if j ∈ blk i then tAd F (t i)⁻¹ else 1) * (∏ i, if j ∈ blk i then tAd F (t i) else 1) = 1 := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun i _ => ?_
  split_ifs
  · exact tAd_inv_mul (ht i)
  · exact one_mul 1

theorem blkScale_inv_blkScale (t : Fin q → ℝ) (ht : ∀ i, t i ≠ 0) (z : κ → AF F) :
    blkScale blk (fun i => (t i)⁻¹) (blkScale blk t z) = z := by
  funext j
  simp only [blkScale]
  rw [← mul_assoc, prod_inv_mul blk t ht j, one_mul]

theorem blkScale_add (s : Fin q → ℝ) (z w : κ → AF F) :
    blkScale blk s (z + w) = blkScale blk s z + blkScale blk s w := by
  funext j
  simp only [blkScale, Pi.add_apply, mul_add]

theorem dot_blkScale (t : Fin q → ℝ) (ht : ∀ i, t i ≠ 0) (x y : κ → AF F) :
    blkScale blk (fun i => (t i)⁻¹) x ⬝ᵥ blkScale blk t y = x ⬝ᵥ y := by
  simp only [dotProduct, blkScale]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_mul_mul_comm, prod_inv_mul blk t ht j, one_mul]

theorem schr_blkScale (ψ : AddChar (AF F) ℂ) (t : Fin q → ℝ) (ht : ∀ i, t i ≠ 0) (p r : κ → AF F)
    (g : (κ → AF F) → ℂ) (x : κ → AF F) :
    schr ψ (blkScale blk (fun i => (t i)⁻¹) p, blkScale blk t r) g (blkScale blk (fun i => (t i)⁻¹) x) =
      schr ψ (p, r) (fun z => g (blkScale blk (fun i => (t i)⁻¹) z)) x := by
  simp only [schr, dot_blkScale blk t ht, blkScale_add]

end GlobalTheory

section Main
variable {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem co_mat_mul {σ : E →ₐ[F] E} {n d q : ℕ} {J : Matrix (Fin n) (Fin n) E} {JW : Matrix (Fin d) (Fin d) E}
    {x y : Fin q → Fin n → E} {co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J) (incM F JW)) (Fin n × Fin d)}
    {blk : Fin q → Finset (Fin n × Fin d)} (hco : IsFrameCo σ J JW x y co blk) {t : Fin q → ℝ} {a : UA σ J}
    (ht : ∀ i, 0 < t i) (hta : IsTorusU x y t a) (w : Matrix (Fin n) (Fin d) (AE F E)) :
    co.e (mat a * w) = (blkScale blk (fun i => (t i)⁻¹) (co.e w).1, blkScale blk t (co.e w).2) := by
  have hw : w = co.e.symm ((co.e w).1, 0) + co.e.symm (0, (co.e w).2) := by
    rw [← map_add]; simp
  conv_lhs => rw [hw]
  rw [Matrix.mul_add, map_add, ((hco.2 t a ht hta) _).1, ((hco.2 t a ht hta) _).2]
  simp

def twist {n d : ℕ} {σ : E →ₐ[F] E} {X : Spc F E n} {W : Spc F E d} (e : Fn F n d →ₗ[ℂ] Fn F n d) (om : Rep σ X W)
    (a : UA σ X.J) {q : ℕ} (blk : Fin q → Finset (Fin n × Fin d)) (t : Fin q → ℝ) : Fn F n d →ₗ[ℂ] Fn F n d :=
  LinearMap.funLeft ℂ ℂ (blkScale blk (fun i => (t i)⁻¹)) ∘ₗ e ∘ₗ om (a, 1)

theorem incM_one (n : ℕ) : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
  simp [incM]

theorem twist_heis {σ : E →ₐ[F] E} {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
    {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ} (hpair : IsPair B M χX χW om r s r' s') {q : ℕ}
    {x y : Fin q → Fin n → E} {M₁ : Model σ X W} {blk : Fin q → Finset (Fin n × Fin d)} {e : Fn F n d →ₗ[ℂ] Fn F n d}
    (hco : IsFrameCo σ X.J W.J x y M₁.co blk) (hev : IsEv B M M₁ 1 1 ∅ e) {t : Fin q → ℝ} {a : UA σ X.J}
    (ht : ∀ i, 0 < t i) (hta : IsTorusU x y t a) (w : Matrix (Fin n) (Fin d) (AE F E)) :
    ∀ Ψ ∈ schA F (Fin n × Fin d), twist e om a blk t (M.co.rho B.ψ w Ψ) = M₁.co.rho B.ψ w (twist e om a blk t Ψ) := by
  intro Ψ hΨ
  have hs := hpair.weil.isUSplitting
  have hΨ' : om (a, 1) Ψ ∈ schA F (Fin n × Fin d) := hs.pres (a, 1) Ψ hΨ
  have h1 : om (a, 1) (M.co.rho B.ψ w Ψ) = M.co.rho B.ψ (mat a * w) (om (a, 1) Ψ) := by
    rw [hs.impl (a, 1) w Ψ hΨ]
    congr 2
    simp [actAB, mat]
  have h2 : e (M.co.rho B.ψ (mat a * w) (om (a, 1) Ψ)) = M₁.co.rho B.ψ (mat a * w) (e (om (a, 1) Ψ)) := by
    simpa [incM_one] using hev.Heisenberg₂ (mat a * w) _ hΨ'
  funext z
  have hne : ∀ i, t i ≠ 0 := fun i => (ht i).ne'
  simp only [twist, LinearMap.comp_apply, LinearMap.funLeft_apply]
  rw [h1, h2]
  simp only [Darboux.rho, co_mat_mul hco ht hta w]
  exact schr_blkScale blk B.ψ t hne _ _ _ z

end Main

theorem norm_eval_torus_le : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (q : ℕ) (x y : Fin q → Fin n → E), IsFrameU σ X.J x y →
    ∀ (M₁ : Model σ X W) (blk : Fin q → Finset (Fin n × Fin d)) (e : Fn F n d →ₗ[ℂ] Fn F n d),
    M₁.IsGood B.ψ → IsFrameCo σ X.J W.J x y M₁.co blk → IsEv B M M₁ 1 1 ∅ e →
    ∀ φ ∈ SB (Fin n × Fin d → Af F),
    ∃ ex : Fin q → ℝ, ∀ (t : Fin q → ℝ) (a : UA σ X.J), (∀ i, 0 < t i) → IsTorusU x y t a →
      ∀ (f : SInf F (Fin n × Fin d)) (κ : UA σ X.J) (h : UA σ W.J) (z : Fin n × Fin d → AF F),
        ‖e (om (a * κ, h) (pureA F f φ)) z‖ ≤ (∏ i, t i ^ ex i) * ‖e (om (κ, h) (pureA F f φ)) (blkScale blk t z)‖ := by
  intro hK F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair q x y hxy M₁ blk e hM₁ hco hev φ hφ
  obtain ⟨ex, hex⟩ := GlobalTheory.T.pair_frame_blocks_evaluation hK F E σ B n d X W M χX χW om r s r' s' hpair q x y hxy M₁ blk e hM₁ hco hev
  refine ⟨ex, fun t a ht hta f κ h z => ?_⟩
  obtain ⟨c, hc⟩ := GlobalTheory.T.pair_evaluation_self_linear hK F E σ B n d X W M χX χW om r s r' s' hpair M₁ e hM₁ hev (twist e om a blk t)
    (fun w => twist_heis hpair hco hev ht hta w)
  have hne : ∀ i, t i ≠ 0 := fun i => (ht i).ne'
  have key : ∀ Ψ ∈ schA F (Fin n × Fin d), ∀ z, e (om (a, 1) Ψ) z = c * e Ψ (blkScale blk t z) := by
    intro Ψ hΨ z
    have := congrFun (hc Ψ hΨ) (blkScale blk t z)
    simpa [twist, blkScale_inv_blkScale blk t hne] using this
  have hc' := hex t a c ht hta key
  have hs := hpair.weil.isUSplitting
  have hΨ0 : om (κ, h) (pureA F f φ) ∈ schA F (Fin n × Fin d) :=
    hs.pres (κ, h) _ (Submodule.subset_span ⟨f, φ, hφ, rfl⟩)
  rw [show ((a * κ, h) : UA σ X.J × UA σ W.J) = (a, 1) * (κ, h) by simp, map_mul, Module.End.mul_apply,
    key _ hΨ0, norm_mul]
  exact mul_le_mul_of_nonneg_right hc' (norm_nonneg _)

end GlobalTheory.ThKTorus.Scale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointFactorIntegralSubalgebra
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.point_factor_integral_subalgebra : ∀ (K B E : Type) [Field K] [CommRing B] [CommRing E]
    [Algebra K B] [Algebra K E] (i : E →ₐ[K] B), Function.Injective i →
    (∀ b : B, _root_.IsIntegral K b → b ∈ i.range) → ∀ (T : Scheme.{0}) (p : T ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)
    [IsFinite p] (t : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp B ⟶ T), t ≫ p = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K B) →
    ∃ u : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp E ⟶ T, u ≫ p = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K E) ∧ t = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap i.toRingHom ≫ u := by
  intro K B E _ _ _ _ _ i hi hint T p _ t ht
  have : IsAffine T := isAffine_of_isAffineHom p
  set e := T.isoSpec
  let φ := Spec.preimage (e.inv ≫ p)
  let α := Spec.preimage (t ≫ e.hom)
  have hφ : Spec.map φ = e.inv ≫ p := Spec.map_preimage _
  have hα : Spec.map α = t ≫ e.hom := Spec.map_preimage _
  have hfin : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]; infer_instance
  have hcomp : φ ≫ α = CommRingCat.ofHom (algebraMap K B) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hα, hφ]
    simpa [Category.assoc] using ht
  have hαφ : α.hom.comp φ.hom = algebraMap K B := by
    rw [← CommRingCat.hom_comp, hcomp, CommRingCat.hom_ofHom]
  have hmem : ∀ a, α.hom a ∈ i.range := by
    intro a
    apply hint
    obtain ⟨P, hP, hPa⟩ := hfin.to_isIntegral a
    refine ⟨P, hP, ?_⟩
    have h2 := congrArg α.hom hPa
    rw [Polynomial.hom_eval₂, map_zero, hαφ] at h2
    exact h2
  let eqv := AlgEquiv.ofInjective i hi
  let β : Γ(T, ⊤) →+* E := eqv.symm.toRingHom.comp (α.hom.codRestrict i.range hmem)
  have hiβ : ∀ a, i (β a) = α.hom a := by
    intro a
    change i (eqv.symm ⟨α.hom a, hmem a⟩) = α.hom a
    rw [← AlgEquiv.ofInjective_apply i hi]
    exact congrArg Subtype.val (eqv.apply_symm_apply _)
  have hβφ : β.comp φ.hom = algebraMap K E := by
    ext k
    apply hi
    rw [RingHom.comp_apply, hiβ, ← RingHom.comp_apply, hαφ]
    exact (i.commutes k).symm
  refine ⟨Spec.map (CommRingCat.ofHom β) ≫ e.inv, ?_, ?_⟩
  · rw [Category.assoc, ← hφ, ← Spec.map_comp]
    change _ = Spec.map (CommRingCat.ofHom (algebraMap K E))
    congr 1
    ext x
    exact congrArg (fun f : K →+* E => f x) hβφ
  · change t = Spec.map (CommRingCat.ofHom i.toRingHom) ≫ _
    rw [← Category.assoc, ← Spec.map_comp]
    have hβα : CommRingCat.ofHom β ≫ CommRingCat.ofHom i.toRingHom = α := by
      ext x; exact hiβ x
    rw [hβα, hα, Category.assoc, e.hom_inv_id, Category.comp_id]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingOfRunModel
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares

namespace GlobalTheory.ShareOn.Reading

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Main2
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

open GlobalTheory.OnTies in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

theorem reading_of_runModel (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r) (i : Fin D.R.m) {C : Type}
    [Finite C] [MulAction p.P.Gp C] (M : TwoLevels D.host.E D.R.r p.P.Gp C) (ka : Wt M.Ψ D.R.r)
    (hb0 : 0 < badN D) (hn : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) (hM : RunModel p r h i M ka) :
    M.Ψ.card = D.R.f ∧ ∃ (ρ : Representation ℂ p.P.Gp (M.cusp ka)) (σ : D.what₂.LL →+* ℂ)
      (f : (Fin (p.R.toRealDat.nW i) → D.what₂.LL) →ₛₗ[σ] M.cusp ka),
      IsPullRep M ka ρ ∧ (∀ g v, ρ g (f v) = f ((p.R.toRealDat.FW i).ρ g v)) ∧
      (LinearIndependent ℂ fun k => f (Pi.single k 1)) ∧ Submodule.span ℂ (Set.range f) = ⊤ := by
  refine ⟨card_of_runModel hM, ?_⟩
  obtain ⟨v, e, ha, hb, hc, -⟩ := hM
  obtain ⟨act, hact, hcu⟩ := h.action v i

  let Rd : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i) →ₛₗ[(r.used v).full.σ₀] M.cusp ka :=
    LinearMap.codRestrict (M.cusp ka) (rdLin h ha) fun F => Submodule.subset_span ⟨_, GlobalTheory.T.usedRunCuspForm_reading_mem_modelCuspForms h ha hb F, rfl⟩
  have hRd : ∀ F, ((Rd F : M.cusp ka) : C → M.dom → ℂ) = rdLin h ha F := fun F => rfl
  letI : Algebra (r.used v).full.J.Q.c.F D.what₂.LL := p.alg
  obtain ⟨σ, hσ⟩ := exists_ext_embedding (K := (r.used v).full.J.Q.c.F) (LL := D.what₂.LL) (r.used v).full.σ₀
  let cu := cuspTo (h.laws v).p (fw2 p) i
  have hcuW : ∀ F, cu F ∈ ((R2 p).FW i).WK := fun F => ((fw2 p).e i _).2
  have hcuinj : Function.Injective cu := by
    intro F G hFG
    have h1 := Subtype.ext hFG
    have h2 := ((fw2 p).e i).injective h1
    exact Submodule.inclusion_injective _ h2
  have hsurj : ∀ w ∈ ((R2 p).FW i).WK, ∃ F, cu F = w := by
    intro w hw
    refine ⟨⟨(((fw2 p).e i).symm ⟨w, hw⟩).1, by
      rw [cutR_eq _ (inR_succ i)]; exact (((fw2 p).e i).symm ⟨w, hw⟩).2⟩, ?_⟩
    show ((((fw2 p).e i) _ : ((R2 p).FW i).WK) : Fin _ → D.what₂.LL) = w
    exact congrArg Subtype.val (LinearEquiv.apply_symm_apply ((fw2 p).e i) ⟨w, hw⟩)
  obtain ⟨m, b', hbW, hbK, hspK, hbL, hspL⟩ := (fw2 p).ks i
  choose bC hbC using fun k => hsurj (b' k) (hbW k)
  have hbC' : (fun k => cu (bC k)) = b' := funext hbC
  have hbs : Submodule.span (recB (h.laws v).p.toLawsCore).KO (Set.range bC) = ⊤ := by
    rw [eq_top_iff]
    intro F _
    have h1 : cu F ∈ Submodule.span p.T.Q.c.F (Set.range b') := by rw [hspK]; exact hcuW F
    obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h1
    have h2 : cu (∑ k, (show (recB (h.laws v).p.toLawsCore).KO from cf k) • bC k) = cu F := by
      rw [map_sum, ← hcf]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, hbC k]
      rfl
    rw [← hcuinj h2]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hbi : LinearIndependent D.what₂.LL (fun k => cu (bC k)) := by rw [hbC']; exact hbL
  have hbt : Submodule.span D.what₂.LL (Set.range fun k => cu (bC k)) = ⊤ := by rw [hbC']; exact hspL
  have hK : LinearIndependent (recB (h.laws v).p.toLawsCore).KO bC := by
    apply LinearIndependent.of_comp cu
    show LinearIndependent _ (fun k => cu (bC k))
    rw [hbC']; exact hbK
  have hR : LinearIndependent ℂ (fun k => Rd (bC k)) :=
    LinearIndependent.of_comp (M.cusp ka).subtype (GlobalTheory.T.cuspForm_family_linearIndependent h ha m bC hK)
  have hRs : Submodule.span ℂ (Set.range Rd) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨y, hy⟩ -
    have hy' : y ∈ (Submodule.span ℂ (Set.range Rd)).map (M.cusp ka).subtype := by
      rw [Submodule.map_span, ← Set.range_comp]
      unfold TwoLevels.cusp at hy
      refine Submodule.span_le.2 ?_ hy
      rintro _ ⟨G, hG, rfl⟩
      obtain ⟨m', α, Fs, hGe⟩ := GlobalTheory.T.modelCuspForms_span_usedRunReadings h ha hb hb0 hn G hG
      have hGs : M.res G = ∑ k, α k • rdLin h ha (Fs k) := by
        funext c x
        simp only [TwoLevels.res, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rdLin_apply]
        exact hGe c x.1 x.2
      rw [hGs]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fs k, rfl⟩)
    obtain ⟨z, hz, hzy⟩ := hy'
    have hz' : z = ⟨y, hy⟩ := Subtype.ext hzy
    rw [← hz']; exact hz
  obtain ⟨f, ρ, hfcu, hint, hind, hspan⟩ := GlobalTheory.T.exists_semilinear_extension_of_form_with_transported_rep (r.used v).full.σ₀ σ hσ cu bC hbs hbi hbt Rd hR hRs ((R2 p).FW i).ρ
  have hρR : ∀ g F, ρ g (Rd F) = Rd (act g F) := by
    intro g F
    rw [← hfcu, ← hfcu, hint, hcu g F]
  obtain ⟨a, hpull⟩ := hc
  refine ⟨ρ, σ, f, ⟨a, fun g G hG c x => ?_⟩, hint, hind, hspan⟩
  obtain ⟨m', α, Fs, hGe⟩ := GlobalTheory.T.modelCuspForms_span_usedRunReadings h ha hb hb0 hn G hG
  have hy : (⟨M.res G, Submodule.subset_span ⟨G, hG, rfl⟩⟩ : M.cusp ka) = ∑ k, α k • Rd (Fs k) := by
    apply Subtype.ext
    funext c' x'
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, TwoLevels.res, hRd,
      rdLin_apply]
    exact hGe c' x'.1 x'.2
  rw [hy, map_sum]
  simp only [map_smul, hρR, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hRd,
    rdLin_apply]
  rw [TwoLevels.pull, hGe (g • c) _ (GlobalTheory.T.twoLevelFlagDomain_transporter_mem_domain M g c x.1 x.2), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := hpull (Fs k) g c x.1 x.2 (psi_eq ha c) (psi_eq ha (g • c))
  rw [rdLin_apply]
  unfold rdFun rdR
  rw [hact g⁻¹ (Fs k)]
  refine (congrArg (α k * ·) hk).trans ?_
  ring
end Main2

end GlobalTheory.ShareOn.Reading
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubstDualWeylExpressibleMatrixMulClosedStatement
section
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowSubstDualWeylExpressible_matrix_mul_closed : ∀ (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (R : Type) [CommRing R] [Algebra O R] (Y Y' : Matrix (Fin N) (Fin N) R), Expr O N ν R Y → Expr O N ν R Y' → Expr O N ν R (Y * Y') := by
  first | exact @GlobalTheory.GenCoef.expr_mul | exact GlobalTheory.GenCoef.expr_mul | (intros; apply GlobalTheory.GenCoef.expr_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunNumericalConditionsHoldAlongFamily
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

namespace GlobalTheory.OntoNum

theorem pageNum_along : ∀ x₁ : ℝ, Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ ι : Fm.Ix x,
    PageNum (Fm.parT x hx ι) x₁ ∧ 3 ≤ (Fm.L x ι).sc.x ∧ ((Fm.D x ι).R.k : ℝ) * (Fm.L x ι).sc.b' ≤ (Fm.L x ι).sc.b ∧
      3 ≤ (Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 5) ∧ 8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 4 ≤ (Fm.D x ι).R.nV := by
  intro x₁
  obtain ⟨ε1, hε1, hS⟩ := GlobalTheory.T.indexBoundParameterRequirements_eventually_family
  refine ⟨ε1, hε1, fun eps he hle => ?_⟩
  obtain ⟨K, hK⟩ := hS eps he hle
  refine ⟨K.sup ⟨1000, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH hc hL => ?_⟩
  obtain ⟨hL1, hL2⟩ := (Fm.large_sup _ _ CH).1 hL
  have hCP : (1000 : ℝ) ≤ Fm.CP := hL2.1 Fm.CP (by simp [FamP.cPre])
  obtain ⟨xa, hxa⟩ := hK Fm CH hc hL1
  obtain ⟨xb, hxb⟩ := GlobalTheory.FinalRows.rows_of_pageFix eps Fm hc.1 hCP
  refine ⟨max (max xa xb) x₁, fun x hx hx0 ι => ?_⟩
  have hs := hxa x hx (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx0) ι
  obtain ⟨hSz, hCnW, hg, hCP', hz, -, -, hsx, -⟩ := hxb x hx (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx0) ι
  have hx1 : x₁ ≤ (Fm.L x ι).sc.x := by rw [hsx]; exact le_trans (le_max_right _ _) hx0
  exact ⟨⟨hSz, hCnW, hg, hCP', hz, hx1⟩, GlobalTheory.IndexAssembly.three_le_scale_of_pow_bound hs.2.1, hs.2.2.2.2.2.2.2.2.1, by linarith [hs.2.1],
    (Fm.parT x hx ι).nV_ge⟩

end GlobalTheory.OntoNum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondLinkOfWeightRowsStatement
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.second_link_of_weight_rows : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), p.Rows → SingleIndexPlacesAreTwisted p → Links2 p := by
  first | exact @GlobalTheory.BigOn.links2_of_rows | exact GlobalTheory.BigOn.links2_of_rows | (intros; apply GlobalTheory.BigOn.links2_of_rows <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBoundFittedIdentityStatement
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_bound_fitted_identity : SetAt → (Closed FamHyp fun Fm _ => EvPt Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → ThbSt → Thb @Comparison₂ := by
  first | exact @GlobalTheory.BigTop.Fun.thb_tie | exact GlobalTheory.BigTop.Fun.thb_tie | (intros; apply GlobalTheory.BigTop.Fun.thb_tie <;> assumption)
end

