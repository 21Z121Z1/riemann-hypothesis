import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0161
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0147
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0183
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothOfDefectZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0162
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0231
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1532
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0934
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannDualFormIndep
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)

noncomputable section

namespace GlobalTheory.RiemIndep

section Frames

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L N : LB A.left} {L' : LB A'.left} {g : ℕ}

theorem ex_add_mem (u : HolUnif A L g) (l : u.Λ) (z : Fin g → ℂ) : u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]

open PullHermitian in

theorem herm_eq_zero (hN : N.IsLB) (h0 : cls N hN = 0) (u : HolUnif A N g) (B : Matrix (Fin g) (Fin g) ℂ)
    (c : u.Λ → ℂ) (hB : B.IsHermitian) (hc : ∀ l, ‖c l‖ = 1)
    (hf : ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ N.U i → u.fr i z =
      c l * Complex.exp (Real.pi * hermForm B z l + Real.pi / 2 * hermForm B l l) * u.fr i (z + l)) : B = 0 := by
  obtain ⟨t, ht⟩ := (CechPic.cls_eq_zero_iff hN).1 h0
  obtain ⟨r, hr, hrφ⟩ := exists_glue (fun i : N.ι => {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ N.U i})
    (fun i => (u.hol _ 0).1) (fun z => exists_chart (u.ex z).left hN)
    (fun i z => valAt' (u.ex z).left _ (t.s i).val / u.fr i z)
    (fun i => by
      simp only [div_eq_mul_inv]
      exact (u.hol _ (t.s i).val).2.mul ((u.fr_hol i).inv fun z hz => u.fr_ne i z hz))
    (fun i j z hi hj => by
      have hij := inf_of _ hi hj
      have e := congrArg (unitVal _ hij) (ht i j)
      have e' : unitVal _ hi (t.s i) = unitVal _ hij (N.g i j) * unitVal _ hj (t.s j) :=
        (unitVal_res _ inf_le_left hij hi _).symm.trans (e.trans ((map_mul _ _ _).trans
          (congrArg (_ * ·) (unitVal_res _ inf_le_right hij hj _))))
      rw [div_eq_div_iff (u.fr_ne _ _ hi) (u.fr_ne _ _ hj), u.fr_compat i j z hij, valAt'_eq_unitVal _ hi,
        valAt'_eq_unitVal _ hj, valAt'_eq_unitVal _ hij, e', Units.val_mul]
      ring)
  haveI := u.discrete
  refine (appellHumbert_trivial_of_nowhere_vanishing g u.Λ u.full B c r hB hc hr (fun z => ?_) fun l z => ?_).1
  · obtain ⟨i, hi⟩ := exists_chart (u.ex z).left hN
    rw [hrφ i z hi, valAt'_eq_unitVal _ hi]
    exact div_ne_zero (Units.ne_zero _) (u.fr_ne _ _ hi)
  · obtain ⟨i, hi⟩ := exists_chart (u.ex z).left hN
    have hi' : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ N.U i := by rwa [ex_add_mem]
    have h1 := u.fr_ne _ _ hi
    have h2 := u.fr_ne _ _ hi'
    rw [hrφ i z hi, hrφ i (z + l) hi', ex_add_mem, div_eq_iff h2, mul_right_comm, ← hf l i z hi]
    field_simp

variable (u : HolUnif A L g) (u' : HolUnif A' L' g) (ψ : A ⟶ A') (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))

theorem covers (hT : ∀ z, u'.ex (T z) = u.ex z ≫ ψ) (k : Fin 3) (z : Fin g → ℂ) :
    u'.ex (![T + T, T, 0] k z) = u.ex z ≫ ![ψ * ψ, ψ, 1] k := by
  fin_cases k
  · change u'.ex (T z + T z) = u.ex z ≫ (ψ * ψ)
    rw [u'.ex_add, hT, MonObj.comp_mul]
  · exact hT z
  · change u'.ex 0 = u.ex z ≫ 1
    rw [MonObj.comp_one]
    exact (u'.ker 0).2 (zero_mem _)

abbrev diagLB (L' : LB A'.left) (ψ : A ⟶ A') : LB A.left :=
  LB.LinComb L' (fun k => (![ψ * ψ, ψ, 1] k).left) ![1, -2, 1]

theorem cls_diagLB (hL' : L'.IsLB) (h : (diagLB L' ψ).IsLB) : cls _ h = lam (cls L' hL') ψ ψ := by
  refine (CechPic.cls_linComb hL' _ _ h).trans ?_
  rw [Fin.sum_univ_three, lam]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  module

theorem factor_diag (hT : ∀ z, u'.ex (T z) = u.ex z ≫ ψ) {H : Matrix (Fin g) (Fin g) ℂ} {χ : u'.Λ → ℂ}
    (hA : u'.IsAH H χ) (l : u.Λ) : ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (diagLB L' ψ).U i →
      (linCombUnif u u' _ _ ![1, -2, 1] (covers u u' ψ T hT)).fr i z =
        c * Complex.exp (Real.pi * (2 * hermForm H (T z) (T l)) + Real.pi / 2 * (2 * hermForm H (T l) (T l))) *
          (linCombUnif u u' _ _ ![1, -2, 1] (covers u u' ψ T hT)).fr i (z + l) := by
  have hl : T l ∈ u'.Λ := by
    rw [← u'.ker, hT, (u.ker l).2 l.2, ← (u.ker 0).2 u.Λ.zero_mem, ← hT, map_zero]
    exact (u'.ker 0).2 u'.Λ.zero_mem
  have hχ := hA.2.2.1
  refine ⟨χ ⟨T l + T l, add_mem hl hl⟩ / χ ⟨T l, hl⟩ ^ 2, by simp [hχ], fun i z hz => ?_⟩
  have hc : ∀ k, ⊤ ≤ (u'.ex (![T + T, T, 0] k z)).left ⁻¹ᵁ L'.U (i k) := fun k => by
    rw [covers u u' ψ T hT]
    exact (CubeValues.le_preimage_wchart (u.ex z).left L' _ i).1 hz k
  have h0 := hA.2.2.2 ⟨T l + T l, add_mem hl hl⟩ (i 0) (T z + T z) (hc 0)
  have h1 := hA.2.2.2 ⟨T l, hl⟩ (i 1) (T z) (hc 1)
  have h4 : χ ⟨T l, hl⟩ ≠ 0 := norm_ne_zero_iff.1 (by rw [hχ]; exact one_ne_zero)
  change ∏ k, u'.fr (i k) (![T + T, T, 0] k z) ^ (![1, -2, 1] k : ℤ) =
    _ * ∏ k, u'.fr (i k) (![T + T, T, 0] k (z + l)) ^ (![1, -2, 1] k : ℤ)
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, LinearMap.add_apply,
    LinearMap.zero_apply, map_add, zpow_one, zpow_neg, zpow_ofNat]
  rw [h0, h1, add_zero]
  simp only [hermForm, star_add, Matrix.mulVec_add, add_dotProduct, dotProduct_add]
  generalize (T z ⬝ᵥ H.mulVec (star (T l))) = a
  generalize (T l ⬝ᵥ H.mulVec (star (T l))) = b
  have e : Complex.exp (Real.pi * (a + a + (a + a)) + Real.pi / 2 * (b + b + (b + b))) =
      Complex.exp (Real.pi * (2 * a) + Real.pi / 2 * (2 * b)) * Complex.exp (Real.pi * a + Real.pi / 2 * b) ^ 2 := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h6 := Complex.exp_ne_zero (Real.pi * a + Real.pi / 2 * b)
  rw [e]
  generalize Complex.exp (Real.pi * a + Real.pi / 2 * b) = s at h6
  simp only [mul_pow, mul_inv]
  field_simp

open PullHermitian in

theorem hermForm_eq_of_lam (hL : L.IsLB) (hL' : L'.IsLB) (hT : ∀ z, u'.ex (T z) = u.ex z ≫ ψ)
    {H H' : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} {χ' : u'.Λ → ℂ} (hA : u.IsAH H χ) (hA' : u'.IsAH H' χ')
    (h : lam (cls L' hL') ψ ψ = lam (cls L hL) (𝟙 A) (𝟙 A)) (z w : Fin g → ℂ) :
    hermForm H' (T z) (T w) = hermForm H z w := by
  have hI : ∀ z, u.ex (LinearMap.id (R := ℂ) z) = u.ex z ≫ 𝟙 A := fun z => (Category.comp_id _).symm
  choose c hc hf using factor_diag u u (𝟙 A) LinearMap.id hI hA
  choose c' hc' hf' using factor_diag u u' ψ T hT hA'
  have d : (diagLB L (𝟙 A)).IsLB := LB.isLB_linComb hL _ _
  have d' : (diagLB L' ψ).IsLB := LB.isLB_linComb hL' _ _
  set H₂ := (LinearMap.toMatrix' T).transpose * H' * (LinearMap.toMatrix' T).transpose.conjTranspose with hH₂
  have hH₂h : H₂.IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose _ hA'.1
  have hs : ∀ z w, hermForm ((2 : ℂ) • H₂ - (2 : ℂ) • H) z w = 2 * hermForm H' (T z) (T w) - 2 * hermForm H z w :=
    fun z w => by rw [hermForm_sub_smul, hH₂, hermForm_pull]
  have key := herm_eq_zero (LB.isLB_div d' d)
    (by rw [CechPic.cls_div d' d, cls_diagLB ψ hL', cls_diagLB _ hL, h, sub_self])
    (SameFactor.divUnif (linCombUnif u u _ _ ![1, -2, 1] (covers u u _ _ hI))
      (linCombUnif u u' _ _ ![1, -2, 1] (covers u u' ψ T hT)) rfl)
    ((2 : ℂ) • H₂ - (2 : ℂ) • H) (fun l => c' l / c l)
    ((hH₂h.smul (by simp [IsSelfAdjoint])).sub (hA.1.smul (by simp [IsSelfAdjoint])))
    (fun l => (norm_div _ _).trans ((congrArg₂ (· / ·) (hc' l) (hc l)).trans (div_one _))) fun l i z hz => by
      obtain ⟨h1, h2⟩ := (top_le_preimage_inf _ _ _).1 hz
      have e1 := hf' l i.1 z h1
      have e2 := hf l i.2 z h2
      refine (congrArg₂ (fun a b => a * b⁻¹) e1 e2).trans ?_
      rw [hs, hs]
      change _ = _ * (_ * _⁻¹)
      rw [mul_sub, mul_sub, sub_add_sub_comm, Complex.exp_sub]
      simp only [LinearMap.id_apply, mul_inv, div_eq_mul_inv]
      ring
  have := hs z w
  rw [key] at this
  simp only [hermForm, Matrix.zero_mulVec, dotProduct_zero] at this ⊢
  linear_combination (-1 / 2 : ℂ) * this

end Frames

theorem exists_lin (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S) (d d' : P.RiemannData y) :
    ∃ T : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ), (∀ z, (d'.u.ex (T z)).left ≫ d'.φ = (d.u.ex z).left ≫ d.φ) ∧
      ∀ z w, hermForm d'.H (T z) (T w) = hermForm d.H z w := by
  obtain ⟨ψ, e⟩ := SharpPull.exists_lift d.isPull d'.isPull (𝟙 P.A)
  have hψ := SharpPull.isMonHom_lift d.isPull d'.isPull e
  have hψφ : ψ.left ≫ d'.φ = d.φ := e.trans (Category.comp_id _)
  have hA := PolPull.isAbelianScheme_of_isGrpPullback P.isAb d.isPull
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback P.isAb d'.isPull
  obtain ⟨t₁, t₂⟩ := TorusTransfer.tangent_bijective d'.u
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback d'.isPull.1 P.smoothDim)
  obtain ⟨T, hT, -⟩ := HomLinear.exists_linear_of_isMonHom d.B d'.B hA hA' d.L d'.L P.g P.g d.u d'.u t₁ t₂ ψ hψ
  refine ⟨T, fun z => ?_, hermForm_eq_of_lam d.u d'.u ψ T d.isLB d'.isLB hT d.isAH d'.isAH ?_⟩
  · rw [hT, Over.comp_left, Category.assoc, hψφ]
  have k (b : P.RiemannData y) (x : d.B ⟶ b.B) : lam (cls b.L b.isLB) x x =
      CechPic.pull ((lift x x).left ≫ sqMap b.isPull.1.w) P.c := by
    rw [CechPic.pull_comp, b.pol, CechPic.pull_lam, lift_fst, lift_snd]
  have k₁ (b : P.RiemannData y) (x : d.B ⟶ b.B) :
      ((lift x x).left ≫ sqMap b.isPull.1.w) ≫ pullback.fst _ _ = x.left ≫ b.φ := by
    refine (Category.assoc _ _ _).trans ((congrArg _ (pullback.lift_fst _ _ _)).trans ?_)
    exact (Category.assoc _ _ _).symm.trans (congrArg (·.left ≫ b.φ) (lift_fst x x))
  have k₂ (b : P.RiemannData y) (x : d.B ⟶ b.B) :
      ((lift x x).left ≫ sqMap b.isPull.1.w) ≫ pullback.snd _ _ = x.left ≫ b.φ := by
    refine (Category.assoc _ _ _).trans ((congrArg _ (pullback.lift_snd _ _ _)).trans ?_)
    exact (Category.assoc _ _ _).symm.trans (congrArg (·.left ≫ b.φ) (lift_snd x x))
  have k₃ : ψ.left ≫ d'.φ = (𝟙 d.B : d.B ⟶ d.B).left ≫ d.φ := hψφ.trans (Category.id_comp _).symm
  rw [k, k]
  congr 2
  exact pullback.hom_ext ((k₁ _ _).trans (k₃.trans (k₁ _ _).symm)) ((k₂ _ _).trans (k₃.trans (k₂ _ _).symm))

open Matrix HermFrame in

theorem riemann_dual_form_indep : ∀ (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S) (d d' : P.RiemannData y)
    (W : P.A.left.Opens) (f f' : Γ(P.A.left, W)), ⊤ ≤ (y ≫ LieVB.unitSec P.A) ⁻¹ᵁ W →
    HermFrame.form (HermFrame.dualGram d.H) (d.cov W f) (d.cov W f') =
      HermFrame.form (HermFrame.dualGram d'.H) (d'.cov W f) (d'.cov W f') := by
  intro S P y d d' W f f' hW
  obtain ⟨T, hT, hH⟩ := RiemIndep.exists_lin S P y d d'
  set M := LinearMap.toMatrix' T with hM
  have hMv : ∀ z, M *ᵥ z = T z := fun z => LinearMap.toMatrix'_mulVec T z
  have hchg : d.H = chg M d'.H := by
    ext a b
    rw [← form_single (chg M d'.H), form_chg, hMv, hMv]
    exact (form_single d.H a b).symm.trans (hH _ _).symm
  have hinj : Function.Injective M.mulVec := by
    refine (injective_iff_map_eq_zero M.mulVecLin).2 fun v hv => ?_
    by_contra hne
    have h1 := (posDef_iff.1 d.posDef).2 v hne
    rw [hchg, form_chg] at h1
    have h0 : M *ᵥ v = 0 := hv
    rw [h0] at h1
    simp [form] at h1
  have hU : IsUnit M := mulVec_injective_iff_isUnit.1 hinj
  have hMN : M * M⁻¹ = 1 := mul_nonsing_inv M ((isUnit_iff_isUnit_det M).1 hU)
  have hfn : ∀ g : Γ(P.A.left, W), d.fn W g = d'.fn W g ∘ T := fun g => by
    funext z
    simp only [PPAS.RiemannData.fn, Function.comp_apply, hT]
  have hTd : ∀ v, fderiv ℂ (⇑T) 0 v = T v := fun v => by
    have := (LinearMap.toContinuousLinearMap T).fderiv (x := 0)
    exact congrArg (fun L => L v) this
  have hcov : ∀ g : Γ(P.A.left, W), d.cov W g = Mᵀ *ᵥ d'.cov W g := fun g => by
    funext a
    have hd := d'.differentiableAt_fn g hW
    have hd' : DifferentiableAt ℂ (d'.fn W g) (T 0) := by rw [map_zero]; exact hd
    have hTdiff : DifferentiableAt ℂ (⇑T) 0 := (LinearMap.toContinuousLinearMap T).differentiableAt
    simp only [PPAS.RiemannData.cov]
    rw [hfn, fderiv_comp 0 hd' hTdiff, ContinuousLinearMap.comp_apply, hTd, map_zero, ← hMv,
      mulVec_single_one]
    change _ = ∑ b, M.col a b * fderiv ℂ (d'.fn W g) 0 (Pi.single b 1)
    generalize fderiv ℂ (d'.fn W g) 0 = L
    conv_lhs => rw [pi_eq_sum_univ (M.col a)]
    simp only [map_sum, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    congr 2
    funext j
    simp [Pi.single_apply, eq_comm]
  rw [hchg, dualGram_chg hMN, form_chg, hcov, hcov, mulVec_mulVec, mulVec_mulVec, ← transpose_mul, hMN,
    transpose_one, one_mulVec, one_mulVec]

end GlobalTheory.RiemIndep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowTypeHasSphericalHeckeEigensystem
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

namespace GlobalTheory.RowEig

open Formalism.IndefR.principalLevelFrame

variable {D : D7}

def rtV (V : HSp D) : GA D V →* Module.End ℂ (GA D V → ℂ) where
  toFun g := { toFun := fun f h => f (h * g), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  map_one' := by ext f h; simp
  map_mul' g g' := by ext f h; simp [mul_assoc]

theorem rtV_apply (V : HSp D) (g : GA D V) (f : GA D V → ℂ) (h : GA D V) : rtV V g f h = f (h * g) := rfl

variable {V : HSp D} {n : ℕ}

theorem pre_psi (Q : RowPsi V n) (z : Formalism.AUTREP.GAf D.host.E n) : pre Q (Q.ψ z) = z := by
  have h : ∃ x, Q.ψ x = Q.ψ z := ⟨z, rfl⟩
  unfold pre
  rw [dif_pos h]
  exact Q.inj h.choose_spec

theorem psi_pre (Q : RowPsi V n) {γ : GA D V} (hγ : γ ∈ GfC V) : Q.ψ (pre Q γ) = γ := by
  obtain ⟨h, hh⟩ := Q.onto γ hγ
  have h' : ∃ x, Q.ψ x = γ := ⟨h, hh⟩
  unfold pre
  rw [dif_pos h']
  exact h'.choose_spec

open Classical in

def lift (Q : RowPsi V n) (x : Formalism.AUTREP.GAf D.host.E n → ℂ) : GA D V → ℂ :=
  fun g => if g ∈ GfC V then x (pre Q g) else 0

theorem rtV_lift_psi (Q : RowPsi V n) (x : Formalism.AUTREP.GAf D.host.E n → ℂ) {γ : GA D V} (hγ : γ ∈ GfC V)
    (y : Formalism.AUTREP.GAf D.host.E n) : rtV V γ (lift Q x) (Q.ψ y) = x (y * pre Q γ) := by
  rw [rtV_apply]
  have hmem : Q.ψ y * γ ∈ GfC V := (GfC V).mul_mem (Q.into y) hγ
  have heq : Q.ψ y * γ = Q.ψ (y * pre Q γ) := by rw [map_mul, psi_pre Q hγ]
  unfold lift
  rw [if_pos hmem, heq, pre_psi]

theorem lift_fixed (Q : RowPsi V n) (x : Formalism.AUTREP.GAf D.host.E n → ℂ) (K : Set (GA D V)) (hK : K ⊆ GfC V)
    (hx : ∀ κ, Q.ψ κ ∈ K → Formalism.L2.NG.rt D.host.E n κ x = x) : ∀ k ∈ K, rtV V k (lift Q x) = lift Q x := by
  intro k hk
  have hkG : k ∈ GfC V := hK hk
  funext g
  rw [rtV_apply]
  by_cases hg : g ∈ GfC V
  · have hgk : g * k ∈ GfC V := (GfC V).mul_mem hg hkG
    have heq : g * k = Q.ψ (pre Q g * pre Q k) := by rw [map_mul, psi_pre Q hg, psi_pre Q hkG]
    have hfix := congrFun (hx (pre Q k) (by rw [psi_pre Q hkG]; exact hk)) (pre Q g)
    unfold lift
    rw [if_pos hgk, if_pos hg, heq, pre_psi]
    exact hfix
  · have hgk : g * k ∉ GfC V := fun h => hg (by simpa using (GfC V).mul_mem h ((GfC V).inv_mem hkG))
    unfold lift
    rw [if_neg hgk, if_neg hg]

theorem heckeOperator_apply' (Q : RowPsi V n) (B : Finset (GA D V)) (x : Formalism.AUTREP.GAf D.host.E n → ℂ) (y : Formalism.AUTREP.GAf D.host.E n) :
    Hecke₃ Q B x y = ∑ γ ∈ B, x (y * pre Q γ) := by
  simp [Hecke₃, heckeG, LinearMap.sum_apply, Finset.sum_apply, Formalism.L2.NG.rt]

theorem sph_mem_GfC {P : Pl D.host.E} {d : List ℤ} {B : Finset (GA D V)} (hB : SphOp V P d B) : ∀ γ ∈ B, γ ∈ GfC V := by
  obtain ⟨e, f, ϖ, α, -, -, -, -, -, -, -, -, -, -, hR⟩ := hB
  exact fun γ hγ => (hR.1 γ hγ).1

theorem hyp_sub (P : Pl D.host.E) : hyp V P ⊆ GfC V := fun k hk => hk.1.1

theorem heckeOperator_eq_of_spherical (Q : RowPsi V n) (P : Pl D.host.E) (d : List ℤ) (B B' : Finset (GA D V)) (hB : SphOp V P d B)
    (hB' : SphOp V P d B') (x : Formalism.AUTREP.GAf D.host.E n → ℂ) (hx : ∀ κ, Q.ψ κ ∈ hyp V P → Formalism.L2.NG.rt D.host.E n κ x = x) :
    Hecke₃ Q B x = Hecke₃ Q B' x := by
  have hu := lift_fixed Q x (hyp V P) (hyp_sub P) hx
  have e1 := ((GlobalTheory.SphLabelOps.label_operators V P).1 d B hB).2 (GA D V → ℂ) (rtV V) (lift Q x) hu
  have e2 := ((GlobalTheory.SphLabelOps.label_operators V P).1 d B' hB').2 (GA D V → ℂ) (rtV V) (lift Q x) hu
  have e := e1.trans e2.symm
  funext y
  have ey := congrFun e (Q.ψ y)
  rw [Finset.sum_apply, Finset.sum_apply] at ey
  rw [heckeOperator_apply', heckeOperator_apply']
  rw [Finset.sum_congr rfl (fun γ hγ => rtV_lift_psi Q x (sph_mem_GfC hB γ hγ) y),
    Finset.sum_congr rfl (fun γ hγ => rtV_lift_psi Q x (sph_mem_GfC hB' γ hγ) y)] at ey
  exact ey

theorem sph_of_full {J : Set (GA D V)} {χ : GA D V → ℂ} {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {P : Pl D.host.E}
    {d : List ℤ} {B : Finset (GA D V)} (h : Hecke₂ V J χ S P d B) : SphOp V P d B := by
  obtain ⟨e, f, ϖ, α, -, hPI, h1, h2, hd, hJ, -, hα, hdiv, hR, hcos⟩ := h
  have hset : {k | k ∈ J ∧ SuppF V f k} = {k | k ∈ KsphC V ∅ ∧ SuppF V f k} := by
    ext k
    exact ⟨fun ⟨a, b⟩ => ⟨(hJ k b).1 a, b⟩, fun ⟨a, b⟩ => ⟨(hJ k b).2 a, b⟩⟩
  rw [hset] at hcos
  exact ⟨e, f, ϖ, α, fun v hv => absurd hv (Finset.notMem_empty v), hPI, h1, h2, hd, fun _ _ => Iff.rfl,
    fun _ _ _ => rfl, hα, hdiv, hR, hcos⟩

end GlobalTheory.RowEig

namespace GlobalTheory.RowEig

open Formalism.IndefR.principalLevelFrame

set_option maxHeartbeats 1000000 in

theorem row_type_eig : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → (∀ χ ∈ A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ SF, IsSF R SF → ∀ {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (PY : principalLevelFrame.RowPsi (Yc D 0) n) (PW : ∀ i, principalLevelFrame.RowPsi (Wc D i) n), StdPsi hF PY → (∀ i, StdPsi hF (PW i)) → ∀ π, π ∈ principalLevelFrame.OccRows R.θ PY (R.MY 0) (fun b => (levS _ (R.βY 0) (R.dat0 (R.levR F b)))) (fun b => (levChi _ (R.βY 0) (R.dat0 (R.levR F b)))) (fun _ => R.e0) → ∀ i0, ∃ c, principalLevelFrame.IsEigOf (PW i0) (levS _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A)))) (levChi _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A)))) SF π c := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s hOk hCore hX SF hSF n hF PY PW hPY hPW π hπ i0
  classical
  have hsc : ∀ Pr d B, SphOp (Wc D i0) Pr d B → ∃ a : ℂ, ∀ x ∈ π.S,
      (∀ κ, (PW i0).ψ κ ∈ hyp (Wc D i0) Pr → Formalism.L2.NG.rt D.host.E n κ x = x) → Hecke₃ (PW i0) B x = a • x :=
    fun Pr d B h => GlobalTheory.T.sphericalHecke_scalar_on_spherical_vectors hF (PW i0) (hPW i0) π Pr d B h

  obtain ⟨c0, hBase⟩ := hCore.lev.βW i0
  rw [one_pow] at hBase

  have hfix : ∀ Pr d B, Hecke₂ (Wc D i0) (levS _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A))))
      (levChi _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A)))) SF Pr d B → ∀ x,
      IsTypeVec ((PW i0).ψ ⁻¹' levS _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A))))
        (fun κ => levChi _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A))) ((PW i0).ψ κ)) x →
      ∀ κ, (PW i0).ψ κ ∈ hyp (Wc D i0) Pr → Formalism.L2.NG.rt D.host.E n κ x = x := by
    intro Pr d B hB x hx κ hκ
    have hOff : OffS D SF Pr := by
      obtain ⟨e, f, ϖ, α, h, -⟩ := hB
      exact h
    have hGood : Good R A.μ0 Pr := ((GlobalTheory.GoodPrimes.good_primes R F hCore.lev).2.2.1 SF hSF Pr).mp hOff
    have hN : ((1 : ℕ) : 𝓞 D.host.E) ∉ Pr.asIdeal := by
      rw [Nat.cast_one]
      exact (Ideal.ne_top_iff_one _).mp Pr.isPrime.ne_top
    have hL := (GlobalTheory.LevOp.level_operators (Wc D i0) (R.βW i0) (R.ΛW i0) 1 (R.datWp i0 (R.levL F false (sg0 D A))) hBase Pr hN
      (fun PP hPP => by
        rcases hPP with h | h
        · exact hGood PP (Or.inl h)
        · exact absurd h (Finset.notMem_empty PP))).1 _ hκ
    have := hx κ hL.1
    rw [this]
    dsimp only
    rw [hL.2, one_smul]
  refine ⟨fun Pr d => if h : ∃ B, Hecke₂ (Wc D i0) (levS _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A))))
      (levChi _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A)))) SF Pr d B then
      (hsc Pr d h.choose (sph_of_full h.choose_spec)).choose else 0, ?_, ?_, ?_⟩
  · exact GlobalTheory.T.rowType_exists_baseLevel_vector R F hOk hCore hX hF PY PW hPY hPW π hπ i0
  · intro Pr d B hB x hxS hx
    have hex : ∃ B, Hecke₂ (Wc D i0) (levS _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A))))
      (levChi _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A)))) SF Pr d B := ⟨B, hB⟩
    have hxf := hfix Pr d B hB x hx
    dsimp only
    rw [dif_pos hex, heckeOperator_eq_of_spherical (PW i0) Pr d B hex.choose (sph_of_full hB) (sph_of_full hex.choose_spec) x hxf]
    exact (hsc Pr d hex.choose (sph_of_full hex.choose_spec)).choose_spec x hxS hxf
  · intro Pr d hne
    exact dif_neg hne

end GlobalTheory.RowEig
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfArtinianSquareZeroLiftingNoetherianBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SmoothCrit

theorem smooth_of_lift (A R : Type) [CommRing A] [IsNoetherianRing A] [CommRing R] (g : A →+* R) (hg : g.FiniteType)
    (H : (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (β : A →+* C) (φ₀ : R →+* C₀), φ₀.comp (g) = π.comp β → ∃ φ : R →+* C, π.comp φ = φ₀ ∧ φ.comp (g) = β)) : g.Smooth := by
  algebraize [g]
  have : Algebra.FinitePresentation A R := Algebra.FinitePresentation.of_finiteType.mp hg
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp (inferInstance : Algebra.FiniteType A R)
  letI := f.toRingHom.toAlgebra
  haveI : IsScalarTower A (MvPolynomial (Fin n) A) R := IsScalarTower.of_algebraMap_eq fun a => (f.commutes a).symm
  have hs : Function.Surjective (algebraMap (MvPolynomial (Fin n) A) R) := hf
  have hmax : ∀ (m : Ideal R) [m.IsMaximal], Algebra.IsSmoothAt A m := by
    intro m _
    letI : Field (R ⧸ m) := Ideal.Quotient.field m
    have key := GlobalTheory.T.injective_cotangentComplexBaseChange_of_forms_extend' A (MvPolynomial (Fin n) A) R (R ⧸ m) fun ℓ => GlobalTheory.T.exists_derivation_extending_kernel_form_of_lifting A (MvPolynomial (Fin n) A) R (R ⧸ m) hs Ideal.Quotient.mk_surjective H ℓ
    exact (GlobalTheory.SS.DefectZero.isSmoothAt_iff_injective A (MvPolynomial (Fin n) A) R (R ⧸ m) hs m
      (Ideal.mk_ker).symm).mpr key
  have hU : Algebra.smoothLocus A R = Set.univ := by
    refine Set.eq_univ_iff_forall.mpr fun q => ?_
    obtain ⟨m, hm, hqm⟩ := Ideal.exists_le_maximal q.asIdeal q.2.ne_top
    have hm' : (⟨m, hm.isPrime⟩ : PrimeSpectrum R) ∈ Algebra.smoothLocus A R := @hmax m hm
    exact ((PrimeSpectrum.le_iff_specializes q ⟨m, hm.isPrime⟩).mp hqm).mem_open Algebra.isOpen_smoothLocus hm'
  exact ⟨Algebra.smoothLocus_eq_univ_iff.mp hU, inferInstance⟩

theorem smooth_of_artinian_lift : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (X : Scheme.{0}) (s : X ⟶ Sp B), LocallyOfFiniteType s → (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (t : Sp C ⟶ Sp B) (x₀ : Sp C₀ ⟶ X), x₀ ≫ s = spMap π ≫ t → ∃ x : Sp C ⟶ X, spMap π ≫ x = x₀ ∧ x ≫ s = t) → Smooth s := by
  intro B _ _ X s hs H
  constructor
  intro U hU V hV e
  haveI : IsNoetherianRing Γ(Sp B, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  exact smooth_of_lift _ _ _ (HasRingHomProperty.appLE @LocallyOfFiniteType s hs ⟨U, hU⟩ ⟨V, hV⟩ e) (GlobalTheory.T.lift_ringHom_affine_open_of_artinian_scheme_lift B X s H U hU V hV e)

end GlobalTheory.SmoothCrit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamePartLeftStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_part_left : ∀ (F : Type) [Field F] [NumberField F] (κ κ₁ κ' : Type) [Fintype κ] [Fintype κ₁] [Fintype κ']
    (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ₁ → AF F) → ℂ)), IsTame F T → IsTame F (partL (κ' := κ') T) := by
  first | exact @GlobalTheory.DoublingEv.PartLTame.isTame_partL | exact GlobalTheory.DoublingEv.PartLTame.isTame_partL | (intros; apply GlobalTheory.DoublingEv.PartLTame.isTame_partL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSeparationOfIwahoriTraceStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_separation_of_iwahori_trace : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IwahoriTrace → GlobalTheory.IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.ExponentsSeparate → Separation := by
  first | exact @GlobalTheory.TrMultSep.separation_of_iwahoriTrace | exact GlobalTheory.TrMultSep.separation_of_iwahoriTrace | (intros; apply GlobalTheory.TrMultSep.separation_of_iwahoriTrace <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingFrameDeltaChangeStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FieldBC GlobalTheory.OneMapAll
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolding_frame_delta_change : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (n r : ℕ) (c c' : Coeff l) (hle : c.F ≤ c'.F) (V : HSp D) (hr : V.rank = r) (d : DeltaDat Xo c n) (u : c'.F) (U₂ : Unf d.Xo₂ d.c₂ (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F)) r) (dict₂ : GA D V → Σ k, Frame (U₂.X k).Ψ r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (c0 : ℂ), d.cδ ∈ sec d.Xo₂ d.c₂ 0 0 → CXiAt V hr c.F.val.toRingHom d U₂ dict₂ io x₀ xi c0 → CXiAt V hr c'.F.val.toRingHom (covBC hle d u) (covUnf hle d u U₂) dict₂ io x₀ xi ((u : ℂ) * c0) := by
  first | exact @GlobalTheory.OneMapAll.cXiAt_covBC | exact GlobalTheory.OneMapAll.cXiAt_covBC | (intros; apply GlobalTheory.OneMapAll.cXiAt_covBC <;> assumption)
end

