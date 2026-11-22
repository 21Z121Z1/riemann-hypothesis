import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedTraitDescentFiniteExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2775
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2699
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2773
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2776
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0056
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0587
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2687
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1111
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2733
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2754

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedTraitMovesToFiniteExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.UniEnlarge

open GlobalTheory.Mum.ClosureDescent GlobalTheory.ThetaDescent

theorem uniTrait_of_finExt : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁], Base R₁ → ∀ (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))), UniTrait D₁.toPre A → ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (i₁₂ : R₁ →+* R₂), FinExt i₁₂ → IsLocalHom i₁₂ → ∀ (D₂ : DegData R₂ (maximalIdeal R₂)), Nonempty (IsPullDeg i₁₂ D₁.toPre D₂.toPre) → ∀ (A₂ : PolAV (Sp (FractionRing R₂))) (a : A₂.A.left ⟶ A.A.left), IsFib i₁₂ A A₂ a → UniTrait D₂.toPre A₂ := by
  intro R₁ _ _ _ _ D₁ A hU R₂ _ _ _ i₁₂ hi₁₂ hl₁₂ D₂ ⟨hD₂⟩ A₂ a₂ hA₂
  classical
  obtain ⟨W, _, _, _, φ, G', _, _, D', A', U', hD', a, hW, hφ, hφl, hG', ga, hga, g₁, l₁⟩ := hU
  obtain ⟨ga₂, hga₂, g₂, l₂⟩ := hA₂
  have hfin : i₁₂.Finite := hi₁₂.2.2
  let β : FractionRing W →+* AlgebraicClosure (FractionRing W) := algebraMap _ _
  have hβ : β.IsIntegral := fun x => Algebra.IsIntegral.isIntegral (R := FractionRing W) x
  obtain ⟨j₁, hj₁⟩ := exists_extend hfin (algebraMap R₁ (FractionRing R₁)) ga₂ (RingHom.ext fun r => hga₂ r)
    (β.comp ga)
  have hjρ : ∀ r, j₁ (algebraMap R₂ _ (i₁₂ r)) = β (((algebraMap W (FractionRing W)).comp φ) r) := fun r => by
    rw [← hga₂, ← RingHom.comp_apply j₁ ga₂, hj₁, RingHom.comp_apply, hga, RingHom.comp_apply]
  obtain ⟨s₀, hs₀⟩ := exists_range_le_gen hfin β ((algebraMap W _).comp φ) j₁ hjρ
  let i := β.codRestrict _ (mem_gen β s₀)
  let k := j₁.codRestrict _ hs₀
  have hi : i.Finite := finite_gen β hβ s₀
  have := hW.1
  have hWb : Base W := ⟨⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩, hW.2.2⟩
  obtain ⟨W₁, _, _, _, io, σ, hio, hiol, hσ⟩ := GlobalTheory.CommonCover.exists_cover_field W hWb _ i hi
  obtain ⟨D₃, hD₃, A₃, U₃, a₃, hA₃⟩ := exists_unif_fib hWb.1 hio.1 io hio.2.1 (map_maximalIdeal_le io) hG' U'
    (σ.comp i) ((RingHom.comp_assoc _ _ _).trans hσ)
  have f₁ : Fib A₃ A ((σ.comp i).comp ga) (a₃ ≫ a) := hA₃.comp ⟨g₁, l₁⟩ rfl
  have e : (σ.comp k).comp ga₂ = (σ.comp i).comp ga := RingHom.ext fun x =>
    congrArg σ (Subtype.ext (DFunLike.congr_fun hj₁ x))
  obtain ⟨d, -, hd⟩ := Fib.cancel (σ.comp k) (⟨g₂, l₂⟩ : Fib A₂ A ga₂ a₂) f₁ e
  haveI := hio.1.2.2.1
  obtain ⟨φ₂, hφ₂, hcomp, hinj, hl⟩ := exists_restrict hfin (io.comp φ) (σ.comp k) fun r => by
    have e₁ : k (algebraMap R₂ _ (i₁₂ r)) = i (algebraMap W _ (φ r)) := Subtype.ext (hjρ r)
    exact (congrArg σ e₁).trans (DFunLike.congr_fun hσ (φ r))
  obtain ⟨q⟩ := GlobalTheory.PullDegComp.nonempty_isPullDeg_comp hφ hio.2.1 hD' hD₃
  rw [← hcomp] at q
  obtain ⟨q₁⟩ := GlobalTheory.PullDegUniq.nonempty_isPullDeg_cancel hi₁₂.2.1 hinj hD₂ q
  exact ⟨W₁, _, _, _, φ₂, _, inferInstance, inferInstance, D₃, A₃, U₃, q₁, d, cDvr_of_finExt hW hio, hinj, hl,
    IsSemiAbelian.pullback _ G' hG', σ.comp k, hφ₂, hd.1, hd.2⟩

end GlobalTheory.Mum.UniEnlarge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizationBaseChangeCompleteDvrStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformization_base_change_complete_dvr : ∀ (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsLocalRing R₀], AdmBase R₀ (maximalIdeal R₀) → ∀ (D₀ : DegData R₀ (maximalIdeal R₀)) (A₀ : PolAV (Sp (FractionRing R₀))) (G₀ : Over (Sp R₀)) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ (U₀ : Unif (maximalIdeal R₀) D₀ A₀ G₀) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R₀ →+* W), Function.Injective φ → IsLocalHom φ → ∀ (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (β : GW.left ⟶ G₀.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), IsGrpPullback GW G₀ (spMap φ) β → LBIso UW.LG.L (U₀.LG.L.pull β) → Nonempty (IsPullDeg φ D₀.toPre DW.toPre) := by
  first | exact @GlobalTheory.Mum.isPullDeg_of_trait_unif | exact GlobalTheory.Mum.isPullDeg_of_trait_unif | (intros; apply GlobalTheory.Mum.isPullDeg_of_trait_unif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnimodLatticeBarBar
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem unimodLattice_bar_bar {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (a : 𝓞 E) :
    H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

theorem unimodLattice_bar_rt {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    H.bar H.rt = -H.rt := by
  apply RingOfIntegers.ext
  rw [H.bar_eq]
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj]
  have hsq : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    have := congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq
    simpa using this
  have hd : (7 : ℝ) ≤ H.d := by
    have := H.d_mod
    have : 7 ≤ H.d := by omega
    exact_mod_cast this
  set z := φ (H.rt : E) with hz
  have hre := congrArg Complex.re hsq
  have him := congrArg Complex.im hsq
  simp [pow_two] at hre him
  have hx : z.re = 0 := by
    have hm : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.1 hm with h | h
    · exact h
    · rw [h] at hre; nlinarith [sq_nonneg z.re]
  have key : starRingEnd ℂ z = -z := by apply Complex.ext <;> simp [hx]
  rw [hz] at key
  simpa using key

theorem unimodLattice_w0_add {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    H.w0 + H.bar H.w0 = 1 := by
  have h1 := H.two_weight_eq_one_add_root
  have h2 : 2 * H.bar H.w0 = 1 - H.rt := by
    have := congrArg H.bar h1
    rw [map_mul, map_add, map_one, unimodLattice_bar_rt, map_ofNat] at this
    rw [this]; ring
  have h3 : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by
    rw [mul_add, h1, h2]; ring
  exact mul_left_cancel₀ two_ne_zero h3

theorem unimodLattice :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), ∃ (r : ℕ) (W : Matrix (Fin r) (Fin r) ℤ) (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), 1 ≤ r ∧ ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef ∧ IsUnit (W + W.transpose).det ∧ (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) ∧ W = (W + W.transpose) * ρ H.w0 := by
  intro E _ _ _ H
  obtain ⟨m, B0, ρ0, hm, hsym, hpd, hadj⟩ := GlobalTheory.T.exists_cmField_traceForm_gram_matrix_posDef E H
  obtain ⟨r, b, ρ, hr, hbs, hbpd, hbu, hbadj⟩ :=
    GlobalTheory.T.exists_unimodular_posDef_form_adjoint_rep_of_posDef (𝓞 E) (H.bar : 𝓞 E →+* 𝓞 E) (unimodLattice_bar_bar H) m B0 ρ0 hm hsym hpd hadj
  have hW : b * ρ H.w0 + (b * ρ H.w0).transpose = b := by
    rw [Matrix.transpose_mul, hbs, hbadj, ← Matrix.mul_add, ← map_add]
    erw [unimodLattice_w0_add H]
    rw [map_one, Matrix.mul_one]
  refine ⟨r, b * ρ H.w0, ρ, hr, ?_, ?_, ?_, ?_⟩
  · rw [hW]; exact hbpd
  · rw [hW]; exact hbu
  · intro a; rw [hW]; exact hbadj a
  · rw [hW]

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentTriangularFactorUnique
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

set_option autoImplicit false

namespace GlobalTheory.FlagCell

theorem uniR_lowerTri {R : Type} [CommRing R] {m : ℕ} (n : Low m → R) :
    (uniR n).BlockTriangular OrderDual.toDual := by
  intro i j hij
  have hij' : i < j := hij
  simp only [uniR_apply]
  rw [dif_neg (not_lt.mpr hij'.le), if_neg (ne_of_lt hij')]

theorem uniR_diag {R : Type} [CommRing R] {m : ℕ} (n : Low m → R) (i : Fin m) :
    uniR n i i = 1 := by
  simp [uniR_apply]

theorem uniR_det {R : Type} [CommRing R] {m : ℕ} (n : Low m → R) : (uniR n).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (uniR_lowerTri n)]
  simp [uniR_diag]

theorem uniR_unique_of_mul_eq (R : Type) [CommRing R] (m : ℕ) (n n' : Low m → R)
    (M M' : Matrix (Fin m) (Fin m) R) (hM : M.BlockTriangular id) (hM' : M'.BlockTriangular id)
    (hdet : IsUnit M.det) (h : uniR n * M = uniR n' * M') : n = n' := by
  set L := uniR n
  set L' := uniR n'
  have hL' : IsUnit L'.det := by rw [uniR_det]; exact isUnit_one
  letI : Invertible M := Matrix.invertibleOfIsUnitDet M hdet
  letI : Invertible L' := Matrix.invertibleOfIsUnitDet L' hL'
  have hP : L'⁻¹ * L = M' * M⁻¹ := by
    calc L'⁻¹ * L = L'⁻¹ * (L * M) * M⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = L'⁻¹ * (L' * M') * M⁻¹ := by rw [h]
      _ = M' * M⁻¹ := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hL', Matrix.one_mul]
  have hlow : (L'⁻¹ * L).BlockTriangular OrderDual.toDual :=
    (Matrix.blockTriangular_inv_of_blockTriangular (uniR_lowerTri n')).mul (uniR_lowerTri n)
  have hup : (M' * M⁻¹).BlockTriangular id :=
    hM'.mul (Matrix.blockTriangular_inv_of_blockTriangular hM)
  set P := L'⁻¹ * L with hPdef
  have hdiag : P = Matrix.diagonal (fun j => P j j) := by
    ext i j
    rcases lt_trichotomy i j with hij | hij | hij
    · rw [Matrix.diagonal_apply_ne _ (ne_of_lt hij)]
      exact hlow hij
    · subst hij; simp
    · rw [Matrix.diagonal_apply_ne _ (ne_of_gt hij), hP]
      exact hup hij
  have hLP : L = L' * P := by
    rw [hPdef, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hL', Matrix.one_mul]
  have hP1 : ∀ j, P j j = 1 := by
    intro j
    have := congrFun (congrFun hLP j) j
    rw [hdiag, Matrix.mul_diagonal] at this
    simpa [L, L', uniR_diag] using this.symm
  have hLL : L = L' := by
    rw [hLP, hdiag]
    simp [hP1]
  funext s
  have := congrFun (congrFun hLL s.1.1) s.1.2
  simpa [L, L', uniR_apply, s.2] using this

end GlobalTheory.FlagCell
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryActionBaseChangeSubalgebraStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ZH GlobalTheory.UPoinc GlobalTheory.UCovSep
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAction_baseChange_subalgebra : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (R R' : Subalgebra o Ω) (h : R ≤ R') (P : PolAV (Sp R)) (P' : PolAV (Sp R')) (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A (spMap (Subalgebra.inclusion h).toRingHom) φ → LBIso P'.L (P.L.pull φ) → ∀ (act : 𝓞 E → (P.A ⟶ P.A)) (u : Sp (ratHull R) ⟶ Xo.XF c), (∀ a, IsMonHom (act a)) → GlobalTheory.UCovSep.UAct Xo c P act (toRat R) u → ∃ act' : 𝓞 E → (P'.A ⟶ P'.A), (∀ a, IsMonHom (act' a)) ∧ (∀ a, (act' a).left ≫ φ = φ ≫ (act a).left) ∧ GlobalTheory.UCovSep.UAct Xo c P' act' (toRat R') (spMap (Subalgebra.inclusion (ratHull_mono h)).toRingHom ≫ u) := by
  first | exact @GlobalTheory.UCovSep.uAct_baseChange | exact GlobalTheory.UCovSep.uAct_baseChange | (intros; apply GlobalTheory.UCovSep.uAct_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTraitLabelsSurjectiveKernelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryTraitLabels_surjective_kernel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X : USetup C) (p : ℕ) [Fact p.Prime] (z : X.M.Z) (ct : UCTrait X p z) (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X), UIsLab X ct yy → Function.Surjective yy ∧ yy.ker = X.S.HH X.M z := by
  first | exact @GlobalTheory.UPoinc.uIsLab_onto_and_ker | exact GlobalTheory.UPoinc.uIsLab_onto_and_ker | (intros; apply GlobalTheory.UPoinc.uIsLab_onto_and_ker <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalTripleFibrePrincipallyPolarisedDimensio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem polFib_univ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] (x : Sp R ⟶ Xo.X), PolFib Xo.univ.t.G Xo.univ.t.PP.L (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) x := by
  intro E _ _ _ H Dw l Xo c R _ x
  obtain ⟨P', φ, hg, hc, hL⟩ :=
    GlobalTheory.PureType.exists_baseChange GlobalTheory.abelianSchemeLaws_all.1.polBaseChange x (GlobalTheory.objPolAV Xo.univ)
  exact ⟨P', φ, hg, hc, hL⟩

end GlobalTheory.UMin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumUnramifiedAlmostAllStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_place_ring_over_prime : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (k : IntermediateField ℚ ℂ), FiniteDimensional ℚ k →
    ∃ R : Subring ℂ, IsPlaceOver l lam k R := by
  first | exact @GlobalTheory.PlaceRingExists.exists_isPlaceOver | exact GlobalTheory.PlaceRingExists.exists_isPlaceOver | (intros; apply GlobalTheory.PlaceRingExists.exists_isPlaceOver <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValGPtOfStalk
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.Poinc.TestAtPt

theorem val_gPt_of_stalk : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (x : M.Z) (R : Type) [CommRing R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), IsLocalHom j → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ c : M.O x, ((ev (j ((M.stalkEquiv x).symm c)) : OO p) : PadicAlgCl p) = M.val (gPt p ≫ y) (c : Ω) := by
  intro o Ω _ _ _ M x R _ _ j _ p _ y ev hy c
  have hsp : ∀ w, (spMap j ≫ M.Z.fromSpecStalk x) w ⤳ x := fun w => by
    have : M.Z.fromSpecStalk x (spMap j w) ∈ Set.range (M.Z.fromSpecStalk x) := ⟨_, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this
  obtain ⟨U, hx, f, hf⟩ := M.Z.presheaf.germ_exist ((M.stalkEquiv x).symm c)
  have hc : c = ⟨valF M.pt U f, RatModel.valF_mem_O hx f⟩ := by
    rw [← RatModel.stalkEquiv_germ hx, hf, RingEquiv.apply_symm_apply]
  have hU : ⊤ ≤ (spMap j ≫ M.Z.fromSpecStalk x) ⁻¹ᵁ U := fun w _ => (hsp w).mem_open U.isOpen hx
  have hU0 : ⊤ ≤ M.Z.fromSpecStalk x ⁻¹ᵁ U := fun w _ => by
    have : M.Z.fromSpecStalk x w ∈ Set.range (M.Z.fromSpecStalk x) := ⟨_, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this.mem_open U.isOpen hx
  have hg : gPt p ≫ y = spMap ((OO p).subtype.comp ev) ≫ (spMap j ≫ M.Z.fromSpecStalk x) := by
    rw [← hy, ← Category.assoc]
    congr 1
    rw [gPt, spMap, spMap, spMap, ← Spec.map_comp]
    rfl
  have hU' : ⊤ ≤ (gPt p ≫ y) ⁻¹ᵁ U := by
    rw [hg]; exact fun w _ => hU (x := spMap ((OO p).subtype.comp ev) w) trivial
  rw [RatModel.val_eq ((top_le_preimage_iff _ _).1 hU') (f := f) (hc ▸ rfl), GlobalTheory.Points.valF_eq_valR, hg,
    GlobalTheory.Points.valR_spMap_comp _ _ U hU]
  have e1 : valR (spMap j ≫ M.Z.fromSpecStalk x) U f = j (valR (A := M.Z.presheaf.stalk x) (M.Z.fromSpecStalk x) U f) :=
    GlobalTheory.Points.valR_spMap_comp (C := M.Z.presheaf.stalk x) j (M.Z.fromSpecStalk x) U hU0 f
  have e2 : valR (A := M.Z.presheaf.stalk x) (M.Z.fromSpecStalk x) U f = M.Z.presheaf.germ U x hx f := by
    have eA : (M.Z.fromSpecStalk x).appLE U ⊤ hU0 =
        M.Z.presheaf.germ U x hx ≫ (Scheme.ΓSpecIso (M.Z.presheaf.stalk x)).inv := by
      rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
      simp only [Category.assoc, ← Functor.map_comp]
      have e : ((homOfLE le_top).op ≫ (homOfLE hU0).op :
          Opposite.op (⊤ : (Spec (M.Z.presheaf.stalk x)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := rfl
      rw [e, CategoryTheory.Functor.map_id, Category.comp_id]
    unfold valR
    erw [dif_pos hU0, eA]
    simp only [CommRingCat.comp_apply]
    erw [Iso.inv_hom_id_apply]
    rfl
  rw [e1]
  exact (congrArg (fun t => ((OO p).subtype.comp ev) (j t)) (e2.trans hf)).symm

end GlobalTheory.Poinc.TestAtPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValPsiZeroMulRigK
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

noncomputable section

namespace GlobalTheory.MumFam

theorem val_psi_zero_mul_rigK : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult →
    ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
      val (D.psi 0) (𝟙 _) z J * val D.rigK (𝟙 _) z J = 1 := by
  intro R _ _ D hB z J hJ
  have h1 := GlobalTheory.PolDeg.Data.val_tau_zero (GlobalTheory.PolDeg.Wit.ofDeg D hB) 0 z J hJ
  have h2 : val ((GlobalTheory.PolDeg.Wit.ofDeg D hB).tau 0 0) (𝟙 _) z J = val (D.tau 0 0) (𝟙 _) z J :=
    (GlobalTheory.PolDeg.Wit.exists_tau D 0 0).choose_spec.2 _ _ z J hJ
  rw [h2] at h1
  unfold DegPre.tau at h1
  rw [val_mul hJ, val_mul hJ, val_mul hJ] at h1
  simp only [val_inv] at h1
  rw [congrArg (fun w => val (D.psi w) (𝟙 _) z J) (add_zero (0 : D.X)), mul_inv_cancel, _root_.one_mul,
    ← mul_inv_rev, inv_eq_one] at h1
  rw [mul_comm]
  exact h1

end GlobalTheory.MumFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValRImageModelSectionSemilinear
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.ImageModel

theorem valR_algX_cxPts {k : Type} [CommRing k] {Y : Scheme.{0}} (p : Y ⟶ Sp k) (τ : k →+* ℂ)
    (U : Y.Opens) (y : GlobalTheory.CxPts p τ) (h : ⊤ ≤ y.1 ⁻¹ᵁ U) (a : k) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR y.1 U (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U a) = τ a := by
  have h1 := GlobalTheory.Points.valR_appLE y.1 p (U := ⊤) (V := U) (by simp) h
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a)
  have h2 : y.1 ≫ p = Spec.map (CommRingCat.ofHom τ) := y.2
  rw [h2] at h1
  exact h1.trans (GlobalTheory.Points.valR_specMap (CommRingCat.ofHom τ) a)

theorem valR_section_sum : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → ∀ (τ : 𝓞 K →+* ℂ) (i : L.B.ι) (y : GlobalTheory.CxPts p τ), y ∈ GlobalTheory.CxPts.ptsIn p τ (L.B.U i) → ∀ (m : ℕ) (β : Fin m → 𝓞 K) (u : Fin m → W) (x : W), (x : V) = ∑ k, β k • (u k : V) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR y.1 (L.B.U i) ((s x).f i) = ∑ k, τ (β k) * ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR y.1 (L.B.U i) ((s (u k)).f i) := by
  intro K V Ω _ _ _ _ _ _ _ _ Nm W ev D X _ p L ψ s hM hev τ i y hy m β u x hx
  have h : ⊤ ≤ y.1 ⁻¹ᵁ L.B.U i := hy
  rw [GlobalTheory.T.imageModel_sections_linear_ringOfIntegers K V Ω Nm W ev D X p L ψ s hM hev m β u x hx i, GlobalTheory.Points.valR_eq _ _ h, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← GlobalTheory.Points.valR_eq _ _ h, GlobalTheory.Points.valR_mul _ _ h, valR_algX_cxPts p τ _ y h]

end GlobalTheory.ImageModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationSqrtNegPrime
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem val_vp_sqrt_neg_prime : ∀ (E : Type) [Field E] (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R],
    (l : R) ∈ IsLocalRing.maximalIdeal R → (∀ p : ℕ, p.Prime → p ≠ l → IsUnit (p : R)) →
    ∀ (d : ℕ), d.Prime → ∀ (δ : E), δ ^ 2 = -(d : E) → ∀ σ : E →+* FractionRing R,
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (σ δ) = (((if l = d then 1 / 2 else 0 : ℚ)) : WithTop ℚ) := by
  intro E _ l _ R _ _ _ _ hl hu d hd δ hδ σ
  have hK : ∀ n : ℕ, n ≠ 0 → (n : FractionRing R) ≠ 0 := fun n hn => by
    rw [← map_natCast (algebraMap R (FractionRing R))]
    exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 (Nat.cast_ne_zero.2 hn)
  have hsq : (σ δ) ^ 2 = -(d : FractionRing R) := by rw [← map_pow, hδ, map_neg, map_natCast]
  have hx : σ δ ≠ 0 := by
    intro h
    rw [h, zero_pow two_ne_zero, eq_comm, neg_eq_zero] at hsq
    exact hK d hd.ne_zero hsq
  have h2 : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R (d : FractionRing R) = 2 * GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R (σ δ) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw
    rw [show (d : FractionRing R) = -((σ δ) ^ 2) by rw [hsq, neg_neg], Valuation.map_neg, map_pow, WithZero.log_pow]
    simp only [nsmul_eq_mul]
    push_cast
    ring
  by_cases hld : l = d
  · subst hld
    have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
    have h1 : (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R) (l : FractionRing R) < 1 := by
      rw [← map_natCast (algebraMap R (FractionRing R)), IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
      exact hl
    have h2' : (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R) (l : FractionRing R) ≠ 0 := by
      simpa using hK l hl0
    have h3 : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R (l : FractionRing R) ≠ 0 := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw
      intro h4
      have := WithZero.exp_log h2'
      rw [neg_eq_zero.1 h4, WithZero.exp_zero] at this
      exact h1.ne this.symm
    have h5 : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R (σ δ) ≠ 0 := by
      intro h6; rw [h2, h6, mul_zero] at h3; exact h3 rfl
    rw [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp, if_neg hx, if_pos rfl, h2]
    congr 1
    push_cast
    field_simp
  · have hunit : IsUnit (d : R) := hu d hd (Ne.symm hld)
    have hv : (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R) (d : FractionRing R) = 1 := by
      rw [← map_natCast (algebraMap R (FractionRing R)), IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
      exact fun hm => (IsLocalRing.maximalIdeal.isMaximal R).ne_top (Ideal.eq_top_of_isUnit_mem _ hm hunit)
    have h0 : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R (d : FractionRing R) = 0 := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw; rw [hv]; simp
    have h5 : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R (σ δ) = 0 := by omega
    rw [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp, if_neg hx, if_neg hld, h5]
    simp

end GlobalTheory
end
end

