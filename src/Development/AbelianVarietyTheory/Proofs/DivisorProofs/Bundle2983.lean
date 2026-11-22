import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2887
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2446
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2892
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2871
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2518
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2584
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0012
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2888
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2512
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2873
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0182
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0786
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2578
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2616
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2624
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2847
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0090
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2889
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantGeneratorLocallyExistsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_generator_locally_exists : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (M : Scheme.{0}) (U : Obj F 𝔠 M)
    (R₀ : Type) [CommRing R₀] (m : M), ∃ (W : M.Opens) (hW : IsAffineOpen W), m ∈ W ∧
      ∀ (X : Obj F 𝔠 (Sp (R₀ ⊗[ℤ] Γ(M, W)))) (φ : X.A.left ⟶ U.A.left),
        X.IsPullBy U (coefSpecMap hW R₀) φ → Nonempty X.DetGen := by
  first | exact @GlobalTheory.RealMult.LocalGen.exists_affine_detGen | exact GlobalTheory.RealMult.LocalGen.exists_affine_detGen | (intros; apply GlobalTheory.RealMult.LocalGen.exists_affine_detGen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantGeneratorRuleBaseChangeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_generator_rule_base_change : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (R₀ : Type) [CommRing R₀] (k : ℕ)
    (s t : Rule (unitObj 𝔠 6) R₀ k) (A : Type) [CommRing A] (Y : Obj F 𝔠 (Sp A)), Nonempty Y.DetGen →
    (∀ (YC : Obj F 𝔠 (Sp (R₀ ⊗[ℤ] A))) (ψ : YC.A.left ⟶ Y.A.left),
      YC.IsPullBy Y (spMap (Algebra.TensorProduct.includeRight : A →ₐ[ℤ] R₀ ⊗[ℤ] A).toRingHom) ψ →
      ∀ (h : IsUnit ((6 : ℕ) : R₀ ⊗[ℤ] A)) (δ : YC.DetGen), s.val _ YC h δ = t.val _ YC h δ) →
    IsUnit ((6 : ℕ) : A) → (∀ (B : Type) [CommRing B] [Algebra R₀ B] (σ : A →+* B) (Y' : Obj F 𝔠 (Sp B)) (φ : Y'.A.left ⟶ Y.A.left),
    Y'.IsPullBy Y (spMap σ) φ → ∀ (h : IsUnit ((6 : ℕ) : B)) (δ : Y'.DetGen), s.val B Y' h δ = t.val B Y' h δ) := by
  first | exact @GlobalTheory.RealMult.Rule.eq_of_eq_extScalars | exact GlobalTheory.RealMult.Rule.eq_of_eq_extScalars | (intros; apply GlobalTheory.RealMult.Rule.eq_of_eq_extScalars <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalFrameStatement
section
open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DiagAH

theorem conj_eq_of_totallyReal {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (φ : F →+* ℂ) (x : F) :
    starRingEnd ℂ (φ x) = φ x := by
  have h : ComplexEmbedding.IsReal φ :=
    (NumberField.InfinitePlace.isReal_mk_iff).1 (IsTotallyReal.isReal _)
  rw [← ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.isReal_iff.1 h]

theorem exists_int_ne {F : Type} [Field F] [NumberField F] {φ ψ : F →+* ℂ} (h : φ ≠ ψ) :
    ∃ a : 𝓞 F, φ (a : F) ≠ ψ (a : F) := by
  by_contra hall
  push_neg at hall
  exact h (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) (RingHom.ext fun a ↦ hall a))

theorem eq_diagonal_of_comm {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) ℂ) (hH : Hm.IsHermitian) (e : Fin n → (F →+* ℂ)) (he : Function.Injective e)
    (h : ∀ (a : 𝓞 F) i j, e i (a : F) * Hm i j = Hm i j * starRingEnd ℂ (e j (a : F))) :
    Hm = Matrix.diagonal fun j ↦ ((Hm j j).re : ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq]
    have := congrFun (congrFun hH i) i
    simp only [Matrix.conjTranspose_apply] at this
    exact (Complex.conj_eq_iff_re.1 this).symm
  · rw [Matrix.diagonal_apply_ne _ hij]
    obtain ⟨a, ha⟩ := exists_int_ne (he.ne hij)
    have h1 := h a i j
    rw [conj_eq_of_totallyReal] at h1
    have h2 : (e i (a : F) - e j (a : F)) * Hm i j = 0 := by linear_combination h1
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 ha)

theorem diagFrame : DiagFrame := by
  intro F _ _ _ 𝔠 X c hc u e he hact
  obtain ⟨u', Hm, χ, hex, hAH⟩ := GlobalTheory.T.exists_appell_humbert_uniformization F 𝔠 X c hc u
  have hact' : ∀ (a : 𝓞 F) w, u'.ex (fun j ↦ e j (a : F) * w j) = u'.ex w ≫ X.rm.act a := by
    rw [hex]; exact hact
  have hsym := GlobalTheory.T.appell_humbert_real_multiplication F 𝔠 X c hc u' e hact' Hm χ hAH
  have hdiag := eq_diagonal_of_comm Hm hAH.1 e he hsym
  refine ⟨u', fun j ↦ (Hm j j).re, hex, χ, ?_⟩
  rw [← hdiag]
  exact hAH

end GlobalTheory.DiagAH
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentialZeroOfNotTangentStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differential_zero_of_not_tangent : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (L : LB X.A.left) (n : ℕ)
    (u : HolUnif X.A L n) (w : Fin n → ℂ) (v : epsR ℂ ⟶ X.A), u.IsDiff w v → ¬ IsTangent v → w = 0 := by
  first | exact @GlobalTheory.UnifOffOrigin.eq_zero_of_isDiff_of_not_isTangent | exact GlobalTheory.UnifOffOrigin.eq_zero_of_isDiff_of_not_isTangent | (intros; apply GlobalTheory.UnifOffOrigin.eq_zero_of_isDiff_of_not_isTangent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerPolyAlgebraHomotopyIdentityStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dividedPowerPolyAlgebra_homotopy_identity : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B) [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J)) (v : Derivation R Q.P Q.P) (h : SemiHom (RingHom.id R) (algebraMap B Q.P)), Q.IsStd δ η → (∀ b, v (algebraMap B Q.P b) = 0) → (∀ n, v (Q.e (n + 1)) = Q.e n) → (∀ n, ∀ a ∈ Q.ext J, v (η.dpow (n + 1) a) = η.dpow n a * v a) → ∀ (ε : Q.P →+* B) (hε : SemiHom (RingHom.id R) ε), IsDPMorphism η δ ε → (∀ b, ε (algebraMap B Q.P b) = b) → (∀ n, ε (Q.e (n + 1)) = 0) → ∀ (N : ℕ) (x : DR R Q.P), x - h.mDR (hε.mDR x) - dDR R Q.P (hot v Q.e N x) - hot v Q.e N (dDR R Q.P x) ∈ filDR R η N := by
  first | exact @GlobalTheory.PDForm.homotopy_identity | exact GlobalTheory.PDForm.homotopy_identity | (intros; apply GlobalTheory.PDForm.homotopy_identity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorOfTensorSectionAdd
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

namespace GlobalTheory.LatChain.CanTens

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k}

theorem presents_dual {D : CartierDiv X} {L : LB X} {r : L.ι → X.functionFieldˣ} (h : Presents D L r) :
    Presents (-D) (CechPic.dual L) fun i => (r i)⁻¹ := by
  refine ⟨isLB_dual h.isLB, fun i j hij => ?_, fun i x hx => (h.isEqn i x hx).neg⟩
  change (((r i)⁻¹ : X.functionFieldˣ) : X.functionField) =
    fnOf (L.U i ⊓ L.U j) hij ((L.g i j)⁻¹ : Γ(X, L.U i ⊓ L.U j)ˣ) * ((r j)⁻¹ : X.functionFieldˣ)
  rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_units_inv, h.isRatSec i j hij, mul_inv]

theorem ratVal_inv {σ : k →+* ℂ} {y : CxPts q σ} {f : X.functionField} (hf : UnitAt (under y) f) :
    ratVal f⁻¹ y = (ratVal f y)⁻¹ := by
  have h1 : UnitAt (under y) (1 : X.functionField) := unitAt_one _
  have e1 : ratVal (1 : X.functionField) y = 1 := by
    have e := ratVal_mul h1.regAt h1.regAt
    rw [mul_one] at e
    exact (mul_eq_left₀ (ratVal_ne_zero h1)).1 e.symm
  have e := ratVal_mul hf.regAt hf.inv.regAt
  rw [mul_inv_cancel₀ hf.ne_zero, e1] at e
  exact eq_inv_of_mul_eq_one_right e.symm

theorem can_tens {M M' : HermLB q} {E E' : CartierDiv X} (h : Can M E) (h' : Can M' E') :
    Can (M.tens M') (E + E') := by
  obtain ⟨r, hr, rfl, H⟩ := h
  obtain ⟨r', hr', rfl, H'⟩ := h'
  have P := (presents_divOfRatSec M.isLB hr).tens (presents_divOfRatSec M'.isLB hr')
  refine ⟨fun c => r c.1 * r' c.2, P.isRatSec, (presents_divOfRatSec _ P.isRatSec).unique P, fun σ y => ?_⟩
  obtain ⟨a, b⟩ := H σ y
  obtain ⟨a', b'⟩ := H' σ y
  refine ⟨mem_offSupp.2 fun hy => ?_, ?_⟩
  · rcases CartierDiv.supp_add_le _ _ hy with hy | hy
    · exact mem_offSupp.1 a hy
    · exact mem_offSupp.1 a' hy
  · have hc := CxPts.mem_ptsIn_inf.1 (CxPts.mem_pick ((M.tens M').φ σ).isLB y)
    rw [logNorm_eq _ hr a hc.1] at b
    rw [logNorm_eq _ hr' a' hc.2] at b'
    have u := hr.unitAt M.isLB a hc.1
    have u' := hr'.unitAt M'.isLB a' hc.2
    have e := Real.log_mul (norm_ne_zero_iff.2 (ratVal_ne_zero u)) (norm_ne_zero_iff.2 (ratVal_ne_zero u'))
    rw [← norm_mul, ← ratVal_mul u.regAt u'.regAt] at e
    refine (congrArg₂ (· - ·) e (add_div _ _ _)).trans ?_
    linarith

theorem can_dual {M : HermLB q} {E : CartierDiv X} (h : Can M E) : Can M.dual (-E) := by
  obtain ⟨r, hr, rfl, H⟩ := h
  have P := presents_dual (presents_divOfRatSec M.isLB hr)
  refine ⟨fun i => (r i)⁻¹, P.isRatSec, (presents_divOfRatSec _ P.isRatSec).unique P, fun σ y => ?_⟩
  obtain ⟨a, b⟩ := H σ y
  refine ⟨mem_offSupp.2 fun hy => hy ?_, ?_⟩
  · have := CartierDiv.IsEqn.neg (not_not.1 (mem_offSupp.1 a))
    rwa [inv_one] at this
  · have hc := CxPts.mem_pick (M.dual.φ σ).isLB y
    rw [logNorm_eq _ hr a hc] at b
    have u := hr.unitAt M.isLB a hc
    have e := congrArg (fun z : ℂ => Real.log ‖z‖) (ratVal_inv u)
    simp only [norm_inv, Real.log_inv] at e
    rw [← Units.val_inv_eq_inv_val] at e
    refine (congrArg₂ (· - ·) e (neg_div _ _)).trans ?_
    linarith

theorem can_tens_dual : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k) (M M' : HermLB q), (∀ E E' : CartierDiv X, Can M E → Can M' E' → Can (M.tens M') (E + E') ∧ Can M.dual (-E)) ∧ ∀ (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r) (r' : M'.B.ι → X.functionFieldˣ) (hr' : IsRatSec M'.B r'), ∃ (s : (M.tens M').B.ι → X.functionFieldˣ) (hs : IsRatSec (M.tens M').B s), (M.tens M').div hs = M.div hr + M'.div hr' := by
  intro k _ X _ q M M'
  refine ⟨fun E E' h h' => ⟨can_tens h h', can_dual h⟩, fun r hr r' hr' => ?_⟩
  have P := (presents_divOfRatSec M.isLB hr).tens (presents_divOfRatSec M'.isLB hr')
  exact ⟨fun c => r c.1 * r' c.2, P.isRatSec, (presents_divOfRatSec _ P.isRatSec).unique P⟩

end GlobalTheory.LatChain.CanTens

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfDvdInCompleteDVRsFiniteResidueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvd_of_dvd_in_completeDVRs_finite_residue : ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CharZero A] [Algebra.FiniteType ℤ A] (a f : A), f ≠ 0 → (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) → ∀ t : A →+* V, t f ≠ 0 → t f ∣ t a) → f ∣ a := by
  first | exact @GlobalTheory.KeyEven.dvd_of_forall_fintrait | exact GlobalTheory.KeyEven.dvd_of_forall_fintrait | (intros; apply GlobalTheory.KeyEven.dvd_of_forall_fintrait <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8FibrationAlgebraicallyClosedFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.e8_fibration_algebraically_closed_field : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ),
  ∃ Mat : Fin 2 → Matrix (Fin (2 * (8 * gQ))) (Fin (2 * (8 * gQ))) ℤ,
  ∀ (l : ℕ), l.Prime → Odd l → ∀ j : ℕ, 1 ≤ j →
  ∀ (K : Type) [Field K] [IsAlgClosed K] (k₀ : Subfield K), IsAlgClosed k₀ → (l : K) ≠ 0 →
  ∀ (P' : PolAV (Sp K)), P'.g = 8 * gQ →
  ∀ (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (M : RigLB B) (pr : Fin 8 → (P'.A ⟶ B)),
  E8Fibration.IsPPFib B gQ M → E8Fibration.IsProd pr → E8Fibration.IsE8WeightedBundle W pr P'.L M.L →
  ∀ act : Fin 2 → (P'.A ⟶ P'.A), (∀ i, IsMonHom (act i)) → (∀ i, E8Fibration.ActsBy pr (act i) (E8Fibration.actMat W i)) →
  ∃ (bT : TBase k₀ ((l ^ j) ^ 2)) (pt : Fin (2 * (8 * gQ)) → (Out.baseOver (Sp K) ⟶ P'.A)),
    (∀ i, pt i ^ ((l ^ j) ^ 2) = 1) ∧
    (∀ (K' : Type) [Field K'] [IsAlgClosed K'] (x : Sp K' ⟶ Sp K) (y : Over.mk x ⟶ P'.A), y ^ ((l ^ j) ^ 2) = 1 →
      ∃! c : Ix (8 * gQ) ((l ^ j) ^ 2), Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp K)) ≫ pt i)
        (fun i => (c i).val) = y) ∧
    (∀ i i', Out.WeilIs P'.A P'.L (((l ^ j) ^ 2 : ℕ) : ℤ) (pt i) (pt i')
      (unitS (spMap k₀.subtype) bT.ζ ^ Out.stdSymp (8 * gQ) i i')) ∧
    ∀ (a : Fin 2) i, pt i ≫ act a = Out.linComb pt (fun i' => ((Mat a i' i : ZMod ((l ^ j) ^ 2))).val) := by
  first | exact @GlobalTheory.Poinc.Sep.E8Fibration.Lab.exists_symplectic_labels | exact GlobalTheory.Poinc.Sep.E8Fibration.Lab.exists_symplectic_labels | (intros; apply GlobalTheory.Poinc.Sep.E8Fibration.Lab.exists_symplectic_labels <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerFibreIsoEqCoordinatewisePower
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PoincDiag

@[reassoc]
theorem mapFst {S S' : Scheme.{0}} (t : S' ⟶ S) {X Y : Over S} (φ : X ⟶ Y) :
    ((Over.pullback t).map φ).left ≫ pullback.fst Y.hom t = pullback.fst X.hom t ≫ φ.left := by
  simp only [Over.pullback_map_left]; exact pullback.lift_fst _ _ _

@[reassoc]
theorem mapSnd {S S' : Scheme.{0}} (t : S' ⟶ S) {X Y : Over S} (φ : X ⟶ Y) :
    ((Over.pullback t).map φ).left ≫ pullback.snd Y.hom t = pullback.snd X.hom t := by
  simp only [Over.pullback_map_left]; exact pullback.lift_snd _ _ _

theorem abBC : ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (B : Over (Sp R)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → IsAbelianScheme ((Over.pullback (spMap f)).obj B) ∧ SmoothOfRelativeDimension g ((Over.pullback (spMap f)).obj B).hom := by
  intro R R' _ _ f B _ g hB hd
  exact GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback f B _ _ g
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback B (spMap f)) hB hd

theorem torsPull : ∀ (S S' : Scheme.{0}) (t : S' ⟶ S) (X : Over S) [GrpObj X] (z : 𝟙_ (Over S') ⟶ (Over.pullback t).obj X) (y : Over.mk t ⟶ X) (n : ℕ), y.left = z.left ≫ pullback.fst X.hom t → z ^ n = 1 → y ^ n = 1 := by
  intro S S' t X _ z y n hy hz
  have hgp := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback X t
  let k : Over.mk ((𝟙_ (Over S')).hom ≫ t) ⟶ Over.mk t := Over.homMk (𝟙 _) (by simp)
  have hw : ((1 : 𝟙_ (Over S') ⟶ (Over.pullback t).obj X).left ≫ pullback.fst X.hom t) ≫ X.hom = (Over.mk t).hom := by
    have e := Over.w (1 : 𝟙_ (Over S') ⟶ (Over.pullback t).obj X)
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    simp only [Over.pullback_obj_hom] at e
    rw [e]
    simp
  let u : Over.mk t ⟶ X := Over.homMk ((1 : 𝟙_ (Over S') ⟶ (Over.pullback t).obj X).left ≫ pullback.fst X.hom t) hw
  have hu : u = 1 := by
    have h := hgp.2 (𝟙_ (Over S')) 1 1 (k ≫ u) (k ≫ u) (by simp [k, u]) (by simp [k, u])
    rw [← MonObj.comp_mul, _root_.mul_one] at h
    have e : u * u = u := Over.OverMorphism.ext (by simpa [k, u] using h)
    exact mul_eq_left.1 e
  have hp : ∀ m : ℕ, (y ^ m).left = (z ^ m).left ≫ pullback.fst X.hom t := by
    intro m
    induction m with
    | zero =>
      simp only [pow_zero]
      rw [← hu]
      rfl
    | succ m ih =>
      have h := hgp.2 (𝟙_ (Over S')) (z ^ m) z (k ≫ y ^ m) (k ≫ y) (by simp [k, ih]) (by simp [k, hy])
      rw [← MonObj.comp_mul, ← pow_succ, ← pow_succ] at h
      simpa [k] using h
  apply Over.OverMorphism.ext
  rw [hp n, hz, ← hu]
  rfl

theorem fibreIso_eq_pow : ∀ (l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∀ j, 1 ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsUnit (l : V₁) → ∀ (Q : Data V) (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁), ∀ (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)) (w : LB.Iso D.P.L (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4) (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2)))), (∀ a, IsMonHom (pr a)) → (∀ (T : Over (Sp V₁)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap ρ)).obj Q.B)), ∃! x : T ⟶ D.P.A, ∀ a, x ≫ pr a = y a) → w.IsGen → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (σ : K ≃+* K), ∀ (f : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A).left), IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A) (𝟙 _) f → LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (D.P.L.pull (f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)))) → (∀ (y : Over.mk (spMap ev) ⟶ D.P.A), (∃ k : ℕ, y ^ (l ^ k) = 1) → ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left, q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ y.left) → ∃ f₁ : ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B).left, IsGrpPullback ((Over.pullback (spMap (ev.comp ρ))).obj Q.B) ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B) (𝟙 _) f₁ ∧ ∀ (a : Fin 8) (T : Scheme.{0}) (x : T ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left) (y : T ⟶ ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left), y ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) = x ≫ pullback.fst D.P.A.hom (spMap ev) ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) → y ≫ pullback.snd Q.B.hom (spMap (ev.comp ρ)) = x ≫ pullback.snd D.P.A.hom (spMap ev) → x ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) = y ≫ f₁ ≫ pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ))) := by
  intro l hl hodd W hW j hj V V₁ _ _ _ _ _ hlu Q ρ hρ D pr w hpr huniv hw K _ _ ev σ f hf hL htor
  haveI := D.P.isAb.comm
  have hfw : f ≫ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A).hom = ((Over.pullback (spMap ev)).obj D.P.A).hom := by
    simpa using hf.1.w
  let F : (Over.pullback (spMap ev)).obj D.P.A ⟶ (Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A := Over.homMk f hfw
  haveI : IsIso f := hf.1.isIso_fst_of_isIso
  haveI hFi : IsIso F := by
    have : IsIso ((Over.forget _).map F) := by change IsIso f; infer_instance
    exact isIso_of_reflects_iso F (Over.forget _)
  haveI hFm : IsMonHom F := GlobalTheory.AmpleRigid.isMonHom_of_mul_comp F
    (fun T x y => GlobalTheory.AmpleRigid.mul_comp_of_grpPullback_id F hf x y)
  obtain ⟨hm₀, hu₀⟩ := GlobalTheory.T.isMonHom_pullback_pr_and_unique_lift_fin_eight _ _ (spMap ev) D.P.A _ pr hpr huniv
  obtain ⟨hm₁, hu₁⟩ := GlobalTheory.T.isMonHom_pullback_pr_and_unique_lift_fin_eight _ _ (spMap (σ.toRingHom.comp ev)) D.P.A _ pr hpr huniv
  have hBab := abBC V V₁ ρ Q.B Q.g Q.isAb Q.smoothDim
  have hB₀ := (abBC V₁ K ev _ Q.g hBab.1 hBab.2).1
  have hB₁ := (abBC V₁ K (σ.toRingHom.comp ev) _ Q.g hBab.1 hBab.2).1
  have hlK : (l : K) ≠ 0 := by
    have := hlu.map ev
    rw [map_natCast] at this
    exact this.ne_zero

  have key : ∀ (z : 𝟙_ (Over (Sp K)) ⟶ (Over.pullback (spMap ev)).obj D.P.A), (∃ k : ℕ, z ^ (l ^ k) = 1) → ∀ a,
      (z ≫ F ≫ (Over.pullback (spMap (σ.toRingHom.comp ev))).map (pr a)).left ≫
          pullback.fst ((Over.pullback (spMap ρ)).obj Q.B).hom (spMap (σ.toRingHom.comp ev)) =
        spMap σ.toRingHom ≫ (z ≫ (Over.pullback (spMap ev)).map (pr a)).left ≫
          pullback.fst ((Over.pullback (spMap ρ)).obj Q.B).hom (spMap ev) := by
    rintro z ⟨k, hk⟩ a
    have hzw : z.left ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ := by simpa using Over.w z
    have hyw : (z.left ≫ pullback.fst D.P.A.hom (spMap ev)) ≫ D.P.A.hom = (Over.mk (spMap ev)).hom := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hzw, Category.id_comp]; rfl
    let y : Over.mk (spMap ev) ⟶ D.P.A := Over.homMk (z.left ≫ pullback.fst D.P.A.hom (spMap ev)) hyw
    have hy : y ^ (l ^ k) = 1 := torsPull _ _ (spMap ev) D.P.A z y (l ^ k) rfl hk
    have h := htor y ⟨k, hy⟩ z.left rfl hzw
    simp only [Over.comp_left, Category.assoc]
    rw [mapFst, mapFst]
    change z.left ≫ f ≫ _ = _
    rw [reassoc_of% h]
    rfl
  have htors : ∀ (z z' : 𝟙_ (Over (Sp K)) ⟶ (Over.pullback (spMap ev)).obj D.P.A), (∃ k : ℕ, z ^ (l ^ k) = 1) →
      (∃ k : ℕ, z' ^ (l ^ k) = 1) → ∀ a a', z ≫ (Over.pullback (spMap ev)).map (pr a) = z' ≫ (Over.pullback (spMap ev)).map (pr a') →
      z ≫ F ≫ (Over.pullback (spMap (σ.toRingHom.comp ev))).map (pr a) = z' ≫ F ≫ (Over.pullback (spMap (σ.toRingHom.comp ev))).map (pr a') := by
    intro z z' hz hz' a a' he
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [key z hz a, key z' hz' a', he]
    · exact (Over.w (z ≫ F ≫ (Over.pullback (spMap (σ.toRingHom.comp ev))).map (pr a))).trans
        (Over.w (z' ≫ F ≫ (Over.pullback (spMap (σ.toRingHom.comp ev))).map (pr a'))).symm
  obtain ⟨f₁', hm, hiso, hco⟩ := GlobalTheory.T.eighthPower_iso_diagonal_of_lPower_torsion_action K _ _ _ _ (GlobalTheory.isSemiAbelian_of_isAbelianScheme _ hB₀)
    (GlobalTheory.isSemiAbelian_of_isAbelianScheme _ hB₁) l hl hlK _ _ hm₀ hm₁ hu₀ hu₁ F hFm hFi htors
  obtain ⟨f₁, hf₁, hcoord⟩ := GlobalTheory.T.fibre_iso_grpPullback_identity_transport V V₁ K Q.B ρ ev σ f₁' hm hiso
  refine ⟨f₁, hf₁, fun a T x y h1 h2 => ?_⟩
  have hc : f ≫ ((Over.pullback (spMap (σ.toRingHom.comp ev))).map (pr a)).left =
      ((Over.pullback (spMap ev)).map (pr a)).left ≫ f₁'.left := congrArg (·.left) (hco a)
  have := hcoord T (x ≫ ((Over.pullback (spMap ev)).map (pr a)).left) y
    (by rw [h1, Category.assoc, mapFst_assoc]) (by rw [h2, Category.assoc, mapSnd])
  rw [← this, Category.assoc, ← reassoc_of% hc, mapFst_assoc]

end GlobalTheory.PoincDiag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerOfMatrixUnitsIdempotentSplitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighthPower_of_matrixUnits_idempotent_split : ∀ {S : Scheme.{0}} (G H : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj H] (E : Fin 8 → Fin 8 → (G ⟶ G)) (hE : ∀ a b, IsMonHom (E a b)) (hrel : ∀ a b c d, E a b ≫ E c d = if b = c then E a d else 1) (hsum : ∏ a, E a a = 𝟙 G) (i : H ⟶ G) (r : G ⟶ H) (hi : IsMonHom i) (hr : IsMonHom r) (hir : i ≫ r = 𝟙 H) (hri : r ≫ i = E 0 0), ∀ (T : Over S) (y : Fin 8 → (T ⟶ H)), ∃! x : T ⟶ G, ∀ a, x ≫ (E a 0 ≫ r) = y a := by
  first | exact @GlobalTheory.matUnits_univ_of_idem | exact GlobalTheory.matUnits_univ_of_idem | (intros; apply GlobalTheory.matUnits_univ_of_idem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerProjectionsExtendUniformisedGroups
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8

def matAddEquiv {M : Type*} [AddCommGroup M] (S : Matrix (Fin 8) (Fin 8) ℤ) (hS : S.det = 1) :
    (Fin 8 → M) ≃+ (Fin 8 → M) where
  toFun w v := ∑ u, S v u • w u
  invFun w v := ∑ u, S.adjugate v u • w u
  left_inv w := by
    funext v
    have h : S.adjugate * S = 1 := by rw [Matrix.adjugate_mul, hS, one_smul]
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, ← Matrix.mul_apply, h, Matrix.one_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  right_inv w := by
    funext v
    have h : S * S.adjugate = 1 := by rw [Matrix.mul_adjugate, hS, one_smul]
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, ← Matrix.mul_apply, h, Matrix.one_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  map_add' x y := by
    funext v
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]

def sumChars {X X' : Type*} [AddCommGroup X] [AddCommGroup X'] (c : Fin 8 → (X →+ X')) : (Fin 8 → X) →+ X' where
  toFun y := ∑ v, c v (y v)
  map_zero' := by simp
  map_add' x y := by simp [Finset.sum_add_distrib]

theorem e8data : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∃ (pG : Fin 8 → (G' ⟶ G)) (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)) (e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X)), (∀ v, IsMonHom (pG v)) ∧ (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) ∧ (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) ∧ ∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y := by
  intro R _ _ _ hR hdvr G _ _ hG D A U G' _ _ hG' D' A' U' W hW pr hpr huniv hL
  haveI := hdvr
  haveI := U.gen_hom
  haveI := U'.gen_hom
  have hpG : ∀ v, ∃ F : G' ⟶ G, IsMonHom F ∧
      (Over.pullback (jK R)).map F = U'.gen.hom ≫ pr v ≫ U.gen.inv := by
    intro v
    haveI := hpr v
    obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.semiAbelian_hom_extends_uniquely_dvr R (FractionRing R) G' G hG' hG
      (U'.gen.hom ≫ pr v ≫ U.gen.inv) inferInstance
    exact ⟨F, hF, hF'⟩
  choose pG hpGm hpGg using hpG
  have hgen : ∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v := by
    intro v
    rw [hpGg v]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  choose c hc using fun v =>
    GlobalTheory.Poinc.HomTor.exists_torMatch R hR G hG D A U G' hG' D' A' U' (pG v) (hpGm v)
  have hbij := (characters_eighthPower_elementaryMatrices R hR hdvr G hG D A U G' hG' D' A' U' W hW pr hpr huniv hL pG hpGm hgen c hc).1
  let Φ := AddEquiv.ofBijective (sumChars c) hbij
  let Sm := matAddEquiv (M := D.toPre.X) (W + W.transpose) hW.2
  refine ⟨pG, c, Φ.symm.trans Sm.symm, hpGm, hgen, hc, fun y => ?_⟩
  have h1 : Sm ((Φ.symm.trans Sm.symm) y) = Φ.symm y := by simp
  have h2 : Φ (Φ.symm y) = y := Φ.apply_symm_apply y
  rw [← h1] at h2
  exact h2

end GlobalTheory.Poinc.Eq8
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfProdZpowSymmetricFormBasisEqStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_prod_zpow_symmetricFormBasis_eq : ∀ (F : Type) [Field F] (r : ℕ) (I : Type) [Fintype I] (ε : Module.Basis I ℤ (balForms (id : ℤ → ℤ) (Fin r → ℤ))) (x y : I → F), (∀ i, x i ≠ 0) → (∀ i, y i ≠ 0) → (∀ a b, ∏ i, x i ^ (ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) a b = ∏ i, y i ^ (ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) a b) → x = y := by
  first | exact @GlobalTheory.SymMono.eq_of_prod_zpow_eq | exact GlobalTheory.SymMono.eq_of_prod_zpow_eq | (intros; apply GlobalTheory.SymMono.eq_of_prod_zpow_eq <;> assumption)
end

