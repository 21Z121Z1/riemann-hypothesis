import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1293
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1254
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqZeroPointOfCotangentLinearMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsAffineOpenPreimageEqOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1299
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlaceRep
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies
open scoped TensorProduct

namespace GlobalTheory.CentralOps

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

section Fields

variable {T : Type} {n : ℕ}

open Classical in

def matDer (τ : T) (X : Matrix (Fin n) (Fin n) ℂ) :
    Derivation ℂ (MvPolynomial (T × Fin n × Fin n) ℂ) (MvPolynomial (T × Fin n × Fin n) ℂ) :=
  MvPolynomial.mkDerivation ℂ fun p =>
    if p.1 = τ then ∑ m, MvPolynomial.X (τ, p.2.1, m) * MvPolynomial.C (X m p.2.2) else 0

open Classical in
theorem matDer_X (τ : T) (X : Matrix (Fin n) (Fin n) ℂ) (p : T × Fin n × Fin n) :
    matDer τ X (MvPolynomial.X p) =
      if p.1 = τ then ∑ m, MvPolynomial.X (τ, p.2.1, m) * MvPolynomial.C (X m p.2.2) else 0 :=
  MvPolynomial.mkDerivation_X _ _ _

theorem matDer_add (τ : T) (X Y : Matrix (Fin n) (Fin n) ℂ) : matDer τ (X + Y) = matDer τ X + matDer τ Y := by
  classical
  refine MvPolynomial.derivation_ext fun p => ?_
  rw [Derivation.add_apply, matDer_X, matDer_X, matDer_X]
  split_ifs
  · simp [mul_add, Finset.sum_add_distrib]
  · simp

theorem matDer_smul (τ : T) (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) : matDer τ (c • X) = c • matDer τ X := by
  classical
  refine MvPolynomial.derivation_ext fun p => ?_
  rw [Derivation.smul_apply, matDer_X, matDer_X]
  split_ifs
  · simp only [Matrix.smul_apply, smul_eq_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.C_mul, MvPolynomial.smul_eq_C_mul]; ring
  · simp

theorem matDer_bracket (τ : T) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ⁅matDer τ X, matDer τ Y⁆ = matDer τ (X * Y - Y * X) := by
  classical
  refine MvPolynomial.derivation_ext fun p => ?_
  rw [Derivation.commutator_apply, matDer_X, matDer_X, matDer_X]
  split_ifs with h
  · simp only [map_sum, Derivation.leibniz, MvPolynomial.derivation_C, smul_zero, zero_add, matDer_X, if_true,
      smul_eq_mul, Finset.sum_mul, Matrix.sub_apply, Matrix.mul_apply, map_sub, map_sum, MvPolynomial.C_mul,
      Finset.mul_sum, mul_sub, Finset.sum_sub_distrib, mul_zero, zero_add]
    refine congrArg₂ (· - ·) ?_ ?_ <;> rw [Finset.sum_comm] <;>
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  · simp

theorem matDer_comm {τ τ' : T} (h : τ ≠ τ') (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ⁅matDer τ X, matDer τ' Y⁆ = 0 := by
  classical
  refine MvPolynomial.derivation_ext fun p => ?_
  rw [Derivation.commutator_apply, matDer_X, matDer_X, Derivation.zero_apply]
  by_cases h1 : p.1 = τ <;> by_cases h2 : p.1 = τ' <;>
    simp [h1, h2, h, Ne.symm h, map_sum, Derivation.leibniz, MvPolynomial.derivation_C, matDer_X]

theorem matDer_commute {τ τ' : T} (h : τ ≠ τ') (X Y : Matrix (Fin n) (Fin n) ℂ) :
    Commute (matDer τ X : Module.End ℂ (MvPolynomial (T × Fin n × Fin n) ℂ)) (matDer τ' Y) := by
  refine LinearMap.ext fun a => ?_
  have := congrArg (fun D : Derivation ℂ _ _ => D a) (matDer_comm h X Y)
  simp only [Derivation.commutator_apply, Derivation.zero_apply, sub_eq_zero] at this
  exact this

end Fields

section Reps

variable {D : D7}

abbrev PolyE (V : HSp D) : Type := MvPolynomial (D.what₂.Tau × Fin V.rank × Fin V.rank) ℂ

def realEntries (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (g : GA D V) :
    D.what₂.Tau × Fin V.rank × Fin V.rank → ℂ :=
  fun p => infMat D.sp.cm.sig V.gram (θ p.1) g p.2.1 p.2.2

def polyFun (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (P : PolyE V) : GA D V → ℂ :=
  fun g => MvPolynomial.eval (realEntries θ V g) P

theorem exists_placeRep (V : HSp D) (τ : D.what₂.Tau) : ∃ π : EnvAt V τ →ₐ[ℂ] Module.End ℂ (PolyE V),
    ∀ X : LieAt V τ, π (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) = (matDer τ X.1 : Module.End ℂ (PolyE V)) := by
  refine GlobalTheory.EnvelopingExtension.exists_algHom_unitary _ _ _ (fun X : LieAt V τ => (matDer τ X.1 : Module.End ℂ (PolyE V)))
    (fun X Y => LinearMap.ext fun a => ?_) (fun c X => LinearMap.ext fun a => ?_) (fun X Y Z h => LinearMap.ext fun a => ?_)
  · change matDer τ (X.1 + Y.1) a = matDer τ X.1 a + matDer τ Y.1 a
    rw [matDer_add]; rfl
  · have e : ((c • X : LieAt V τ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) = (c : ℂ) • X.1 := by
      ext i j; simp [Complex.real_smul]
    change matDer τ ((c • X : LieAt V τ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) a = (c : ℂ) • matDer τ X.1 a
    rw [e, matDer_smul]; rfl
  · change matDer τ Z.1 a = matDer τ X.1 (matDer τ Y.1 a) - matDer τ Y.1 (matDer τ X.1 a)
    rw [h, ← matDer_bracket, Derivation.commutator_apply]

def placeRep (V : HSp D) (τ : D.what₂.Tau) : EnvAt V τ →ₐ[ℂ] Module.End ℂ (PolyE V) := (exists_placeRep V τ).choose

theorem placeRep_ι (V : HSp D) (τ : D.what₂.Tau) (X : LieAt V τ) :
    placeRep V τ (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) = (matDer τ X.1 : Module.End ℂ (PolyE V)) :=
  (exists_placeRep V τ).choose_spec X

theorem placeRep_tmul (V : HSp D) (τ : D.what₂.Tau) (c : ℂ) (X : LieAt V τ) :
    placeRep V τ (UniversalEnvelopingAlgebra.ι ℂ (c ⊗ₜ[ℝ] X)) = c • (matDer τ X.1 : Module.End ℂ (PolyE V)) := by
  rw [show c ⊗ₜ[ℝ] X = c • ((1 : ℂ) ⊗ₜ[ℝ] X) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, map_smul,
    placeRep_ι]

theorem placeRep_comm (V : HSp D) {τ τ' : D.what₂.Tau} (h : τ ≠ τ') (x : ℂ ⊗[ℝ] LieAt V τ) (y : ℂ ⊗[ℝ] LieAt V τ') :
    Commute (placeRep V τ (UniversalEnvelopingAlgebra.ι ℂ x)) (placeRep V τ' (UniversalEnvelopingAlgebra.ι ℂ y)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => rw [map_add, map_add]; exact hx.add_left hx'
  | tmul c X =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => rw [map_add, map_add]; exact hy.add_right hy'
    | tmul c' Y =>
      rw [placeRep_tmul, placeRep_tmul]
      exact ((matDer_commute h X.1 Y.1).smul_left c).smul_right c'

open Classical in

def polyLie (V : HSp D) : GlobalTheory.AutFinLit.LieC V →ₗ⁅ℂ⁆ Module.End ℂ (PolyE V) :=
  DirectSum.toLieAlgebra _ (fun τ => (placeRep V τ).toLieHom.comp (UniversalEnvelopingAlgebra.ι ℂ)) fun τ τ' h x y => by
    change placeRep V τ (UniversalEnvelopingAlgebra.ι ℂ x) * placeRep V τ' (UniversalEnvelopingAlgebra.ι ℂ y) -
      placeRep V τ' (UniversalEnvelopingAlgebra.ι ℂ y) * placeRep V τ (UniversalEnvelopingAlgebra.ι ℂ x) = 0
    rw [(placeRep_comm V h x y).eq, sub_self]

def polyRep (V : HSp D) : GlobalTheory.AutFinLit.Env V →ₐ[ℂ] Module.End ℂ (PolyE V) :=
  UniversalEnvelopingAlgebra.lift ℂ (polyLie V)

open Classical in
theorem polyRep_ι_of (V : HSp D) (τ : D.what₂.Tau) (x : ℂ ⊗[ℝ] LieAt V τ) :
    polyRep V (UniversalEnvelopingAlgebra.ι ℂ (DirectSum.of (fun τ => ℂ ⊗[ℝ] LieAt V τ) τ x)) =
      placeRep V τ (UniversalEnvelopingAlgebra.ι ℂ x) := by
  rw [polyRep, UniversalEnvelopingAlgebra.lift_ι_apply, polyLie]
  exact DirectSum.toModule_lof ℂ (M := fun τ => ℂ ⊗[ℝ] LieAt V τ) τ x

end Reps

end GlobalTheory.CentralOps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaledEmbeddingNormBoundHostFieldStatement
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scaledEmbeddingNorm_bound_hostField : ∀ (D : D7) (κ : Type) [Fintype κ] [DecidableEq κ] (m n : ℕ) (T : Matrix κ (Fin m) D.host.E), ∃ C : ℝ, 1 ≤ C ∧ ∀ (s : κ → ℝ), (∀ k, 0 < s k) → ∀ B : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ, (∀ τ, T.map (tauE D τ) * B τ = Matrix.diagonal (fun k => ((s k : ℝ) : ℂ)⁻¹) * T.map (tauE D τ)) → ∀ ξ : Matrix (Fin m) (Fin n) D.host.E, ∑ p : κ × Fin n, (∑ τ, ‖tauE D τ ((T * ξ) p.1 p.2)‖) / s p.1 ≤ C * ∑ τ, ∑ i, ∑ j, ‖(B τ * ξ.map (tauE D τ)) i j‖ := by
  first | exact @GlobalTheory.tGnorm | exact GlobalTheory.tGnorm | (intros; apply GlobalTheory.tGnorm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecondKindCoordinatesUnitaryArchimedeanPlaStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut Filter Topology
open scoped TensorProduct ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_secondKindCoordinates_unitaryArchimedeanPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ w : InfinitePlace F, ∃ (d : ℕ) (η : Fin d → ℝ → GAd σ J) (s : GArch σ J w → Fin d → ℝ), (∀ i, IsRealLine σ J (η i)) ∧ Tendsto s (𝓝 1) (𝓝 0) ∧ ∀ᶠ y in 𝓝 1, embArch σ J w y = (List.ofFn fun i => η i (s y i)).prod := by
  first | exact @GlobalTheory.UAut.exists_coordSecondKind_arch | exact GlobalTheory.UAut.exists_coordSecondKind_arch | (intros; apply GlobalTheory.UAut.exists_coordSecondKind_arch <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceBelowCMFieldStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitPlaceBelowCMField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ w : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w := by
  first | exact @GlobalTheory.SplitPlaceExists.exists_isSplitAt | exact GlobalTheory.SplitPlaceExists.exists_isSplitAt | (intros; apply GlobalTheory.SplitPlaceExists.exists_isSplitAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqZeroPointOfCotangentLinearMapStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sqZeroPoint_of_cotangent_linearMap : ∀ (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A], (GlobalTheory.LieVB.omega A).IsQuasicoherent → ∀ (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (l : GlobalTheory.SqZeroPt.Wmod A →ₗ[O] M), ∃ (v : GlobalTheory.SqZeroPt.TM O M ⟶ A) (h : GlobalTheory.SqZeroPt.zeroSec O M ≫ v = η[A]), ∀ w, GlobalTheory.SqZeroPt.Phi v h w = l w := by
  first | exact @GlobalTheory.SqZeroPt.exists_Phi_eq_of_linearMap | exact GlobalTheory.SqZeroPt.exists_Phi_eq_of_linearMap | (intros; apply GlobalTheory.SqZeroPt.exists_Phi_eq_of_linearMap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStandardChartsFormalTowerOfVeryAmple
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg.ChartsEx

section Level0

variable {X : Scheme.{0}} {H : LB X}

theorem exists_chart_of_mem_nonzeroLocus (s : LB.Sec H) {x : X} (hx : x ∈ nonzeroLocus s) :
    ∃ k, x ∈ H.U k := by
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  exact ⟨l, X.basicOpen_le _ hl⟩

theorem mem_nonzeroLocus_iff_basicOpen (s : LB.Sec H) (k : H.ι) {x : X} (hk : x ∈ H.U k) :
    x ∈ nonzeroLocus s ↔ x ∈ X.basicOpen (s.f k) := by
  refine ⟨fun hx => ?_, fun hx => TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx⟩⟩
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have e := congrArg X.basicOpen (s.compat k l)
  rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit (H.g k l).isUnit] at e
  erw [Scheme.basicOpen_res, Scheme.basicOpen_res] at e
  have hx' : x ∈ H.U k ⊓ H.U l := ⟨hk, X.basicOpen_le _ hl⟩
  exact (e.ge ⟨hx', hx', hl⟩).2

theorem isUnit_rs (s : LB.Sec H) (k : H.ι) {O : X.Opens} (hk : O ≤ H.U k)
    (h : O ≤ nonzeroLocus s) : IsUnit (rs X hk (s.f k)) := by
  have hb : O ≤ X.basicOpen (s.f k) := fun x hx => (mem_nonzeroLocus_iff_basicOpen s k (hk hx)).1 (h hx)
  have hu : IsUnit (rs X (X.basicOpen_le (s.f k)) (s.f k)) :=
    X.toRingedSpace.isUnit_res_basicOpen (s.f k)
  simpa only [rs_rs] using hu.map (rs X hb)

theorem ratio_self (s : LB.Sec H) {V : X.Opens} (h : V ≤ nonzeroLocus s) (r : Γ(X, V))
    (hr : ∀ k, rs X (inf_le_right : V ⊓ H.U k ≤ H.U k) (s.f k) =
      rs X (inf_le_left : V ⊓ H.U k ≤ V) r * rs X (inf_le_right : V ⊓ H.U k ≤ H.U k) (s.f k)) :
    r = 1 := by
  refine X.sheaf.eq_of_locally_eq' (fun k : H.ι => V ⊓ H.U k) V (fun k => homOfLE inf_le_left)
    (fun x hx => ?_) _ _ fun k => ?_
  · obtain ⟨l, hl⟩ := exists_chart_of_mem_nonzeroLocus s (h hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨l, hx, hl⟩
  · change rs X inf_le_left r = rs X inf_le_left 1
    rw [map_one]
    exact (isUnit_rs s k inf_le_right (inf_le_left.trans h)).mul_right_cancel
      ((hr k).symm.trans (_root_.one_mul _).symm)

variable {n : ℕ} (s : Fin (n + 1) → LB.Sec H) (r : ∀ i, Fin (n + 1) → Γ(X, nonzeroLocus (s i)))
  (hr : ∀ i j k, rs X (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s j).f k) =
    rs X (inf_le_left : nonzeroLocus (s i) ⊓ H.U k ≤ nonzeroLocus (s i)) (r i j) *
      rs X (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s i).f k))

include hr in

theorem basicOpen_ratio (i j : Fin (n + 1)) :
    X.basicOpen (r i j) = nonzeroLocus (s i) ⊓ nonzeroLocus (s j) := by
  have key : ∀ k, (nonzeroLocus (s i) ⊓ H.U k) ⊓ X.basicOpen ((s j).f k) =
      (nonzeroLocus (s i) ⊓ H.U k) ⊓ X.basicOpen (r i j) := by
    intro k
    have e := congrArg X.basicOpen (hr i j k)
    rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit (isUnit_rs (s i) k inf_le_right inf_le_left)] at e
    erw [Scheme.basicOpen_res, Scheme.basicOpen_res] at e
    rw [e, inf_assoc, inf_comm (X.basicOpen (r i j)), ← inf_assoc, inf_idem]
  ext x
  constructor
  · intro hx
    have hxi : x ∈ nonzeroLocus (s i) := X.basicOpen_le _ hx
    obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus (s i) hxi
    have hm : x ∈ (nonzeroLocus (s i) ⊓ H.U k) ⊓ X.basicOpen (r i j) := ⟨⟨hxi, hk⟩, hx⟩
    rw [← key k] at hm
    exact ⟨hxi, TopologicalSpace.Opens.mem_iSup.2 ⟨k, hm.2⟩⟩
  · rintro ⟨hxi, hxj⟩
    obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus (s i) hxi
    have hm : x ∈ (nonzeroLocus (s i) ⊓ H.U k) ⊓ X.basicOpen ((s j).f k) :=
      ⟨⟨hxi, hk⟩, (mem_nonzeroLocus_iff_basicOpen (s j) k hk).1 hxj⟩
    rw [key k] at hm
    exact hm.2

include hr in

theorem ratio_cocycle (i j l : Fin (n + 1)) :
    rs X (inf_le_left : nonzeroLocus (s i) ⊓ nonzeroLocus (s j) ≤ nonzeroLocus (s i)) (r i l) =
      rs X (inf_le_left : nonzeroLocus (s i) ⊓ nonzeroLocus (s j) ≤ nonzeroLocus (s i)) (r i j) *
        rs X (inf_le_right : nonzeroLocus (s i) ⊓ nonzeroLocus (s j) ≤ nonzeroLocus (s j)) (r j l) := by
  refine X.sheaf.eq_of_locally_eq' (fun k : H.ι => (nonzeroLocus (s i) ⊓ nonzeroLocus (s j)) ⊓ H.U k)
    (nonzeroLocus (s i) ⊓ nonzeroLocus (s j)) (fun k => homOfLE inf_le_left) (fun x hx => ?_) _ _
    fun k => ?_
  · obtain ⟨l', hl⟩ := exists_chart_of_mem_nonzeroLocus (s i) hx.1
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨l', hx, hl⟩
  · change rs X inf_le_left _ = rs X inf_le_left _
    have hi : (nonzeroLocus (s i) ⊓ nonzeroLocus (s j)) ⊓ H.U k ≤ nonzeroLocus (s i) ⊓ H.U k :=
      inf_le_inf_right _ inf_le_left
    have hj : (nonzeroLocus (s i) ⊓ nonzeroLocus (s j)) ⊓ H.U k ≤ nonzeroLocus (s j) ⊓ H.U k :=
      inf_le_inf_right _ inf_le_right
    have e1 := congrArg (rs X hi) (hr i l k)
    have e2 := congrArg (rs X hi) (hr i j k)
    have e3 := congrArg (rs X hj) (hr j l k)
    simp only [map_mul, rs_rs] at e1 e2 e3 ⊢
    have hu := isUnit_rs (s i) k (inf_le_right : (nonzeroLocus (s i) ⊓ nonzeroLocus (s j)) ⊓ H.U k ≤ H.U k)
      (inf_le_left.trans inf_le_left)
    refine hu.mul_right_cancel ?_
    rw [← e1, e3, e2]
    ring

end Level0

end GlobalTheory.FormalAlg.ChartsEx

namespace GlobalTheory.FormalAlg.ChartsEx

section Tower

variable {R : Type} [CommRing R] {I : Ideal R}

theorem surjective_thickTrans (e : ℕ) : Surjective (thickTrans R I e) := by
  refine ⟨fun x => ?_⟩
  have h : I ^ (e + 1 + 1) ≤ I ^ (e + 1) := Ideal.pow_le_pow_right (by omega)
  have hx : (x : PrimeSpectrum (R ⧸ I ^ (e + 1 + 1))) ∈
      Set.range (PrimeSpectrum.comap (Ideal.Quotient.factor h)) := by
    rw [_root_.range_comap_of_surjective _ _ (Ideal.Quotient.factor_surjective h)]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have ha' : a ∈ I ^ (e + 1) := by
      simpa [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using ha
    refine x.2.mem_of_pow_mem 2 ?_
    have : Ideal.Quotient.mk (I ^ (e + 1 + 1)) a ^ 2 = 0 := by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      refine Ideal.pow_le_pow_right (show e + 1 + 1 ≤ (e + 1) * 2 by omega) ?_
      rw [pow_mul]
      exact Ideal.pow_mem_pow ha' 2
    rw [this]
    exact Ideal.zero_mem _
  exact hx

theorem isNilpotent_ker_factor (e : ℕ) (h : I ^ (e + 1 + 1) ≤ I ^ (e + 1)) :
    IsNilpotent (RingHom.ker (Ideal.Quotient.factor h)) := by
  refine ⟨2, le_bot_iff.1 ?_⟩
  rw [pow_two, Ideal.mul_le]
  intro x hx y hy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  have ha : a ∈ I ^ (e + 1) := by simpa [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using hx
  have hb : b ∈ I ^ (e + 1) := by simpa [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using hy
  rw [← map_mul, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
  refine Ideal.pow_le_pow_right (show e + 1 + 1 ≤ (e + 1) + (e + 1) by omega) ?_
  rw [pow_add]
  exact Ideal.mul_mem_mul ha hb

variable {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
  {β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left} {n : ℕ}

variable (Y n) in

abbrev Lvl (e : ℕ) : Type :=
  {p : (Σ D : Fin (n + 1) → (Y e).left.Opens, ∀ i, Fin (n + 1) → Γ((Y e).left, D i)) //
    ∀ i, IsAffineOpen (p.1 i)}

variable (β) in

def Lifts (e : ℕ) (q : Lvl Y n e) (q' : Lvl Y n (e + 1)) : Prop :=
  ∃ h : ∀ i, β e ⁻¹ᵁ q'.1.1 i = q.1.1 i,
    ∀ i j, ((β e).appLE (q'.1.1 i) (q.1.1 i) (h i).ge).hom (q'.1.2 i j) = q.1.2 i j

theorem exists_lifts {e : ℕ} (hsq : IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
    (q : Lvl Y n e) : ∃ q' : Lvl Y n (e + 1), Lifts β e q q' := by
  have hle : I ^ (e + 1 + 1) ≤ I ^ (e + 1) := Ideal.pow_le_pow_right (by omega)
  have hsurj : Function.Surjective (Ideal.Quotient.factor hle) := Ideal.Quotient.factor_surjective hle
  have hD := fun i => GlobalTheory.AffineThickening.exists_isAffineOpen_preimage_eq_of_isNilpotent _ _
    (Ideal.Quotient.factor hle) hsurj (isNilpotent_ker_factor e hle) _ _ (Y (e + 1)).hom (Y e).hom
    (β e) hsq (q.1.1 i) (q.2 i)
  choose D' hD' hpre using hD
  haveI : IsClosedImmersion (β e) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq.flip
      (IsClosedImmersion.spec_of_surjective _ hsurj)
  have hs : ∀ i, Function.Surjective ((β e).appLE (D' i) (q.1.1 i) (hpre i).ge).hom := by
    intro i y
    obtain ⟨x, hx⟩ := (β e).app_surjective (D' i) (hD' i) (rs _ (hpre i).le y)
    refine ⟨x, ?_⟩
    change rs _ (hpre i).ge (((β e).app (D' i)).hom x) = y
    rw [hx, rs_rs, rs_self]
  choose ρ' hρ' using fun i j => hs i (q.1.2 i j)
  exact ⟨⟨⟨D', ρ'⟩, hD'⟩, hpre, hρ'⟩

variable (β) in

def seq (hsq : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
    (q₀ : Lvl Y n 0) (e : ℕ) : Lvl Y n e :=
  Nat.rec (motive := Lvl Y n) q₀ (fun e q => Classical.choose (exists_lifts (hsq e) q)) e

theorem seq_lifts (hsq : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
    (q₀ : Lvl Y n 0) (e : ℕ) : Lifts β e (seq β hsq q₀ e) (seq β hsq q₀ (e + 1)) :=
  Classical.choose_spec (exists_lifts (hsq e) (seq β hsq q₀ e))

end Tower

end GlobalTheory.FormalAlg.ChartsEx

open GlobalTheory.FormalAlg.ChartsEx in

theorem GlobalTheory.FormalAlg.exists_charts_of_veryAmpleBy : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (H₀ : LB (Y 0).left) (n : ℕ) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → VeryAmpleBy (Y 0).hom H₀ s₀ → ∃ C : Charts I Y β n, (∀ i, C.D 0 i = nonzeroLocus (s₀ i)) ∧ ∀ i j (m : H₀.ι), rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ j).f m) = rs (Y 0).left (inf_le_left : C.D 0 i ⊓ H₀.U m ≤ C.D 0 i) (C.ρ 0 i j) * rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ i).f m) := by
  intro R _ I Y β hsq H₀ n s₀ _ hva
  obtain ⟨hcov, hloc⟩ := hva
  choose haff r hrel hsurj using hloc
  let q₀ : Lvl Y n 0 := ⟨⟨fun i => nonzeroLocus (s₀ i), r⟩, haff⟩
  have hsurjβ : ∀ e, Surjective (β e) := fun e =>
    MorphismProperty.of_isPullback (P := @Surjective) (hsq e).flip (surjective_thickTrans e)
  have hcover : ∀ e, ⨆ i, (seq β hsq q₀ e).1.1 i = ⊤ := by
    intro e
    induction e with
    | zero => exact hcov
    | succ e ih =>
      obtain ⟨hpre, -⟩ := seq_lifts hsq q₀ e
      refine top_unique fun y _ => ?_
      obtain ⟨x, rfl⟩ := (hsurjβ e).surj y
      have hx : x ∈ β e ⁻¹ᵁ (⨆ i, (seq β hsq q₀ (e + 1)).1.1 i) := by
        rw [Scheme.Hom.preimage_iSup]
        simp only [hpre]
        rw [ih]
        trivial
      exact hx
  refine ⟨{ D := fun e => (seq β hsq q₀ e).1.1
            aff := fun e => (seq β hsq q₀ e).2
            cover := hcover
            pre := fun e => (seq_lifts hsq q₀ e).1
            ρ := fun e => (seq β hsq q₀ e).1.2
            ρ_pull := fun e => (seq_lifts hsq q₀ e).2
            ρ_self := fun i => ratio_self (s₀ i) le_rfl (r i i) (hrel i i)
            basic := fun i j => basicOpen_ratio s₀ r hrel i j
            cocycle := fun i j l => ratio_cocycle s₀ r hrel i j l
            surj := hsurj }, fun i => rfl, hrel⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationSqZeroPointsUnitToPointStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_translation_sqZeroPoints_unit_to_point : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], ∃ τ : ∀ (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M], (Sp B ⟶ A.left) → (Sp (TrivSqZeroExt B M) ⟶ A.left) → (Sp (TrivSqZeroExt B M) ⟶ A.left), (∀ (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (P : Sp B ⟶ A.left), P ≫ A.hom = spMap (algebraMap R B) → Set.BijOn (τ B M P) {z | Lifts A.hom (unitPt A B) z} {z | Lifts A.hom P z}) ∧ ∀ (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (B' M' : Type) [CommRing B'] [Algebra R B'] [AddCommGroup M'] [Module B' M'] [Module B'ᵐᵒᵖ M'] [IsCentralScalar B' M'] (α : B →ₐ[R] B') (f : M → M') (β : TrivSqZeroExt B M →+* TrivSqZeroExt B' M'), IsSum β α f → ∀ (P : Sp B ⟶ A.left), P ≫ A.hom = spMap (algebraMap R B) → ∀ z, Lifts A.hom (unitPt A B) z → Lifts A.hom (unitPt A B') (spMap β ≫ z) ∧ τ B' M' (spMap (α : B →+* B') ≫ P) (spMap β ≫ z) = spMap β ≫ τ B M P z := by
  first | exact @GlobalTheory.AbTan.exists_translation | exact GlobalTheory.AbTan.exists_translation | (intros; apply GlobalTheory.AbTan.exists_translation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedConjDeltaOfUnitModNormsStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twistedConj_delta_of_unit_mod_norms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ (u : B.A) (Q : (w.adicCompletion E)[X]), Q.Separable → aeval u (Q.map e.symm.toRingHom) = 0 → Algebra.adjoin K.E {u} = ⊤ → ∀ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * ((-1) ^ (m - 1) * u) → (∀ x : B.Aˣ, IsUnit (GlobalTheory.TwLat.gram e b ((β₀ : B.A) * x))) → ∀ y : GLw m w, (nrmL m w y).val.charpoly = Q → ∃ x : B.Aˣ, B.σ (x : B.A) = x ∧ ∃ g : GLw m w, y = g⁻¹ * GlobalTheory.TwLat.dlt e b ((β₀ : B.A) * x) * thL m w g := by
  first | exact @GlobalTheory.TwLat.ClSurj.exists_twConj_dlt | exact GlobalTheory.TwLat.ClSurj.exists_twConj_dlt | (intros; apply GlobalTheory.TwLat.ClSurj.exists_twConj_dlt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueRingHomOfSqZeroExtPointAffineStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_ringHom_of_sqZeroExt_point_affine : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (U : X.affineOpens) (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (ρ : Sec s U.1 →+* B) (z : Sp (TrivSqZeroExt B M) ⟶ X), spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ z = spMap ρ ≫ affPt s U → ∃! c : Sec s U.1 →+* TrivSqZeroExt B M, spMap c ≫ affPt s U = z ∧ ∀ b, (c b).fst = ρ b := by
  first | exact @GlobalTheory.AbTan.exists_unique_ringHom_of_sqZero | exact GlobalTheory.AbTan.exists_unique_ringHom_of_sqZero | (intros; apply GlobalTheory.AbTan.exists_unique_ringHom_of_sqZero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryModelOfSelfDualLatticeCountNeZeroStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_model_of_selfDualLatticeCount_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (n : ℕ) (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A), Fits w e B Q u → Q.natDegree = n → B.σ x = x → IsUnit x → B.N x ≠ 0 → ∃ γ : GLw n w, γ ∈ UL n w ∧ IsModel w e B u x γ := by
  first | exact @GlobalTheory.KapLat.exists_model_of_N_ne_zero | exact GlobalTheory.KapLat.exists_model_of_N_ne_zero | (intros; apply GlobalTheory.KapLat.exists_model_of_N_ne_zero <;> assumption)
end

