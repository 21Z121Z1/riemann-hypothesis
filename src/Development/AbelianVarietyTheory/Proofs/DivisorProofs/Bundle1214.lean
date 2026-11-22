import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1171
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1203
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1172
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1139
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1085
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1185
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1064
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadPlacesPrimeToHostBaseTupleStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.badPlacesPrimeToHost_baseTuple : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → PrimeToHost R A.μ0 := by
  first | exact @GlobalTheory.LowRow.primeToHost_base | exact GlobalTheory.LowRow.primeToHost_base | (intros; apply GlobalTheory.LowRow.primeToHost_base <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFrameBorelActsExtremalVectorByWeightStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseFrameBorel_acts_extremalVector_by_weight : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → ∀ τ, SmoothVec (lieH (gramAt D V τ)) (M.rep τ) (v τ : M.H τ) ∧ ∀ a c : Fin V.rank, a ≤ c → dRepC (gramAt D V τ) (M.rep τ) (x0Mat M τ * Matrix.single a c 1 * (x0Mat M τ)⁻¹) (v τ : M.H τ) = if a = c then (w τ a : ℂ) • (v τ : M.H τ) else 0 := by
  first | exact @GlobalTheory.HolDict.VKill.borel_extVec | exact GlobalTheory.HolDict.VKill.borel_extVec | (intros; apply GlobalTheory.HolDict.VKill.borel_extVec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirationalModelRegularUnitValuesStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.birationalModel_regular_unit_values : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (π : Y ⟶ X) (hπ : π ≫ p = q) (φ : X.functionField →+* Y.functionField), IsModel π φ → (∀ (y : Y) (f : X.functionField), RegAt (π y) f → RegAt y (φ f)) ∧ (∀ (y : Y) (f : X.functionField), UnitAt (π y) f → UnitAt y (φ f)) ∧ (∀ (U : X.Opens) (h : genericPoint X ∈ U) (h' : genericPoint Y ∈ π ⁻¹ᵁ U) (a : Γ(X, U)), φ (fnOf U h a) = fnOf (π ⁻¹ᵁ U) h' (π.app U a)) ∧ ∀ (σ : k →+* ℂ) (z : CxPts q σ) (f : X.functionField), RegAt (π (under z)) f → ratVal (φ f) z = ratVal f (GlobalTheory.Points.PtsOver.map π hπ _ z) := by
  first | exact @GlobalTheory.HSNef.model_regAt_unitAt_values | exact GlobalTheory.HSNef.model_regAt_unitAt_values | (intros; apply GlobalTheory.HSNef.model_regAt_unitAt_values <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockDiagonalEigenvalueLeOfCasimirNearMinStatement
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockDiagonal_eigenvalue_le_of_casimir_nearMin : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (s : ι → Bool) (α β : ℂ), ∃ R : ℝ, ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (F : ι → ι → Module.End ℂ M), IsGl F → (∀ a b, qop F α β a b = 0) → LocU s F → ∀ ω : ℝ, (∀ (ω' : ℝ) (v : M), v ≠ 0 → cas s F v = (ω' : ℂ) • v → ω < ω' + 1) → ∀ (x : ℝ) (y : ι → M), y ≠ 0 → (∀ a, s a = false → y a = 0) → (∀ a, s a = true → ∑ b, F a b (y b) = (x : ℂ) • y a) → (∀ a, cas s F (y a) = (ω : ℂ) • y a) → x ≤ R := by
  first | exact @GlobalTheory.HoweR.diag_eig_le_of_cas_min | exact GlobalTheory.HoweR.diag_eig_le_of_cas_min | (intros; apply GlobalTheory.HoweR.diag_eig_le_of_cas_min <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixValuesUnipotentDiagonal
section
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

namespace GlobalTheory.GamMul

theorem toGL_of_inv {R : Type} [CommRing R] {n : ℕ} (M N : Matrix (Fin n) (Fin n) R) (h₁ : M * N = 1)
    (h₂ : N * M = 1) : toGL M = ⟨M, N, h₁, h₂⟩ := by
  unfold toGL
  have hu : IsUnit M := ⟨⟨M, N, h₁, h₂⟩, rfl⟩
  rw [dif_pos hu]
  exact Units.ext rfl

theorem eye_mul_eye {R : Type} [CommRing R] (n o₁ o₂ o₃ b : ℕ) (h : o₂ + b ≤ n) :
    eye R n o₁ o₂ b * eye R n o₂ o₃ b = eye R n o₁ o₃ b := by
  unfold eye
  rw [(put_mul_put R n o₁ o₂ o₃ 0 b b b b (1 : Matrix (Fin b) (Fin b) R) 1 1).1 h, Matrix.mul_one]

theorem eye_mul_eye_zero {R : Type} [CommRing R] (n o₁ o₂ o₃ o₄ b c : ℕ) (h : o₂ + b ≤ o₃ ∨ o₃ + c ≤ o₂) :
    eye R n o₁ o₂ b * eye R n o₃ o₄ c = 0 := by
  unfold eye
  exact (put_mul_put R n o₁ o₂ o₃ o₄ b b c c (1 : Matrix (Fin b) (Fin b) R) 0 1).2 h

theorem val_uni_dg_shuf : ∀ (R : Type) [CommRing R] (n o₁ o₂ p q : ℕ),
    (∀ X : Matrix (Fin p) (Fin q) R, (o₁ + p ≤ o₂ ∨ o₂ + q ≤ o₁) →
      (uni n o₁ o₂ X).val = 1 + put n o₁ o₂ X ∧ (uni n o₁ o₂ X)⁻¹.val = 1 - put n o₁ o₂ X) ∧
    (∀ g : GL (Fin p) R, o₁ + p ≤ n →
      (dg n o₁ g).val = 1 - eye R n o₁ o₁ p + put n o₁ o₁ g.val ∧
      (dg n o₁ g)⁻¹.val = 1 - eye R n o₁ o₁ p + put n o₁ o₁ g⁻¹.val) ∧
    (p ≤ n → (shuf R n p).val = eye R n 0 p (n - p) + eye R n (n - p) 0 p ∧
      (shuf R n p)⁻¹.val = eye R n p 0 (n - p) + eye R n 0 (n - p) p) := by
  intro R _ n o₁ o₂ p q
  refine ⟨?_, ?_, ?_⟩
  · intro X hX
    have hPP : put n o₁ o₂ X * put n o₁ o₂ X = 0 :=
      (put_mul_put R n o₁ o₂ o₁ o₂ p q q p X 0 X).2 hX.symm
    have h₁ : (1 + put n o₁ o₂ X) * (1 - put n o₁ o₂ X) = 1 := by
      rw [add_mul, one_mul, mul_sub, mul_one, hPP]; abel
    have h₂ : (1 - put n o₁ o₂ X) * (1 + put n o₁ o₂ X) = 1 := by
      rw [sub_mul, one_mul, mul_add, mul_one, hPP]; abel
    have e : uni n o₁ o₂ X = ⟨_, _, h₁, h₂⟩ := toGL_of_inv _ _ h₁ h₂
    rw [e]; exact ⟨rfl, rfl⟩
  · intro g hg
    have hm : ∀ A B : Matrix (Fin p) (Fin p) R, put n o₁ o₁ A * put n o₁ o₁ B = put n o₁ o₁ (A * B) :=
      fun A B => (put_mul_put R n o₁ o₁ o₁ o₁ p p p p A B B).1 hg
    have key : ∀ a b : GL (Fin p) R, a * b = 1 →
        (1 - eye R n o₁ o₁ p + put n o₁ o₁ a.val) * (1 - eye R n o₁ o₁ p + put n o₁ o₁ b.val) = 1 := by
      intro a b hab
      have hab' : a.val * b.val = 1 := by rw [← Units.val_mul, hab]; rfl
      simp only [eye, sub_mul, add_mul, mul_sub, mul_add, one_mul, mul_one, hm, Matrix.one_mul, Matrix.mul_one, hab']
      abel
    have h₁ := key g g⁻¹ (mul_inv_cancel g)
    have h₂ := key g⁻¹ g (inv_mul_cancel g)
    have e : dg n o₁ g = ⟨_, _, h₁, h₂⟩ := toGL_of_inv _ _ h₁ h₂
    rw [e]; exact ⟨rfl, rfl⟩
  · intro hp
    have hpk := (put_lin_pack R n 0 0 (n - p) p).2.2.2.2.1
    have hpk' := (put_lin_pack R n 0 0 p (n - p)).2.2.2.2.1
    have hone := (put_lin_pack R n 0 0 0 0).2.2.2.2.2.1
    have hs : n - p + p = n := Nat.sub_add_cancel hp
    have hs' : p + (n - p) = n := by omega
    rw [hs, hone, zero_add] at hpk
    rw [hs', hone, zero_add] at hpk'
    have h₁ : (eye R n 0 p (n - p) + eye R n (n - p) 0 p) * (eye R n p 0 (n - p) + eye R n 0 (n - p) p) = 1 := by
      rw [add_mul, mul_add, mul_add, eye_mul_eye n 0 p 0 (n - p) (by omega),
        eye_mul_eye_zero n 0 p 0 (n - p) (n - p) p (Or.inr (by omega)),
        eye_mul_eye_zero n (n - p) 0 p 0 p (n - p) (Or.inl (by omega)),
        eye_mul_eye n (n - p) 0 (n - p) p (by omega), hpk]
      abel
    have h₂ : (eye R n p 0 (n - p) + eye R n 0 (n - p) p) * (eye R n 0 p (n - p) + eye R n (n - p) 0 p) = 1 := by
      rw [add_mul, mul_add, mul_add, eye_mul_eye n p 0 p (n - p) (by omega),
        eye_mul_eye_zero n p 0 (n - p) 0 (n - p) p (Or.inl (by omega)),
        eye_mul_eye_zero n 0 (n - p) 0 p p (n - p) (Or.inr (by omega)),
        eye_mul_eye n 0 (n - p) 0 p (by omega), hpk']
      abel
    have e : shuf R n p = ⟨_, _, h₁, h₂⟩ := toGL_of_inv _ _ h₁ h₂
    rw [e]; exact ⟨rfl, rfl⟩

end GlobalTheory.GamMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUnipotentDetOneAndTrivial
section
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

namespace GlobalTheory.GamMul.Hom

variable {R : Type} [CommRing R]

theorem put_entry (n o₁ o₂ : ℕ) {p q : ℕ} (X : Matrix (Fin p) (Fin q) R) (i j : Fin n) :
    put n o₁ o₂ X i j =
      if h : (o₁ ≤ i.val ∧ i.val < o₁ + p) ∧ (o₂ ≤ j.val ∧ j.val < o₂ + q) then
        X ⟨i.val - o₁, by omega⟩ ⟨j.val - o₂, by omega⟩ else 0 := rfl

theorem toGL_coe {n : ℕ} {M : Matrix (Fin n) (Fin n) R} (h : IsUnit M) :
    ((toGL M : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = M := by
  unfold toGL
  rw [dif_pos h]
  rfl

theorem det_one_add_put (n o₁ o₂ : ℕ) {p q : ℕ} (X : Matrix (Fin p) (Fin q) R)
    (hd : o₁ + p ≤ o₂ ∨ o₂ + q ≤ o₁) : (1 + put n o₁ o₂ X).det = 1 := by
  have hdiag : ∀ i : Fin n, (1 + put n o₁ o₂ X) i i = 1 := by
    intro i
    rw [Matrix.add_apply, Matrix.one_apply_eq, put_entry, dif_neg (by omega), add_zero]
  rcases hd with hd | hd
  · rw [Matrix.det_of_upperTriangular]
    · simp [hdiag]
    · intro i j hij
      have h' : j.val < i.val := hij
      rw [Matrix.add_apply, Matrix.one_apply_ne (show i ≠ j from fun e => by subst e; omega), put_entry, dif_neg (by omega), add_zero]
  · rw [Matrix.det_of_lowerTriangular]
    · simp [hdiag]
    · intro i j hij
      have h' : i.val < j.val := hij
      rw [Matrix.add_apply, Matrix.one_apply_ne (show i ≠ j from fun e => by subst e; omega), put_entry, dif_neg (by omega), add_zero]

theorem blk_mul (n o p : ℕ) (hp : o + p ≤ n) (A B : Matrix (Fin p) (Fin p) R) :
    (1 - eye R n o o p + put n o o A) * (1 - eye R n o o p + put n o o B) =
      1 - eye R n o o p + put n o o (A * B) := by
  have hm : ∀ X Y : Matrix (Fin p) (Fin p) R, put n o o X * put n o o Y = put n o o (X * Y) :=
    fun X Y => (put_mul_put R n o o o 0 p p p 0 X Y 0).1 hp
  unfold eye
  simp only [sub_mul, mul_sub, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, hm]
  abel

end GlobalTheory.GamMul.Hom

namespace GlobalTheory.GamMul.Hom

variable {R : Type} [CommRing R]

theorem uni_coe (n o₁ o₂ : ℕ) {p q : ℕ} (X : Matrix (Fin p) (Fin q) R) (hd : o₁ + p ≤ o₂ ∨ o₂ + q ≤ o₁) :
    ((uni n o₁ o₂ X : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = 1 + put n o₁ o₂ X :=
  toGL_coe ((Matrix.isUnit_iff_isUnit_det _).2 (by rw [det_one_add_put n o₁ o₂ X hd]; exact isUnit_one))

theorem dg_coe (n o : ℕ) {p : ℕ} (g : GL (Fin p) R) (hp : o + p ≤ n) :
    ((dg n o g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = 1 - eye R n o o p + put n o o g.val := by
  have h1 := blk_mul (R := R) n o p hp g.val g⁻¹.val
  have h2 := blk_mul (R := R) n o p hp g⁻¹.val g.val
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one] at h1
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one] at h2
  have e1 : (1 : Matrix (Fin n) (Fin n) R) - eye R n o o p + put n o o (1 : Matrix (Fin p) (Fin p) R) = 1 := by
    unfold eye; abel
  rw [e1] at h1 h2
  exact toGL_coe ⟨⟨_, _, h1, h2⟩, rfl⟩

theorem dg_one' (n o p : ℕ) : dg n o (1 : GL (Fin p) R) = 1 := by
  unfold dg
  rw [Units.val_one]
  have e1 : (1 : Matrix (Fin n) (Fin n) R) - eye R n o o p + put n o o (1 : Matrix (Fin p) (Fin p) R) = 1 := by
    unfold eye; abel
  rw [e1]
  exact Units.ext (toGL_coe isUnit_one)

theorem dg_mul' (n o : ℕ) {p : ℕ} (hp : o + p ≤ n) (g g' : GL (Fin p) R) :
    dg n o (g * g') = dg n o g * dg n o g' := by
  apply Units.ext
  rw [Units.val_mul, dg_coe n o _ hp, dg_coe n o _ hp, dg_coe n o _ hp, blk_mul n o p hp, Units.val_mul]

end GlobalTheory.GamMul.Hom

namespace GlobalTheory.GamMul.Hom

variable {R : Type} [CommRing R]

theorem dgM_in (n o p : ℕ) (A : Matrix (Fin p) (Fin p) R) (i j : Fin n) (hi : o ≤ i.val ∧ i.val < o + p)
    (hj : o ≤ j.val ∧ j.val < o + p) :
    (1 - eye R n o o p + put n o o A) i j = A ⟨i.val - o, by omega⟩ ⟨j.val - o, by omega⟩ := by
  unfold eye
  rw [Matrix.add_apply, Matrix.sub_apply, put_entry, put_entry, dif_pos ⟨hi, hj⟩, dif_pos ⟨hi, hj⟩]
  simp only [Matrix.one_apply, Fin.ext_iff]
  by_cases h : i.val = j.val
  · have h' : i.val - o = j.val - o := by omega
    simp [h, h']
  · have h' : i.val - o ≠ j.val - o := by omega
    simp [h, h']

theorem dgM_out (n o p : ℕ) (A : Matrix (Fin p) (Fin p) R) (i j : Fin n)
    (h : ¬((o ≤ i.val ∧ i.val < o + p) ∧ (o ≤ j.val ∧ j.val < o + p))) :
    (1 - eye R n o o p + put n o o A) i j = (1 : Matrix (Fin n) (Fin n) R) i j := by
  unfold eye
  rw [Matrix.add_apply, Matrix.sub_apply, put_entry, put_entry, dif_neg h, dif_neg h, sub_zero, add_zero]

theorem det_dg' (n o : ℕ) {p : ℕ} (hp : o + p ≤ n) (g : GL (Fin p) R) :
    GeneralLinearGroup.det (dg n o g) = GeneralLinearGroup.det g := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply, dg_coe n o g hp]
  let P : Fin n → Prop := fun i => o ≤ i.val ∧ i.val < o + p
  let f : {i : Fin n // P i} ≃ Fin p :=
    { toFun := fun i => ⟨i.1.val - o, by have := i.2; simp only [P] at this; omega⟩
      invFun := fun j => ⟨⟨o + j.val, by omega⟩, by simp only [P]; omega⟩
      left_inv := fun i => by
        have := i.2; simp only [P] at this
        apply Subtype.ext; apply Fin.ext; simp only; omega
      right_inv := fun j => by apply Fin.ext; simp only; omega }
  rw [Matrix.twoBlockTriangular_det _ P]
  · have h1 : toSquareBlockProp (1 - eye R n o o p + put n o o g.val) P = (g.val).submatrix f f := by
      ext i j
      have hi := i.2
      have hj := j.2
      simp only [P] at hi hj
      rw [toSquareBlockProp_def, Matrix.of_apply]
      rw [dgM_in n o p g.val i.1 j.1 hi hj]
      rfl
    have h2 : toSquareBlockProp (1 - eye R n o o p + put n o o g.val) (fun i => ¬P i) = 1 := by
      ext i j
      have hi := i.2
      rw [toSquareBlockProp_def, Matrix.of_apply]
      rw [dgM_out n o p g.val i.1 j.1 (fun h => hi h.1)]
      simp only [Matrix.one_apply, Subtype.ext_iff]
    rw [h1, h2, Matrix.det_submatrix_equiv_self, Matrix.det_one, mul_one]
  · intro i hi j hj
    rw [dgM_out n o p g.val i j (fun h => hi h.1), Matrix.one_apply_ne (by rintro rfl; exact hi hj)]

end GlobalTheory.GamMul.Hom

namespace GlobalTheory.GamMul.Hom

variable {R : Type} [CommRing R]

theorem dg_mul_dg_eq_emb₂ (n p q : ℕ) (h : p + q = n) (a : GL (Fin p) R) (b : GL (Fin q) R) :
    dg n 0 a * dg n p b = emb₂ R (stdSum h) (a, b) := by
  apply Units.ext
  rw [Units.val_mul, dg_coe n 0 a (by omega), dg_coe n p b (by omega), val_emb₂]
  have hz : ∀ (X : Matrix (Fin p) (Fin p) R) (Z : Matrix (Fin q) (Fin q) R),
      put n 0 0 X * put n p p Z = 0 :=
    fun X Z => (put_mul_put R n 0 0 p p p p q q X 0 Z).2 (Or.inl (by omega))
  have hsum : put n 0 0 (1 : Matrix (Fin p) (Fin p) R) + put n p p (1 : Matrix (Fin q) (Fin q) R) = 1 := by
    have h1 := (put_lin_pack R n 0 0 p q).2.2.2.2.1
    have h2 := (put_lin_pack R n 0 0 p q).2.2.2.2.2.1
    simp only [zero_add] at h1
    rw [h] at h1
    rw [← h2, h1]
    rfl
  have key : (1 - eye R n 0 0 p + put n 0 0 a.val) * (1 - eye R n p p q + put n p p b.val) =
      put n 0 0 a.val + put n p p b.val := by
    unfold eye
    simp only [sub_mul, mul_sub, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, hz]
    rw [← hsum]
    abel
  rw [key]
  ext i j
  obtain ⟨i, rfl⟩ := (stdSum h).surjective i
  obtain ⟨j, rfl⟩ := (stdSum h).surjective j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    Matrix.add_apply, put_entry, put_entry]
  rcases i with i | i <;> rcases j with j | j
  · have hi := i.2
    have hj := j.2
    rw [dif_pos (by simp only [stdSum_inl]; omega), dif_neg (by simp only [stdSum_inl]; omega), add_zero,
      fromBlocks_apply₁₁]
    congr 1 <;> apply Fin.ext <;> simp
  · have hi := i.2
    rw [dif_neg (by simp only [stdSum_inl, stdSum_inr]; omega), dif_neg (by simp only [stdSum_inl, stdSum_inr]; omega), add_zero,
      fromBlocks_apply₁₂, Matrix.zero_apply]
  · have hj := j.2
    rw [dif_neg (by simp only [stdSum_inl, stdSum_inr]; omega), dif_neg (by simp only [stdSum_inl, stdSum_inr]; omega), add_zero,
      fromBlocks_apply₂₁, Matrix.zero_apply]
  · have hi := i.2
    have hj := j.2
    rw [dif_neg (by simp only [stdSum_inr]; omega), dif_pos (by simp only [stdSum_inr]; omega), zero_add,
      fromBlocks_apply₂₂]
    show _ = (b : Matrix (Fin q) (Fin q) R) i j
    exact congrArg₂ (fun x y => (b : Matrix (Fin q) (Fin q) R) x y) (Fin.ext (by simp)) (Fin.ext (by simp))

theorem shuf_zero' (n : ℕ) : shuf R n 0 = 1 := by
  unfold shuf
  have h1 := (put_lin_pack R n 0 0 0 0).2.2.2.2.2.1
  have h2 := (put_lin_pack R n n 0 0 0).2.2.2.2.2.2.1 (1 : Matrix (Fin 0) (Fin 0) R) (Or.inl rfl)
  rw [Nat.sub_zero]
  change toGL (eye R n 0 0 n + put n n 0 (1 : Matrix (Fin 0) (Fin 0) R)) = 1
  rw [h1, h2, add_zero]
  exact Units.ext (toGL_coe isUnit_one)

theorem dg_zero_self (n : ℕ) (g : GL (Fin n) R) : dg n 0 g = g := by
  unfold dg
  rw [(put_lin_pack R n 0 0 0 0).2.2.2.2.2.1, (put_lin_pack R n 0 0 0 0).2.2.2.2.2.2.2, sub_self, zero_add]
  exact toGL_val g

end GlobalTheory.GamMul.Hom

namespace GlobalTheory.GamMul

theorem uni_dg_hom : ∀ (R : Type) [CommRing R] (n o₁ o₂ p q : ℕ), ((o₁ + p ≤ o₂ ∨ o₂ + q ≤ o₁) → (∀ X Y : Matrix (Fin p) (Fin q) R, uni n o₁ o₂ (X + Y) = uni n o₁ o₂ X * uni n o₁ o₂ Y) ∧ (∀ X : Matrix (Fin p) (Fin q) R, GeneralLinearGroup.det (uni n o₁ o₂ X) = 1)) ∧ uni n o₁ o₂ (0 : Matrix (Fin p) (Fin q) R) = 1 ∧ (∀ X : Matrix (Fin p) (Fin q) R, (p = 0 ∨ q = 0) → uni n o₁ o₂ X = 1) ∧ dg n o₁ (1 : GL (Fin p) R) = 1 ∧ (o₁ + p ≤ n → (∀ g g' : GL (Fin p) R, dg n o₁ (g * g') = dg n o₁ g * dg n o₁ g') ∧ ∀ g : GL (Fin p) R, GeneralLinearGroup.det (dg n o₁ g) = GeneralLinearGroup.det g) ∧ (∀ (h : p + q = n) (a : GL (Fin p) R) (b : GL (Fin q) R), dg n 0 a * dg n p b = emb₂ R (stdSum h) (a, b)) ∧ shuf R n 0 = 1 ∧ (∀ g : GL (Fin n) R, dg n 0 g = g) := by
  intro R _ n o₁ o₂ p q
  have hone : ∀ M : Matrix (Fin n) (Fin n) R, M = 0 → toGL (1 + M) = 1 := by
    intro M hM
    rw [hM, add_zero]
    exact Units.ext (Hom.toGL_coe isUnit_one)
  refine ⟨fun hd => ⟨fun X Y => ?_, fun X => ?_⟩, ?_, fun X hX => ?_, Hom.dg_one' n o₁ p,
    fun hp => ⟨fun g g' => Hom.dg_mul' n o₁ hp g g', fun g => Hom.det_dg' n o₁ hp g⟩,
    fun h a b => Hom.dg_mul_dg_eq_emb₂ n p q h a b, Hom.shuf_zero' n, Hom.dg_zero_self n⟩
  · apply Units.ext
    rw [Units.val_mul, Hom.uni_coe n o₁ o₂ _ hd, Hom.uni_coe n o₁ o₂ _ hd, Hom.uni_coe n o₁ o₂ _ hd,
      (put_lin_pack R n o₁ o₂ p q).1, add_mul, mul_add, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
      (put_mul_put R n o₁ o₂ o₁ o₂ p q q p X 0 Y).2 (hd.symm.imp id id)]
    abel
  · apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, Hom.uni_coe n o₁ o₂ _ hd, Hom.det_one_add_put n o₁ o₂ X hd, Units.val_one]
  · exact hone _ (put_lin_pack R n o₁ o₂ p q).2.2.1
  · exact hone _ ((put_lin_pack R n o₁ o₂ p q).2.2.2.2.2.2.1 X hX)

end GlobalTheory.GamMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxMonomialFamilyProdMemNormBallOfExponentLt
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef.BoxProd

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem nu_nonneg (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    0 ≤ P.nu a b σ y f := by
  unfold Pair.nu; positivity

theorem mul_mem_Bl (P : Pair p) {a b a' b' : ℤ} {R R' : ℝ} (hR : 0 ≤ R) {f g : X.functionField}
    (hf : f ∈ P.Bl a b R) (hg : g ∈ P.Bl a' b' R') : f * g ∈ P.Bl (a + a') (b + b') (R * R') := by
  obtain ⟨h1, h2⟩ := GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul _ _ _ P a b a' b' f g hf.1 hg.1
  refine ⟨h1, fun σ y => ?_⟩
  rw [h2 σ y]
  exact mul_le_mul (hf.2 σ y) (hg.2 σ y) (nu_nonneg _ _ _ _ _ _) hR

theorem one_mem_Bl (P : Pair p) : (1 : X.functionField) ∈ P.Bl 0 0 1 := by
  refine ⟨fun x i j _ _ => ?_, fun σ y => ?_⟩
  · simp only [Pair.loc, zpow_zero, mul_one]
    exact ⟨1, map_one _⟩
  · have e := IntExample.ratVal_nat y 1
    simp only [Nat.cast_one] at e
    simp [Pair.nu, Pair.loc, e]

theorem prod_mem_of_le (P : Pair p) (D : ℕ) (J : Type) (e : J → X.functionField) (x : Fin D → X.functionField)
    (a b : ℤ) (R : ℝ) (hR : 0 ≤ R) (h : ∀ c, boxFam e x c ∈ P.Bl a b R) :
    ∀ (m : ℕ) (u : Fin m → J) (n : Fin D → ℕ), (∀ i, n i ≤ m) →
      (∏ l, e (u l)) * ∏ i, x i ^ n i ∈ P.Bl (m * a) (m * b) (R ^ m) := by
  intro m
  induction m with
  | zero =>
    intro u n hn
    have h0 : ∀ i, n i = 0 := fun i => Nat.le_zero.1 (hn i)
    simp only [h0, pow_zero, Finset.prod_const_one, Finset.univ_eq_empty, Finset.prod_empty, mul_one,
      Nat.cast_zero, zero_mul]
    exact one_mem_Bl P
  | succ m ih =>
    intro u n hn
    have hx : ∏ i, x i ^ n i =
        (∏ i ∈ Finset.univ.filter (fun i => 0 < n i), x i) * ∏ i, x i ^ (n i - 1) := by
      rw [Finset.prod_filter, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rcases Nat.eq_zero_or_pos (n i) with h0 | h0
      · simp [h0]
      · rw [if_pos h0, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ n i)]
    have key : (∏ l, e (u l)) * ∏ i, x i ^ n i =
        boxFam e x (u 0, Finset.univ.filter (fun i => 0 < n i)) *
          ((∏ l : Fin m, e (u l.succ)) * ∏ i, x i ^ (n i - 1)) := by
      rw [Fin.prod_univ_succ, hx]
      simp only [boxFam]
      ring
    rw [key]
    have hm := mul_mem_Bl P hR (h (u 0, Finset.univ.filter (fun i => 0 < n i)))
      (ih (fun l => u l.succ) (fun i => n i - 1) (fun i => by have := hn i; omega))
    have ea : ((m + 1 : ℕ) : ℤ) * a = a + m * a := by push_cast; ring
    have eb : ((m + 1 : ℕ) : ℤ) * b = b + m * b := by push_cast; ring
    rw [ea, eb, pow_succ']
    exact hm

theorem prod_mem_Bl : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (D : ℕ) (J : Type) (e : J → X.functionField) (x : Fin D → X.functionField) (a b : ℤ) (R : ℝ), 0 ≤ R → (∀ c, boxFam e x c ∈ P.Bl a b R) → ∀ (m : ℕ) (u : Fin m → J) (n : Fin D → ℕ), (∀ i, n i < m) → (∏ l, e (u l)) * ∏ i, x i ^ n i ∈ P.Bl (m * a) (m * b) (R ^ m) := by
  intro k _ X _ p P D J e x a b R hR h m u n hn
  exact prod_mem_of_le P D J e x a b R hR h m u n fun i => (hn i).le

end GlobalTheory.HSNef.BoxProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliCoeffDualWeylEqCoeffProdStatement
section
open Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame Formalism.CohomologicalDescent.LD GlobalTheory.CapelliLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelliCoeff_dualWeyl_eq_coeff_prod : ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (N : ℕ), ∃ F : ℕ → FreeAlgebra O (Fin N × Fin N), ∀ ν : Fin N → ℕ, Antitone ν → ∀ f ∈ Formalism.GradedWeylDivisibility.dualWeyl O N N ν, ∀ k : ℕ, evalPol O N (F k) f = (((∏ a : Fin N, (Polynomial.X + Polynomial.C (((ν a : ℤ) - (a : ℕ) : ℤ)))).coeff k : ℤ) : O) • f := by
  first | exact @GlobalTheory.CapelliCoeffs.capelli_coeff_dualWeyl | exact GlobalTheory.CapelliCoeffs.capelli_coeff_dualWeyl | (intros; apply GlobalTheory.CapelliCoeffs.capelli_coeff_dualWeyl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardKerIntegralCombinationEndoLePow
section
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.OEndDegree

theorem card_ker_le : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : Over (Sp k)) [GrpObj A] (act : OAct (𝓞 E) A) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (d : ℕ) (a : Fin d → 𝓞 E), ∃ C : ℕ, ∀ (n : Fin d → ℤ) (K : ℕ), (∀ i, (n i).natAbs ≤ K) → ∑ i, n i • a i ≠ 0 → Finite {x : 𝟙_ (Over (Sp k)) ⟶ A // x ≫ act.act (∑ i, n i • a i) = 1} ∧ Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ A // x ≫ act.act (∑ i, n i • a i) = 1} ≤ C * K ^ (2 * g) := by
  intro E _ _ k _ _ _ A _ act g hB hg d a
  haveI := hB.comm
  haveI : GeometricallyIntegral A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected
  haveI : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  obtain ⟨H, m, s, c, hH, hs, hc, hsec⟩ := GlobalTheory.T.exists_veryAmple_bound_ringAction_pullback E k A act g hB hg d a
  obtain ⟨C, hC⟩ := GlobalTheory.T.degree_le_of_pullback_le_pow_finiteEtale k A.left A.hom g hg H m s hH hs
  refine ⟨C * c ^ g, fun n K hn hb => ?_⟩
  have hK : 1 ≤ K := by
    rcases Nat.eq_zero_or_pos K with rfl | h
    · exfalso; apply hb
      refine Finset.sum_eq_zero fun i _ => ?_
      have := hn i
      rw [Nat.le_zero, Int.natAbs_eq_zero] at this
      rw [this, zero_smul]
    · exact h
  obtain ⟨hfin, het, hker⟩ := GlobalTheory.T.ringAction_finite_etale_abelianVariety_charZero E k A act g hB hg _ hb
  refine ⟨hker, ?_⟩
  have hrank := GlobalTheory.finrank_eq_card_kernel_points_of_etale k A hB (act.act (∑ i, n i • a i))
  have hφ : (act.act (∑ i, n i • a i)).left ≫ A.hom = A.hom := Over.w _
  have hq : 1 ≤ c * K ^ 2 := Nat.one_le_iff_ne_zero.2 (mul_ne_zero (by omega) (pow_ne_zero _ (by omega)))
  have h := hC (act.act (∑ i, n i • a i)).left hφ _ (c * K ^ 2) hq hrank (hsec n K hK hn)
  calc _ ≤ C * (c * K ^ 2) ^ g := h
    _ = C * c ^ g * K ^ (2 * g) := by ring

end GlobalTheory.OEndDegree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivOfGlobalSectionPowNumEquivMultipleStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartierDivOfGlobalSection_pow_numEquiv_multiple : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (hN : N.IsLB) (l m : ℕ) (s : (lbPow N l).Sec) (hs : genericPoint X ∈ nonzeroLocus s), 0 < m → (divOfSec (isLB_lbPow hN l) s hs).Eff ∧ QNum p N ((l : ℚ) / m) (qWeil (divOfSec (isLB_lbPow hN l) s hs) m) := by
  first | exact @GlobalTheory.PairStep.qNum_divOfSec | exact GlobalTheory.PairStep.qNum_divOfSec | (intros; apply GlobalTheory.PairStep.qNum_divOfSec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralCharacterSubquotientProductIrreduciblesStatement
section
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralCharacter_subquotient_productIrreducibles : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ x : IrrGL k, ∃ ω : kˣ →* ℂˣ, HasCentralChar x.rep ω) ∧ ∀ (t m : ℕ) (x : Fin t → IrrGL k) (hd : ∑ a, (x a).1 = m) (ω : Fin t → kˣ →* ℂˣ), (∀ a, HasCentralChar (x a).rep (ω a)) → ∀ (τ : IrrRep (GL (Fin m) k)) (ω' : kˣ →* ℂˣ), IsSubquotient τ.ρ (prodIrr x hd) → HasCentralChar τ.ρ ω' → ω' = ∏ a, ω a := by
  first | exact @GlobalTheory.GamMul.centralChar_subquotient_prodIrr | exact GlobalTheory.GamMul.centralChar_subquotient_prodIrr | (intros; apply GlobalTheory.GamMul.centralChar_subquotient_prodIrr <;> assumption)
end

