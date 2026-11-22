import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0469
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
import Formalism.SharpRestriction.Bundle0002
import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0477
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinEquivApply
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 10000000

namespace GlobalTheory.BKGal.CrisTensor

variable {l : ℕ} [Fact l.Prime] {LL : FinExt l}

section Zl

@[reducible] def zlT (T : QLat LL) : Module ℤ_[l] ↥T.L.T := Module.compHom _ (algebraMap ℤ_[l] ↥(OL LL))

@[reducible] def zlV (T : QLat LL) : Module ℤ_[l] T.V := Module.compHom _ (algebraMap ℤ_[l] ℚ_[l])

@[reducible] def zlB (Pl : LocPrime l) : Module ℤ_[l] Pl.R.B := Module.compHom _ (algebraMap ℤ_[l] ℚ_[l])

attribute [local instance] zlT zlV zlB

theorem towT (T : QLat LL) : IsScalarTower ℤ_[l] ↥(OL LL) ↥T.L.T :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

theorem towV (T : QLat LL) : IsScalarTower ℤ_[l] ℚ_[l] T.V :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

theorem towB (Pl : LocPrime l) : IsScalarTower ℤ_[l] ℚ_[l] Pl.R.B :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

attribute [local instance] towT towV towB

def incl (T : QLat LL) : ↥T.L.T →ₗ[ℤ_[l]] T.V where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' z x := by
    change ((algebraMap ℤ_[l] ↥(OL LL) z • x : ↥T.L.T) : T.V) = algebraMap ℤ_[l] ℚ_[l] z • (x : T.V)
    rw [Submodule.coe_smul, ← algebraMap_smul ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) z) (x : T.V),
      ← algebraMap_smul ↥LL.1 (algebraMap ℤ_[l] ℚ_[l] z) (x : T.V)]
    rfl

theorem exists_pow_mul_mem (LL : FinExt l) (a : ↥LL.1) :
    ∃ k : ℕ, (l : ↥LL.1) ^ k * a ∈ OL LL := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have h1 : IsAlgebraic ℚ_[l] a := Algebra.IsAlgebraic.isAlgebraic a
  have h2 : IsAlgebraic ℤ_[l] a := (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).2 h1
  obtain ⟨y, hy, hi⟩ := h2.exists_integral_multiple
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy
    (PadicInt.irreducible_p (p := l))
  refine ⟨k, ?_⟩
  have h3 := hi.smul ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l])
  rw [smul_smul, ← mul_assoc, Units.inv_mul, one_mul, Algebra.smul_def, map_pow, map_natCast] at h3
  exact h3

theorem exists_pow_smul_mem (T : QLat LL) (v : T.V) :
    ∃ n : ℕ, (l : ↥LL.1) ^ n • v ∈ T.L.T := by
  first
  | exact @_root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem
  | exact _root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem
  | (apply _root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem ..)

theorem zl_smul_V (T : QLat LL) (z : ℤ_[l]) (v : T.V) : z • v = algebraMap ℚ_[l] ↥LL.1 (z : ℚ_[l]) • v := by
  change algebraMap ℤ_[l] ℚ_[l] z • v = _
  rw [← algebraMap_smul ↥LL.1 (algebraMap ℤ_[l] ℚ_[l] z) v]
  rfl

theorem isLoc (T : QLat LL) : IsLocalizedModule (nonZeroDivisors ℤ_[l]) (incl T) := by
  refine ⟨fun s => ?_, fun y => ?_, fun {x₁ x₂} h => ⟨1, ?_⟩⟩
  · have hs : ((s : ℤ_[l]) : ℚ_[l]) ≠ 0 := by
      rw [Ne, PadicInt.coe_eq_zero]; exact nonZeroDivisors.coe_ne_zero s
    have hs' : algebraMap ℚ_[l] ↥LL.1 ((s : ℤ_[l]) : ℚ_[l]) ≠ 0 := by
      rwa [Ne, map_eq_zero_iff _ (algebraMap ℚ_[l] ↥LL.1).injective]
    refine (Module.End.isUnit_iff _).2 ⟨fun a b hab => ?_, fun a => ?_⟩
    · rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, zl_smul_V, zl_smul_V] at hab
      exact smul_right_injective _ hs' hab
    · refine ⟨(algebraMap ℚ_[l] ↥LL.1 ((s : ℤ_[l]) : ℚ_[l]))⁻¹ • a, ?_⟩
      rw [Module.algebraMap_end_apply, zl_smul_V, smul_smul, mul_inv_cancel₀ hs', one_smul]
  · obtain ⟨n, hn⟩ := exists_pow_smul_mem T y
    have hl : ((l : ℤ_[l]) ^ n) ∈ nonZeroDivisors ℤ_[l] :=
      mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero))
    refine ⟨(⟨_, hn⟩, ⟨_, hl⟩), ?_⟩
    show ((l : ℤ_[l]) ^ n) • y = (l : ↥LL.1) ^ n • y
    rw [zl_smul_V]
    congr 1
    simp
  · simp only [one_smul]; exact Subtype.ext h

theorem hbc (T : QLat LL) : IsBaseChange ℚ_[l] (incl T) :=
  (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ_[l]) ℚ_[l] (incl T)).1 (isLoc T)

variable {Bc : Type} [CommRing Bc] [Algebra ℤ_[l] Bc] {Pl : LocPrime l}

def ringLin (eB : Pl.R.B ≃+* Bc) (hz : ∀ z : ℤ_[l], eB (algebraMap ℚ_[l] Pl.R.B (z : ℚ_[l])) = algebraMap ℤ_[l] Bc z) :
    Bc ≃ₗ[ℤ_[l]] Pl.R.B :=
  { eB.symm.toAddEquiv with
    map_smul' := fun z b => by
      show eB.symm (z • b) = algebraMap ℤ_[l] ℚ_[l] z • eB.symm b
      rw [Algebra.smul_def z b, map_mul, Algebra.smul_def]
      congr 1
      rw [RingEquiv.symm_apply_eq]
      exact (hz z).symm }

def swapLat (T : QLat LL) : TW (↥(OL LL) ⊗[ℤ_[l]] Bc) T ≃ₗ[↥(OL LL)] ↥T.L.T ⊗[↥(OL LL)] (↥(OL LL) ⊗[ℤ_[l]] Bc) :=
  TensorProduct.comm ↥(OL LL) (↥(OL LL) ⊗[ℤ_[l]] Bc) ↥T.L.T

def cancelCoeff (T : QLat LL) : ↥T.L.T ⊗[↥(OL LL)] (↥(OL LL) ⊗[ℤ_[l]] Bc) ≃ₗ[↥(OL LL)] ↥T.L.T ⊗[ℤ_[l]] Bc :=
  AlgebraTensorModule.cancelBaseChange ℤ_[l] ↥(OL LL) ↥(OL LL) ↥T.L.T Bc

def changeRing (T : QLat LL) (eB : Pl.R.B ≃+* Bc)
    (hz : ∀ z : ℤ_[l], eB (algebraMap ℚ_[l] Pl.R.B (z : ℚ_[l])) = algebraMap ℤ_[l] Bc z) :
    ↥T.L.T ⊗[ℤ_[l]] Bc ≃ₗ[ℤ_[l]] Pl.R.B ⊗[ℤ_[l]] ↥T.L.T :=
  (TensorProduct.congr (LinearEquiv.refl ℤ_[l] ↥T.L.T) (ringLin eB hz)).trans (TensorProduct.comm ℤ_[l] ↥T.L.T Pl.R.B)

variable (Pl) in

def invertPrime (T : QLat LL) : Pl.R.B ⊗[ℤ_[l]] ↥T.L.T ≃ₗ[ℚ_[l]] T.V ⊗[ℚ_[l]] Pl.R.B :=
  (AlgebraTensorModule.cancelBaseChange ℤ_[l] ℚ_[l] ℚ_[l] Pl.R.B ↥T.L.T).symm.trans
     ((TensorProduct.congr (LinearEquiv.refl ℚ_[l] Pl.R.B) (hbc T).equiv).trans
       (TensorProduct.comm ℚ_[l] Pl.R.B T.V))

def addEquiv (T : QLat LL) (eB : Pl.R.B ≃+* Bc)
    (hz : ∀ z : ℤ_[l], eB (algebraMap ℚ_[l] Pl.R.B (z : ℚ_[l])) = algebraMap ℤ_[l] Bc z) :
    TW (↥(OL LL) ⊗[ℤ_[l]] Bc) T ≃+ T.V ⊗[ℚ_[l]] Pl.R.B :=
  (((swapLat T).trans (cancelCoeff T)).toAddEquiv.trans (changeRing T eB hz).toAddEquiv).trans (invertPrime Pl T).toAddEquiv

theorem addEquiv_tmul (T : QLat LL) (eB : Pl.R.B ≃+* Bc)
    (hz : ∀ z : ℤ_[l], eB (algebraMap ℚ_[l] Pl.R.B (z : ℚ_[l])) = algebraMap ℤ_[l] Bc z)
    (o : ↥(OL LL)) (b : Bc) (x : ↥T.L.T) :
    addEquiv T eB hz ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = (((o • x : ↥T.L.T)) : T.V) ⊗ₜ[ℚ_[l]] eB.symm b := by
  simp [addEquiv, swapLat, cancelCoeff, changeRing, invertPrime, ringLin, IsBaseChange.equiv_tmul, incl]

end Zl

variable {Pl : LocPrime l}

theorem addEquiv_smul (T : QLat LL) (eB : Pl.R.B ≃+* Per.Bcris l)
    (hz : ∀ z : ℤ_[l], eB (algebraMap ℚ_[l] Pl.R.B (z : ℚ_[l])) = algebraMap ℤ_[l] (Per.Bcris l) z)
    (c : ↥(OL LL)) (w : TW (OB l ↥(OL LL)) T) :
    addEquiv T eB hz (c • w) = c • addEquiv T eB hz w := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add x y hx hy =>
    rw [smul_add, map_add, map_add]
    exact (congrArg₂ (· + ·) hx hy).trans (smul_add c _ _).symm
  | tmul y x =>
    rw [TensorProduct.smul_tmul']
    induction y using TensorProduct.induction_on with
    | zero => simp only [smul_zero, zero_tmul, map_zero]
    | add y₁ y₂ h₁ h₂ =>
      rw [smul_add, add_tmul, add_tmul, map_add, map_add]
      exact (congrArg₂ (· + ·) h₁ h₂).trans (smul_add c _ _).symm
    | tmul o b =>
      have e : (((c • o) • x : ↥T.L.T) : T.V) = (c : ↥LL.1) • ((o • x : ↥T.L.T) : T.V) := by
        rw [smul_assoc, Submodule.coe_smul, ← algebraMap_smul ↥LL.1 c]
        rfl
      rw [TensorProduct.smul_tmul', addEquiv_tmul, addEquiv_tmul, e]
      exact (TensorProduct.smul_tmul' (c : ↥LL.1) _ _).symm

def linEquiv (T : QLat LL) (eB : Pl.R.B ≃+* Per.Bcris l)
    (hz : ∀ z : ℤ_[l], eB (algebraMap ℚ_[l] Pl.R.B (z : ℚ_[l])) = algebraMap ℤ_[l] (Per.Bcris l) z) :
    TW (OB l ↥(OL LL)) T ≃ₗ[↥(OL LL)] T.V ⊗[ℚ_[l]] Pl.R.B :=
  (addEquiv T eB hz).toLinearEquiv (addEquiv_smul T eB hz)

theorem linEquiv_apply (T : QLat LL) (eB : Pl.R.B ≃+* Per.Bcris l)
    (hz : ∀ z : ℤ_[l], eB (algebraMap ℚ_[l] Pl.R.B (z : ℚ_[l])) = algebraMap ℤ_[l] (Per.Bcris l) z)
    (w : TW (OB l ↥(OL LL)) T) : linEquiv T eB hz w = addEquiv T eB hz w := rfl

theorem linEquiv_one (T : QLat LL) (eB : Pl.R.B ≃+* Per.Bcris l)
    (hz : ∀ z : ℤ_[l], eB (algebraMap ℚ_[l] Pl.R.B (z : ℚ_[l])) = algebraMap ℤ_[l] (Per.Bcris l) z)
    (x : ↥T.L.T) :
    linEquiv T eB hz ((1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x) = (x : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.B) := by
  rw [linEquiv_apply, Algebra.TensorProduct.one_def, addEquiv_tmul, one_smul, map_one]

theorem linEquiv_act (T : QLat LL) (eB : Pl.R.B ≃+* Per.Bcris l)
    (hz : ∀ z : ℤ_[l], eB (algebraMap ℚ_[l] Pl.R.B (z : ℚ_[l])) = algebraMap ℤ_[l] (Per.Bcris l) z)
    (hact : ∀ (g : GQ l) (b : Pl.R.B), eB (Pl.actQ g b) = Per.σB g (eB b))
    (g : Gl l) (w : TW (OB l ↥(OL LL)) T) :
    linEquiv T eB hz (actB (sQ l) T g w) = actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (linEquiv T eB hz w) := by
  rw [linEquiv_apply, linEquiv_apply]
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy =>
    rw [map_add, map_add, map_add, map_add]
    exact congrArg₂ (· + ·) hx hy
  | tmul y x =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [zero_tmul, map_zero]
    | add y₁ y₂ h₁ h₂ =>
      rw [add_tmul, map_add, map_add, map_add, map_add]
      exact congrArg₂ (· + ·) h₁ h₂
    | tmul o b =>
      have h1 : actB (sQ l) T g ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) =
          (o ⊗ₜ[ℤ_[l]] Per.σB (g : GQ l) b) ⊗ₜ[↥(OL LL)] T.actT g x := rfl
      rw [h1, addEquiv_tmul, addEquiv_tmul]
      simp only [actVB, AlgebraTensorModule.map_tmul]
      congr 1
      · rw [Submodule.coe_smul, Submodule.coe_smul, ← algebraMap_smul ↥LL.1 o, ← algebraMap_smul ↥LL.1 o,
          map_smul]
        rfl
      · rw [LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply, AlgEquiv.coe_toAlgHom, Pl.PD_actB,
          RingEquiv.symm_apply_eq, hact, RingEquiv.apply_symm_apply]

theorem linEquiv_frob (T : QLat LL) (eB : Pl.R.B ≃+* Per.Bcris l)
    (hz : ∀ z : ℤ_[l], eB (algebraMap ℚ_[l] Pl.R.B (z : ℚ_[l])) = algebraMap ℤ_[l] (Per.Bcris l) z)
    (hfr : ∀ b : Pl.R.B, eB (Pl.φB b) = Per.φB l (eB b))
    (w : TW (OB l ↥(OL LL)) T) :
    linEquiv T eB hz (TWmap (frobOB l ↥(OL LL)) T w) =
      φVB (LL := ↥LL.1) (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (linEquiv T eB hz w) := by
  rw [linEquiv_apply, linEquiv_apply]
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy =>
    rw [map_add, map_add, map_add, map_add]
    exact congrArg₂ (· + ·) hx hy
  | tmul y x =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [zero_tmul, map_zero]
    | add y₁ y₂ h₁ h₂ =>
      rw [add_tmul, map_add, map_add, map_add, map_add]
      exact congrArg₂ (· + ·) h₁ h₂
    | tmul o b =>
      have h1 : TWmap (frobOB l ↥(OL LL)) T ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) =
          (o ⊗ₜ[ℤ_[l]] Per.φB l b) ⊗ₜ[↥(OL LL)] x := rfl
      rw [h1, addEquiv_tmul, addEquiv_tmul]
      simp only [φVB, AlgebraTensorModule.map_tmul, LinearMap.id_apply]
      congr 1
      rw [AlgHom.toLinearMap_apply, Pl.PD_φ, RingEquiv.symm_apply_eq, hfr, RingEquiv.apply_symm_apply]

end GlobalTheory.BKGal.CrisTensor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentOfMutualSpanOfIndep
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory

theorem linIndep_of_mutual_span_of_indep :
    ∀ (R W : Type) [CommRing R] [AddCommGroup W] (act : R →+ (W →+ W)),
      (∀ (r s : R) (w : W), act (r * s) w = act r (act s w)) → (∀ w : W, act 1 w = w) →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (b f : ι → W),
        (∀ d : ι → R, ∑ k, act (d k) (b k) = 0 → ∀ k, d k = 0) →
        (∀ i, ∃ d : ι → R, f i = ∑ k, act (d k) (b k)) →
        (∀ k, ∃ d : ι → R, b k = ∑ i, act (d i) (f i)) →
        ∀ d : ι → R, ∑ i, act (d i) (f i) = 0 → ∀ i, d i = 0 := by
  intro R W _ _ act hmul hone ι _ _ b f hb hf hbf d hd
  letI : Module R W :=
    { smul := fun r w => act r w
      one_smul := hone
      mul_smul := fun r s w => hmul r s w
      smul_zero := fun r => map_zero (act r)
      smul_add := fun r x y => map_add (act r) x y
      add_smul := fun r s w => by
        show act (r + s) w = act r w + act s w
        rw [map_add, AddMonoidHom.add_apply]
      zero_smul := fun w => by
        show act 0 w = 0
        rw [map_zero, AddMonoidHom.zero_apply] }
  have hs : ∀ (r : R) (w : W), act r w = r • w := fun _ _ => rfl
  simp only [hs] at hb hf hbf hd
  choose P hP using hf
  choose Q hQ using hbf
  have expand : ∀ c : ι → R,
      ∑ i, c i • f i = ∑ k, (Matrix.vecMul c (Matrix.of P)) k • b k := by
    intro c
    simp only [hP, Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Matrix.of_apply,
      Finset.sum_smul]
    rw [Finset.sum_comm]
  have hQP : Matrix.of Q * Matrix.of P = 1 := by
    ext k k'
    have h0 : ∑ k'', ((Matrix.vecMul (Q k) (Matrix.of P)) k'' - (1 : Matrix ι ι R) k k'') • b k''
        = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ← expand, ← hQ, Matrix.one_apply,
        ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]
    have := hb _ h0 k'
    rw [sub_eq_zero] at this
    rw [← this, Matrix.mul_apply]
    simp [Matrix.vecMul, dotProduct]
  have hPQ : Matrix.of P * Matrix.of Q = 1 := mul_eq_one_comm.mp hQP
  have he : Matrix.vecMul d (Matrix.of P) = 0 := by
    rw [expand] at hd
    funext k
    exact hb _ hd k
  have : d = 0 := by
    rw [← Matrix.vecMul_one d, ← hPQ, ← Matrix.vecMul_vecMul, he, Matrix.zero_vecMul]
  intro i
  rw [this]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesConditionTwoThree
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLinkAdmF

theorem placesOver_three_nonempty (D : D7) : (placesOver D.host.E 3).Nonempty := by
  have hl : Nat.Prime 3 := Nat.prime_three
  have hne : ((3 : ℕ) : 𝓞 D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have hnu : ¬ IsUnit ((3 : ℕ) : 𝓞 D.host.E) := by
    intro h
    have h1 := h.map (Algebra.norm ℤ)
    have h2 : Algebra.norm ℤ ((3 : ℕ) : 𝓞 D.host.E) = ((3 : ℕ) : ℤ) ^ Module.finrank ℤ (𝓞 D.host.E) := by
      rw [← Algebra.norm_algebraMap (R := ℤ) (S := 𝓞 D.host.E) ((3 : ℕ) : ℤ)]; simp
    rw [h2, isUnit_pow_iff Module.finrank_pos.ne', Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at h1
    exact hl.one_lt.ne' h1
  obtain ⟨M, hM, hlM⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hnu)
  exact ⟨⟨M, hM.isPrime, fun h => hne (by simp [h] at hlM)⟩, hlM⟩

theorem sumOver_three_even (D : D7) (c : ℝ) :
    TwistedPlaces.sumOver D 3 (fun _ => c / ((placesOver D.host.E 3).ncard : ℝ)) = c := by
  have hfin : (placesOver D.host.E 3).Finite := FamilyRepresentationConstants.placesOver_finite D.host.E 3 (by norm_num)
  have hpos : 0 < (placesOver D.host.E 3).ncard :=
    (Set.ncard_pos hfin).2 (placesOver_three_nonempty D)
  unfold TwistedPlaces.sumOver
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_const, nsmul_eq_mul,
    ← Set.ncard_eq_toFinset_card _ hfin]
  have : ((placesOver D.host.E 3).ncard : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  field_simp

theorem localBoundTableAllPrimes_conditionTwoThree : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.SmallPrimeLengthBound L tf C → TwistedPlaces.SmallPrimeLengthBound L (tab L X tf C) C := by
  intro D L P X C tf _ hF i hi hl
  have hFi := hF i hi hl
  by_cases h2 : D.nd.l i ∈ D.host.small
  · have hlen : (tab L X tf C).len i = fun _ => 0 := by
      funext lam
      simp only [tab, if_pos h2]
    have hBB : (tab L X tf C).BB i = TwistedPlaces.sumOver D (D.nd.l i) (tf.len i) + tf.BB i := by
      simp only [tab, if_pos h2]
    show TwistedPlaces.sumOver D _ ((tab L X tf C).len i) + (tab L X tf C).BB i ≤ _
    rw [hlen, hBB]
    have h0 : TwistedPlaces.sumOver D (D.nd.l i) (fun _ => (0 : ℝ)) = 0 := by simp [TwistedPlaces.sumOver]
    rw [h0, zero_add]
    exact hFi
  · have h3 : D.nd.l i = 3 := hl.resolve_left h2
    have hq : D.host.q ≠ 3 := D.host.q_ne_three
    have hd : D.host.d ≠ 3 := by
      have := D.host.hyp.2.2.2.1
      omega
    have hlen : (tab L X tf C).len i =
        fun _ => (TwistedPlaces.sumOver D 3 (tf.len i) + tf.BB i) / ((placesOver D.host.E 3).ncard : ℝ) := by
      funext lam
      simp only [tab, if_neg h2, if_pos h3]
    have hBB : (tab L X tf C).BB i = 0 := by
      have h1 : ¬ (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) := by omega
      have hR : ¬ KillingConditions.RangeAD L X.exc (D.nd.l i) := fun hr => hr.1 (Or.inr h3)
      simp only [tab, if_neg h2, if_neg h1, if_neg hR]
    show TwistedPlaces.sumOver D (D.nd.l i) ((tab L X tf C).len i) + (tab L X tf C).BB i ≤ _
    have hFi' : TwistedPlaces.sumOver D (D.nd.l i) (tf.len i) + tf.BB i ≤ _ := hFi
    rw [h3] at hFi'
    rw [hlen, hBB, h3, sumOver_three_even, add_zero]
    exact hFi'

end GlobalTheory.NLinkAdmF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesRamifiedTypePrimes
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem localBoundTableAllPrimes_ramified_typePrimes : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L),
    Concl L P X C → TwistedPlaces.RamifiedPrimeLengthBound L (tab L X tf C) C ∧ TwistedPlaces.GeneratorPrimeEtaBound L (tab L X tf C) C := by
  intro D L P X C tf hC
  refine ⟨⟨?_, hC.small.2.2.2.2.1⟩, ?_⟩
  · intro i _ hl
    obtain ⟨hq, hd, hq8, hd16, -⟩ := D.host.hyp
    have h3q := D.host.q_ne_three
    have h2 : D.nd.l i ∉ D.host.small := UpperTheory.Small.not_mem_of_qd D.host hl
    have h3 : D.nd.l i ≠ 3 := by rcases hl with h | h <;> rw [h] <;> omega
    have hR : ¬ KillingConditions.RangeAD L X.exc (D.nd.l i) := fun h => h.2.1 hl
    have hlen : (tab L X tf C).len i = fun _ => 0 := by
      funext lam
      simp only [tab, h2, h3, hR, if_false]
    have hBB : (tab L X tf C).BB i = TwistedPlaces.midG L C (D.nd.l i) := by
      simp only [tab, h2, hl, if_false, if_true]
    rw [hlen, hBB]
    simp [TwistedPlaces.sumOver]
  · intro j hj l hl
    exact ⟨hC.typ j hj l hl, le_rfl⟩

end GlobalTheory.NLink
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesSizeConditionFive
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem adm5_tab : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L),
    Concl L P X C → TwistedPlaces.adm5 L (tab L X tf C) C := by
  classical
  intro D L P X C tf h i hi hl
  obtain ⟨h2, hq, hd, hg⟩ := hl
  have hqd : ¬ (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) := by tauto
  have hR0 : 0 ≤ C * D.R.f * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * (TwistedPlaces.large₂ L) ^ 2 := by
    have := h.pos
    positivity
  show (if D.nd.l i ∈ D.host.small then TwistedPlaces.sumOver D (D.nd.l i) (tf.len i) + tf.BB i
    else if D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d then TwistedPlaces.midG L C (D.nd.l i)
    else if KillingConditions.RangeAD L X.exc (D.nd.l i) then KillingConditions.supZ i (X.errorBoundHub i) else 0) ≤ _
  rw [if_neg h2, if_neg hqd]
  split_ifs with hR
  · unfold KillingConditions.supZ
    split_ifs with hne
    · exact Finset.sup'_le hne _ (fun π hπ => h.bb i hi hg hR π hπ)
    · exact hR0
  · exact hR0

end GlobalTheory.NLink
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesSizeConditionSix
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem adm6_tab : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L),
    Concl L P X C → TwistedPlaces.adm6 L (tab L X tf C) := by
  intro D L P X C tf hC
  refine ⟨?_, ?_⟩
  · intro i hi π hπ
    have hk := ((hC.kill i hi).1 π hπ).2
    show (Br.sPi D.loc D.nbr i (X.ρ i) π : ℝ) + TwistedPlaces.epsL (D.nd.l i) ≤ _
    unfold TwistedPlaces.epsL at hk ⊢
    have : (2 : ℝ) / (D.nd.l i : ℝ) ^ 2 = 1 / (D.nd.l i : ℝ) ^ 2 + 1 / (D.nd.l i : ℝ) ^ 2 := by ring
    rw [this]
    linarith
  · intro j _ l _
    show TwistedPlaces.epsL l + TwistedPlaces.epsL l ≤ 2 / (l : ℝ) ^ 2
    unfold TwistedPlaces.epsL
    apply le_of_eq
    ring

end GlobalTheory.NLink
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesVanishingExcluded
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem largePrimeLengthVanishing_and_exceptionalBounded_tab : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ)
    (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.LargePrimeLengthVanishing L (tab L X tf C) ∧ TwistedPlaces.ExceptionalPrimesBounded L (tab L X tf C) := by
  intro D L P X C tf h
  obtain ⟨h3, hq, hd, -, -, hsl⟩ := h.small
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i _ hl
    obtain ⟨hlt, -, hexc⟩ := hl
    have hexc' : D.nd.l i ∉ X.exc := hexc
    have h2 : D.nd.l i ∉ D.host.small := fun he => by linarith [hsl _ he]
    have h3' : D.nd.l i ≠ 3 := by
      rintro he; rw [he] at hlt; push_cast at hlt; linarith
    have hq' : D.nd.l i ≠ D.host.q := by
      rintro he; rw [he] at hlt; linarith
    have hd' : D.nd.l i ≠ D.host.d := by
      rintro he; rw [he] at hlt; linarith
    have hR : ¬ KillingConditions.RangeAD L X.exc (D.nd.l i) := fun hr => hr.2.2 ⟨hlt, hexc'⟩
    refine ⟨fun lam _ => ?_, ?_⟩
    · simp only [tab, h2, h3', hR, if_false]
    · simp only [tab, h2, hR, if_false]
      rw [if_neg (by rintro (he | he) <;> contradiction)]
  · exact h.exc.1
  · exact h.exc.2

end GlobalTheory.NLink
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalFieldsAtAuxiliaryPrimesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_fields_at_auxiliary_primes : ∀ D : D7, EmbeddingTypeJumps.Conclusion0 D ∧ EmbeddingTypeJumps.Conclusion1 D := by
  first | exact @GlobalTheory.LocalFieldsQD.main | exact GlobalTheory.LocalFieldsQD.main | (intros; apply GlobalTheory.LocalFieldsQD.main <;> assumption)
end

