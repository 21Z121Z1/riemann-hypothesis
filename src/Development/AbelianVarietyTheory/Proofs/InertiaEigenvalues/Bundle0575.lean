import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0562
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0541
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0815
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0569
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0571
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0515
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0504
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0469
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0563
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineOfInertiaTrivialOnCrystallinePeriods
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0570
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualExponentialKernelCyclotomicCocycles
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinMuPowSmulFrobeniusMemAinfStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_mu_pow_smul_frobenius_mem_ainf : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (α β : ℕ), (∀ m ∈ P.L, E K l e ^ α • m ∈ P.M) → (∀ m ∈ P.M, E K l e ^ β • m ∈ P.L) → ∀ ε δ : OCb l, IsEps ε → δ ^ l = ε → ∀ (y : ME P), y.1 ∈ P.EM α → ∀ m₀, phiW t ϖ P m₀ - m₀ = toW t ϖ P y → inclO l O (1 ⊗ₜ (muOf δ ^ (β + α))) • m₀ ∈ MA P ∧ inclO l O (1 ⊗ₜ (muOf ε ^ (β + α))) • phiW t ϖ P m₀ ∈ LA t ϖ P := by
  first | exact @GlobalTheory.BKGal.LiftStep.mu_pow_smul_mem | exact GlobalTheory.BKGal.LiftStep.mu_pow_smul_mem | (intros; apply GlobalTheory.BKGal.LiftStep.mu_pow_smul_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CauchyIdentitySchurFormalDegree
section
noncomputable section

open MvPolynomial

namespace GlobalTheory.JSW.CauchyGlue

theorem map_jtDet {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (m : ℕ) (h : ℕ → A)
    (l : Fin m → ℕ) : f (jtDet m h l) = jtDet m (fun k => f (h k)) l := by
  rw [jtDet, jtDet, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem map_alternant {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (m : ℕ) (μ : Fin m → ℕ) :
    MvPolynomial.map f (alternant A m μ) = alternant B m μ := by
  rw [alternant, alternant, RingHom.map_det]
  congr 1
  ext i j
  simp

theorem alternant_eq_det (A : Type*) [CommRing A] (m : ℕ) (μ : Fin m → ℕ) :
    alternant A m μ = Matrix.det (Matrix.of fun i j : Fin m => (X i : MvPolynomial (Fin m) A) ^ μ j) := by
  rw [alternant, ← Matrix.det_transpose]
  rfl

theorem alternant_staircase_ne_zero (m : ℕ) : alternant ℂ m (staircase m) ≠ 0 := by
  have e : (Matrix.of fun i j : Fin m => (X j : MvPolynomial (Fin m) ℂ) ^ staircase m i) =
      (Matrix.transpose (Matrix.vandermonde (fun j : Fin m => (X j : MvPolynomial (Fin m) ℂ)))).submatrix Fin.revPerm id := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.vandermonde_apply,
      Fin.revPerm_apply, id, staircase, Fin.val_rev]
    congr 1
    omega
  rw [alternant, e, Matrix.det_permute, Matrix.det_transpose]
  refine mul_ne_zero ?_ ?_
  · rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin m))) with h | h <;> simp [h]
  · exact (Matrix.det_vandermonde_ne_zero_iff).2 (MvPolynomial.X_injective)

theorem bialt_int (m : ℕ) (l : Fin m → ℕ) (hl : Antitone l) :
    schur m l * alternant ℤ m (staircase m) = alternant ℤ m (fun i => l i + staircase m i) := by
  simp only [alternant_eq_det, staircase]
  rw [schur_mul_det_eq_det m l hl]
  congr 1
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.of_apply]
  congr 1
  have := j.2
  omega

theorem cauchy_formal : ∀ {m n : ℕ} (hmn : m ≤ n) (α : Fin n → ℂ) (β : Fin m → ℂ) (d : ℕ),
    ∑ l ∈ GlobalTheory.JSW.antiParts m d, GlobalTheory.JSW.schurAt (GlobalTheory.JSW.padTo hmn l) α * GlobalTheory.JSW.schurAt l β =
      ∑ k ∈ Finset.Nat.antidiagonalTuple m d,
        ∏ j, MvPolynomial.eval₂ (Int.castRingHom ℂ) α (MvPolynomial.hsymm (Fin n) ℤ (k j)) * β j ^ (k j) := by
  intro m n hmn α β d
  set hC : ℕ → ℂ := fun k => eval₂ (Int.castRingHom ℂ) α (hsymm (Fin n) ℤ k) with hhC
  have hA := GlobalTheory.T.jacobi_trudi_alternant_expansion (A := ℂ) m d hC
  have hpad : ∀ l : Fin m → ℕ, schurAt (padTo hmn l) α = jtDet m hC l := by
    intro l
    rw [schurAt, GlobalTheory.T.schurPolynomial_padZeros_eq_jacobiTrudiDeterminant hmn l, ← MvPolynomial.coe_eval₂Hom, map_jtDet]
    rfl
  have hbi : ∀ l ∈ antiParts m d, alternant ℂ m (fun i => l i + staircase m i) =
      MvPolynomial.map (Int.castRingHom ℂ) (schur m l) * alternant ℂ m (staircase m) := by
    intro l hl
    have := congrArg (MvPolynomial.map (Int.castRingHom ℂ)) (bialt_int m l (mem_antiParts.1 hl).2)
    rw [map_mul, map_alternant, map_alternant] at this
    exact this.symm
  have hR : ∑ l ∈ antiParts m d, C (jtDet m hC l) * alternant ℂ m (fun i => l i + staircase m i) =
      alternant ℂ m (staircase m) *
        ∑ l ∈ antiParts m d, C (jtDet m hC l) * MvPolynomial.map (Int.castRingHom ℂ) (schur m l) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [hbi l hl]
    ring
  rw [hR] at hA
  have hP := mul_left_cancel₀ (alternant_staircase_ne_zero m) hA
  have hE := congrArg (MvPolynomial.eval β) hP
  simp only [map_sum, map_prod, map_mul, eval_C, eval_X, map_pow, MvPolynomial.eval_map] at hE
  refine (Finset.sum_congr rfl fun l _ => ?_).trans hE.symm
  rw [hpad]
  rfl

end GlobalTheory.JSW.CauchyGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryMemCocyclesOddPrime
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.CobCont

theorem inj1 : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL),
    Function.Injective (fun x : ↥T.L.T => (1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x) := GlobalTheory.T.one_tmul_bcris_galoisLattice_injective

theorem nbhd : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (U : Set T.V), U ∈ nhds (0 : T.V) →
    ∃ m : ℕ, ∀ x ∈ T.L.T, ((l : ↥LL.1) ^ m) • x ∈ U := GlobalTheory.T.galoisLattice_prime_pow_smul_tendsto_zero

theorem cont1 : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (LL : FinExt l) (T : QLat LL) (b : TW (OB l ↥(OL LL)) T)
    (c : Gl l → T.V), IsCobOf (sQ l) T b c → ∀ m : ℕ, ∀ᶠ g in nhds (1 : Gl l),
      ∃ x ∈ T.L.T, c g = ((l : ↥LL.1) ^ m) • x := GlobalTheory.T.bcrisCoboundary_eventually_mem_prime_pow_lattice

variable {l : ℕ} [Fact l.Prime] {LL : FinExt l}

theorem o_smul_mem (T : QLat LL) (o : ↥(OL LL)) (x : T.V) (hx : x ∈ T.L.T) : (o : ↥LL.1) • x ∈ T.L.T := by
  have := T.L.T.smul_mem o hx
  rwa [← algebraMap_smul ↥LL.1 o x] at this

theorem lpow_smul_mem (T : QLat LL) (n : ℕ) (x : T.V) (hx : x ∈ T.L.T) : (l : ↥LL.1) ^ n • x ∈ T.L.T := by
  have := o_smul_mem T ((l : ↥(OL LL)) ^ n) x hx
  simpa using this

theorem exists_pow_smul_mem (T : QLat LL) (v : T.V) : ∃ n : ℕ, (l : ↥LL.1) ^ n • v ∈ T.L.T := by
  first
  | exact @_root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem
  | exact _root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem
  | (apply _root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem ..)

theorem actB_tmul_one (T : QLat LL) (g : Gl l) (x : ↥T.L.T) :
    actB (sQ l) T g ((1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x) = (1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] T.actT g x := by
  simp [actB, TWact]

theorem galOB_mul' {O : Type} [CommRing O] [Algebra ℤ_[l] O] (g h : GQ l) (o : OB l O) :
    galOB O (g * h) o = galOB O g (galOB O h o) := by
  induction o using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a w =>
    exact congrArg (fun z => a ⊗ₜ[ℤ_[l]] z) ((GlobalTheory.MemLoc.ActLaws.act_laws l).1 _ _ w)

theorem actT_mul (T : QLat LL) (g h : Gl l) (x : ↥T.L.T) : T.actT (g * h) x = T.actT g (T.actT h x) :=
  Subtype.ext (by
    show T.ρ (g * h) (x : T.V) = T.ρ g (T.ρ h x)
    rw [map_mul]; rfl)

theorem actB_tmul (T : QLat LL) (g : Gl l) (o : OB l ↥(OL LL)) (x : ↥T.L.T) :
    actB (sQ l) T g (o ⊗ₜ[↥(OL LL)] x) = (galOB ↥(OL LL) (sQ l g) o) ⊗ₜ[↥(OL LL)] T.actT g x :=
  TensorProduct.map_tmul _ _ _ _

set_option maxHeartbeats 1000000 in
theorem actB_mul_a (T : QLat LL) (g h : Gl l) (o : OB l ↥(OL LL)) (x : ↥T.L.T) :
    actB (sQ l) T (g * h) (o ⊗ₜ[↥(OL LL)] x) = actB (sQ l) T g (actB (sQ l) T h (o ⊗ₜ[↥(OL LL)] x)) := by
  have e1 := actB_tmul T (g*h) o x
  have e2 := actB_tmul T h o x
  have e3 := actB_tmul T g (galOB _ (sQ l h) o) (T.actT h x)
  refine e1.trans (Eq.trans ?_ ((congrArg (actB (sQ l) T g) e2).trans e3).symm)
  refine congrArg₂ (fun a b => a ⊗ₜ[↥(OL LL)] b) ?_ (actT_mul T g h x)
  rw [map_mul]
  exact galOB_mul' _ _ o

theorem actB_mul (T : QLat LL) (g h : Gl l) (y : TW (OB l ↥(OL LL)) T) :
    actB (sQ l) T (g * h) y = actB (sQ l) T g (actB (sQ l) T h y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul o x => exact actB_mul_a T g h o x

theorem abs_cocycle {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (Fg Fh Fgh : M →ₗ[R] M)
    (hmul : ∀ y, Fgh y = Fg (Fh y)) (b y1 y2 y3 : M) (r : R) (e1 : y1 = r • (Fg b - b))
    (e2 : y2 = r • (Fh b - b)) (e3 : y3 = r • (Fgh b - b)) : y3 = Fg y2 + y1 := by
  rw [e3, e2, e1, hmul, map_smul, map_sub, ← smul_add]
  congr 1
  abel

theorem pow_le_mem (T : QLat LL) {k n : ℕ} (hk : k ≤ n) (v : T.V) (hv : (l : ↥LL.1) ^ k • v ∈ T.L.T) :
    (l : ↥LL.1) ^ n • v ∈ T.L.T := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pow_add, mul_comm, mul_smul]
  exact lpow_smul_mem T _ _ hv

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem cocycle (T : QLat LL) (b : TW (OB l ↥(OL LL)) T) (c : Gl l → T.V) (hc : IsCobOf (sQ l) T b c)
    (g h : Gl l) : c (g * h) = c g + T.ρ g (c h) := by
  obtain ⟨n1, h1⟩ := exists_pow_smul_mem T (c g)
  obtain ⟨n2, h2⟩ := exists_pow_smul_mem T (c h)
  obtain ⟨n3, h3⟩ := exists_pow_smul_mem T (c (g * h))
  have m1 := pow_le_mem T (n := n1 + n2 + n3) (by omega) _ h1
  have m2 := pow_le_mem T (n := n1 + n2 + n3) (by omega) _ h2
  have m3 := pow_le_mem T (n := n1 + n2 + n3) (by omega) _ h3
  have e1 := hc g _ ⟨_, m1⟩ rfl
  have e2 := hc h _ ⟨_, m2⟩ rfl
  have e3 := hc (g * h) _ ⟨_, m3⟩ rfl
  have key : (⟨_, m3⟩ : ↥T.L.T) = T.actT g ⟨_, m2⟩ + ⟨_, m1⟩ := by
    apply inj1 l LL T
    have := abs_cocycle (actB (sQ l) T g) (actB (sQ l) T h) (actB (sQ l) T (g * h)) (actB_mul T g h) _ _ _ _ _ e1 e2 e3
    refine this.trans ?_
    refine (congrArg (· + _) (actB_tmul_one T g _)).trans ?_
    exact (TensorProduct.tmul_add _ _ _).symm
  have key' := congrArg (fun z : ↥T.L.T => (z : T.V)) key
  simp only [Submodule.coe_add] at key'
  change (l : ↥LL.1) ^ (n1 + n2 + n3) • c (g * h) =
    T.ρ g ((l : ↥LL.1) ^ (n1 + n2 + n3) • c h) + (l : ↥LL.1) ^ (n1 + n2 + n3) • c g at key'
  rw [map_smul, ← smul_add] at key'
  have hl : ((l : ↥LL.1) ^ (n1 + n2 + n3)) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  rw [smul_right_injective T.V hl key', add_comm]

theorem c_one (T : QLat LL) (b : TW (OB l ↥(OL LL)) T) (c : Gl l → T.V) (hc : IsCobOf (sQ l) T b c) :
    c 1 = 0 := by
  have h := cocycle T b c hc 1 1
  rw [mul_one, map_one, Module.End.one_apply] at h
  exact left_eq_add.1 h

theorem contAt_one (hl2 : l ≠ 2) (T : QLat LL) (b : TW (OB l ↥(OL LL)) T) (c : Gl l → T.V)
    (hc : IsCobOf (sQ l) T b c) : ContinuousAt c 1 := by
  rw [ContinuousAt, c_one T b c hc]
  intro U hU
  obtain ⟨m, hm⟩ := nbhd l LL T U hU
  rw [Filter.mem_map]
  filter_upwards [cont1 l hl2 LL T b c hc m] with g hg
  obtain ⟨x, hx, e⟩ := hg
  rw [Set.mem_preimage, e]
  exact hm x hx

theorem main : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (LL : FinExt l) (T : QLat LL) (b : TW (OB l ↥(OL LL)) T)
    (c : Gl l → T.V), IsCobOf (sQ l) T b c → c ∈ continuousCocycles T.ρ := by
  intro l _ hl2 LL T b c hc
  refine ⟨?_, cocycle T b c hc⟩
  have h1 := contAt_one hl2 T b c hc
  have hρ : ∀ g : Gl l, Continuous (T.ρ g) := fun g =>
    IsModuleTopology.continuous_of_linearMap (T.ρ g)
  rw [continuous_iff_continuousAt]
  intro g0
  have e : c = fun g => c g0 + T.ρ g0 (c (g0⁻¹ * g)) := by
    funext g
    rw [← cocycle T b c hc, mul_inv_cancel_left]
  rw [e]
  refine continuousAt_const.add ((hρ g0).continuousAt.comp ?_)
  refine ContinuousAt.comp (f := fun g => g0⁻¹ * g) ?_ (continuous_const.mul continuous_id).continuousAt
  simpa using h1

end GlobalTheory.CobCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComparisonMatrixExistsOnDisc
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.RelEx

theorem map_smul_ring {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {m n : Type} (a : R)
    (M : Matrix m n R) : (a • M).map φ = φ a • M.map φ := by
  ext i j; simp

theorem alg {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (N : ℕ)
    (A Zf Zfi G Y Zg : Matrix n n R) (gE fE wi c lam : R) (hZ : Zf * Zfi = 1) (hAG : A * G = lam • Y)
    (hw : gE * wi = fE) (hc : c * lam = 1) :
    gE ^ N • (A * Zf * ((wi ^ N * c) • (Zfi * G * Zg))) = fE ^ N • (Y * Zg) := by
  have h1 : A * Zf * (Zfi * G * Zg) = lam • (Y * Zg) := by
    rw [Matrix.mul_assoc A Zf, ← Matrix.mul_assoc Zf, ← Matrix.mul_assoc Zf, hZ, Matrix.one_mul,
      ← Matrix.mul_assoc, hAG, Matrix.smul_mul]
  rw [Matrix.mul_smul, h1, smul_smul, smul_smul]
  congr 1
  calc gE ^ N * (wi ^ N * c) * lam = (gE * wi) ^ N * (c * lam) := by ring
    _ = fE ^ N := by rw [hw, hc, mul_one]

theorem cancel {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (Xf X'f Y G : Matrix n n R)
    (e lk lc : R) (he : e ∈ nonZeroDivisors R) (hXX : Xf * X'f = (lc * e) • 1) (hG : e • G = lk • (X'f * Y)) :
    Xf * G = (lk * lc) • Y := by
  have h2 : e • (Xf * G) = e • ((lk * lc) • Y) := by
    rw [← Matrix.mul_smul, hG, Matrix.mul_smul, ← Matrix.mul_assoc, hXX, Matrix.smul_mul, Matrix.one_mul,
      smul_smul, smul_smul]
    congr 1; ring
  ext i j
  have h3 := congrFun (congrFun h2 i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h3
  exact (mul_cancel_left_mem_nonZeroDivisors he).1 h3

theorem map_unit_eq {R S : Type} [CommRing R] [CommRing S] (T : R →+* S) (a b : R) (w : Rˣ) (hw : a * w = b) :
    T b * T (↑w⁻¹ : R) = T a := by
  rw [← hw, ← map_mul, mul_assoc, Units.mul_inv, mul_one]

theorem inv_pow_map {R S : Type} [CommRing R] [CommRing S] (T : R →+* S) (x : R) (li : S) (h : li * T x = 1)
    (m : ℕ) : li ^ m * T (x ^ m) = 1 := by
  rw [map_pow, ← mul_pow, h, one_pow]

end GlobalTheory.BSP.RelEx

namespace GlobalTheory.BSP.Height

open GlobalTheory.BSP.RelEx

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ}
  {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]} {τ : Ainf l} {s : Seed bk d ρ τ} (ht : Height s)

theorem bas_map_disc {B : Obj l ↥(OL K)} (u : B.A) (h : Hom bk.prism B) (F : bk.DS bk.ρ₀ →+* Disc l u bk.ρ₀)
    (hF : IsDiscMap (BK.hf h) F) :
    ht.bas.map F = (s.X.map (BK.hf h)).map (toDisc l u bk.ρ₀) * ht.Z.map F := by
  rw [Height.bas, Matrix.map_mul]
  congr 1
  ext i j
  simp only [Matrix.map_apply]
  exact hF.ext _

theorem rel_exists_of {B : Obj l ↥(OL K)} (u : B.A) (f g : Hom bk.prism B)
    (Ff Fg : bk.DS bk.ρ₀ →+* Disc l u bk.ρ₀) (hF : IsDiscMap (BK.hf f) Ff) (hG : IsDiscMap (BK.hf g) Fg)
    (w : B.Aˣ) (hw : BK.hf f bk.E * w = BK.hf g bk.E) (G : Matrix (Fin d) (Fin d) B.A) (m : ℕ)
    (hAG : s.X.map (BK.hf f) * G = (l : B.A) ^ m • s.X.map (BK.hf g)) :
    ∃ ε : Matrix (Fin d) (Fin d) (Disc l u bk.ρ₀), ht.Rel u f g ε := by
  obtain ⟨Z', hZ'⟩ : ∃ Z', ht.Z * Z' = 1 := by
    obtain ⟨U, hU⟩ := ht.Z_unit
    exact ⟨↑U⁻¹, by rw [← hU]; exact U.mul_inv⟩
  obtain ⟨li, hli⟩ : ∃ li : Disc l u bk.ρ₀, li * toDisc l u bk.ρ₀ (l : B.A) = 1 :=
    ((IsLocalization.Away.algebraMap_isUnit (S := PreDisc l u bk.ρ₀) (l : B.A)).map (ofPre l u bk.ρ₀)).exists_left_inv
  have key : toDisc l u bk.ρ₀ (BK.hf g bk.E) ^ s.N • (ht.bas.map Ff *
      ((toDisc l u bk.ρ₀ (↑w⁻¹ : B.A) ^ s.N * li ^ m) •
        (Z'.map Ff * G.map (toDisc l u bk.ρ₀) * ht.Z.map Fg))) =
      toDisc l u bk.ρ₀ (BK.hf f bk.E) ^ s.N • ht.bas.map Fg := by
    have e1 := ht.bas_map_disc u f Ff hF
    have e2 := ht.bas_map_disc u g Fg hG
    have h4 := alg s.N ((s.X.map (BK.hf f)).map (toDisc l u bk.ρ₀)) (ht.Z.map Ff) (Z'.map Ff)
      (G.map (toDisc l u bk.ρ₀)) ((s.X.map (BK.hf g)).map (toDisc l u bk.ρ₀)) (ht.Z.map Fg)
      (toDisc l u bk.ρ₀ (BK.hf g bk.E)) (toDisc l u bk.ρ₀ (BK.hf f bk.E))
      (toDisc l u bk.ρ₀ (↑w⁻¹ : B.A)) (li ^ m) (toDisc l u bk.ρ₀ ((l : B.A) ^ m))
      (by rw [← Matrix.map_mul, hZ', Matrix.map_one _ (map_zero _) (map_one _)])
      (by rw [← Matrix.map_mul, hAG, map_smul_ring])
      (map_unit_eq _ _ _ w hw)
      (inv_pow_map _ _ li hli m)
    exact (congrArg (fun M => toDisc l u bk.ρ₀ (BK.hf g bk.E) ^ s.N • (M *
      ((toDisc l u bk.ρ₀ (↑w⁻¹ : B.A) ^ s.N * li ^ m) • (Z'.map Ff * G.map (toDisc l u bk.ρ₀) * ht.Z.map Fg)))) e1).trans
      (h4.trans (congrArg (fun M => toDisc l u bk.ρ₀ (BK.hf f bk.E) ^ s.N • M) e2.symm))
  refine ⟨(toDisc l u bk.ρ₀ (↑w⁻¹ : B.A) ^ s.N * li ^ m) •
    (Z'.map Ff * G.map (toDisc l u bk.ρ₀) * ht.Z.map Fg), ?_⟩
  unfold Height.Rel
  intro Ff' Fg' hF' hG'
  have e1 : Ff' = Ff := (hF.unique hF').symm
  have e2 : Fg' = Fg := (hG.unique hG').symm
  subst e1 e2
  exact key

end GlobalTheory.BSP.Height

namespace GlobalTheory.BSP.Height

open GlobalTheory.BSP.RelEx

theorem rel_exists : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s)
    (B : Obj l ↥(OL K)) (u : B.A) (f g : Hom bk.prism B),
    ∃ ε : Matrix (Fin d) (Fin d) (Disc l u bk.ρ₀), ht.Rel u f g ε := by
  intro l _ K bk d ρ τ s ht B u f g
  by_cases hex : ∃ Ff Fg : bk.DS bk.ρ₀ →+* Disc l u bk.ρ₀, IsDiscMap (BK.hf f) Ff ∧ IsDiscMap (BK.hf g) Fg
  swap
  · refine ⟨0, ?_⟩
    unfold Height.Rel
    intro Ff Fg hF hG
    exact (hex ⟨Ff, Fg, hF, hG⟩).elim
  obtain ⟨Ff, Fg, hF, hG⟩ := hex
  obtain ⟨hreg, ⟨w, hw⟩, -⟩ := GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk B f g
  obtain ⟨k, hk⟩ := s.nopole f g
  choose G hGc using hk
  have hXX : s.X.map (BK.hf f) * s.X'.map (BK.hf f) = ((l : B.A) ^ s.c₂ * BK.hf f bk.E ^ (2 * s.N)) • 1 := by
    rw [← Matrix.map_mul, s.X_mul, map_smul_ring, Matrix.map_one _ (map_zero _) (map_one _)]
    simp
  have hGm : BK.hf f bk.E ^ (2 * s.N) • Matrix.of G = (l : B.A) ^ k • (s.X'.map (BK.hf f) * s.X.map (BK.hf g)) := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
    exact (hGc i j).symm
  have hAG : s.X.map (BK.hf f) * Matrix.of G = (l : B.A) ^ (k + s.c₂) • s.X.map (BK.hf g) := by
    rw [pow_add]
    exact cancel _ _ _ _ _ _ _ (pow_mem hreg _) (by rw [hXX, mul_comm]) hGm
  exact ht.rel_exists_of u f g Ff Fg hF hG w hw (Matrix.of G) (k + s.c₂) hAG

end GlobalTheory.BSP.Height
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeDiscSpanFrobeniusStableStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineLattice_discSpan_frobenius_stable : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∀ y, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) y → (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) (fun a => WittVector.frobenius (y a)) := by
  first | exact @GlobalTheory.BSP.seed_span_frobenius_stable | exact GlobalTheory.BSP.seed_span_frobenius_stable | (intros; apply GlobalTheory.BSP.seed_span_frobenius_stable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeFrobeniusInverseMatrixStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineLattice_frobenius_inverse_matrix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap WittVector.frobenius Φ → (s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map bk.iS * s.W'.map Φ = (((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) * bk.iS bk.E ^ (2 * s.N)) • s.W' := by
  first | exact @GlobalTheory.BSP.seed_frob_inverse | exact GlobalTheory.BSP.seed_frob_inverse | (intros; apply GlobalTheory.BSP.seed_frob_inverse <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeFrobeniusRationalColumnsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineLattice_frobenius_rational_columns : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ) (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (Z1 : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), Y1.det ≠ 0 → (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W * Z1.map j = Y1.map bk.iA) → ∃ (δ : bk.S) (A1 : Matrix (Fin d) (Fin d) (bk.S)), δ ≠ 0 ∧ bk.ev δ • Y1.map WittVector.frobenius = Y1 * A1.map bk.ev := by
  first | exact @GlobalTheory.BSP.FrobRational.main | exact GlobalTheory.BSP.FrobRational.main | (intros; apply GlobalTheory.BSP.FrobRational.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeHodgeTateJumpsFiniteStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineLattice_hodgeTateJumps_finite : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → (Jumps (PD := (D.loc l).PD K) T).Finite := by
  first | exact @GlobalTheory.NL.JumpsFinite.jumps_finite | exact GlobalTheory.NL.JumpsFinite.jumps_finite | (intros; apply GlobalTheory.NL.JumpsFinite.jumps_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeRationalInColumnsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineLattice_rational_in_columns : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ) (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (Z1 : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), (Y1.map (inclW l)).det ≠ 0 → (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W * Z1.map j = Y1.map bk.iA) → ∀ y, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) y → ∃ (δ : bk.S) (c : Fin d → bk.S), δ ≠ 0 ∧ (fun a => bk.ev δ * y a) = Y1 *ᵥ fun a => bk.ev (c a) := by
  first | exact @GlobalTheory.BSP.rational_in_columns | exact GlobalTheory.BSP.rational_in_columns | (intros; apply GlobalTheory.BSP.rational_in_columns <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineOfInertiaTrivialOnCrystallinePeriodsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_of_inertia_trivial_on_crystallinePeriods : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (K' F : FinExt l), (GK K').Normal → ∀ T : QLat LL, IsCrys (Pl.PD K') (resF T K').ρ → ((∀ g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), (g : GQ l) ∈ GK F → ∀ x ∈ Dcris (Pl.PD K') (resF T K').ρ, actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g x = x) → IsCrys (Pl.PD F) (resF T F).ρ) ∧ ∀ g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), ∀ p : Polynomial ↥LL.1, (∀ x ∈ Dcris (Pl.PD K') (resF T K').ρ, Polynomial.aeval (actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g : Module.End ↥LL.1 (T.V ⊗[ℚ_[l]] Pl.R.B)) p x = 0) → ∀ x ∈ Dcris (Pl.PD F) (resF T F).ρ, Polynomial.aeval (actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g : Module.End ↥LL.1 (T.V ⊗[ℚ_[l]] Pl.R.B)) p x = 0 := by
  first | exact @GlobalTheory.CrysInertDescent.main | exact GlobalTheory.CrysInertDescent.main | (intros; apply GlobalTheory.CrysInertDescent.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DDeRhamEqDCrisOfUnramified
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.FontaineAdmissibility

theorem intersectionNumber_baseChange : ∀ D : D7, Formalism.MainNotions.TruncatedSeriesCountingBounds.adm15 D :=
  fun D l _ K LL hb V _ _ _ _ _ ρ _ _ _ hc =>
    GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR l (D.loc l) (D.locA l) (D.locT l) K LL hb V ρ hc

end GlobalTheory.FontaineAdmissibility
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualExponentialKernelCyclotomicCocyclesStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualExponential_kernel_cyclotomic_cocycles : ∀ (D : Formalism.BasicNotions.D7), adm2 D → ArchimedeanSignatureMatching D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ) (z : GQ l → ℚ_[l]), ExpStar D.loc (Gj K s) e z 0 → (0 < e → CobOn (Gj K s) (fun σ y => (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * y) Set.univ z) ∧ (e = 0 → ∀ σ ∈ Gj K s, (∀ x : Om l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) → z σ = 0) := by
  first | exact @GlobalTheory.Cyc.ExpKernel.ker_expStar | exact GlobalTheory.Cyc.ExpKernel.ker_expStar | (intros; apply GlobalTheory.Cyc.ExpKernel.ker_expStar <;> assumption)
end

