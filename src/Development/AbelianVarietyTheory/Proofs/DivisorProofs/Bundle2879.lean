import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2785
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0858
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicCompactDensity.ExistsNatLocal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2561
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0546
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2818
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0166
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0135
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2786
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2787
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmOrderUniformizationEndomorphismsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_order_uniformization_endomorphisms : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (c : Ideal (OF E)), c ≠ ⊥ → ∀ (𝔠 : FracId (FR E)) (L : Set E) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X)
      (α : orderC c → (X.A ⟶ X.A)) [∀ a, IsMonHom (α a)],
      (∀ (a : orderC c) w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α a) →
      Fil X.A = ⨆ i, ⨅ a : orderC c,
        Module.End.eigenspace (push (dp0 ℂ) (𝟙 _) (α a)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i) a) := by
  first | exact @GlobalTheory.FilCx.fil_eq_iSup_eigenspace_bar | exact GlobalTheory.FilCx.fil_eq_iSup_eigenspace_bar | (intros; apply GlobalTheory.FilCx.fil_eq_iSup_eigenspace_bar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPeriodTranscendenceRelationStatement
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_period_transcendence_relation : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E)
    (𝔠 : FracId (FR E)) (X₀ : Obj (FR E) 𝔠 (Sp Qb)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (p : X.A.left ⟶ X₀.A.left)
    (U : Unif φ L 0 X) (v₀ : I → X₀.Lie) (v : I → X.Lie) (a : I → ℂ) (hp : X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p),
    IsCMType φ →
    (∀ i, Obj.LieCorr (algebraMap Qb ℂ) p (v₀ i) (v i) ∧ U.u.IsDiff (Pi.single (U.e.symm i) (a i)) (v i).hom ∧ a i ≠ 0) →
    (∀ b : E, (∀ x ∈ L, b * x ∈ L) → ∃ α : X.A ⟶ X.A, IsMonHom α ∧
      ∀ w', U.u.ex (fun j ↦ φ (U.e j) b * w' j) = U.u.ex w' ≫ α) →
    (∀ (b : E) (α : X.A ⟶ X.A) [IsMonHom α], (∀ w', U.u.ex (fun j ↦ φ (U.e j) b * w' j) = U.u.ex w' ≫ α) →
      ∃ α₀ : X₀.A ⟶ X₀.A, IsMonHom α₀ ∧ α.left ≫ p = p ≫ α₀.left) →
    ∃ (y₀ : I → HdR X₀.A) (yv : I → HdR X.A) (w : I → ℂ), ∀ i,
      y₀ i ≠ 0 ∧ (GlobalTheory.Published.AbelianDeRham.bcMor hp.grp).Corr (y₀ i) (yv i) ∧ U.IsCMVec i (yv i) (w i) ∧ w i ≠ 0 ∧
        IsAlgebraic ℚ (w i / a i) := by
  first | exact @GlobalTheory.CMEigen.exists_algebraic_eigenvectors | exact GlobalTheory.CMEigen.exists_algebraic_eigenvectors | (intros; apply GlobalTheory.CMEigen.exists_algebraic_eigenvectors <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPeriodsAlgebraicNonzeroStatement
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_periods_algebraic_nonzero : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E)
      (𝔠 : FracId (FR E)) (X₀ : Obj (FR E) 𝔠 (Sp Qb)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (p : X.A.left ⟶ X₀.A.left)
      (U : Unif φ L 0 X), IsCMType φ → X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p →
    ∀ (i : I) (y₀ : HdR X₀.A), y₀ ≠ 0 →
      (∀ (b : 𝓞 (FR E)) (β : Qb), algebraMap Qb ℂ β = φ i ((b : FR E) : E) →
        act (dp0 Qb) (𝟙 _) X₀.rm b y₀ = β • y₀) →
    ∀ f f' : Module.Dual Qb (HdR X₀.A), f y₀ = 0 → f' y₀ = 0 →
      (∀ (b : 𝓞 (FR E)) (β : Qb), algebraMap Qb ℂ β = φ i ((b : FR E) : E) →
        ∀ x, f (act (dp0 Qb) (𝟙 _) X₀.rm b x) = β * f x ∧ f' (act (dp0 Qb) (𝟙 _) X₀.rm b x) = β * f' x) →
      ∀ x y, f x * f' y = f y * f' x := by
  first | exact @GlobalTheory.EigenFunctional.mul_comm_of_eigen | exact GlobalTheory.EigenFunctional.mul_comm_of_eigen | (intros; apply GlobalTheory.EigenFunctional.mul_comm_of_eigen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmRiemannFormGaloisConjugate
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.ConjRiemannPos

theorem exists_ne_zero_mem_lattice {E : Type} [Field E] [NumberField E] (c : Ideal (OF E)) (y : (Af E)ˣ)
    (hc : c ≠ ⊥) : ∃ u ∈ lattice c y, u ≠ 0 := by
  set N : ℕ := Ideal.absNorm c with hNdef
  have hN : N ≠ 0 := by rwa [hNdef, Ne, Ideal.absNorm_eq_zero_iff]
  have hNc : (N : OF E) ∈ c := Ideal.absNorm_mem c
  obtain ⟨m, hm, hym⟩ := PI.AdCpctDenWork.exists_nat_adele (F := E) ((y⁻¹ : (Af E)ˣ) : Af E)
  have key := GlobalTheory.CMVal.PicFin.mul_mem_hatO hNc (y := (m : Af E) * ((y⁻¹ : (Af E)ˣ) : Af E)) (fun v => hym v)
  refine ⟨(N : E) * m, ?_, ?_⟩
  · show algebraMap E (Af E) ((N : E) * m) * _ ∈ hatO c
    rw [map_natCast, map_natCast] at key
    rw [map_mul, map_natCast, map_natCast, _root_.mul_assoc]
    exact key
  · exact mul_ne_zero (Nat.cast_ne_zero.mpr hN) (Nat.cast_ne_zero.mpr hm.ne')

theorem exists_pos_pair : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ g : ℂ ≃+* ℂ, (∀ x, g (io x) = io x) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I]
    (φ : I → E →+* ℂ), (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
    ∀ (n : ℕ) (e : Fin n ≃ I) (h : I → ℝ) (Hm : Matrix (Fin n) (Fin n) ℂ), 0 < n →
      (∀ z : Fin n → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ (Matrix.diagonal fun j ↦ (h (e j) : ℂ)).mulVec (star z)).re) → Hm.IsHermitian →
      (∀ z : Fin n → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) →
      ∃ u ∈ lattice c y, ∃ u' ∈ lattice c y, (∑ i, h i * (φ i u * starRingEnd ℂ (φ i u')).im) ≠ 0 ∧
        0 < (∑ i, h i * (φ i u * starRingEnd ℂ (φ i u')).im) * ((fun j ↦ g (φ (e j) u)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (e j) u'))).im := by
  intro K _ _ d δ io _ hd hδ g hg E _ _ _ _ I _ φ hφ c y hc n e h Hm hn hdiag _ hH
  obtain ⟨u, hu, hu0⟩ := exists_ne_zero_mem_lattice c y hc
  set N : ℕ := Ideal.absNorm c with hNdef
  have hN : N ≠ 0 := by rwa [hNdef, Ne, Ideal.absNorm_eq_zero_iff]
  have hNc : (N : OF E) ∈ c := Ideal.absNorm_mem c
  set δ' : E := algebraMap K E δ with hδ'
  have hδ'2 : δ' ^ 2 = -(d : E) := by rw [hδ', ← map_pow, hδ]; simp
  have hint : IsIntegral ℤ δ' := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    have e1 : algebraMap ℤ E (-(d : ℤ)) = -(d : E) := by simp
    rw [hδ'2, ← e1]
    exact isIntegral_algebraMap
  let b : 𝓞 E := ⟨δ', hint⟩
  have hb : algebraMap (𝓞 E) E b = δ' := rfl
  have hmem : (N : E) * δ' ∈ orderC c := mem_orderC.2 ⟨0, algebraMap (OF E) (𝓞 E) (N : OF E) * b,
    Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hNc), by simp [hb]⟩
  have hu' : (N : E) * δ' * u ∈ lattice c y := by
    show algebraMap E (Af E) _ * _ ∈ hatO c
    rw [map_mul, _root_.mul_assoc]
    exact mul_mem (algebraMap_mem_hatO hmem) hu
  refine ⟨u, hu, (N : E) * δ' * u, hu', ?_⟩
  set w : ℂ := io δ with hw
  have hφδ : ∀ i, φ i δ' = w := fun i => by rw [hδ', ← RingHom.comp_apply, hφ i]
  have hw2 : w ^ 2 = -(d : ℂ) := by rw [hw, ← map_pow, hδ]; simp
  have hre := congrArg Complex.re hw2
  have him := congrArg Complex.im hw2
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
    Complex.natCast_im, neg_zero] at hre him
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hwre : w.re = 0 := by
    by_contra hne
    have h0 : w.im = 0 := by
      have : 2 * w.re * w.im = 0 := by linarith
      rcases mul_eq_zero.1 this with h1 | h1
      · exact absurd (by linarith : w.re = 0) hne
      · exact h1
    rw [h0] at hre
    nlinarith [mul_self_nonneg w.re]
  have hwim : w.im ^ 2 = d := by rw [hwre] at hre; nlinarith
  have hφu' : ∀ i, φ i ((N : E) * δ' * u) = (N : ℂ) * w * φ i u := fun i => by
    rw [map_mul, map_mul, map_natCast, hφδ]

  set P : ℝ := ∑ i, h i * Complex.normSq (φ i u) with hP
  have hS : (∑ i, h i * (φ i u * starRingEnd ℂ (φ i ((N : E) * δ' * u))).im) = -((N : ℝ) * w.im) * P := by
    rw [hP, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hφu']
    simp only [map_mul, Complex.conj_natCast, Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.natCast_re, Complex.natCast_im, hwre, Complex.normSq_apply]
    ring
  have hPpos : 0 < P := by
    have hz : (fun j => φ (e j) u) ≠ 0 := by
      intro h0
      have := congrFun h0 ⟨0, hn⟩
      exact (map_ne_zero (φ (e ⟨0, hn⟩))).2 hu0 this
    have := hdiag _ hz
    convert this using 1
    simp only [Matrix.mulVec_diagonal, dotProduct, Complex.re_sum, Pi.star_apply]
    rw [hP, ← e.sum_comp]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im, Complex.mul_im, Complex.normSq_apply]
    ring

  set W : Fin n → ℂ := fun j => g (φ (e j) u) with hWdef
  have hW' : (star fun j => g (φ (e j) ((N : E) * δ' * u))) = (starRingEnd ℂ ((N : ℂ) * w)) • star W := by
    funext j
    simp only [Pi.star_apply, Pi.smul_apply, smul_eq_mul, hWdef, hφu', map_mul, map_natCast, hw, hg δ, star_mul',
      Complex.star_def]
  have hWne : W ≠ 0 := by
    intro h0
    have := congrFun h0 ⟨0, hn⟩
    exact (map_ne_zero g).2 ((map_ne_zero (φ (e ⟨0, hn⟩))).2 hu0) this
  have hQ := hH W hWne
  set Q : ℂ := W ⬝ᵥ Hm.mulVec (star W) with hQdef
  have hQ' : (W ⬝ᵥ Hm.mulVec (star fun j => g (φ (e j) ((N : E) * δ' * u)))).im = -((N : ℝ) * w.im) * Q.re := by
    rw [hW', Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, ← hQdef]
    simp only [map_mul, Complex.conj_natCast, Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.natCast_re, Complex.natCast_im, hwre]
    ring
  have hwim0 : w.im ≠ 0 := by
    intro h0; rw [h0] at hwim; nlinarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  refine ⟨?_, ?_⟩
  · rw [hS]
    exact mul_ne_zero (neg_ne_zero.2 (mul_ne_zero hNR.ne' hwim0)) hPpos.ne'
  · rw [hS, hQ']
    have hk : 0 < ((N : ℝ) * w.im) ^ 2 := by positivity
    have : -((N : ℝ) * w.im) * P * (-((N : ℝ) * w.im) * Q.re) = ((N : ℝ) * w.im) ^ 2 * (P * Q.re) := by ring
    rw [this]
    exact mul_pos hk (mul_pos hPpos hQ)

end GlobalTheory.ConjRiemannPos
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpFormEqZeroOfPullbackVanishing
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.CechDR KaehlerDifferential
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PtVanish

section Affine

variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}
variable {A R' : Type} [CommRing A] [Algebra R A] [CommRing R'] [Algebra R R'] [Algebra A R']
  [IsScalarTower R A R']

def nbdMap (l : Ω[A⁄R] →ₗ[A] R') : TrivSqZeroExt A Ω[A⁄R] →ₐ[R] TrivSqZeroExt R' R' :=
  { toFun := fun c ↦ TrivSqZeroExt.inl (algebraMap A R' c.fst) + TrivSqZeroExt.inr (l c.snd)
    map_one' := by ext <;> simp
    map_zero' := by ext <;> simp
    map_add' := fun a b ↦ by ext <;> simp <;> ring
    map_mul' := fun a b ↦ by
      have hop : ∀ (b : A) (ω : Ω[A⁄R]), MulOpposite.op b • ω = b • ω := fun _ _ ↦ rfl
      ext
      · simp
      · simp only [TrivSqZeroExt.snd_mul, hop, map_add, map_smul, TrivSqZeroExt.snd_add,
          TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_add,
          TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, smul_eq_mul, Algebra.smul_def]
        simp [MulOpposite.smul_eq_mul_unop]
        ring
    commutes' := fun r ↦ by
      ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl', ← IsScalarTower.algebraMap_apply] }

theorem snd_nbdMap (l : Ω[A⁄R] →ₗ[A] R') (c : TrivSqZeroExt A Ω[A⁄R]) :
    (nbdMap l c).snd = l c.snd := by
  simp [nbdMap]

theorem fst_nbdMap (l : Ω[A⁄R] →ₗ[A] R') (c : TrivSqZeroExt A Ω[A⁄R]) :
    (nbdMap l c).fst = algebraMap A R' c.fst := by
  simp [nbdMap]

theorem snd_val_affine_eq (U : X.affineOpens) [Algebra (Sec s U.1) R'] [IsScalarTower R (Sec s U.1) R']
    (l : Ω[Sec s U.1⁄R] →ₗ[Sec s U.1] R') (y : Sp (TrivSqZeroExt R' R') ⟶ X)
    (hy : y ≫ s = spMap (algebraMap R (TrivSqZeroExt R' R')))
    (e : spMap ((nbdMap l).comp (diagSec R (Sec s U.1)) : Sec s U.1 →+* TrivSqZeroExt R' R') ≫
      affPt s U = y) (f : Form s) :
    TrivSqZeroExt.snd ((SqExt.ofModule R R' R').val y hy f.1) =
      l (connForm f.1 (affPt s U) (affPt_w s U)) := by
  have hx := affPt_w s U
  let Φ := nbdMap (R := R) l
  let α : Sec s U.1 →ₐ[R] TrivSqZeroExt R' R' := Φ.comp (diagSec R (Sec s U.1))
  let α₀ : Sec s U.1 →ₐ[R] R' := (TrivSqZeroExt.fstHom R R' R').comp α
  have hπ : ∀ c, α₀ ((diagExt R (Sec s U.1)).π c) = (SqExt.ofModule R R' R').π (Φ c) := fun c ↦ by
    change (Φ (diagSec R (Sec s U.1) c.fst)).fst = (Φ c).fst
    rw [fst_nbdMap, fst_nbdMap, fst_derSec]
  have e₀ : spMap (α₀ : Sec s U.1 →+* R') ≫ affPt s U =
      spMap ((SqExt.ofModule R R' R').π : TrivSqZeroExt R' R' →+* R') ≫ y := by
    rw [← e, ← Category.assoc, ← Cris.spMap_comp]; rfl
  let Ψ := (diagExt R (Sec s U.1)).thickHom (SqExt.ofModule R R' R') Φ α₀ hπ hx
    ((SqExt.ofModule R R' R').red_w hy) e₀
  let a1 : Thick.triv (Sec s U.1) (affPt s U) hx ⟶
      Thick.triv R' _ ((SqExt.ofModule R R' R').red_w hy) := Thick.trivHom α₀ e₀
  let a2 : Thick.triv (Sec s U.1) (affPt s U) hx ⟶ Thick.triv (TrivSqZeroExt R' R') y hy :=
    Thick.trivHom α e
  have k1 := Form.ev_sq f a1 ((SqExt.ofModule R R' R').secHom ((SqExt.ofModule R R' R').red_w hy)
    (SqExt.ofModule R R' R').i (SqExt.ofModule R R' R').π_i)
    ((diagExt R (Sec s U.1)).secHom hx (diagExt R (Sec s U.1)).i fun _ ↦ rfl) Ψ rfl rfl fun c ↦ by
      change TrivSqZeroExt.inl (α₀ c) = Φ (TrivSqZeroExt.inl c)
      ext
      · change (Φ (diagSec R (Sec s U.1) c)).fst = (Φ (TrivSqZeroExt.inl c)).fst
        rw [fst_nbdMap, fst_nbdMap, fst_derSec, TrivSqZeroExt.fst_inl]
      · rw [TrivSqZeroExt.snd_inl, snd_nbdMap, TrivSqZeroExt.snd_inl, map_zero]
  have k2 := Form.ev_sq f a2 ((SqExt.ofModule R R' R').idHom hy)
    ((diagExt R (Sec s U.1)).secHom hx (diagSec R (Sec s U.1)) (fst_derSec _)) Ψ rfl rfl
    fun _ ↦ rfl
  rw [SqExt.val_apply, k1, k2, add_sub_add_right_eq_sub]
  change TrivSqZeroExt.snd (Φ _ - Φ _) = _
  rw [← map_sub, snd_nbdMap]
  rfl

end Affine

theorem tanVal_pull_eq {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {A : Over (Sp R)}
    {B : Over (Sp R')} {φ : B.left ⟶ A.left}
    (m : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R') (B.hom ≫ 𝟙 _) (algebraMap R R') φ) (v' : epsR R' ⟶ B)
    (y : Sp (TrivSqZeroExt R' R') ⟶ A.left)
    (hy : y ≫ A.hom ≫ 𝟙 _ = spMap (algebraMap R (TrivSqZeroExt R' R')))
    (e : v'.left ≫ φ = y) (f : Form (A.hom ≫ 𝟙 _)) :
    tanVal v' (m.pullForm f) = TrivSqZeroExt.snd ((SqExt.ofModule R R' R').val y hy f.1) := by
  subst e
  let E := SqExt.ofModule R R' R'
  let E' := SqExt.dual R'
  have hy' := pt_w v'
  have hc : ∀ r : R, algebraMap R E.C r = algebraMap R' E'.C (algebraMap R R' r) := fun r ↦ by
    ext <;> simp [E, E', TrivSqZeroExt.algebraMap_eq_inl']
  have e₀ : spMap (RingHom.id R') ≫ spMap (E.π : E.C →+* E.B) ≫ v'.left ≫ φ =
      (spMap (E'.π : E'.C →+* E'.B) ≫ v'.left) ≫ φ := by
    rw [Cris.spMap_id, Category.id_comp, Category.assoc]; rfl
  let Φ : E.thick _ (E.red_w hy) ⟶ m.obj (E'.thick _ (E'.red_w hy')) :=
    { φ := { RingHom.id E.C with commutes' := hc }
      φ₀ := RingHom.id R'
      comm := fun _ ↦ rfl
      dp := isDPMorphism_sqDP E.sq E'.sq _ fun _ ha ↦ ha
      pt := e₀ }
  let a : Thick.triv E.C _ hy ⟶ m.obj (Thick.triv E'.C _ hy') :=
    Thick.trivHom { RingHom.id E.C with commutes' := hc } (by
      change spMap (RingHom.id E.C) ≫ v'.left ≫ φ = v'.left ≫ φ
      rw [Cris.spMap_id, Category.id_comp])
  let b : Thick.triv E.B _ (E.red_w hy) ⟶ m.obj (Thick.triv E'.B _ (E'.red_w hy')) :=
    Thick.trivHom { RingHom.id R' with commutes' := fun _ ↦ rfl } e₀
  have k1 := Form.ev_sq f a (m.functor.map (E'.idHom hy')) (E.idHom hy) Φ rfl rfl fun _ ↦ rfl
  have k2 := Form.ev_sq f b (m.functor.map (E'.secHom (E'.red_w hy') E'.i E'.π_i))
    (E.secHom (E.red_w hy) E.i E.π_i) Φ rfl rfl fun _ ↦ rfl
  have k : E'.val v'.left hy' (m.pullForm f).1 = E.val (v'.left ≫ φ) hy f.1 :=
    (congrArg₂ (fun u v : E'.C ↦ u - v) k2 k1).trans (add_sub_add_right_eq_sub (G := E'.C) _ _ _)
  rw [tanVal_apply]
  exact congrArg (TrivSqZeroExt.snd (R := R')) k

theorem sec_smooth {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (hs : Smooth s)
    (U : X.affineOpens) : Algebra.Smooth R (Sec s U.1) := by
  have h1 : RingHom.Smooth (s.appLE ⊤ U.1 le_top).hom :=
    HasRingHomProperty.appLE @Smooth s hs ⟨⊤, isAffineOpen_top _⟩ U le_top
  have h2 : RingHom.Smooth (secMap s U.1).hom :=
    RingHom.Smooth.respectsIso.2 _ (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv h1
  exact h2

end GlobalTheory.PtVanish

namespace GlobalTheory.PtVanish

theorem connForm_eq_zero {K : Type} [Field K] {X : Over (Sp K)} (hX : Smooth X.hom)
    (f : Form (X.hom ≫ 𝟙 (Sp K)))
    (H : ∀ (L : Type) [Field L] (σ : K →+* L), ∃ (X' : Over (Sp L)) (φ : X'.left ⟶ X.left)
      (m : IsMor (dp0 K) (X.hom ≫ 𝟙 (Sp K)) (dp0 L) (X'.hom ≫ 𝟙 (Sp L)) σ φ),
      IsPullback φ X'.hom X.hom (spMap σ) ∧ ∀ u : epsR L ⟶ X', tanVal u (m.pullForm f) = 0)
    (U : X.left.affineOpens) :
    connForm f.1 (affPt (X.hom ≫ 𝟙 (Sp K)) U) (affPt_w (X.hom ≫ 𝟙 (Sp K)) U) = 0 := by
  have hsm : Smooth (X.hom ≫ 𝟙 (Sp K)) := by rw [Category.comp_id]; exact hX
  haveI : Algebra.Smooth K (Sec (X.hom ≫ 𝟙 (Sp K)) U.1) := sec_smooth _ hsm U
  haveI : _root_.IsReduced (Sec (X.hom ≫ 𝟙 (Sp K)) U.1) :=
    GlobalTheory.T.isReduced_of_smooth_over_field' K (Sec (X.hom ≫ 𝟙 (Sp K)) U.1)
  refine GlobalTheory.T.eq_zero_of_forall_residueField_functional' (Sec (X.hom ≫ 𝟙 (Sp K)) U.1) Ω[Sec (X.hom ≫ 𝟙 (Sp K)) U.1⁄K] _ ?_
  intro p _ l
  obtain ⟨X', φ, m, hpb, hv⟩ := H p.ResidueField (algebraMap K p.ResidueField)
  let α : Sec (X.hom ≫ 𝟙 (Sp K)) U.1 →ₐ[K] TrivSqZeroExt p.ResidueField p.ResidueField :=
    (nbdMap l).comp (diagSec K (Sec (X.hom ≫ 𝟙 (Sp K)) U.1))
  let y := spMap (α : Sec (X.hom ≫ 𝟙 (Sp K)) U.1 →+* TrivSqZeroExt p.ResidueField p.ResidueField) ≫
    affPt (X.hom ≫ 𝟙 (Sp K)) U
  have hy : y ≫ X.hom ≫ 𝟙 (Sp K) =
      spMap (algebraMap K (TrivSqZeroExt p.ResidueField p.ResidueField)) := by
    simp only [y, Category.assoc, affPt_w, ← Cris.spMap_comp, α.comp_algebraMap]
  have hcomp : (algebraMap p.ResidueField (DualNumber p.ResidueField)).comp
      (algebraMap K p.ResidueField) =
      algebraMap K (TrivSqZeroExt p.ResidueField p.ResidueField) :=
    RingHom.ext fun r ↦ by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl']
  have w : y ≫ X.hom = spMap (algebraMap p.ResidueField (DualNumber p.ResidueField)) ≫
      spMap (algebraMap K p.ResidueField) := by
    rw [← Cris.spMap_comp, hcomp, ← hy, Category.comp_id]
  let u : epsR p.ResidueField ⟶ X' :=
    Over.homMk (hpb.lift y (spMap (algebraMap p.ResidueField (DualNumber p.ResidueField))) w)
      (hpb.lift_snd _ _ _)
  have e : u.left ≫ φ = y := hpb.lift_fst _ _ _
  have h := hv u
  rw [tanVal_pull_eq m u y hy e f, snd_val_affine_eq U l y hy rfl f] at h
  exact h

theorem cmpForm_eq_zero_of_tanVal : ∀ (K : Type) [Field K] (X : Over (Sp K)), Smooth X.hom → ∀ f : Form (X.hom ≫ 𝟙 (Sp K)), (∀ (L : Type) [Field L] (σ : K →+* L), ∃ (X' : Over (Sp L)) (φ : X'.left ⟶ X.left) (m : IsMor (dp0 K) (X.hom ≫ 𝟙 (Sp K)) (dp0 L) (X'.hom ≫ 𝟙 (Sp L)) σ φ), IsPullback φ X'.hom X.hom (spMap σ) ∧ ∀ u : epsR L ⟶ X', tanVal u (m.pullForm f) = 0) → GlobalTheory.CechDR.cmpForm (X.hom ≫ 𝟙 (Sp K)) f = 0 := by
  intro K _ X hX f H
  refine Subtype.ext (Subtype.ext (funext fun U ↦ ?_))
  exact (cmpForm_apply _ f U).trans (connForm_eq_zero hX f H U.unop)

end GlobalTheory.PtVanish
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientGermsZeroFiniteFreeBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.FreeCoord

open GlobalTheory.BoxIndep TensorProduct

theorem eq_zero_of_germOf_max {B : CommRingCat.{0}} (a : B)
    (h : ∀ z : Spec B, z.asIdeal.IsMaximal → germOf (𝟙 (Spec B)) z a = 0) : a = 0 := by
  have : (Ideal.span {a}).annihilator = ⊤ := by
    by_contra hne
    obtain ⟨p, hp, hI⟩ := Ideal.exists_le_maximal _ hne
    let z : Spec B := ⟨p, hp.isPrime⟩
    have h1 : algebraMap B ((Spec.structureSheaf B).presheaf.stalk z) a = 0 := h z hp
    have := StructureSheaf.IsLocalization.to_stalk B z
    obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff z.asIdeal.primeCompl _ _).1 h1
    exact c.2 (hI (Submodule.mem_annihilator_span_singleton _ _ |>.2 hc))
  have h1 : (1 : B) ∈ (Ideal.span {a}).annihilator := this ▸ Submodule.mem_top
  exact (one_smul B _).symm.trans ((Submodule.mem_annihilator_span_singleton _ _).1 h1)

theorem gs_comp' {Z Y X : Scheme.{0}} (r : Z ⟶ Y) (F : Y ⟶ X) (z : Z) (U : X.Opens) (h : F (r z) ∈ U) (f : Γ(X, U)) :
    gs (r ≫ F) z U f = (r.stalkMap z).hom (gs F (r z) U f) := by
  rw [← gs_pull r F z U h, gs_stalkMap r z _ h, gs_pull (𝟙 _) F (r z) U h, Category.id_comp]

theorem germ_eq_zero : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ₁ : R →+* R₁) (d : ℕ) (b : Fin d → R₁), (∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l) → ∀ (X : Scheme.{0}) (f : X ⟶ Sp R) (U : X.Opens) (a : Fin d → Γ(X, U)) (x : X), x ∈ U → (∀ z : (pullback f (spMap ρ₁) : Scheme.{0}), (pullback.fst f (spMap ρ₁)) z = x → ∑ l, gs (pullback.snd f (spMap ρ₁)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs (pullback.fst f (spMap ρ₁)) z U (a l) = 0) → ∀ l, gs (𝟙 X) x U (a l) = 0 := by
  intro R R₁ _ _ ρ₁ d b hb X f U a x hx h
  let _ : Algebra R R₁ := ρ₁.toAlgebra
  let A : CommRingCat.{0} := X.presheaf.stalk x
  let _ : Algebra R A := (germOf (B := CommRingCat.of R) f x).toAlgebra
  have hli : LinearIndependent R b := Fintype.linearIndependent_iff.2 fun c hc =>
    congrFun ((hb 0).unique (y₁ := c) (y₂ := 0) (by simp only [Algebra.smul_def] at hc; exact hc.symm) (by simp))
  have hsp : ⊤ ≤ Submodule.span R (Set.range b) := fun r _ => by
    obtain ⟨c, hc, -⟩ := hb r
    rw [hc]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ (c l) (Submodule.subset_span ⟨l, rfl⟩)
  let β := Module.Basis.mk hli hsp
  have : Module.Finite R R₁ := Module.Finite.of_basis β
  let B : CommRingCat.{0} := CommRingCat.of (A ⊗[R] R₁)
  let iA : A ⟶ B := CommRingCat.ofHom (algebraMap A (A ⊗[R] R₁))
  let iR : CommRingCat.of R₁ ⟶ B := CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := R₁)).toRingHom
  have w : (Spec.map iA ≫ X.fromSpecStalk x) ≫ f = Spec.map iR ≫ spMap ρ₁ := by
    rw [Category.assoc, fromSpecStalk_comp (B := CommRingCat.of R)]
    refine (Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_comp _ _))
    ext r
    exact (IsScalarTower.algebraMap_apply R A (A ⊗[R] R₁) r).symm.trans
      ((Algebra.TensorProduct.includeRight (R := R) (A := A) (B := R₁)).commutes r).symm
  let r : Spec B ⟶ pullback f (spMap ρ₁) := pullback.lift _ _ w
  have r1 : r ≫ pullback.fst f (spMap ρ₁) = Spec.map iA ≫ X.fromSpecStalk x := pullback.lift_fst _ _ _
  have r2 : r ≫ pullback.snd f (spMap ρ₁) = Spec.map iR := pullback.lift_snd _ _ _
  have key : (∑ l, iR.hom (b l) * iA.hom (gs (𝟙 X) x U (a l)) : B) = 0 := by
    refine eq_zero_of_germOf_max _ fun z hz => ?_
    have hm : (z.asIdeal.comap (algebraMap A (A ⊗[R] R₁))).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) (S := A ⊗[R] R₁) z.asIdeal
    have hc : Spec.map iA z = closedPoint A := PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hm)
    have hzx : pullback.fst f (spMap ρ₁) (r z) = x := by
      have : (r ≫ pullback.fst f (spMap ρ₁)) z = X.fromSpecStalk x (Spec.map iA z) := by rw [r1]; rfl
      rw [hc, Scheme.fromSpecStalk_closedPoint] at this
      exact this
    have e := congrArg (r.stalkMap z).hom (h (r z) hzx)
    rw [map_zero, map_sum] at e
    rw [← e, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, map_mul, ← gs_comp' r _ z ⊤ trivial, ← gs_comp' r _ z U (hzx ▸ hx), r1, r2,
      gs_fromSpecStalk x hx, ← germOf_apply, ← germOf_map, ← germOf_map, Category.id_comp, Category.id_comp]
  have hli' := (Algebra.TensorProduct.basis A β).linearIndependent
  refine Fintype.linearIndependent_iff.1 hli' (fun l => gs (𝟙 X) x U (a l)) ?_
  refine Eq.trans (Finset.sum_congr rfl fun l _ => ?_) key
  rw [Algebra.smul_def, _root_.mul_comm, Algebra.TensorProduct.basis_apply, Module.Basis.mk_apply]
  rfl

end GlobalTheory.Mum.FreeCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleReductionSystemGivesThickeningTowerStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatibleReductionSystem_gives_thickening_tower : ∀ (R : Type) [CommRing R] (I : Ideal R) (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (t : ℕ → W.IdealSheafData), IsSystem f I t → ∃ (q : ∀ e, (t e).subscheme ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (β : ∀ e, (t e).subscheme ⟶ (t (e + 1)).subscheme), (∀ e, (t e).subschemeι ≫ f = q e ≫ thick R I e) ∧ (∀ e, β e ≫ (t (e + 1)).subschemeι = (t e).subschemeι) ∧ ∀ e, IsPullback (β e) (q e) (q (e + 1)) (thickTrans R I e) := by
  first | exact @GlobalTheory.FormalAlg.isSystem_tower | exact GlobalTheory.FormalAlg.isSystem_tower | (intros; apply GlobalTheory.FormalAlg.isSystem_tower <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamHypercohomologyOneBaseChangeFlatBijectiveStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRhamHypercohomologyOne_baseChange_flat_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] (C : Type) [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (α : ∀ T : C, F.obj T →+* F'.obj T) (hn : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), α T' (mp F φ b) = mp F' φ (α T b)) (hs : ∀ (T : C) (r : R) (b : F.obj T), α T (r • b) = algebraMap R R' r • α T b), (∀ (T : C) (f : F.obj T →ₛₗ[algebraMap R R'] F'.obj T), (∀ b, f b = α T b) → Function.Bijective (liftSemi f)) → Function.Bijective (liftSemi (pullHyp1 (⟨𝟭 C, α, hn, hs⟩ : CoefMap (algebraMap R R') F F'))) := by
  first | exact @GlobalTheory.liftSemi_pullHyp1_bijective_of_finite | exact GlobalTheory.liftSemi_pullHyp1_bijective_of_finite | (intros; apply GlobalTheory.liftSemi_pullHyp1_bijective_of_finite <;> assumption)
end

