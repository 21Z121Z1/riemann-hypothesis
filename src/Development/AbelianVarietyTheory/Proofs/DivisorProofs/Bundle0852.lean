import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0843
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0811
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0836
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.LtChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0316
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0288
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0295
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0083
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0707
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0838
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0844
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPKerRepsPowFourMul
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem prod_derivWeierstrassP_kerReps_pow_four_mul :
    ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S →
      Even S.card →
      (∏ t ∈ S, L.derivWeierstrassP t) ^ 4 * α ^ 12 = (latticeCurve L).Δ ^ S.card := by
  intro L α S hα hst hS hev
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a = L.ω₁ / 2 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℂ, b = L.ω₂ / 2 := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = L.ω₁ / (4 * α) := ⟨_, rfl⟩
  have haL : a ∉ L.lattice := ha ▸ L.ω₁_div_two_notMem_lattice
  have hbL : b ∉ L.lattice := hb ▸ L.ω₂_div_two_notMem_lattice
  have habL : a + b ∉ L.lattice := by
    intro h
    have := (PeriodPair.mul_ω₁_add_mul_ω₂_mem_lattice (L := L) (α := 1 / 2) (β := 1 / 2)).mp
      (by convert h using 1; rw [ha, hb]; push_cast; ring)
    norm_num at this
  have ha2 : 2 * a ∈ L.lattice := by
    have : 2 * a = L.ω₁ := by rw [ha]; ring
    rw [this]; exact L.ω₁_mem_lattice
  have hb2 : 2 * b ∈ L.lattice := by
    have : 2 * b = L.ω₂ := by rw [hb]; ring
    rw [this]; exact L.ω₂_mem_lattice
  have hab2 : 2 * (a + b) ∈ L.lattice := by
    rw [mul_add]; exact add_mem ha2 hb2
  have hz2 : 2 * (α * z) ∉ L.lattice := by
    have : 2 * (α * z) = L.ω₁ / 2 := by rw [hz]; field_simp; ring
    rw [this]; exact L.ω₁_div_two_notMem_lattice
  have two : ∀ x, x ∈ L.lattice → 2 * x ∈ L.lattice := fun x hx => by
    rw [two_mul]; exact add_mem hx hx
  have hshift : ∀ c, 2 * c ∈ L.lattice → α * (z + c) ∉ L.lattice := by
    intro c hc h
    apply hz2
    have := sub_mem (two _ h) (hst _ hc)
    convert this using 1; ring
  have hz1 : α * z ∉ L.lattice := fun h => hz2 (two _ h)
  have hαc : ∀ c, 2 * c ∈ L.lattice → 2 * (α * c) ∈ L.lattice := fun c hc => by
    have := hst _ hc
    convert this using 1; ring
  have h0 := GlobalTheory.T.derivWeierstrassP_mul_prod_translate_of_kernel_reps L α S hα hst hS hev z hz1
  have h1 := GlobalTheory.T.derivWeierstrassP_mul_prod_translate_of_kernel_reps L α S hα hst hS hev (z + a) (hshift a ha2)
  have h2 := GlobalTheory.T.derivWeierstrassP_mul_prod_translate_of_kernel_reps L α S hα hst hS hev (z + b) (hshift b hb2)
  have h3 := GlobalTheory.T.derivWeierstrassP_mul_prod_translate_of_kernel_reps L α S hα hst hS hev (z + (a + b)) (hshift _ hab2)
  have hzz : 2 * z ∉ L.lattice := fun h => hz2 (hαc z h)
  have hL0 := GlobalTheory.T.product_derivWeierstrassP_half_periods_discriminant L a b z haL hbL habL ha2 hb2 hzz
  have hLt : ∀ t ∈ S, L.derivWeierstrassP (z + t) * L.derivWeierstrassP (z + a + t)
      * L.derivWeierstrassP (z + b + t) * L.derivWeierstrassP (z + (a + b) + t)
        = (latticeCurve L).Δ := by
    intro t ht
    have h2t : 2 * (z + t) ∉ L.lattice := by
      intro h
      apply hz2
      have := sub_mem (hαc _ h) (two _ (hS.1 t ht).1)
      convert this using 1; ring
    have := GlobalTheory.T.product_derivWeierstrassP_half_periods_discriminant L a b (z + t) haL hbL habL ha2 hb2 h2t
    rw [← this, add_right_comm z a t, add_right_comm z b t, add_right_comm z (a + b) t]
  have hR := GlobalTheory.T.product_derivWeierstrassP_half_periods_discriminant L (α * a) (α * b) (α * z)
    (fun h => haL (GlobalTheory.T.not_mem_half_lattice_of_odd_multiplier L α a S hα hst hS hev h ha2))
    (fun h => hbL (GlobalTheory.T.not_mem_half_lattice_of_odd_multiplier L α b S hα hst hS hev h hb2))
    (fun h => habL (GlobalTheory.T.not_mem_half_lattice_of_odd_multiplier L α (a + b) S hα hst hS hev (by rwa [mul_add]) hab2))
    (hαc a ha2) (hαc b hb2) hz2
  rw [← mul_add α a b, ← mul_add, ← mul_add, ← mul_add] at hR
  have hP : (∏ t ∈ S, L.derivWeierstrassP (z + t)) * (∏ t ∈ S, L.derivWeierstrassP (z + a + t))
      * (∏ t ∈ S, L.derivWeierstrassP (z + b + t))
      * (∏ t ∈ S, L.derivWeierstrassP (z + (a + b) + t)) = (latticeCurve L).Δ ^ S.card := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
      Finset.prod_congr rfl hLt, Finset.prod_const]
  apply mul_left_cancel₀ (latticeCurve_Δ_ne_zero L)
  have hall := congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) h0 h1) h2) h3
  rw [← hP]
  nth_rewrite 1 [← hR]
  rw [← hL0]
  linear_combination -hall

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDvdNorm
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.BKReal Formalism.BasicNotions.Examples₂.LB
open scoped Formalism.Per

namespace GlobalTheory.ConjNorm

theorem det_dvd_det {D : Type*} [CommRing D] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (V : Matrix m n D) (W : Matrix n m D) (M : Matrix n n D) (Y : Matrix m m D) (h1 : V * W = 1)
    (h2 : V * M = Y * V) : Y.det ∣ M.det := by
  have e : M = (1 + W * ((Y - 1) * V)) * ((1 - W * V) * M + W * V) := by
    have h3 : ∀ X : Matrix m n D, V * (W * X) = X := fun X => by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_assoc,
      h3, h2]
    abel
  rw [e, Matrix.det_mul, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, h1, Matrix.mul_one, add_sub_cancel]
  exact dvd_mul_right _ _

section Norm

variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]

theorem norm_map {A' S' ι : Type*} [CommRing A'] [CommRing S'] [Algebra A' S'] [Fintype ι]
    (b : Module.Basis ι A S) (b' : Module.Basis ι A' S') (f : A →+* A') (F : S →+* S')
    (hf : ∀ a, F (algebraMap A S a) = algebraMap A' S' (f a)) (hb : ∀ i, F (b i) = b' i) (x : S) :
    Algebra.norm A' (F x) = f (Algebra.norm A x) := by
  classical
  have hr : ∀ y i, b'.repr (F y) i = f (b.repr y i) := fun y i => by
    conv_lhs => rw [← b.sum_repr y]
    simp only [map_sum, Algebra.smul_def, map_mul, hf, hb]
    simp [← Algebra.smul_def, Finsupp.single_apply]
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b', RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, ← hb, ← map_mul, hr]

theorem prod_dvd_norm [Module.Free A S] [Module.Finite A S] {D m : Type*} [CommRing D] [Fintype m] [DecidableEq m]
    (φ : m → S →+* D) (ψ : A →+* D) (h : ∀ i a, φ i (algebraMap A S a) = ψ a) (c : m → S)
    (hc : IsUnit (Matrix.of fun i k => φ i (c k)).det) (x : S) : ∏ i, φ i x ∣ ψ (Algebra.norm A x) := by
  classical
  let b := Module.Free.chooseBasis A S
  have hr : ∀ i y, ∑ k, φ i (b k) * ψ (b.repr y k) = φ i y := fun i y => by
    conv_rhs => rw [← b.sum_repr y]
    simp only [map_sum, Algebra.smul_def, map_mul, h, mul_comm]
  rw [Algebra.norm_eq_matrix_det b, RingHom.map_det, ← Matrix.det_diagonal]
  refine det_dvd_det (Matrix.of fun i k => φ i (b k))
    ((Matrix.of fun k j => ψ (b.repr (c j) k)) * (Matrix.of fun i k => φ i (c k))⁻¹) _ _ ?_ ?_
  · rw [← Matrix.mul_assoc, ← Matrix.mul_nonsing_inv _ hc]
    congr 1
    ext i j
    exact hr i (c j)
  · ext i k
    rw [Matrix.diagonal_mul, Matrix.mul_apply, Matrix.of_apply, ← map_mul, ← hr]
    simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul]

theorem dvd_norm [Module.Free A S] [Module.Finite A S] (x : S) : x ∣ algebraMap A S (Algebra.norm A x) := by
  simpa using prod_dvd_norm (fun _ : Unit => RingHom.id S) (algebraMap A S) (fun _ _ => rfl) (fun _ => 1)
    (by simp) x

theorem mul_dvd_norm [Module.Free A S] [Module.Finite A S] {D : Type*} [CommRing D] (φ₁ φ₂ : S →+* D)
    (h : ∀ a, φ₂ (algebraMap A S a) = φ₁ (algebraMap A S a)) (c : S) (hc : IsUnit (φ₂ c - φ₁ c)) (x : S) :
    φ₁ x * φ₂ x ∣ φ₁ (algebraMap A S (Algebra.norm A x)) := by
  simpa using prod_dvd_norm ![φ₁, φ₂] (φ₁.comp (algebraMap A S)) (fun i a => by fin_cases i <;> simp [h])
    ![1, c] (by simpa [Matrix.det_fin_two] using hc) x

end Norm

variable {l : ℕ} [hl : Fact l.Prime] (K : FinExt l)

theorem norm_unif {π : ↥(OL K)} (hπ : Irreducible π) :
    ∃ u : W0 K, IsUnit u ∧ Algebra.norm (W0 K) π = (l : W0 K) * u := by
  haveI : FaithfulSMul (W0 K) ↥(OL K) := (faithfulSMul_iff_algebraMap_injective _ _).2 (thetaW_injective K)
  haveI : CharZero (W0 K) := (algebraMap (W0 K) ↥(OL K)).charZero
  let P := IsLocalRing.maximalIdeal ↥(OL K)
  let p := IsLocalRing.maximalIdeal (W0 K)
  haveI hlo : P.LiesOver p := by
    constructor
    have : (P.under (W0 K)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
    exact (IsLocalRing.eq_maximalIdeal this).symm
  have hrel := Ideal.relNorm_eq_pow_of_isMaximal P p
  have hf : P.inertiaDeg (W0 K) = 1 := by
    rw [Ideal.inertiaDeg_eq_of_isMaximal p P]
    letI := Ideal.Quotient.field p
    letI := Ideal.Quotient.field P
    refine Algebra.finrank_eq_one_iff_bijective_algebraMap.2 ⟨RingHom.injective _, fun y => ?_⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨w, hw⟩ := exists_thetaW (card_res K) x
    exact ⟨Ideal.Quotient.mk _ w, hw⟩
  have hP : P = Ideal.span {π} := hπ.maximalIdeal_eq
  have hp : p = Ideal.span {(l : W0 K)} := (WittVector.irreducible l).maximalIdeal_eq
  rw [hf, pow_one, hP, Ideal.relNorm_singleton, hp, Algebra.intNorm_eq_norm] at hrel
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hrel.symm
  exact ⟨u, u.isUnit, hu.symm⟩

theorem exists_lang (u : W0 K) (hu : IsUnit u) :
    ∃ a : Per.Ainf l, IsUnit a ∧ Per.φA l a = wA l (fK K) u * a := by
  obtain ⟨f⟩ := GlobalTheory.Per.nonempty_algClosure_zmod_to_tilt l
  have hr : ∀ x : Fq l (fK K), ∃ y, f y = Fq.val l (fK K) x := fun x => by
    have h1 := one_lt_pow_l l (fK K)
    have hm : (Polynomial.X ^ l ^ fK K - Polynomial.X : Polynomial (AlgebraicClosure (ZMod l))).Monic :=
      Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast h1)
    have h2 := congrArg (Polynomial.eval₂ f (Fq.val l (fK K) x))
      ((IsAlgClosed.splits _).eq_prod_roots_of_monic hm)
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, ← map_pow, Fq.pow_card, sub_self,
      Polynomial.eval₂_multiset_prod, eq_comm, Multiset.prod_eq_zero_iff, Multiset.map_map] at h2
    obtain ⟨y, -, hy⟩ := Multiset.mem_map.1 h2
    refine ⟨y, ?_⟩
    simp only [Function.comp, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C] at hy
    exact (sub_eq_zero.1 hy).symm
  choose r hr using hr
  let u' : WittVector l (AlgebraicClosure (ZMod l)) := WittVector.mk l fun n => r (u.coeff n)
  have hfu : WittVector.map f u' = wA l (fK K) u := WittVector.ext fun n => hr (u.coeff n)
  have hu' : IsUnit u' := WittVector.isUnit_of_coeff_zero_ne_zero _ fun h => by
    have h0 : u.coeff 0 ≠ 0 := (hu.map (WittVector.constantCoeff (p := l) (R := Fq l (fK K)))).ne_zero
    have h1 := hr (u.coeff 0)
    rw [show r (u.coeff 0) = 0 from h, map_zero, eq_comm, map_eq_zero] at h1
    exact h0 h1
  obtain ⟨w, hw, hφ⟩ := GlobalTheory.MemLoc.exists_unit_frobenius_eq_mul l _ u' hu'
  refine ⟨WittVector.map f w, hw.map _, ?_⟩
  rw [← hfu, ← map_mul, ← hφ]
  refine WittVector.ext fun n => ?_
  have h := GlobalTheory.AinfK.coeff_iter 1 (WittVector.map f w) n
  rw [Function.iterate_one, pow_one] at h
  rw [h, WittVector.map_coeff, WittVector.map_coeff, WittVector.coeff_frobenius_charP, map_pow]

end GlobalTheory.ConjNorm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectorOfIntegrableDiscreteSeriesCoefficient
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial MeasureTheory GlobalTheory.FockTensor

noncomputable section

namespace GlobalTheory.CoefProjector

variable {p q : ℕ} {T : GrpData p q}

theorem inner_opE (πU : URep T) {e : T.G → ℂ} (hi : Integrable e T.haar)
    (hc : Continuous e) (z x : πU.H) :
    inner ℂ z (opE T πU.π e x) = ∫ g, e g * inner ℂ z (πU.π g x) ∂T.haar := by
  have h : Integrable (fun g => e g • πU.π g x) T.haar := by
    refine Integrable.mono' (hi.norm.mul_const ‖x‖) (hc.smul (πU.cont x)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => ?_)
    rw [norm_smul, πU.isom]
  unfold opE
  rw [← integral_inner h]
  simp only [inner_smul_right]

theorem continuous_eFun (D : DSRep T) (v : D.HK.V) : Continuous (eFun D v) :=
  continuous_const.mul (continuous_const.inner (D.U.cont _)).star

theorem pi_mul (πU : URep T) (g h : T.G) (x : πU.H) : πU.π (g * h) x = πU.π g (πU.π h x) := by
  rw [map_mul]; rfl

theorem eFun_inv (D : DSRep T) (v : D.HK.V) (g : T.G) : eFun D v g⁻¹ = star (eFun D v g) := by
  simp only [eFun, mcoef]
  rw [← inner_pi_left]
  simp [inner_conj_symm]

theorem fdeg_ne (D : DSRep T) : (D.fdeg : ℂ) ≠ 0 := by exact_mod_cast D.fdeg_pos.ne'

theorem integral_eFun_mul (D : DSRep T) (v : D.HK.V) (w u : D.U.H) :
    ∫ g, eFun D v g * inner ℂ w (D.U.π g u) ∂T.haar = inner ℂ (D.ι v) u * inner ℂ w (D.ι v) := by
  have h := (GlobalTheory.SchurPol.schur_polarised p q T D u w (D.ι v) (D.ι v)).2
  have h2 : ∀ g, eFun D v g * inner ℂ w (D.U.π g u) =
      (D.fdeg : ℂ) * (inner ℂ w (D.U.π g u) * star (inner ℂ (D.ι v) (D.U.π g (D.ι v)))) := by
    intro g; simp only [eFun, mcoef]; ring
  simp only [h2]
  rw [integral_const_mul, h]
  have := fdeg_ne D
  have h3 : star (inner ℂ (D.ι v) w) = inner ℂ w (D.ι v) := inner_conj_symm _ _
  rw [h3]
  field_simp

theorem opE_self (D : DSRep T) (v : D.HK.V) (hi : Integrable (eFun D v) T.haar) (u : D.U.H) :
    opE T D.U.π (eFun D v) u = inner ℂ (D.ι v) u • D.ι v := by
  refine ext_inner_left ℂ fun w => ?_
  rw [inner_opE D.U hi (continuous_eFun D v), integral_eFun_mul, inner_smul_right]

theorem opE_selfAdjoint (D : DSRep T) (v : D.HK.V) (hi : Integrable (eFun D v) T.haar) (πU : URep T)
    (x y : πU.H) :
    inner ℂ (opE T πU.π (eFun D v) x) y = inner ℂ x (opE T πU.π (eFun D v) y) := by
  haveI := (GlobalTheory.HolDS.haar_unimodular p q T).2
  rw [← inner_conj_symm, inner_opE πU hi (continuous_eFun D v), inner_opE πU hi (continuous_eFun D v),
    ← integral_conj, ← integral_inv_eq_self]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [map_mul, inner_conj_symm, inner_pi_left, inv_inv, eFun_inv]
  simp

theorem eFun_conv (D : DSRep T) (v : D.HK.V) (x h : T.G) :
    ∫ g, eFun D v g * eFun D v (x⁻¹ * (g⁻¹ * h)) ∂T.haar = mcoef D v x * eFun D v h := by
  have h2 : ∀ g, eFun D v g * eFun D v (x⁻¹ * (g⁻¹ * h)) =
      (D.fdeg : ℂ) * (eFun D v g * inner ℂ (D.U.π h (D.ι v)) (D.U.π g (D.U.π x (D.ι v)))) := by
    intro g
    have : eFun D v (x⁻¹ * (g⁻¹ * h)) =
        (D.fdeg : ℂ) * inner ℂ (D.U.π h (D.ι v)) (D.U.π g (D.U.π x (D.ι v))) := by
      simp only [eFun, mcoef]
      rw [pi_mul, pi_mul, ← inner_pi_left, ← inner_pi_left]
      congr 1
      exact inner_conj_symm _ _
    rw [this]; ring
  simp only [h2]
  rw [integral_const_mul, integral_eFun_mul]
  simp only [eFun, mcoef]
  have h3 : star (inner ℂ (D.ι v) (D.U.π h (D.ι v))) = inner ℂ (D.U.π h (D.ι v)) (D.ι v) :=
    inner_conj_symm _ _
  rw [h3]; ring

theorem opE_pi_opE (D : DSRep T) (v : D.HK.V) (hi : Integrable (eFun D v) T.haar) (πU : URep T)
    (x : T.G) (y : πU.H) :
    opE T πU.π (eFun D v) (πU.π x (opE T πU.π (eFun D v) y)) =
      mcoef D v x • opE T πU.π (eFun D v) y := by
  have hc := continuous_eFun D v
  refine ext_inner_left ℂ fun z => ?_
  rw [inner_smul_right, inner_opE πU hi hc, inner_opE πU hi hc z y, ← integral_const_mul]
  have h1 : ∀ g, eFun D v g * inner ℂ z (πU.π g (πU.π x (opE T πU.π (eFun D v) y))) =
      ∫ h, eFun D v g * eFun D v (x⁻¹ * (g⁻¹ * h)) * inner ℂ z (πU.π h y) ∂T.haar := by
    intro g
    have e1 : inner ℂ z (πU.π g (πU.π x (opE T πU.π (eFun D v) y))) =
        inner ℂ (πU.π (g * x)⁻¹ z) (opE T πU.π (eFun D v) y) := by
      rw [inner_pi_left, inv_inv, pi_mul]
    rw [e1, inner_opE πU hi hc, ← integral_const_mul, ← integral_mul_left_eq_self _ (g * x)⁻¹]
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    simp only
    rw [pi_mul, inner_pi_pi, mul_inv_rev, mul_assoc x⁻¹, mul_assoc]
  simp only [h1]
  have hi' : Integrable (fun k => eFun D v (x⁻¹ * k)) T.haar := hi.comp_mul_left x⁻¹
  have hp := ((measurePreserving_prod_inv_mul T.haar T.haar).integrable_comp_of_integrable
    (hi.mul_prod hi'))
  have hcont : Continuous fun h : T.G × T.G => inner ℂ z (πU.π h.2 y) :=
    (continuous_const.inner (πU.cont y)).comp continuous_snd
  have hp2 := hp.mul_bdd (c := ‖z‖ * ‖y‖) hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun h => by
      simpa [πU.isom] using norm_inner_le_norm (𝕜 := ℂ) z (πU.π h.2 y))
  rw [integral_integral_swap hp2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only
  rw [integral_mul_const, eFun_conv, mul_assoc]

theorem dense_orbit (D : DSRep T) (u : D.U.H) (hu : u ≠ 0) :
    DenseRange (Finsupp.linearCombination ℂ fun g : T.G => D.U.π g u) := by
  have : Dense ((LinearMap.range (Finsupp.linearCombination ℂ fun g : T.G => D.U.π g u) :
      Submodule ℂ D.U.H) : Set D.U.H) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
      Submodule.eq_bot_iff]
    intro w hw
    have h := ext_orbit D u hu (innerSL ℂ w) 0 fun g => by
      refine Submodule.inner_left_of_mem_orthogonal ?_ hw
      exact ⟨Finsupp.single g 1, by simp⟩
    have h2 := congrArg (fun f : D.U.H →L[ℂ] ℂ => f w) h
    simpa using h2
  exact this

theorem exists_intertwiner (D : DSRep T) (v : D.HK.V) (hv : ‖D.ι v‖ = 1) (πU : URep T) (ξ : πU.H)
    (hξ : ∀ g, inner ℂ ξ (πU.π g ξ) = mcoef D v g * inner ℂ ξ ξ) :
    ∃ io : D.U.H →L[ℂ] πU.H, IsHomG D πU io ∧ io (D.ι v) = ξ ∧ ∀ x, ‖io x‖ = ‖ξ‖ * ‖x‖ := by
  have hu : D.ι v ≠ 0 := by
    intro h; rw [h, norm_zero] at hv; exact zero_ne_one hv
  set A := Finsupp.linearCombination ℂ fun g : T.G => D.U.π g (D.ι v) with hA
  set B := Finsupp.linearCombination ℂ fun g : T.G => πU.π g ξ with hB
  have hd : DenseRange A := dense_orbit D _ hu
  have hgram : ∀ g h, inner ℂ (πU.π g ξ) (πU.π h ξ) =
      inner ℂ (D.U.π g (D.ι v)) (D.U.π h (D.ι v)) * inner ℂ ξ ξ := by
    intro g h
    rw [inner_pi_left, inner_pi_left, ← pi_mul, ← pi_mul, hξ, mcoef]
  have hn : ∀ c, ‖B c‖ = ‖ξ‖ * ‖A c‖ := by
    intro c
    have h : inner ℂ (B c) (B c) = inner ℂ (A c) (A c) * inner ℂ ξ ξ := by
      simp only [hA, hB, Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
        inner_smul_left, inner_smul_right, hgram, Finset.sum_mul, mul_assoc]
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    have h' : ‖B c‖ ^ 2 = (‖ξ‖ * ‖A c‖) ^ 2 := by
      rw [mul_pow, mul_comm]; exact_mod_cast h
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h'
  have hT : ∀ c, B.extendOfNorm A (A c) = B c :=
    LinearMap.extendOfNorm_eq hd ⟨‖ξ‖, fun c => (hn c).le⟩
  have hg : ∀ g, B.extendOfNorm A (D.U.π g (D.ι v)) = πU.π g ξ := fun g => by
    simpa [hA, hB] using hT (Finsupp.single g 1)
  refine ⟨B.extendOfNorm A, fun g => ext_orbit D _ hu _ _ fun h => ?_, ?_, fun x => ?_⟩
  · show B.extendOfNorm A (D.U.π g (D.U.π h (D.ι v))) = πU.π g (B.extendOfNorm A (D.U.π h (D.ι v)))
    rw [← pi_mul, hg, hg, pi_mul]
  · simpa using hg 1
  · refine hd.induction_on (p := fun x => ‖B.extendOfNorm A x‖ = ‖ξ‖ * ‖x‖) x
      (isClosed_eq (by fun_prop) (by fun_prop)) fun c => ?_
    rw [hT, hn]

theorem projector_of_integrable_coefficient :
    ∀ (p q : ℕ) (T : GrpData p q) (D : DSRep T) (v : D.HK.V), ‖D.ι v‖ = 1 → MeasureTheory.Integrable (eFun D v) T.haar → (∀ u, opE T D.U.π (eFun D v) u = inner ℂ (D.ι v) u • D.ι v) ∧ ∀ πU : URep T, (∀ x y, inner ℂ (opE T πU.π (eFun D v) x) y = inner ℂ x (opE T πU.π (eFun D v) y)) ∧ (∀ g x, opE T πU.π (eFun D v) (πU.π g (opE T πU.π (eFun D v) x)) = mcoef D v g • opE T πU.π (eFun D v) x) ∧ ∀ ξ, opE T πU.π (eFun D v) ξ = ξ → ∃ io : D.U.H →L[ℂ] πU.H, IsHomG D πU io ∧ io (D.ι v) = ξ ∧ ∀ x, ‖io x‖ = ‖ξ‖ * ‖x‖ := by
  intro p q T D v hv hi
  refine ⟨opE_self D v hi, fun πU => ⟨opE_selfAdjoint D v hi πU, opE_pi_opE D v hi πU, fun ξ hξ => ?_⟩⟩
  refine exists_intertwiner D v hv πU ξ fun g => ?_
  have h1 := opE_selfAdjoint D v hi πU ξ (πU.π g (opE T πU.π (eFun D v) ξ))
  rw [opE_pi_opE D v hi, hξ, inner_smul_right] at h1
  exact h1

end GlobalTheory.CoefProjector
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsCoordsAndNonvanishingAtFinset
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem sections_coords_and_nonvanishing_at_finset : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (H : La), (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ (T : Finset Y) (G : La), ∃ k0 : ℕ, ∀ k ≥ k0, ∃ (t0 : ι → Y → ℂ) (t : Fin n → ι → Y → ℂ) (a : ι → Y → ℂ), A.IsSec (A.kap + k • H) t0 ∧ (∀ j, A.IsSec (A.kap + k • H) (t j)) ∧ A.IsSec (A.kap + (G + k • H)) a ∧ ∀ P ∈ T, t0 (A.pick P) P ≠ 0 ∧ A.IsCoordAt t0 t P ∧ a (A.pick P) P ≠ 0 := by
  intro n Y _ _ _ _ _ _ ι La _ A H hH T G
  obtain ⟨q, hq, hk9⟩ := GlobalTheory.T.exists_sections_approx_firstJets_positive n Y ι La A H hH T
  obtain ⟨ε, hε, hk10⟩ := GlobalTheory.T.quotient_jets_fderiv_det_ne_zero n
  obtain ⟨k0, hk0⟩ := hk9 0 (fun _ _ => 1) (fun _ => differentiable_const _) ε hε
  have hpj : ∀ j : Fin n, ∀ P : Y,
      Differentiable ℂ (fun v : V n => v j - (A.chart (A.pick P) P) j) := fun j P =>
    ((EuclideanSpace.proj (𝕜 := ℂ) j).differentiable).sub_const _
  choose kj hkj using fun j : Fin n =>
    hk9 0 (fun P v => v j - (A.chart (A.pick P) P) j) (hpj j) ε hε
  obtain ⟨ka, hka⟩ := hk9 G (fun _ _ => 1) (fun _ => differentiable_const _) (1/2) (by norm_num)
  refine ⟨max k0 (max ka (Finset.univ.sup kj)), fun k hk => ?_⟩
  have hk0' : k ≥ k0 := le_trans (le_max_left _ _) hk
  have hka' : k ≥ ka := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hkj' : ∀ j, k ≥ kj j := fun j =>
    le_trans (le_trans (Finset.le_sup (f := kj) (Finset.mem_univ j))
      (le_trans (le_max_right _ _) (le_max_right _ _))) hk
  obtain ⟨F0, hF0s, hF0⟩ := hk0 k hk0'
  choose Fj hFjs hFj using fun j => hkj j k (hkj' j)
  obtain ⟨Fa, hFas, hFa⟩ := hka k hka'
  rw [zero_add] at hF0s hFjs
  refine ⟨F0, Fj, Fa, hF0s, hFjs, hFas, fun P hP => ?_⟩
  set i := A.pick P with hi
  set p := A.chart i P with hp
  have hPs : P ∈ (A.chart i).source := A.mem_pick P
  have hpt : p ∈ (A.chart i).target := (A.chart i).map_source hPs
  have hsymm : (A.chart i).symm p = P := (A.chart i).left_inv hPs
  have hdiffF : ∀ F : ι → Y → ℂ, ∀ la, A.IsSec la F →
      DifferentiableAt ℂ (fun v => F i ((A.chart i).symm v)) p := by
    intro F la hF
    have h1 := hF.1 i
    have h2 : (A.chart i).target ∩ (A.chart i).symm ⁻¹' Set.univ = (A.chart i).target := by simp
    rw [h2] at h1
    exact h1.differentiableAt ((A.chart i).open_target.mem_nhds hpt)
  have hE : DifferentiableAt ℂ (fun v => Complex.exp (-((k : ℂ) * q P v))) p :=
    ((((hq P hP) p).const_mul (k : ℂ)).neg).cexp
  set w0 : V n → ℂ := fun v => F0 i ((A.chart i).symm v) * Complex.exp (-((k : ℂ) * q P v)) with hw0
  set w : Fin n → V n → ℂ := fun j v => Fj j i ((A.chart i).symm v) * Complex.exp (-((k : ℂ) * q P v)) with hw
  have hd0 : DifferentiableAt ℂ w0 p := (hdiffF F0 _ hF0s).mul hE
  have hdj : ∀ j, DifferentiableAt ℂ (w j) p := fun j => (hdiffF (Fj j) _ (hFjs j)).mul hE
  obtain ⟨h0a, h0b⟩ := hF0 P hP
  have e1 : ‖w0 p - 1‖ ≤ ε := by
    simp only [hw0, hsymm]; exact h0a
  have e2 : ‖fderiv ℂ (fun v => w0 v - 1) p‖ ≤ ε := h0b
  have e3 : ∀ j, ‖w j p‖ ≤ ε := by
    intro j
    have := (hFj j P hP).1
    simp only [sub_self, sub_zero] at this
    simp only [hw, hsymm]; exact this
  have e4 : ∀ j, ‖fderiv ℂ (fun v : V n => w j v - (v j - p j)) p‖ ≤ ε := fun j => (hFj j P hP).2
  obtain ⟨hne, hdet⟩ := hk10 p w0 w hd0 hdj e1 e2 e3 e4
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    apply hne
    simp only [hw0, hsymm, h0, zero_mul]
  · unfold WeightedAtlas.IsCoordAt
    have hfun : A.zLoc F0 Fj i = fun v : V n => (WithLp.toLp 2 (fun j => w j v / w0 v) : V n) := by
      funext v
      simp only [WeightedAtlas.zLoc, hw, hw0]
      congr 1
      funext j
      rw [mul_div_mul_right _ _ (Complex.exp_ne_zero _)]
    rw [← hi, ← hp, hfun]
    exact hdet
  · intro h0
    have := (hFa P hP).1
    rw [h0, zero_mul, zero_sub, norm_neg, norm_one] at this
    norm_num at this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPeriodEqPeriodOverThickeningStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylor_period_eq_period_over_thickening_alt : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam Empty g Λ} {B D : Type} [CommRing B] [CommRing D] [Algebra ℂ D] {X X₀ : Scheme.{0}} {s : X ⟶ Sp B} {s₀ : X₀ ⟶ Sp ℂ} {σ : B →+* Hol F.V} (e : Unif F s σ) (u₀ : Unif F₀ s₀ (algebraMap ℂ (Hol F₀.V))), X.IsSeparated → X₀.IsSeparated → 0 ∈ F.V → (∀ z, z ∈ F₀.V) → (∀ l z, F₀.τ l z = F.τ l 0) → ∀ (φ₀ : X₀ ⟶ X), (∀ p : Tot Empty g, u₀.E p ≫ φ₀ = e.E (0, p.2)) → ∀ (π : D →ₐ[ℂ] ℂ), IsNilpotent (RingHom.ker π) → ∀ {J : Ideal D} (dl : DividedPowers J), (∀ d ∈ J, π d = 0) → ∀ (N : ℕ) (t : I → D), (∀ i, π (t i) = 0) → (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (j : B →+* D), (∀ b, j b = taylor N t (σ b).fn) → ∀ (s' : X₀ ⟶ Sp D), s' = s₀ ≫ spMap (π : D →+* ℂ) → ∀ (n : IsMor (dp0 B) s dl s' j φ₀) (ψ : X₀ ⟶ X₀) (k : IsMor (dp0 ℂ) s₀ dl s' (algebraMap ℂ D) ψ), ψ = 𝟙 X₀ → ∀ (c : FirstDeRham s) (per : Λ →+ Hol F.V), IsPeriod e c per → ∀ {io : Type} (S : Finset io) (d : io → D) (a : io → FirstDeRham s₀) (p : io → Λ → ℂ) (p' : io → (Λ →+ Hol F₀.V)), (∀ i l, p' i l = algebraMap ℂ _ (p i l)) → (∀ i, IsPeriod u₀ (a i) (p' i)) → n.pull1 c = ∑ i ∈ S, d i • k.pull1 (a i) → ∀ l, ∑ i ∈ S, d i * algebraMap ℂ D (p i l) = taylor N t (per l).fn := by
  first | exact @GlobalTheory.GaussManinTaylor.taylor_period_eq_period_over_thickening | exact GlobalTheory.GaussManinTaylor.taylor_period_eq_period_over_thickening | (intros; apply GlobalTheory.GaussManinTaylor.taylor_period_eq_period_over_thickening <;> assumption)
end

