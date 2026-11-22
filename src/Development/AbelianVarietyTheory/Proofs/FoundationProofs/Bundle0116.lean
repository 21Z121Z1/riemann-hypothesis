import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0092
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0095
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0110
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0094
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0102
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowHeckeNorm
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTranslateNormProductEqOfDvdStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTranslateNormProduct_eq_of_dvd : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (M M' q : ℕ) (f : X.K), 0 < q → M ∣ M' → Nat.Coprime q M' → Lev X M f → Nq X M q f = Nq X M' q f := by
  first | exact @GlobalTheory.KZ.ES.Nq_eq_of_dvd | exact GlobalTheory.KZ.ES.Nq_eq_of_dvd | (intros; apply GlobalTheory.KZ.ES.Nq_eq_of_dvd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HomogeneousPolyCocycleDiffCoboundaryOfEqOn
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3

private theorem ent_gamma {K d : ℕ} (hd : d ∣ K) {δ : SL(2, ℤ)} (h : δ ∈ CongruenceSubgroup.Gamma K)
    (i j : Fin 2) :
    (((δ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod d) = (((1 : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod d) := by
  rw [CongruenceSubgroup.Gamma_mem] at h
  obtain ⟨h00, h01, h10, h11⟩ := h
  have key : ∀ x : ℤ, ∀ y : ZMod K, (x : ZMod K) = y → (x : ZMod d) = ZMod.castHom hd (ZMod d) y := by
    intro x y hxy; rw [← hxy, map_intCast]
  fin_cases i <;> fin_cases j
  · have := key _ _ h00; rw [map_one] at this; simpa using this
  · simpa using key _ _ h01
  · simpa using key _ _ h10
  · have := key _ _ h11; rw [map_one] at this; simpa using this

private theorem gamma_le {K d : ℕ} (hd : d ∣ K) {δ : SL(2, ℤ)} (h : δ ∈ CongruenceSubgroup.Gamma K) :
    δ ∈ CongruenceSubgroup.Gamma d := by
  rw [CongruenceSubgroup.Gamma_mem]
  have e := ent_gamma hd h
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using e 0 0
  · simpa using e 0 1
  · simpa using e 1 0
  · simpa using e 1 1

theorem adj_of_near : ∀ (N l w n : ℕ), 0 < N → l.Prime → l ≠ 2 → ¬ l ∣ N → Odd w →
    ∀ z z' : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)), IsCoc w (Gam N l) z → IsCoc w (Gam N l) z' →
    Near z z' → ∃ p : MvPolynomial (Fin 2) (ZMod (l ^ n)), p.IsHomogeneous w ∧
      ∀ γ ∈ Gam N l, z γ - z' γ = slP (γ : Matrix (Fin 2) (Fin 2) ℤ) p - p := by
  intro N l w n hN hl hl2 hlN hw z z' hz hz' hnear
  obtain ⟨M', hM', hM'eq⟩ := hnear
  obtain ⟨e, M, hlM, hMe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM'.ne' l hl.one_lt.ne'
  have hM : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h; simp at hMe; omega
    · exact h
  set a := max e n
  obtain ⟨c, hcG, hcomm, hcmod⟩ := GlobalTheory.T.exists_scalar_gamma1CapGamma0_mod_level N l a M hN hl hl2 hlN hM hlM
  obtain ⟨L1, L2, L3, -, -, L6, L7⟩ := GlobalTheory.T.twoVarPolySubstMatrix_basic_laws (ZMod (l ^ n))
  let R := ZMod (l ^ n)
  let V := MvPolynomial (Fin 2) R
  let G := ↥(Gam N l)
  let ρ : G → V →ₗ[R] V := fun g => (slP ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).toLinearMap
  let S : Submodule R V := MvPolynomial.homogeneousSubmodule (Fin 2) R w
  let K := M * N * l ^ a
  let Δ : Subgroup G := (CongruenceSubgroup.Gamma K).subgroupOf (Gam N l)
  have hρmul : ∀ g h v, ρ (g * h) v = ρ h (ρ g v) := by
    intro g h v
    simp only [ρ, AlgHom.toLinearMap_apply, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    exact L1 _ _ v
  have hρone : ∀ v, ρ 1 v = v := by
    intro v
    simp only [ρ, AlgHom.toLinearMap_apply, OneMemClass.coe_one, Matrix.SpecialLinearGroup.coe_one]
    exact L2 v
  have h2 : IsUnit (2 : R) := by
    have hc : Nat.Coprime 2 (l ^ n) :=
      Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_two hl).mpr (Ne.symm hl2))
    exact_mod_cast (ZMod.isUnit_iff_coprime 2 (l ^ n)).mpr hc
  have hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S := by
    intro g v hv
    exact L3 _ w v hv
  have hΔn : Δ.Normal := by
    haveI := CongruenceSubgroup.Gamma_normal (M * N * l ^ a)
    exact Subgroup.normal_subgroupOf
  have hM'K : M' ∣ K := by
    rw [hMe]
    have := mul_dvd_mul (pow_dvd_pow l (le_max_left e n)) (dvd_mul_right M N)
    simpa [K, mul_comm, mul_assoc, mul_left_comm] using this
  have hnK : l ^ n ∣ K := Dvd.dvd.mul_left (pow_dvd_pow l (le_max_right e n)) _
  have hΔ : ∀ δ ∈ Δ, ∀ v, ρ δ v = v := by
    intro δ hδ v
    rw [Subgroup.mem_subgroupOf] at hδ
    simp only [ρ, AlgHom.toLinearMap_apply]
    rw [L6 _ 1 v (ent_gamma hnK hδ), L2 v]
  let c' : G := ⟨c, hcG⟩
  have hc1 : ∀ v ∈ S, ρ c' v = -v := by
    intro v hv
    simp only [ρ, AlgHom.toLinearMap_apply, c']
    have hent : ∀ i j, (((c : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : R) = (((-1 : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : R) := by
      intro i j
      have h1 := congrArg (ZMod.castHom (pow_dvd_pow l (le_max_right e n)) R) (hcmod i j)
      rw [map_intCast] at h1
      rw [h1]
      by_cases hij : i = j
      · subst hij; rw [if_pos rfl, map_neg, map_one]; simp [Matrix.neg_apply]
      · simp [hij, Matrix.neg_apply, Matrix.one_apply]
    rw [L6 _ _ v hent, L7 w v hv, hw.neg_one_pow, neg_one_smul]
  have hc2 : ∀ g, c' * g * c'⁻¹ * g⁻¹ ∈ Δ := by
    intro g
    rw [Subgroup.mem_subgroupOf]
    exact hcomm g
  let zz : G → V := fun g => z g - z' g
  have hzS : ∀ g, zz g ∈ S := by
    intro g
    exact (hz.1 g g.2).sub (hz'.1 g g.2)
  have hzc : ∀ g h, zz (g * h) = ρ h (zz g) + zz h := by
    intro g h
    have hgh : ((g * h : G) : SL(2, ℤ)) = (g : SL(2, ℤ)) * h := rfl
    simp only [zz, ρ, AlgHom.toLinearMap_apply, map_sub]
    rw [hgh, hz.2 g g.2 h h.2, hz'.2 g g.2 h h.2]
    abel
  have hzΔ : ∀ δ ∈ Δ, zz δ = 0 := by
    intro δ hδ
    rw [Subgroup.mem_subgroupOf] at hδ
    simp only [zz]
    rw [hM'eq _ (gamma_le hM'K hδ), sub_self]
  obtain ⟨p, hpS, hp⟩ := GlobalTheory.T.cocycle_isCoboundary_of_neg_central_element G R V ρ hρmul hρone h2 S hS Δ hΔn hΔ c' hc1 hc2 zz hzS hzc hzΔ
  refine ⟨p, hpS, fun γ hγ => ?_⟩
  exact hp ⟨γ, hγ⟩

end GlobalTheory.KZ.H3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralConjugateSL2IntLawsStatement
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralConjugateSL2Int_laws : (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (M : ℕ), 0 < m.det → ∀ δ ∈ CongruenceSubgroup.Gamma (M * m.det.natAbs), m * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (cj m δ : Matrix (Fin 2) (Fin 2) ℤ) * m ∧ cj m δ ∈ CongruenceSubgroup.Gamma M) ∧ (∀ γ δ : SL(2, ℤ), cj (γ : Matrix (Fin 2) (Fin 2) ℤ) δ = γ * δ * γ⁻¹) ∧ (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (δ δ' : SL(2, ℤ)), 0 < m.det → m * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * m → ∀ z ∈ Hs, mob (toGQ m) (mob (ofSL δ) z) = mob (ofSL δ') (mob (toGQ m) z)) := by
  first | exact @GlobalTheory.KZ.cj_laws | exact GlobalTheory.KZ.cj_laws | (intros; apply GlobalTheory.KZ.cj_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgZpOfPow
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5

noncomputable section

namespace GlobalTheory.Glue.EvTwist

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

def part (N i : ℤ) (a : Lau p) : Lau p where
  coeff r := if r % N = i then a.coeff r else 0
  isPWO_support' := a.isPWO_support.mono (fun r hr h => hr (by simp [h]))

theorem part_coeff (N i : ℤ) (a : Lau p) (r : ℤ) :
    (part N i a).coeff r = if r % N = i then a.coeff r else 0 := rfl

def contr (N : ℤ) (hN : 0 < N) (b : Lau p) : Lau p where
  coeff j := b.coeff (N * j)
  isPWO_support' := by
    refine Set.IsWF.isPWO (BddBelow.wellFoundedOn_lt ⟨-|b.order|, fun j hj => ?_⟩)
    have h : b.order ≤ N * j := HahnSeries.order_le_of_coeff_ne_zero hj
    have h1 := neg_abs_le b.order
    have h2 := abs_nonneg b.order
    by_contra hc
    push_neg at hc
    nlinarith

theorem sum_ite {M : Type} [AddCommMonoid M] (N : ℕ) (hN : 0 < N) (r : ℤ) (f : ℕ → M) :
    ∑ i : Fin N, (if r % (N : ℤ) = ((i : ℕ) : ℤ) then f i else 0) = f (r % (N : ℤ)).toNat := by
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  have h0 := Int.emod_nonneg r hN'.ne'
  have h1 := Int.emod_lt_of_pos r hN'
  rw [Finset.sum_eq_single (⟨(r % (N : ℤ)).toNat, by omega⟩ : Fin N)]
  · rw [if_pos (by simp only; omega)]
  · intro i _ hi
    rw [if_neg]
    intro h
    exact hi (Fin.ext (by simp only; omega))
  · intro h; exact absurd (Finset.mem_univ _) h

theorem isAlgZp_of_pow {z : Ω} {N : ℕ} (hN : 0 < N) (h : z ^ N = 1) : IsAlgZp p z :=
  ⟨Polynomial.X ^ N - 1, by simpa using Polynomial.X_pow_sub_C_ne_zero hN (1 : ℤ_[p]), by simp [h]⟩

theorem isInt_of_pow {z : Ω} {N : ℕ} (hN : 0 < N) (h : z ^ N = 1) : IsInt p z :=
  IsIntegral.of_pow hN (by rw [h]; exact isIntegral_one)

end GlobalTheory.Glue.EvTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgebraicOfFiniteComplexAutomorphismOrbitStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAlgebraic_of_finite_complex_automorphism_orbit : ∀ (E : Subfield ℂ) (x : ℂ), (Set.range fun g : ℂ ≃ₐ[E] ℂ => g x).Finite → IsAlgebraic E x := by
  first | exact @GlobalTheory.FinOrbit.isAlgebraic_of_finite_orbit | exact GlobalTheory.FinOrbit.isAlgebraic_of_finite_orbit | (intros; apply GlobalTheory.FinOrbit.isAlgebraic_of_finite_orbit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspExpansionAtInfinityCompRatAffineStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspExpansionAtInfinity_comp_rat_affine : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (f f' : ℍ → ℂ) (l m : ℚ) (h h' : HahnSeries ℚ Ω), 0 < l → (∀ z ∈ Hs, up f' z = up f ((l : ℂ) * z + m)) → (∀ r : ℚ, ε (h'.coeff (r * l)) = Complex.exp (2 * Real.pi * Complex.I * ((r * m : ℚ) : ℂ)) * ε (h.coeff r)) → IsExp ε f h → IsExp ε f' h' := by
  first | exact @GlobalTheory.FN.isExp_comp_affine | exact GlobalTheory.FN.isExp_comp_affine | (intros; apply GlobalTheory.FN.isExp_comp_affine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFunctionalValueGalBEquivariantStatement
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspFunctionalValue_galB_equivariant : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n w : ℕ) (s : Ω ≃ₐ[ℚ] Ω), (l : Ω) ∈ A.nonunits → (∀ x, x ∈ A ↔ s x ∈ A) → ∀ b : X.Fn l, b ∈ X.B N l w → ∀ φ : HahnSeries ℚ Ω,
  IsThB X A N l n b φ → IsThB X A N l n (X.galB l s b) (HahnSeries.map φ (s : Ω →+* Ω)) := by
  first | exact @GlobalTheory.isThB_galB | exact GlobalTheory.isThB_galB | (intros; apply GlobalTheory.isThB_galB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowHeckeNormStatement
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLogDerivQExpansionModPrimePow_heckeNorm : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (l : ℕ) [Fact l.Prime] (n : ℕ) (f : X.K) (φ : HahnSeries ℚ Ω),
  X.sl (ofSL ModularGroup.T) f = f → (∀ r : ℚ, φ.coeff r ≠ 0 → r.den = 1) → IsDl X A l n 1 f φ →
  IsDl X A l n 1 (∏ j ∈ Finset.range l, X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) f) (hq ε l φ) := by
  first | exact @GlobalTheory.NormDl.isDl_norm | exact GlobalTheory.NormDl.isDl_norm | (intros; apply GlobalTheory.NormDl.isDl_norm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowRescaleStatement
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLogDerivQExpansionModPrimePow_rescale : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n N : ℕ) (s : ℚ) (f : X.K) (φ φ' : HahnSeries ℚ Ω), 0 < N → (∀ r : ℚ, φ'.coeff r = φ.coeff (r / N)) → (IsDl X A l n s f φ ↔ IsDl X A l n (s / N) (X.sl (toGQ !![(N : ℤ), 0; 0, 1]) f) φ') := by
  first | exact @GlobalTheory.Glue.isDl_rescale | exact GlobalTheory.Glue.isDl_rescale | (intros; apply GlobalTheory.Glue.isDl_rescale <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionUpperTriangularActionStatement
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLogDerivQExpansion_upperTriangular_action : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n : ℕ) (g : GQ), ent g 1 0 = 0 → 0 < ent g 0 0 → 0 < ent g 1 1 → algebraMap ℚ Ω (ent g 0 0 / ent g 1 1) ∈ A →
  ∀ (f : X.K) (φ : HahnSeries ℚ Ω), IsDl X A l n 1 f φ →
    IsDl X A l n 1 (X.sl g f) (HahnSeries.C (algebraMap ℚ Ω (ent g 0 0 / ent g 1 1)) * sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) φ) := by
  first | exact @GlobalTheory.DlUp.isDl_sl_upper | exact GlobalTheory.DlUp.isDl_sl_upper | (intros; apply GlobalTheory.DlUp.isDl_sl_upper <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KroneckerCongruenceFrobeniusDiagStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kronecker_congruence_frobenius_diag : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (q : ℕ), q.Prime → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), FrobV V q s → ∀ a : X.K, IntC X V a → SmallC X V (X.sl (toGQ !![(q : ℤ), 0; 0, 1]) a - (X.gal s.symm a) ^ q) := by
  first | exact @GlobalTheory.KZ.ES.kron_frob_diag | exact GlobalTheory.KZ.ES.kron_frob_diag | (intros; apply GlobalTheory.KZ.ES.kron_frob_diag <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KroneckerHeckeProductInvariantPrincipalLevelStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kroneckerHeckeProduct_invariant_principal_level : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M q : ℕ) (σ : SL(2, ℤ)) (f : X.K), 0 < M → q.Prime → Nat.Coprime q M → (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) → ((en σ 0 1 : ZMod M) = 0 ∧ (en σ 1 0 : ZMod M) = 0 ∧ (en σ 1 1 : ZMod M) = q) → ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) f) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f) = ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) f) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f) := by
  first | exact @GlobalTheory.kronecker_product_level | exact GlobalTheory.kronecker_product_level | (intros; apply GlobalTheory.kronecker_product_level <;> assumption)
end

