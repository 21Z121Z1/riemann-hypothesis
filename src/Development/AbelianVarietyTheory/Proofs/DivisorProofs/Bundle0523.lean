import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0503
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0511
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0508
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0514
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0509
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumDeformedLatticeEisensteinSummandWeightTwo
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory.WeightTwoCompare

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem prodCpow {J : Type} (t : Finset J) (f : J → ℝ) (hf : ∀ j, 0 ≤ f j) (w : ℂ) :
    ∏ j ∈ t, ((f j : ℝ) : ℂ) ^ w = (((∏ j ∈ t, f j : ℝ)) : ℂ) ^ w := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf a) (Finset.prod_nonneg fun j _ => hf j)]

theorem norm_cpow_eq_exp {h : ℂ} (hh : h ≠ 0) (σ : ℂ) :
    ((‖h‖ : ℝ) : ℂ) ^ (-2 * σ) = Complex.exp (-σ * ((Real.log (Complex.normSq h) : ℝ) : ℂ)) := by
  have hn : ((‖h‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hh
  rw [Complex.cpow_def_of_ne_zero hn, ← Complex.ofReal_log (norm_nonneg _), Complex.normSq_eq_norm_sq,
    Real.log_pow]
  congr 1
  push_cast
  ring

variable [IsCMField E]

theorem defCoord_eq (φ : I → E →+* ℂ) (e : I ≃ Emb (maximalRealSubfield E))
    (he : ∀ (i : I) (a : maximalRealSubfield E), φ i (a : E) = ((e i a : ℝ) : ℂ)) (θ : E) {z : I → ℂ}
    (hz : z ∈ polydisc I) (a b : maximalRealSubfield E) (i : I) :
    defCoord φ z ((a : E) + (b : E) * θ) i =
      (1 + z i) / (2 * (Real.pi : ℂ) * Complex.I) * latPt (modPt φ e θ z) (a, b) (e i) := by
  have h1 := one_add_ne_zero hz i
  have hπ : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero this) Complex.I_ne_zero
  simp only [defCoord, latPt, modPt, Equiv.symm_apply_apply, map_add, map_mul, he, Complex.conj_ofReal]
  field_simp
  ring

theorem defTerm_eq (φ : I → E →+* ℂ) (e : I ≃ Emb (maximalRealSubfield E))
    (he : ∀ (i : I) (a : maximalRealSubfield E), φ i (a : E) = ((e i a : ℝ) : ℂ)) (θ : E) {z : I → ℂ}
    (hz : z ∈ polydisc I) (σ : ℂ) (a b : maximalRealSubfield E) :
    defTerm φ 2 z σ ((a : E) + (b : E) * θ) =
      (homFac z)⁻¹ ^ 2 * Complex.exp (-σ * logFac z) * eisTerm 2 σ (modPt φ e θ z) (a, b) := by
  set w := latPt (modPt φ e θ z) (a, b)
  set c : I → ℂ := fun i => (1 + z i) / (2 * (Real.pi : ℂ) * Complex.I)
  have hc : homFac z = ∏ i, c i := rfl
  have hw : ∏ τ, w τ = ∏ i, w (e i) := (Equiv.prod_comp e w).symm
  unfold defTerm eisTerm logFac
  simp only [defCoord_eq φ e he θ hz a b]
  rw [Finset.prod_mul_distrib]
  have h1 : ∏ i, (c i * w (e i))⁻¹ ^ 2 = (homFac z)⁻¹ ^ 2 * (∏ τ, w τ)⁻¹ ^ 2 := by
    rw [hc, hw, ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib, ← Finset.prod_pow, ← Finset.prod_pow,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_inv, mul_pow]
  have h2 : ∏ i, ((‖c i * w (e i)‖ : ℝ) : ℂ) ^ (-2 * σ) =
      ((‖homFac z‖ : ℝ) : ℂ) ^ (-2 * σ) * ((‖∏ τ, w τ‖ : ℝ) : ℂ) ^ (-2 * σ) := by
    rw [prodCpow _ _ (fun i => norm_nonneg _), hc, hw, norm_prod, norm_prod,
      ← Complex.mul_cpow_ofReal_nonneg (Finset.prod_nonneg fun i _ => norm_nonneg _)
        (Finset.prod_nonneg fun i _ => norm_nonneg _), ← Complex.ofReal_mul, ← Finset.prod_mul_distrib]
    simp only [norm_mul]
  rw [h1, h2, norm_cpow_eq_exp (homFac_ne_zero hz)]
  ring

end GlobalTheory.WeightTwoCompare

namespace GlobalTheory.WeightTwoCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem eq_of_add_mul {θ : E} (hθ : θ ∉ maximalRealSubfield E) {a b a' b' : maximalRealSubfield E}
    (h : (a : E) + (b : E) * θ = (a' : E) + (b' : E) * θ) : a = a' ∧ b = b' := by
  by_cases hb : b = b'
  · subst hb
    refine ⟨Subtype.ext ?_, rfl⟩
    simpa using h
  · exfalso
    apply hθ
    have hb' : ((b : E) - (b' : E)) ≠ 0 := by
      intro h0; apply hb; exact Subtype.ext (sub_eq_zero.1 h0)
    have : θ = ((a' : E) - (a : E)) / ((b : E) - (b' : E)) := by
      field_simp
      linear_combination h
    rw [this]
    exact div_mem (sub_mem a'.2 a.2) (sub_mem b.2 b'.2)

end GlobalTheory.WeightTwoCompare

namespace GlobalTheory.WeightTwoCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem algebraMap_unit (u : (OF E)ˣ) :
    algebraMap (OF E) E (u : OF E) = (((u : 𝓞 (maximalRealSubfield E)) : maximalRealSubfield E) : E) := rfl

noncomputable def classMap (𝔞 𝔟 : Frac (maximalRealSubfield E)) (θ : E) (L : Set E) (hθ : θ ∉ maximalRealSubfield E)
    (hL : ∀ x : E, x ∈ L ↔ ∃ a ∈ latM 𝔞, ∃ b ∈ (𝔟 : FractionalIdeal (𝓞 (maximalRealSubfield E))⁰ (maximalRealSubfield E)),
      x = (a : E) + (b : E) * θ)
    (c : Quotient (latRel 𝔞 𝔟)) : modUnits L :=
  ⟨Quotient.mk _ ((c.out.1.1 : E) + (c.out.1.2 : E) * θ),
    (c.out.1.1 : E) + (c.out.1.2 : E) * θ, (hL _).2 ⟨_, c.out.2.1, _, c.out.2.2.1, rfl⟩, fun h0 => c.out.2.2.2 (by
      have h := eq_of_add_mul hθ (a := c.out.1.1) (b := c.out.1.2) (a' := 0) (b' := 0) (by simpa using h0)
      exact Prod.ext h.1 h.2), rfl⟩

end GlobalTheory.WeightTwoCompare

namespace GlobalTheory.WeightTwoCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem classMap_bijective (𝔞 𝔟 : Frac (maximalRealSubfield E)) (θ : E) (L : Set E) (hθ : θ ∉ maximalRealSubfield E)
    (hL : ∀ x : E, x ∈ L ↔ ∃ a ∈ latM 𝔞, ∃ b ∈ (𝔟 : FractionalIdeal (𝓞 (maximalRealSubfield E))⁰ (maximalRealSubfield E)),
      x = (a : E) + (b : E) * θ) :
    Function.Bijective (classMap 𝔞 𝔟 θ L hθ hL) := by
  constructor
  · intro c c' h
    have h1 := Quotient.exact (congrArg Subtype.val h)
    obtain ⟨u, hu⟩ := h1
    rw [algebraMap_unit, mul_add, ← mul_assoc, ← Subfield.coe_mul, ← Subfield.coe_mul] at hu
    obtain ⟨ha, hb⟩ := eq_of_add_mul hθ hu
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    exact Quotient.sound ⟨u, ha, hb⟩
  · rintro ⟨q, x, hxL, hx0, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := (hL x).1 hxL
    have hp : ((a, b) : maximalRealSubfield E × maximalRealSubfield E) ≠ 0 := by
      intro h0
      apply hx0
      have h1 : a = 0 := congrArg Prod.fst h0
      have h2 : b = 0 := congrArg Prod.snd h0
      simp [h1, h2]
    let p : LatPair 𝔞 𝔟 := ⟨(a, b), ha, hb, hp⟩
    refine ⟨Quotient.mk _ p, Subtype.ext ?_⟩
    obtain ⟨ε, h1, h2⟩ : (latRel 𝔞 𝔟).r (Quotient.mk (latRel 𝔞 𝔟) p).out p := Quotient.exact (Quotient.out_eq _)
    show Quotient.mk _ _ = Quotient.mk _ _
    refine Quotient.sound ⟨ε, ?_⟩
    rw [algebraMap_unit]
    have e1 : a = p.1.1 := rfl
    have e2 : b = p.1.2 := rfl
    rw [e1, e2, h1, h2, Subfield.coe_mul, Subfield.coe_mul]
    ring

end GlobalTheory.WeightTwoCompare

namespace GlobalTheory.WeightTwoCompare

theorem hasSum_defTerm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (e : I ≃ Emb (maximalRealSubfield E)), (∀ (i : I) (a : maximalRealSubfield E), φ i (a : E) = ((e i a : ℝ) : ℂ)) →
    ∀ (𝔞 𝔟 : Frac (maximalRealSubfield E)) (θ : E) (L : Set E), θ ∉ maximalRealSubfield E →
    (∀ x : E, x ∈ L ↔ ∃ a ∈ latM 𝔞, ∃ b ∈ (𝔟 : FractionalIdeal (𝓞 (maximalRealSubfield E))⁰ (maximalRealSubfield E)),
      x = (a : E) + (b : E) * θ) →
    ∀ z ∈ polydisc I, ∀ (σ S : ℂ), HasSum (eisClass 𝔞 𝔟 2 σ (modPt φ e θ z)) S →
      HasSum (fun q : modUnits L => defTerm φ 2 z σ q.1.out) ((homFac z)⁻¹ ^ 2 * Complex.exp (-σ * logFac z) * S) := by
  intro E _ _ _ I _ φ e he 𝔞 𝔟 θ L hθ hL z hz σ S hS
  let g := Equiv.ofBijective _ (classMap_bijective 𝔞 𝔟 θ L hθ hL)
  rw [← g.hasSum_iff]
  have key1 : ∀ c, defTerm φ 2 z σ (g c).1.out =
      (homFac z)⁻¹ ^ 2 * Complex.exp (-σ * logFac z) * eisClass 𝔞 𝔟 2 σ (modPt φ e θ z) c := by
    intro c
    set x : E := (c.out.1.1 : E) + (c.out.1.2 : E) * θ with hx
    have hg : (g c).1 = Quotient.mk _ x := rfl
    obtain ⟨u, hu⟩ : unitRel.r x (g c).1.out := Quotient.exact (by rw [hg, Quotient.out_eq])
    rw [hu, hx, algebraMap_unit, mul_add, ← mul_assoc, ← Subfield.coe_mul, ← Subfield.coe_mul,
      defTerm_eq φ e he θ hz, eisTerm_unit (by decide)]
    rfl
  have key : (fun q : modUnits L => defTerm φ 2 z σ q.1.out) ∘ g =
      fun c => (homFac z)⁻¹ ^ 2 * Complex.exp (-σ * logFac z) * eisClass 𝔞 𝔟 2 σ (modPt φ e θ z) c := by
    funext c
    simp only [Function.comp_apply]
    exact key1 c
  rw [key]
  exact hS.mul_left _

end GlobalTheory.WeightTwoCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertDiagonalRestrictionCoeffIsAlgebraic
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma coeff_mul_mem_algebraicClosure {f g : PowerSeries ℂ}
    (hf : ∀ n, PowerSeries.coeff n f ∈ algebraicClosure ℚ ℂ)
    (hg : ∀ n, PowerSeries.coeff n g ∈ algebraicClosure ℚ ℂ) (n : ℕ) :
    PowerSeries.coeff n (f * g) ∈ algebraicClosure ℚ ℂ := by
  rw [PowerSeries.coeff_mul]
  exact sum_mem fun p _ ↦ mul_mem (hf _) (hg _)

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma coeff_pow_mem_algebraicClosure {f : PowerSeries ℂ}
    (hf : ∀ n, PowerSeries.coeff n f ∈ algebraicClosure ℚ ℂ) (e : ℕ) :
    ∀ n, PowerSeries.coeff n (f ^ e) ∈ algebraicClosure ℚ ℂ := by
  induction e with
  | zero =>
    intro n
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | succ e ih =>
    rw [pow_succ]
    exact coeff_mul_mem_algebraicClosure ih hf

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma isAlgebraic_exp_two_pi_I_mul_rat (q : ℚ) :
    IsAlgebraic ℚ (Complex.exp (2 * ↑Real.pi * Complex.I * (q : ℂ))) := by
  refine (IsIntegral.of_pow q.den_pos ?_).isAlgebraic
  have h : Complex.exp (2 * ↑Real.pi * Complex.I * (q : ℂ)) ^ q.den = 1 := by
    rw [← Complex.exp_nat_mul]
    have hq : (q : ℂ) * q.den = q.num := by exact_mod_cast Rat.mul_den_eq_num q
    have hmul : (q.den : ℂ) * (2 * ↑Real.pi * Complex.I * (q : ℂ)) =
        (q.num : ℂ) * (2 * ↑Real.pi * Complex.I) := by
      linear_combination (2 * ↑Real.pi * Complex.I) * hq
    rw [hmul, Complex.exp_int_mul_two_pi_mul_I]
  rw [h]
  exact isIntegral_one

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma isAlgebraic_realEmbedding_apply {F : Type} [Field F] [NumberField F]
    (i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F) (y : F) : IsAlgebraic ℚ ((i y : ℝ) : ℂ) :=
  (Algebra.IsAlgebraic.isAlgebraic y).algHom (Complex.ofRealHom.comp i).toRatAlgHom

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma ecoef_mem_algebraicClosure_of_isCoef {F : Type} [Field F] [NumberField F] {k : ℕ}
    {𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F} {a₀ : ℂ} {a : F → ℂ}
    (ha : _root_.GlobalTheory.HilbFam.IsCoef k 𝔞 𝔟 a₀ a) (ha₀ : IsAlgebraic ℚ a₀) (N : ℕ)
    (x : F) (μ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ) (n : ℕ) :
    _root_.GlobalTheory.HilbFam.ecoef N a x μ n ∈ algebraicClosure ℚ ℂ := by
  unfold _root_.GlobalTheory.HilbFam.ecoef
  refine finsum_mem_induction _ (zero_mem _) (fun _ _ ↦ add_mem) fun ξ _ ↦ ?_
  refine mul_mem (mul_mem ?_ ?_) (prod_mem fun i _ ↦ pow_mem ?_ _)
  · rw [mem_algebraicClosure_iff]
    by_cases hξ : ξ = 0
    · rw [hξ, ha.1]
      exact ha₀
    · obtain ⟨m, hm⟩ := ha.2.1 ξ hξ
      rw [hm]
      exact isAlgebraic_int _
  · rw [mem_algebraicClosure_iff]
    unfold _root_.GlobalTheory.HilbFam.eTr
    exact isAlgebraic_exp_two_pi_I_mul_rat _
  · rw [mem_algebraicClosure_iff]
    exact isAlgebraic_realEmbedding_apply i ξ

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in

theorem _root_.GlobalTheory.HilbFam.hser_coeff_isAlgebraic : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (s N : ℕ) (κ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ) (c : ℕ → ℂ) (n : ℕ), k = 2 * s → _root_.GlobalTheory.HilbFam.IsCoef k 𝔞 𝔟 a₀ a → IsAlgebraic ℚ a₀ → (∀ m, IsAlgebraic ℚ (c m)) → IsAlgebraic ℚ (PowerSeries.coeff n (_root_.GlobalTheory.HilbFam.hser k N 𝔞 a x κ c)) := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x s N κ c n hk ha ha₀ hc
  rw [← mem_algebraicClosure_iff]
  unfold _root_.GlobalTheory.HilbFam.hser
  simp only [map_smul, map_sum, smul_eq_mul]
  refine mul_mem ?_ (sum_mem fun μ _ ↦ mul_mem (intCast_mem _ _) ?_)
  · rw [hk, _root_.GlobalTheory.HilbFam.omegaFactor_pow_two_mul]
    exact SubfieldClass.ratCast_mem _ _
  · refine coeff_mul_mem_algebraicClosure
      (coeff_pow_mem_algebraicClosure (fun m ↦ ?_) _) (fun m ↦ ?_) n
    · rw [PowerSeries.coeff_mk, mem_algebraicClosure_iff]
      exact hc m
    · rw [PowerSeries.coeff_mk]
      exact ecoef_mem_algebraicClosure_of_isCoef ha ha₀ N x μ m

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinValueLinearTransfer
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

variable {F : Type} [Field F] [NumberField F]

set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
variable {F : Type} [Field F] [NumberField F] in
theorem _root_.GlobalTheory.HilbFam.transf_units_smul (T : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) (ε : (𝓞 F)ˣ) (x : Fin 2 → F) :
    T (ε • x) = ε • T x := by
  change T.toLinearMap ((ε : 𝓞 F) • x) = (ε : 𝓞 F) • T.toLinearMap x
  exact LinearMap.map_smul_of_tower T.toLinearMap _ _

noncomputable def transfQuot (T : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) :
    Quotient (MulAction.orbitRel (𝓞 F)ˣ (Fin 2 → F)) ≃ Quotient (MulAction.orbitRel (𝓞 F)ˣ (Fin 2 → F)) :=
  Quotient.congr T.toEquiv (by
    intro x y
    simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨ε, rfl⟩
      exact ⟨ε, (transf_units_smul T ε y).symm⟩
    · rintro ⟨ε, h⟩
      refine ⟨ε, T.injective ?_⟩
      rw [transf_units_smul]
      exact h)

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousCorrectionNextLevel
section
open MvPolynomial

namespace GlobalTheory.UnifCorr

variable {R : Type} [CommRing R] {σ : Type}

theorem coeff_X_pow_mul_mem (I : Ideal R) (i : σ) (k : ℕ) (G : MvPolynomial σ R)
    (h : ∀ m, coeff m G ∈ I) : ∀ m, coeff m ((X i : MvPolynomial σ R) ^ k * G) ∈ I := by
  intro m
  rw [X_pow_eq_monomial, coeff_monomial_mul']
  split_ifs
  · exact I.mul_mem_left _ (h _)
  · exact I.zero_mem

theorem mem_of_coeff_mem (I : Ideal R) (K : Ideal (MvPolynomial σ R))
    (hC : ∀ a ∈ I, C a ∈ K) (G : MvPolynomial σ R) (h : ∀ m, coeff m G ∈ I) : G ∈ K := by
  rw [G.as_sum]
  refine K.sum_mem fun v _ => ?_
  rw [← mul_one (coeff v G), ← C_mul_monomial]
  exact K.mul_mem_right _ (hC _ (h v))

end GlobalTheory.UnifCorr

open GlobalTheory.UnifCorr in
theorem GlobalTheory.homogeneous_correction_next_level : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (n : ℕ) (K : ℕ → Ideal (MvPolynomial (Fin (n + 1)) R)), (∀ (e t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → (∀ i, ∃ N : ℕ, (X i : MvPolynomial (Fin (n + 1)) R) ^ N * F ∈ K e) → F ∈ K e) → (∀ e, ∀ a ∈ I ^ (e + 1), C a ∈ K e) → (∀ (e t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → F ∈ K e → ∀ i, ∃ (N : ℕ) (G : MvPolynomial (Fin (n + 1)) R), G.IsHomogeneous (t + N) ∧ (∀ m, coeff m G ∈ I ^ (e + 1)) ∧ (X i : MvPolynomial (Fin (n + 1)) R) ^ N * F - G ∈ K (e + 1)) → ∃ t₀ : ℕ, ∀ t, t₀ ≤ t → ∀ (e : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → F ∈ K e → ∃ G : MvPolynomial (Fin (n + 1)) R, G.IsHomogeneous t ∧ (∀ m, coeff m G ∈ I ^ (e + 1)) ∧ F - G ∈ K (e + 1) := by
  intro R _ _ I n K hsat hC hstep
  have hcoef : ∀ e (G : MvPolynomial (Fin (n + 1)) R), (∀ m, coeff m G ∈ I ^ (e + 1)) → G ∈ K e :=
    fun e G h => mem_of_coeff_mem (I ^ (e + 1)) (K e) (hC e) G h
  have hJ : ∀ (e t : ℕ) (a : R) (F : MvPolynomial (Fin (n + 1)) R), a ∈ I → F.IsHomogeneous t →
      (∀ m, coeff m F ∈ I ^ e) → F ∈ K e → C a * F ∈ K (e + 1) := by
    intro e t a F ha hF _ hFK
    have hCF : (C a * F).IsHomogeneous t := by
      have := (isHomogeneous_C (Fin (n + 1)) a).mul hF
      rwa [zero_add] at this
    apply hsat (e + 1) t (C a * F) hCF
    intro i
    obtain ⟨N, G, _, hGc, hk⟩ := hstep e t F hF hFK i
    refine ⟨N, ?_⟩
    have h1 : C a * G ∈ K (e + 1) := by
      apply hcoef (e + 1)
      intro m
      rw [coeff_C_mul]
      have := Ideal.mul_mem_mul ha (hGc m)
      rwa [← pow_succ'] at this
    have : (X i : MvPolynomial (Fin (n + 1)) R) ^ N * (C a * F) = C a * (X i ^ N * F - G) + C a * G := by ring
    rw [this]
    exact add_mem ((K (e + 1)).mul_mem_left _ hk) h1
  obtain ⟨d₀, hd₀⟩ := GlobalTheory.T.uniform_serre_sections_alt R I n K hJ
  refine ⟨d₀, fun t ht e F hF hFK => ?_⟩
  choose N G hG hGc hk using hstep e t F hF hFK
  obtain ⟨M, hNM⟩ : ∃ M, ∀ i, N i ≤ M :=
    ⟨∑ i, N i, fun i => Finset.single_le_sum (fun j _ => Nat.zero_le (N j)) (Finset.mem_univ i)⟩
  let G' : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R := fun i => X i ^ (M - N i) * G i
  have hXM : ∀ i, (X i : MvPolynomial (Fin (n + 1)) R) ^ M = X i ^ (M - N i) * X i ^ N i := fun i => by
    rw [← pow_add, Nat.sub_add_cancel (hNM i)]
  have hG'h : ∀ i, (G' i).IsHomogeneous (t + M) := fun i => by
    show (X i ^ (M - N i) * G i).IsHomogeneous (t + M)
    rw [show t + M = (M - N i) + (t + N i) by have := hNM i; omega]
    exact (isHomogeneous_X_pow i (M - N i)).mul (hG i)
  have hG'c : ∀ i m, coeff m (G' i) ∈ I ^ (e + 1) := fun i => coeff_X_pow_mul_mem _ i _ _ (hGc i)
  have hk' : ∀ i, (X i : MvPolynomial (Fin (n + 1)) R) ^ M * F - G' i ∈ K (e + 1) := fun i => by
    have : (X i : MvPolynomial (Fin (n + 1)) R) ^ M * F - G' i = X i ^ (M - N i) * (X i ^ N i * F - G i) := by
      simp only [G', hXM i]; ring
    rw [this]; exact (K (e + 1)).mul_mem_left _ (hk i)
  obtain ⟨G0, hG0, hG0c, hL⟩ := hd₀ t ht (e + 1) M G' hG'h hG'c (fun i j => ⟨0, by
    have : ((X i : MvPolynomial (Fin (n + 1)) R) * X j) ^ 0 * (X j ^ M * G' i - X i ^ M * G' j)
        = X i ^ M * (X j ^ M * F - G' j) - X j ^ M * (X i ^ M * F - G' i) := by ring
    rw [this]
    exact sub_mem ((K (e + 1)).mul_mem_left _ (hk' j)) ((K (e + 1)).mul_mem_left _ (hk' i))⟩)
  refine ⟨G0, hG0, hG0c, ?_⟩
  apply hsat (e + 1) t (F - G0) (hF.sub hG0)
  intro i
  obtain ⟨L, hLi⟩ := hL i
  refine ⟨L + M, ?_⟩
  have : (X i : MvPolynomial (Fin (n + 1)) R) ^ (L + M) * (F - G0)
      = X i ^ L * (X i ^ M * F - G' i) + X i ^ L * (G' i - X i ^ M * G0) := by ring
  rw [this]
  exact add_mem ((K (e + 1)).mul_mem_left _ (hk' i)) hLi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureProjectiveOverStandardOpenRingStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralClosure_projective_over_standardOpenRing : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ i, Module.Projective (rA k x {i}) (integralClosure (rA k x {i}) K) := by
  first | (exact @GlobalTheory.integralClosure_projective_rA) | (exact GlobalTheory.integralClosure_projective_rA) | (intros; apply GlobalTheory.integralClosure_projective_rA  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMultipleInLieLatticeStatement
section
open NumberField Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_multiple_in_lie_lattice : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → ∀ X : Matrix (Fin r) (Fin r) E, X.trace = 0 → (∀ x y, herm G (X *ᵥ x) y + herm G x (X *ᵥ y) = 0) → ∃ N : ℕ, 0 < N ∧ (N : E) • X ∈ lieLat G Λ := by
  first | exact @GlobalTheory.DenClear.exists_natSmul_mem_lieLat | exact GlobalTheory.DenClear.exists_natSmul_mem_lieLat | (intros; apply GlobalTheory.DenClear.exists_natSmul_mem_lieLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageAndFiniteAppOfIsFiniteRestri
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory

theorem isAffineOpen_preimage_and_finite_app_of_isFinite_restrict :
    ∀ (X Z : Scheme.{0}) (φ : X ⟶ Z) (V : Z.Opens), IsAffineOpen V → IsFinite (φ ∣_ V) →
      IsAffineOpen (φ ⁻¹ᵁ V) ∧ (φ.app V).hom.Finite := by
  intro X Z φ V hV hf
  haveI : IsAffine (V : Scheme) := hV
  have h1 : IsAffine (φ ⁻¹ᵁ V : Scheme) := isAffine_of_isAffineHom (φ ∣_ V)
  refine ⟨h1, ?_⟩
  have h2 := hf.finite_app ⊤ (isAffineOpen_top _)
  rw [morphismRestrict_app] at h2
  have e : V.ι ''ᵁ ⊤ = V := by simp
  rw [← e]
  exact (RingHom.finite_respectsIso.cancel_right_isIso _ _).mp h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionMorphismRestrictBasicOpenOfMulM
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory

theorem appLE_basicOpen_surjective_of_mul_mem_range {X Z : Scheme.{0}} (φ : X ⟶ Z) {V : Z.Opens}
    (haff : IsAffineOpen (φ ⁻¹ᵁ V)) (r : Γ(Z, V))
    (h : ∀ c : Γ(X, φ ⁻¹ᵁ V), ∃ b : Γ(Z, V), (φ.app V).hom r * c = (φ.app V).hom b)
    (A : Z.Opens) (B : X.Opens) (e : B ≤ φ ⁻¹ᵁ A) (hA : A = Z.basicOpen r)
    (hB : B = X.basicOpen ((φ.app V).hom r)) : Function.Surjective (φ.appLE A B e) := by
  subst hA hB
  set s := (φ.app V).hom r with hs
  intro y
  let resX : Γ(X, φ ⁻¹ᵁ V) →+* Γ(X, X.basicOpen s) := (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom
  let resZ : Γ(Z, V) →+* Γ(Z, Z.basicOpen r) := (Z.presheaf.map (homOfLE (Z.basicOpen_le r)).op).hom
  let g := (φ.appLE (Z.basicOpen r) (X.basicOpen s) e).hom
  haveI := haff.isLocalization_basicOpen s
  obtain ⟨⟨c, ⟨_, n, rfl⟩⟩, hc⟩ := IsLocalization.surj (Submonoid.powers s) y
  obtain ⟨b, hb⟩ := h c
  have hu : IsUnit (resZ r) := Z.toRingedSpace.isUnit_res_basicOpen r
  have hv : IsUnit (resX s) := X.toRingedSpace.isUnit_res_basicOpen s
  have hg : ∀ t, g (resZ t) = resX (φ.app V t) := by
    intro t
    simp only [g, resZ, resX]
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rfl
  have hc' : y * resX s ^ n = resX c := by rw [← map_pow]; exact hc
  let x := resZ b * ((hu.unit⁻¹ : (Γ(Z, Z.basicOpen r))ˣ) : Γ(Z, Z.basicOpen r)) ^ (n + 1)
  refine ⟨x, ?_⟩
  have hx : g x * resX s ^ (n + 1) = y * resX s ^ (n + 1) := by
    calc g x * resX s ^ (n + 1) = g (x * resZ r ^ (n + 1)) := by rw [RingHom.map_mul g x (resZ r ^ (n + 1)), map_pow, hg r]
      _ = g (resZ b) := by
          congr 1
          simp only [x, mul_assoc, ← mul_pow]
          rw [show ((hu.unit⁻¹ : (Γ(Z, Z.basicOpen r))ˣ) : Γ(Z, Z.basicOpen r)) * resZ r = 1 from
            hu.val_inv_mul, one_pow, mul_one]
      _ = resX (φ.app V b) := hg b
      _ = resX (s * c) := by rw [hb]
      _ = y * resX s ^ (n + 1) := by rw [map_mul, ← hc']; ring
  exact (hv.pow (n + 1)).mul_left_inj.1 hx

theorem isClosedImmersion_morphismRestrict_basicOpen_of_mul_mem_range :
    ∀ (X Z : Scheme.{0}) (φ : X ⟶ Z) (V : Z.Opens), IsAffineOpen V → IsAffineOpen (φ ⁻¹ᵁ V) →
      ∀ r : Γ(Z, V), (∀ c : Γ(X, φ ⁻¹ᵁ V), ∃ b : Γ(Z, V), (φ.app V).hom r * c = (φ.app V).hom b) →
        IsClosedImmersion (φ ∣_ Z.basicOpen r) := by
  intro X Z φ V hV haff r h
  have hpre : φ ⁻¹ᵁ Z.basicOpen r = X.basicOpen ((φ.app V).hom r) := Scheme.preimage_basicOpen φ r
  haveI : IsAffine (Z.basicOpen r) := hV.basicOpen r
  haveI : IsAffine (φ ⁻¹ᵁ Z.basicOpen r) := by
    have := haff.basicOpen ((φ.app V).hom r)
    rw [← hpre] at this
    exact this
  apply IsClosedImmersion.of_surjective_of_isAffine
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, morphismRestrict_appLE]
  exact appLE_basicOpen_surjective_of_mul_mem_range φ haff r h _ _ _ (by simp) (by simp [hpre])

end GlobalTheory
end

