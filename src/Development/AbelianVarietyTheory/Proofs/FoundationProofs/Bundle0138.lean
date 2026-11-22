import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0084
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0131
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0113
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0132
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0158
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0237
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0133
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlmostPurityMovesIntegersOfNeOne
section
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem moves_of_ne_one : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → 0 < v (p : L) → v (p : L) < 1 → ∀ (G : Type) [Group G] [MulSemiringAction G L] [Finite G] [FaithfulSMul G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ ζ : L, IsPrimitiveRoot ζ p → (∀ g : G, g • ζ = ζ) → ApproxRoot p v (Fix L (⊤ : Subgroup G)) → ∀ σ : G, σ ≠ 1 → Moves v ⊤ σ := by
  intro L _ v p hp hp0 hp1 G _ _ _ _ hinv ζ hζ hζfix hroot σ hσ
  obtain ⟨N, hNn, hNmem, i, hi, hNi⟩ := GlobalTheory.T.exists_normal_subgroup_not_moves_uniform_bound L v G hinv
  by_contra hmov
  have hσN : σ ∈ N := (hNmem σ).2 hmov
  have hfixN : ∀ τ ∈ N, ∀ x ∈ Fix L N, τ • x = x := fun τ hτ x hx => hx ⟨τ, hτ⟩
  have hdesc : ∀ τ : G, τ ∉ N → Moves v (Fix L N) τ := fun τ hτ =>
    GlobalTheory.T.movesIntegersAlmostUnitDistance_fixedSubfield L v G hinv N i hi hNi τ (by_contra fun h => hτ ((hNmem τ).2 h))
  have hsep : AlmostSep v N := GlobalTheory.T.fixedFieldAlmostEtale_of_moves_integers L v G hinv N hNn inferInstance hdesc
  have hF : ApproxRoot p v (Fix L N) := GlobalTheory.T.approxPthRoot_fixedSubfield_of_almostEtale L v p hp hp0 hp1 G hinv N inferInstance hsep hroot
  have hpg : IsPGroup p N := by
    intro τ
    set n := orderOf (τ : G) with hn
    have hn0 : n ≠ 0 := (orderOf_pos (τ : G)).ne'
    set k := n.factorization p
    refine ⟨k, ?_⟩
    have hcop : Nat.Coprime (n / p ^ k) p := (Nat.coprime_ordCompl hp hn0).symm
    have hτ' : ((τ : G) ^ (p ^ k)) ∈ N := N.pow_mem τ.2 _
    by_contra hne
    have hne' : (τ : G) ^ (p ^ k) ≠ 1 := by
      intro h; apply hne; ext; simpa using h
    have hl : ((τ : G) ^ (p ^ k)) ^ (n / p ^ k) = 1 := by
      rw [← pow_mul, Nat.mul_div_cancel' (Nat.ordProj_dvd n p), hn, pow_orderOf_eq_one]
    obtain ⟨y, hy⟩ : ∃ y : L, ((τ : G) ^ (p ^ k)) • y ≠ y := by
      by_contra h
      push_neg at h
      exact hne' (eq_of_smul_eq_smul (α := L) (fun y => by rw [h y, one_smul]))
    exact (hNmem _).1 hτ' (GlobalTheory.T.movesIntegersAlmostUnit_of_coprime_order L v p hp (Fix L N) hF hp0 hp1 G hinv _ (hfixN _ hτ') _ hcop hl ⟨y, hy⟩)
  haveI : Nontrivial N := ⟨⟨⟨σ, hσN⟩, 1, fun h => hσ (congrArg Subtype.val h)⟩⟩
  haveI : FaithfulSMul N L := ⟨fun {a b} h => Subtype.ext (eq_of_smul_eq_smul (α := L) h)⟩
  obtain ⟨σ₀, α, hα0, hσα, hαp⟩ := GlobalTheory.T.exists_lagrange_resolvent_of_pGroup_faithful L p hp N hpg ζ hζ (fun g => hζfix g)
  have hαF : α ^ p ∈ Fix L N := fun g => hαp g
  exact (hNmem _).1 σ₀.2 (GlobalTheory.T.kummer_automorphism_moves_integers_almost_unit L v p hp (Fix L N) hF hp0 hp1 G (σ₀ : G) (hfixN _ σ₀.2) ζ α hζ hα0 hαF hσα)

end GlobalTheory.AlmostEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BinaryFormCoeffOfGamma1CapGamma0InvariantStatement
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.binaryForm_coeff_of_gamma1CapGamma0_invariant : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], [IsAlgClosed Ω] → ∀ (N w : ℕ) (b : X.Fn l) (c : Fin (w + 1) → X.Khat l), (∀ u, b u = ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • c i) → ∀ γ ∈ Gam N l, X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b → ∀ i, c i = ∑ k, (cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) • X.kmap l (X.sl (ofSL γ)).toRingEquiv (c k) := by
  first | exact @GlobalTheory.KZ.H3.coef_of_inv | exact GlobalTheory.KZ.H3.coef_of_inv | (intros; apply GlobalTheory.KZ.H3.coef_of_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EigEqZeroOfMemAugOfNotIntertwineStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_mem_aug_of_isEig_of_not_intertwine : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (J N : Set G) (θ : G → ℂ), Datum J θ → Datum N (fun _ => 1) → (∀ y ∈ N, (y ∈ J ∧ θ y = 1) ∨ ∃ j ∈ J, y * j * y⁻¹ ∈ J ∧ θ j ≠ θ (y * j * y⁻¹)) → ∀ u ∈ aug π N (fun _ => 1), IsEig π J θ u → u = 0 := by
  first | exact @GlobalTheory.PsType.eig_eq_zero_of_mem_aug_of_not_intertwine | exact GlobalTheory.PsType.eig_eq_zero_of_mem_aug_of_not_intertwine | (intros; apply GlobalTheory.PsType.eig_eq_zero_of_mem_aug_of_not_intertwine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqUnitMulPowCyclotomicUniformizerStatement
section
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_unit_mul_pow_cyclotomic_uniformizer : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω), ∀ b ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), b ≠ 0 → ∃ (n k : ℕ), 1 ≤ n ∧ ∃ u ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), ∃ u' ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), u * u' = 1 ∧ b = u * (T.ζ n - 1) ^ k := by
  first | exact @GlobalTheory.K5.UnitPow.eq_unit_mul_pow | exact GlobalTheory.K5.UnitPow.eq_unit_mul_pow | (intros; apply GlobalTheory.K5.UnitPow.eq_unit_mul_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalSeriesCongIffCoeffAndIsUnit
section
open scoped MatrixGroups NNReal
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.Glue.EvInj

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

def zpHom (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] : ℤ_[p] →+* Ω :=
  (algebraMap (O0 p) Ω).comp ((algebraMap (Lau p) (O0 p)).comp HahnSeries.C)

theorem zp_eq (z : ℤ_[p]) : zp Ω z = zpHom p Ω z := by
  simp [zp, zpHom, HahnSeries.C_apply]

theorem psi_C {T : GlobalTheory.K5.Tower p Ω} {n : ℕ} {ψ : O0 p →+* Ω} (h : IsReb T n ψ) (z : ℤ_[p]) :
    ψ (algebraMap (Lau p) (O0 p) (HahnSeries.C z)) = zp Ω z := by
  have hpn : ((p : ℤ) ^ n) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  rw [h.sub (HahnSeries.C z) (HahnSeries.C z), zp, HahnSeries.C_apply]
  · intro i
    by_cases hi : i = 0
    · simp [hi, HahnSeries.C_apply, HahnSeries.coeff_single]
    · have : (p : ℤ) ^ n * i ≠ 0 := mul_ne_zero hpn hi
      simp [hi, this, HahnSeries.C_apply, HahnSeries.coeff_single]
  · intro r hr
    have : r ≠ 0 := by rintro rfl; exact hr (dvd_zero _)
    simp [this, HahnSeries.C_apply, HahnSeries.coeff_single]

theorem psi_int {T : GlobalTheory.K5.Tower p Ω} {n : ℕ} {ψ : O0 p →+* Ω} (h : IsReb T n ψ) (y : O0 p) :
    IsInt p (ψ y) := by
  have hq : IsIntegral (O0 p) (T.qq n) := by
    refine IsIntegral.of_pow (pow_pos (Fact.out : p.Prime).pos n) ?_
    rw [GlobalTheory.K5.Basic.qq_pow]; exact isIntegral_algebraMap
  have hm : ψ y ∈ ψ.range := ⟨y, rfl⟩
  rw [h.rng, Subalgebra.mem_toSubring] at hm
  exact adjoin_le_integralClosure hq hm

theorem dvd_C_iff (k : ℕ) (z : ℤ_[p]) : (p : Lau p) ^ k ∣ HahnSeries.C z ↔ (p : ℤ_[p]) ^ k ∣ z := by
  rw [GlobalTheory.K5.Basic.natCast_pow_dvd_iff]
  constructor
  · intro h; simpa [HahnSeries.C_apply, HahnSeries.coeff_single] using h 0
  · intro h m
    by_cases hm : m = 0
    · simpa [hm, HahnSeries.C_apply, HahnSeries.coeff_single] using h
    · simp [hm, HahnSeries.C_apply, HahnSeries.coeff_single]

section Val

variable (v : Valuation Ω ℝ≥0)

theorem cong_iff (hv : ∀ x, v x ≤ 1 ↔ IsInt p x) (hp0 : 0 < v (p : Ω)) (k : ℕ) (y : Ω) :
    Cong p k y 0 ↔ v y ≤ v (p : Ω) ^ k := by
  have hpk : (p : Ω) ^ k ≠ 0 := by
    intro h
    have := congrArg v h
    rw [map_pow, map_zero] at this
    exact (pow_pos hp0 k).ne' this
  constructor
  · rintro ⟨z, hz, e⟩
    rw [sub_zero] at e
    rw [e, map_mul, map_pow]
    exact mul_le_of_le_one_right zero_le' ((hv z).2 hz)
  · intro hy
    refine ⟨y / (p : Ω) ^ k, (hv _).1 ?_, by rw [sub_zero]; field_simp⟩
    rw [map_div₀, map_pow]
    exact div_le_one_of_le₀ hy zero_le'

def S (ψ : O0 p →+* Ω) {E F : ℕ} (π : Ω) (κ : Fin F → Ω) (b : Fin F → Fin E → Lau p) : Ω :=
  ∑ j, ∑ s : Fin E, κ j * π ^ (s : ℕ) * ψ (algebraMap (Lau p) (O0 p) (b j s))

theorem S_mul (ψ : O0 p →+* Ω) {E F : ℕ} (π : Ω) (κ : Fin F → Ω) (m : ℕ) (b : Fin F → Fin E → Lau p) :
    S ψ π κ (fun j s => (p : Lau p) ^ m * b j s) = (p : Ω) ^ m * S ψ π κ b := by
  simp only [S, map_mul, map_pow, map_natCast, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun s _ => by ring

theorem S_le_one (ψ : O0 p →+* Ω) {E F : ℕ} (π : Ω) (κ : Fin F → Ω) (hπ : v π ≤ 1) (hκ : ∀ j, v (κ j) ≤ 1)
    (hψ : ∀ y, v (ψ y) ≤ 1) (b : Fin F → Fin E → Lau p) : v (S ψ π κ b) ≤ 1 := by
  refine v.map_sum_le fun j _ => v.map_sum_le fun s _ => ?_
  rw [map_mul, map_mul, map_pow]
  exact mul_le_one' (mul_le_one' (hκ j) (pow_le_one' hπ _)) (hψ _)

theorem key_k (hp0 : 0 < v (p : Ω)) (hp1 : v (p : Ω) < 1) (ψ : O0 p →+* Ω) {E F : ℕ} (π : Ω) (κ : Fin F → Ω)
    (hπ : v π ≤ 1) (hκ : ∀ j, v (κ j) ≤ 1) (hψ : ∀ y, v (ψ y) ≤ 1)
    (K1 : ∀ b : Fin F → Fin E → Lau p, v (S ψ π κ b) ≤ v (p : Ω) → ∀ j s, (p : Lau p) ∣ b j s) :
    ∀ (k : ℕ) (b : Fin F → Fin E → Lau p), v (S ψ π κ b) ≤ v (p : Ω) ^ k ↔ ∀ j s, (p : Lau p) ^ k ∣ b j s := by
  intro k
  induction k with
  | zero => intro b; simpa using S_le_one v ψ π κ hπ hκ hψ b
  | succ k ih =>
    intro b
    constructor
    · intro h
      have h1 : ∀ j s, (p : Lau p) ∣ b j s :=
        K1 b (h.trans (pow_le_of_le_one zero_le' hp1.le (Nat.succ_ne_zero k)))
      choose b' hb' using h1
      have hb : b = fun j s => (p : Lau p) ^ 1 * b' j s := by
        funext j s; rw [pow_one]; exact hb' j s
      rw [hb, S_mul, map_mul, map_pow, pow_one, pow_succ'] at h
      have h2 : v (S ψ π κ b') ≤ v (p : Ω) ^ k := le_of_mul_le_mul_left h hp0
      intro j s
      rw [hb' j s, pow_succ']
      exact mul_dvd_mul_left _ ((ih b').1 h2 j s)
    · intro h
      choose b' hb' using h
      have hb : b = fun j s => (p : Lau p) ^ (k + 1) * b' j s := by
        funext j s; exact hb' j s
      rw [hb, S_mul, map_mul, map_pow]
      exact mul_le_of_le_one_right zero_le' (S_le_one v ψ π κ hπ hκ hψ b')

end Val

end GlobalTheory.Glue.EvInj

end

open GlobalTheory.Glue.EvInj in

theorem GlobalTheory.Glue.ev_cong_iff_and_unit : ∀ (p : ℕ) [Fact p.Prime], ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (n : ℕ), ∀ (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ (k : ℕ) (c : ℤ → Ω) (x x' : Ω), Ev ψ c x x' → ((Cong p k x 0 ↔ ∀ r, Cong p k (c r) 0) ∧ ((∃ r, c r ≠ 0 ∧ IsInt p (c r)⁻¹) → x ≠ 0 ∧ IsInt p x⁻¹)) := by
  intro p _ Ω _ _ hC T n ψ hψ k c x x' hEv
  obtain ⟨v, hv, -, hp0, hp1⟩ := GlobalTheory.K5.exists_valuation_isInt p Ω hC
  obtain ⟨d, e, a, he, hc, hx, -⟩ := hEv
  have hψv : ∀ y, v (ψ y) ≤ 1 := fun y => (hv _).2 (psi_int hψ y)
  have hzp : ∀ z : ℤ_[p], v (zp Ω z) ≤ 1 := fun z => (hv _).2 (by rw [zp]; exact isIntegral_algebraMap)
  have hev : ∀ t, v (e t) ≤ 1 := fun t => (hv _).2 (he t).1
  have hcv : ∀ r, v (c r) ≤ 1 := fun r => by
    rw [hc r]; exact v.map_sum_le fun t _ => by rw [map_mul]; exact mul_le_one' (hev t) (hzp _)
  have hxv : v x ≤ 1 := by
    rw [hx]; exact v.map_sum_le fun t _ => by rw [map_mul]; exact mul_le_one' (hev t) (hψv _)
  refine ⟨?_, ?_⟩
  · obtain ⟨E, F, π, κ, lam, hE, -, hπE, hκ, hκu, hesp⟩ := GlobalTheory.T.exists_integral_basis_of_integral_algebraic_elements p Ω hC v hv hp0 hp1 d e he
    have hπ1 : v π < 1 := by
      by_contra h
      push_neg at h
      have h2 : 1 ≤ v π ^ E := one_le_pow₀ h
      rw [hπE] at h2
      exact absurd hp1 (not_lt.2 h2)
    have hκv : ∀ j, v (κ j) ≤ 1 := fun j => (hv _).2 (hκ j).1
    have LeviInductionForms : ∀ b : Fin F → Lau p, v (∑ j, κ j * ψ (algebraMap (Lau p) (O0 p) (b j))) < 1 →
        ∀ j, (p : Lau p) ∣ b j := by
      intro b hb j
      have hr := GlobalTheory.T.residue_linear_disjointness_coeff_lt_one p Ω hC v hv hp1 T n ψ hψ F κ b (fun j => hκ j) hb
      rw [← pow_one (p : Lau p), GlobalTheory.K5.Basic.natCast_pow_dvd_iff]
      intro r
      by_contra hnd
      have h1 := hκu (fun j => (b j).coeff r) ⟨j, by simpa using hnd⟩
      have h2 := hr r
      rw [h1] at h2
      exact lt_irrefl _ h2
    have K1 := GlobalTheory.T.ramified_divisibility_of_unramified_divisibility p Ω v ψ E F π κ hE hp0 hp1 hπE hκv hψv LeviInductionForms
    have Kk := key_k v hp0 hp1 ψ π κ hπ1.le hκv hψv K1
    obtain ⟨B, hB⟩ : ∃ B : Fin F → Fin E → Lau p, ∀ j s, B j s = ∑ t, HahnSeries.C (lam t j s) * a t :=
      ⟨_, fun _ _ => rfl⟩
    have hx2 : x = S ψ π κ B := by
      simp only [S, hB, map_sum, map_mul, psi_C hψ, hx, hesp, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring
    have hc2 : ∀ r, c r = S ψ π κ (fun j s => HahnSeries.C ((B j s).coeff r)) := by
      intro r
      simp only [S, psi_C hψ, hB, HahnSeries.coeff_sum, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
        smul_eq_mul, zp_eq, map_sum, map_mul, hc, hesp, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by
        rw [← HahnSeries.C_mul_eq_smul, map_mul, map_mul, psi_C hψ, psi_C hψ, zp_eq, zp_eq]
        ring
    rw [cong_iff v hv hp0, hx2, Kk]
    simp_rw [cong_iff v hv hp0, hc2, Kk, dvd_C_iff, GlobalTheory.K5.Basic.natCast_pow_dvd_iff]
    exact ⟨fun h r j s => h j s r, fun h j s r => h r j s⟩
  · rintro ⟨r, hr0, hri⟩
    have hcr : v (c r) = 1 := by
      refine le_antisymm (hcv r) ?_
      have h1 := (hv _).2 hri
      rw [map_inv₀] at h1
      have h0 : v (c r) ≠ 0 := (Valuation.ne_zero_iff v).2 hr0
      exact (inv_le_one₀ (pos_iff_ne_zero.2 h0)).1 h1
    have hx1 : v x = 1 := by
      refine le_antisymm hxv (not_lt.1 fun hlt => ?_)
      have h3 := GlobalTheory.T.residue_linear_disjointness_coeff_lt_one p Ω hC v hv hp1 T n ψ hψ d e a he (by rwa [← hx]) r
      rw [← hc r, hcr] at h3
      exact lt_irrefl _ h3
    have hx0 : x ≠ 0 := by
      intro h
      rw [h, map_zero] at hx1
      exact zero_ne_one hx1
    exact ⟨hx0, (hv _).1 (by rw [map_inv₀, hx1, inv_one])⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlgebraicNumberCongrModPrimePowStatement
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraicNumber_congr_mod_prime_pow : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (A : ValuationSubring Ω) (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ j : Ω →+* Ωl, (∀ x, x ∈ A ↔ IsInt p (j x)) → ∀ (k : ℕ) (e : Ωl), IsInt p e → IsAlgZp p e → ∃ a ∈ A, Cong p k e (j a) := by
  first | exact @GlobalTheory.K5.DenseAlg.exists_mem_cong | exact GlobalTheory.K5.DenseAlg.exists_mem_cong | (intros; apply GlobalTheory.K5.DenseAlg.exists_mem_cong <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoeffwiseConjugateOfIntegralQuotient
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FN

theorem conjEx_hasQ_zero (N : ℕ) : HasQ N (fun _ => (0 : ℂ)) (fun _ => 0) := fun _ => by
  simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)

theorem conjEx_conv_coeff (a b : ℕ → ℂ) (n : ℕ) :
    conv a b n = PowerSeries.coeff n (PowerSeries.mk a * PowerSeries.mk b) := by
  simp [conv, PowerSeries.coeff_mul]

theorem conjEx_conv_map (g : ℂ ≃+* ℂ) (a b : ℕ → ℂ) :
    (fun n => g (conv a b n)) = conv (fun n => g (a n)) (fun n => g (b n)) := by
  funext n; simp [conv, map_sum, map_mul]

theorem conjEx_conv_cancel (a b d : ℕ → ℂ) (hd : d ≠ 0) (h : conv a d = conv b d) : a = b := by
  have hmk : PowerSeries.mk d ≠ 0 := by
    intro h0; apply hd; funext n
    have := congrArg (PowerSeries.coeff n) h0
    simpa using this
  have hm : PowerSeries.mk a * PowerSeries.mk d = PowerSeries.mk b * PowerSeries.mk d := by
    ext n
    have := congrFun h n
    rwa [conjEx_conv_coeff, conjEx_conv_coeff] at this
  have := mul_right_cancel₀ hmk hm
  funext n
  have := congrArg (PowerSeries.coeff n) this
  simpa using this

theorem conj_exists : ∀ (g : ℂ ≃+* ℂ) (N n : ℕ) (f D D' A A' : ℍ → ℂ) (s s' : Fin n → ℍ → ℂ), 0 < N → (∃ a, HasQ N f a) → QConj g N D D' → QConj g N A A' → (∀ j, QConj g N (s j) (s' j)) → D ≠ 0 → (∀ τ, f τ * D τ = A τ) → (∀ τ, f τ ^ n + ∑ j, s j τ * f τ ^ (j : ℕ) = 0) → ∃ f' : ℍ → ℂ, QConj g N f f' ∧ ∀ τ, f' τ * D' τ = A' τ := by
  intro g N n f D D' A A' s s' hN ⟨a, ha⟩ ⟨d, hd, hd'⟩ ⟨e, he, he'⟩ hs hD hfA hpol
  obtain ⟨uc, uf⟩ := GlobalTheory.QFam.hasQ_unique_both
  have hz := conjEx_hasQ_zero N
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hD (uf N D (fun _ => 0) _ hd hz)
  have hgd0 : (fun n => g (d n)) ≠ 0 := by
    intro h0; apply hd0; funext k
    have := congrFun h0 k
    simpa using this
  have hD' : D' ≠ 0 := by
    rintro rfl
    exact hgd0 (uc N (fun _ => 0) _ _ hN hd' hz)
  obtain ⟨_, hadd, _, hmul, hpow, hsumprod⟩ := GlobalTheory.QFam.qConj_ring g N hN
  have hA : QConj g N A A' := ⟨e, he, he'⟩
  have hDD : QConj g N D D' := ⟨d, hd, hd'⟩
  have hP : QConj g N (fun τ => A τ ^ n + ∑ j, s j τ * A τ ^ (j : ℕ) * D τ ^ (n - j))
      (fun τ => A' τ ^ n + ∑ j, s' j τ * A' τ ^ (j : ℕ) * D' τ ^ (n - j)) := by
    refine hadd _ _ _ _ (hpow _ _ n hA) ?_
    refine (hsumprod (Fin n) Finset.univ (fun j τ => s j τ * A τ ^ (j : ℕ) * D τ ^ (n - j))
      (fun j τ => s' j τ * A' τ ^ (j : ℕ) * D' τ ^ (n - j)) ?_).1
    intro j _
    exact hmul _ _ _ _ (hmul _ _ _ _ (hs j) (hpow _ _ _ hA)) (hpow _ _ _ hDD)
  have hP0 : (fun τ => A τ ^ n + ∑ j, s j τ * A τ ^ (j : ℕ) * D τ ^ (n - j)) = fun _ => 0 := by
    funext τ
    have hx : A τ ^ n + ∑ j, s j τ * A τ ^ (j : ℕ) * D τ ^ (n - j) =
        D τ ^ n * (f τ ^ n + ∑ j, s j τ * f τ ^ (j : ℕ)) := by
      rw [mul_add, Finset.mul_sum, ← hfA τ, mul_pow]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro j _
        rw [mul_pow, show D τ ^ n = D τ ^ (j : ℕ) * D τ ^ (n - j) by
          rw [← pow_add, Nat.add_sub_cancel' j.2.le]]
        ring
    rw [hx, hpol τ, mul_zero]
  have hP'0 : ∀ τ, A' τ ^ n + ∑ j, s' j τ * A' τ ^ (j : ℕ) * D' τ ^ (n - j) = 0 := by
    obtain ⟨c, hc, hc'⟩ := hP
    rw [hP0] at hc
    have hc0 : c = fun _ => 0 := uc N _ _ _ hN hc hz
    subst hc0
    simp only [map_zero] at hc'
    have := uf N _ _ _ hc' hz
    exact fun τ => congrFun this τ
  obtain ⟨h, b, hb, hAh⟩ := GlobalTheory.T.exists_hasQ_quotient_of_integral N n A' D' s' hN ⟨_, he'⟩ ⟨_, hd'⟩
    (fun j => by obtain ⟨c, _, hc'⟩ := hs j; exact ⟨_, hc'⟩) hD' hP'0
  have hfD : HasQ N A (conv a d) := by
    have := GlobalTheory.QFam.hasQ_mul_conv N f D a d hN ha hd
    have hAe : (fun τ => f τ * D τ) = A := funext hfA
    rwa [hAe] at this
  have he1 : e = conv a d := uc N A _ _ hN he hfD
  have hhD : HasQ N A' (conv b fun n => g (d n)) := by
    have := GlobalTheory.QFam.hasQ_mul_conv N h D' b _ hN hb hd'
    have hAe : (fun τ => h τ * D' τ) = A' := funext fun τ => (hAh τ).symm
    rwa [hAe] at this
  have he2 : (fun n => g (e n)) = conv b fun n => g (d n) := uc N A' _ _ hN he' hhD
  rw [he1, conjEx_conv_map] at he2
  have hba : b = fun n => g (a n) := (conjEx_conv_cancel _ _ _ hgd0 he2).symm
  refine ⟨h, ⟨a, ha, hba ▸ hb⟩, fun τ => (hAh τ).symm⟩

end GlobalTheory.FN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspExpansionDiscriminantIntegerLeadingOne
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNExpD

theorem hasQ_DD_int : HasQ 1 DD fun n => ((PowerSeries.coeff n ReciprocityTheory.ChartRestriction.L1.dZ : ℤ) : ℂ) := by
  rw [hasQ_iff]
  intro τ
  have := ReciprocityTheory.ChartRestriction.L1.isMF_DD.hasSum τ
  rw [← ReciprocityTheory.ChartRestriction.L1.dC_eq] at this
  simpa [ReciprocityTheory.ChartRestriction.L1.qm, ReciprocityTheory.ChartRestriction.L1.dC, PowerSeries.coeff_map] using this

theorem expD : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), ∃ h : HahnSeries ℚ Ω, IsExp ε DD h ∧ h ≠ 0 ∧
    h.leadingCoeff = 1 ∧ ∀ r : ℚ, ∃ n : ℤ, h.coeff r = n := by
  intro Ω _ ε
  have hD : HasQ 1 DD fun n => ε ((PowerSeries.coeff n ReciprocityTheory.ChartRestriction.L1.dZ : ℤ) : Ω) := by
    simpa only [map_intCast] using hasQ_DD_int
  obtain ⟨h, hexp, hk, hz⟩ := GlobalTheory.T.exists_hahnSeries_isExp_of_hasQ Ω ε 1 DD
    (fun n => ((PowerSeries.coeff n ReciprocityTheory.ChartRestriction.L1.dZ : ℤ) : Ω)) one_pos hD
  have h1 : h.coeff 1 = 1 := by
    have := hk 1
    simpa [ReciprocityTheory.ChartRestriction.L1.dZ_coeff_one] using this
  have hlow : ∀ r : ℚ, r < 1 → h.coeff r = 0 := by
    intro r hr
    by_cases hr' : ∃ k : ℕ, r = (k : ℚ) / ((1 : ℕ) : ℚ)
    · obtain ⟨k, rfl⟩ := hr'
      have hk1 : (k : ℚ) < 1 := by simpa using hr
      have hk0 : k = 0 := by
        have : k < 1 := by exact_mod_cast hk1
        omega
      subst hk0
      rw [hk 0]
      simp [ReciprocityTheory.ChartRestriction.L1.dZ_coeff_zero]
    · push_neg at hr'
      exact hz r hr'
  have hne : h ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero (h1 ▸ one_ne_zero)
  have hord : h.order = 1 := by
    refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero (h1 ▸ one_ne_zero)) ?_
    by_contra hlt
    push_neg at hlt
    exact (HahnSeries.coeff_order_eq_zero.not.mpr hne) (hlow _ hlt)
  refine ⟨h, hexp, hne, ?_, ?_⟩
  · rw [HahnSeries.leadingCoeff_eq, hord, h1]
  · intro r
    by_cases hr : ∃ k : ℕ, r = (k : ℚ) / ((1 : ℕ) : ℚ)
    · obtain ⟨k, rfl⟩ := hr
      exact ⟨_, hk k⟩
    · push_neg at hr
      exact ⟨0, by simpa using hz r hr⟩

end GlobalTheory.FNExpD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHomogeneousPolyCocycleEqOnCongruenceStatement
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homogeneousPolyCocycle_eqOn_congruence : ∀ (N l w : ℕ), 0 < N → l.Prime → l ≠ 2 → ¬ l ∣ N → Odd w → ∀ Φ, IsFam l w (Gam N l) Φ → ∀ n : ℕ, ∃ z : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)), IsCoc w (Gam N l) z ∧ Near z (Φ n) := by
  first | exact @GlobalTheory.KZ.H3.exists_coc_near | exact GlobalTheory.KZ.H3.exists_coc_near | (intros; apply GlobalTheory.KZ.H3.exists_coc_near <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsRootOfMemUnStatement
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isRoot_of_mem_Un_of_jHol : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) , JHol X → ∀ (m : ℕ), 0 < m → ∀ f ∈ X.Un m, ∃ a b : ℂ → ℂ, IsRoot X m f a b := by
  first | exact @GlobalTheory.KZ.H3.UnRoot.exists_isRoot_of_mem_Un | exact GlobalTheory.KZ.H3.UnRoot.exists_isRoot_of_mem_Un | (intros; apply GlobalTheory.KZ.H3.UnRoot.exists_isRoot_of_mem_Un <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKummerCharacterOfUpperHalfPlaneRootStatement
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kummerCharacter_of_upperHalfPlane_root : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ, ∀ (x : X.Khat l) (f : X.Kˣ) (a b : ℂ → ℂ), AdicCompletion.eval (idl l) (X.Kl l) n x = X.cls l n f → IsRoot X (l ^ n) f a b → ∃ χ : SL(2, ℤ) → ZMod (l ^ n), Kum X l n x χ := by
  first | exact @GlobalTheory.KZ.H3.kum_of_isRoot | exact GlobalTheory.KZ.H3.kum_of_isRoot | (intros; apply GlobalTheory.KZ.H3.kum_of_isRoot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeierstrassPFamilySeparatingGl2ZModStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weierstrassP_family_separating_gl2ZMod : ∀ (N : ℕ) [NeZero N], ∃ c₁ c₂ : ℕ, ∀ α β : GL (Fin 2) (ZMod N), (fun τ => wp N (vmul ![1, 0] α) τ + (c₁ : ℂ) * wp N (vmul ![0, 1] α) τ + (c₂ : ℂ) * wp N (vmul ![1, 1] α) τ) = (fun τ => wp N (vmul ![1, 0] β) τ + (c₁ : ℂ) * wp N (vmul ![0, 1] β) τ + (c₂ : ℂ) * wp N (vmul ![1, 1] β) τ) → α = β ∨ α = -β := by
  first | exact @GlobalTheory.FNSep.sep_family | exact GlobalTheory.FNSep.sep_family | (intros; apply GlobalTheory.FNSep.sep_family <;> assumption)
end

