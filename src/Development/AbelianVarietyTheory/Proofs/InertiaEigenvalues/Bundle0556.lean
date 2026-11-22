import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0315
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0543
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0257
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0535
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0541
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0436
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0526
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0456
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0531
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0513
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0530
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReciprocityAuxiliaryPlacesSecondHalf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerFinrankEqDual
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0542
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicTraceGeWhittakerDimensionGLn
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.MirabolicComparison

theorem tr_add {G : Type} [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) (f h : G → ℂ) :
    tr a (fun x => f x + h x) = tr a f + tr a h := by
  simp [tr, mul_add, Finset.sum_add_distrib]

theorem tr_mul_const {G : Type} [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) (f : G → ℂ) (c : ℂ) :
    tr a (fun x => f x * c) = tr a f * c := by
  simp only [tr, Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem tr_tr_list_nat {G H : Type} [Group G] [Fintype G] [Group H] [Fintype H]
    (a : MonoidAlgebra ℂ G) (b : MonoidAlgebra ℂ H) (ha : a * a = a) (hb : b * b = b) :
    ∀ L : List ((G → ℂ) × (H → ℂ)), (∀ p ∈ L, IsChar p.1 ∧ IsChar p.2) →
      ∃ n : ℕ, tr a (fun x => tr b (fun y => (L.map fun p => p.1 x * p.2 y).sum)) = n := by
  intro L
  induction L with
  | nil =>
    intro _
    exact ⟨0, by simp [tr]⟩
  | cons p L ih =>
    intro hL
    obtain ⟨m, hm⟩ := ih (fun q hq => hL q (List.mem_cons_of_mem _ hq))
    obtain ⟨n₁, hn₁⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree G a p.1).1 ha (hL p (List.mem_cons_self ..)).1
    obtain ⟨n₂, hn₂⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree H b p.2).1 hb (hL p (List.mem_cons_self ..)).2
    refine ⟨n₁ * n₂ + m, ?_⟩
    simp only [List.map_cons, List.sum_cons]
    rw [show (fun x => tr b (fun y => p.1 x * p.2 y + (L.map fun p => p.1 x * p.2 y).sum)) =
        (fun x => p.1 x * tr b p.2 + tr b (fun y => (L.map fun p => p.1 x * p.2 y).sum)) from by
      funext x
      rw [tr_add]
      congr 1
      simp only [tr, Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring]
    rw [tr_add, tr_mul_const, hm, hn₁, hn₂]
    push_cast
    ring

end GlobalTheory.GLq.MirabolicComparison

namespace GlobalTheory.GLq.MirabolicComparison

theorem isClass_of_isChar {G : Type} [Group G] {χ : G → ℂ} (h : IsChar χ) : IsClass χ := by
  obtain ⟨V, hV⟩ := h
  intro x y
  rw [← hV, ← hV]
  exact FDRep.char_conj V x y

theorem isChar_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsChar χ := by
  obtain ⟨V, _, hV⟩ := h
  exact ⟨V, hV⟩

theorem wh_der_nat (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (N i : ℕ) (hi : i ≤ N)
    (χ : Gn g N → ℂ) (hχ : IsChar χ) : ∃ n : ℕ, wh ψ (der ψ i χ) = n := by
  obtain ⟨L, hL, hLeq⟩ := (GlobalTheory.T.harishChandra_induction_character_restriction_decomp g i (N - i) N (by omega)).2 χ hχ
  have hres : (fun h : Gn g i => wh ψ (res i (N - i) χ h)) =
      fun h => tr (eU g (N - i) ψ) (fun y => (L.map fun p => p.1 h * p.2 y).sum) := by
    funext h
    simp only [wh]
    congr 1
    funext y
    exact hLeq h y
  show ∃ n : ℕ, tr (eU g i ψ) (fun h => wh ψ (res i (N - i) χ h)) = n
  rw [hres]
  exact tr_tr_list_nat _ _ (GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g i 0 0 ψ).1 (GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g (N - i) 0 0 ψ).1 L
    (fun p hp => ⟨isChar_of_isIrr (hL p hp).1, isChar_of_isIrr (hL p hp).2⟩)

theorem wh_der_zero (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (N : ℕ) (χ : Gn g N → ℂ) :
    wh ψ (der ψ 0 χ) = wh ψ χ := by
  haveI : Subsingleton (Gn g 0) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
  have h1 : (eU g 0 ψ).coeff 1 = 1 := by
    rw [(GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g 0 0 0 ψ).2.1]; simp
  have hres : res 0 (N - 0) χ 1 = χ := by
    funext y
    change Gn g N at y
    simp only [res, Nat.zero_mul, pow_zero, inv_one, one_mul]
    rw [Finset.sum_eq_single y]
    · have : InPar 0 ((y : Gn g N) : Mt g N) ∧ tl 0 ((y : Gn g N) : Mt g N) = ((1 : Gn g 0) : Mt g 0) ∧
          br 0 (N - 0) ((y : Gn g N) : Mt g N) = ((y : Gn g (N - 0)) : Mt g (N - 0)) := by
        refine ⟨fun i j hj _ => absurd hj (Nat.not_lt_zero _), Subsingleton.elim _ _, ?_⟩
        funext i j
        simp [br, entN]
      rw [if_pos this]
    · intro x _ hx
      rw [if_neg]
      rintro ⟨_, _, hb⟩
      apply hx
      apply Units.ext
      rw [← hb]
      funext i j
      simp [br, entN]
    · intro h; exact absurd (Finset.mem_univ _) h
  show tr (eU g 0 ψ) (fun h => wh ψ (res 0 (N - 0) χ h)) = wh ψ χ
  simp only [tr]
  rw [Fintype.sum_subsingleton _ 1, h1, one_mul, hres]

end GlobalTheory.GLq.MirabolicComparison

namespace GlobalTheory.GLq.MirabolicComparison

theorem mirabolic_comparison : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (N k s : ℕ),
    N = k + 2 * s + 1 → 1 ≤ k → ∀ χ : Gn g N → ℂ, IsChar χ →
      ((g : ℝ) ^ k - (g : ℝ) ^ (k - 1)) * (wh ψ χ).re ≤ (tr (eJ g N k s ψ) χ).re := by
  intro g _ ψ hψ N k s hN hk χ hχ
  have hcl := isClass_of_isChar hχ
  rw [GlobalTheory.T.groupAlgebraTrace_patternIdempotent_exchange g ψ hψ N k s hN χ hcl, GlobalTheory.T.trace_unitriangularColumnVanishingIdempotent_eq_sum_derivatives g ψ hψ N k hk (by omega) χ hcl]
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast (Fact.out : g.Prime).one_lt.le
  have hterm : ∀ i a b, (wh ψ (der ψ i χ) * ((g : ℂ) ^ a - (g : ℂ) ^ b)).re =
      (wh ψ (der ψ i χ)).re * ((g : ℝ) ^ a - (g : ℝ) ^ b) := by
    intro i a b
    rw [show ((g : ℂ) ^ a - (g : ℂ) ^ b) = (((g : ℝ) ^ a - (g : ℝ) ^ b : ℝ) : ℂ) by push_cast; ring]
    exact Complex.re_mul_ofReal _ _
  have hnn : ∀ i, i ≤ N → 0 ≤ (wh ψ (der ψ i χ)).re := by
    intro i hi
    obtain ⟨n, hn⟩ := wh_der_nat g ψ N i hi χ hχ
    rw [hn]
    simp
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Finset.sum_range_succ', Complex.add_re, Complex.add_re, Complex.re_sum, hterm 0, wh_der_zero]
  have hrest : 0 ≤ ∑ i ∈ Finset.range k', (wh ψ (der ψ (i + 1) χ) *
      ((g : ℂ) ^ (k' + 1 - (i + 1)) - (g : ℂ) ^ (k' + 1 - (i + 1) - 1))).re := by
    apply Finset.sum_nonneg
    intro i hi
    rw [Finset.mem_range] at hi
    rw [hterm]
    apply mul_nonneg (hnn _ (by omega))
    rw [sub_nonneg]
    exact pow_le_pow_right₀ hg1 (by omega)
  have hlast := hnn (k' + 1) (by omega)
  have h0 : (wh ψ χ).re * ((g : ℝ) ^ (k' + 1 - 0) - (g : ℝ) ^ (k' + 1 - 0 - 1)) =
      ((g : ℝ) ^ (k' + 1) - (g : ℝ) ^ (k' + 1 - 1)) * (wh ψ χ).re := by
    simp only [Nat.sub_zero]
    ring
  linarith

end GlobalTheory.GLq.MirabolicComparison
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MkSumProdHsymmMulProdOneSub
section
noncomputable section

open Finset PowerSeries

namespace GlobalTheory.JSW

theorem sum_finsuppAntidiag_univ_fin {M : Type*} [AddCommMonoid M] {m : ℕ} (d : ℕ)
    (F : (Fin m → ℕ) → M) :
    ∑ l ∈ finsuppAntidiag (univ : Finset (Fin m)) d, F l =
      ∑ k ∈ Finset.Nat.antidiagonalTuple m d, F k := by
  refine Finset.sum_equiv Finsupp.equivFunOnFinite ?_ ?_
  · intro l
    simp [mem_finsuppAntidiag, Finset.Nat.mem_antidiagonalTuple]
  · intro l _
    rfl

theorem coeff_prod_mk_fin {m : ℕ} (f : Fin m → ℕ → ℂ) (d : ℕ) :
    coeff d (∏ j, PowerSeries.mk (f j)) =
      ∑ k ∈ Finset.Nat.antidiagonalTuple m d, ∏ j, f j (k j) := by
  rw [coeff_prod, sum_finsuppAntidiag_univ_fin d (fun k => ∏ j, coeff (k j) (PowerSeries.mk (f j)))]
  simp only [coeff_mk]

theorem prod_map_X_eq_monomial_toFinsupp {n : ℕ} (s : Multiset (Fin n)) :
    (s.map (MvPolynomial.X : Fin n → MvPolynomial (Fin n) ℤ)).prod =
      MvPolynomial.monomial (Multiset.toFinsupp s) 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih, ← Multiset.singleton_add, map_add,
      Multiset.toFinsupp_singleton, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]

theorem sum_toFinsupp_fin {n : ℕ} (s : Multiset (Fin n)) :
    ∑ i, Multiset.toFinsupp s i = Multiset.card s := by
  simp [Multiset.toFinsupp_apply, Multiset.sum_count_eq_card]

theorem hsymm_fin_eq_sum_monomial {n : ℕ} (k : ℕ) :
    MvPolynomial.hsymm (Fin n) ℤ k =
      ∑ l ∈ finsuppAntidiag (univ : Finset (Fin n)) k, MvPolynomial.monomial l 1 := by
  rw [MvPolynomial.hsymm]
  refine Finset.sum_bij (fun s _ => Multiset.toFinsupp s.1) ?_ ?_ ?_ ?_
  · intro s _
    rw [mem_finsuppAntidiag]
    refine ⟨?_, subset_univ _⟩
    rw [sum_toFinsupp_fin, s.2]
  · intro a _ b _ h
    exact Sym.coe_injective (Multiset.toFinsupp.injective h)
  · intro l hl
    rw [mem_finsuppAntidiag] at hl
    refine ⟨⟨Finsupp.toMultiset l, ?_⟩, mem_univ _, ?_⟩
    · rw [Finsupp.card_toMultiset, Finsupp.sum_fintype _ _ (fun _ => rfl)]
      exact hl.1
    · simp
  · intro s _
    exact prod_map_X_eq_monomial_toFinsupp s.1

theorem eval₂_hsymm_fin {n : ℕ} (α : Fin n → ℂ) (k : ℕ) :
    MvPolynomial.eval₂ (Int.castRingHom ℂ) α (MvPolynomial.hsymm (Fin n) ℤ k) =
      ∑ l ∈ Finset.Nat.antidiagonalTuple n k, ∏ i, α i ^ l i := by
  rw [hsymm_fin_eq_sum_monomial, MvPolynomial.eval₂_sum,
    ← sum_finsuppAntidiag_univ_fin k (fun l => ∏ i, α i ^ l i)]
  refine sum_congr rfl fun l _ => ?_
  rw [MvPolynomial.eval₂_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]

theorem one_sub_C_mul_X_mul_mk_pow (a : ℂ) :
    (1 - PowerSeries.C a * PowerSeries.X) * PowerSeries.mk (fun k => a ^ k) = 1 := by
  ext k
  rw [sub_mul, one_mul, map_sub, mul_assoc, coeff_C_mul]
  cases k with
  | zero => simp
  | succ k => simp [pow_succ, mul_comm]

theorem mk_hsymm_mul_prod_one_sub {n : ℕ} (α : Fin n → ℂ) (u : ℂ) :
    PowerSeries.mk (fun k => MvPolynomial.eval₂ (Int.castRingHom ℂ) α
        (MvPolynomial.hsymm (Fin n) ℤ k) * u ^ k) *
      ∏ i, (1 - PowerSeries.C (α i * u) * PowerSeries.X) = 1 := by
  have h : PowerSeries.mk (fun k => MvPolynomial.eval₂ (Int.castRingHom ℂ) α
        (MvPolynomial.hsymm (Fin n) ℤ k) * u ^ k) =
      ∏ i, PowerSeries.mk (fun k => (α i * u) ^ k) := by
    ext k
    rw [coeff_prod_mk_fin, coeff_mk, eval₂_hsymm_fin, sum_mul]
    refine sum_congr rfl fun l hl => ?_
    rw [Finset.Nat.mem_antidiagonalTuple] at hl
    simp_rw [mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum, hl]
  rw [h, ← prod_mul_distrib]
  exact prod_eq_one fun i _ => by rw [mul_comm]; exact one_sub_C_mul_X_mul_mk_pow _

theorem mk_sum_prod_hsymm_mul_prod_one_sub : ∀ {m n : ℕ} (α : Fin n → ℂ) (β : Fin m → ℂ) (T : ℂ),
    PowerSeries.mk (fun d => T ^ d * ∑ k ∈ Finset.Nat.antidiagonalTuple m d,
        ∏ j, MvPolynomial.eval₂ (Int.castRingHom ℂ) α (MvPolynomial.hsymm (Fin n) ℤ (k j)) * β j ^ (k j)) *
      ∏ p : Fin n × Fin m, (1 - PowerSeries.C (α p.1 * β p.2 * T) * PowerSeries.X) = 1 := by
  intro m n α β T
  have h1 : PowerSeries.mk (fun d => T ^ d * ∑ k ∈ Finset.Nat.antidiagonalTuple m d,
        ∏ j, MvPolynomial.eval₂ (Int.castRingHom ℂ) α (MvPolynomial.hsymm (Fin n) ℤ (k j)) * β j ^ (k j)) =
      ∏ j, PowerSeries.mk (fun k => MvPolynomial.eval₂ (Int.castRingHom ℂ) α
        (MvPolynomial.hsymm (Fin n) ℤ k) * (β j * T) ^ k) := by
    ext d
    rw [coeff_mk, coeff_prod_mk_fin, mul_sum]
    refine sum_congr rfl fun k hk => ?_
    rw [Finset.Nat.mem_antidiagonalTuple] at hk
    simp_rw [mul_pow, ← mul_assoc, prod_mul_distrib, prod_pow_eq_pow_sum, hk]
    ring
  have h2 : ∏ p : Fin n × Fin m, (1 - PowerSeries.C (α p.1 * β p.2 * T) * PowerSeries.X) =
      ∏ j, ∏ i, (1 - PowerSeries.C (α i * (β j * T)) * PowerSeries.X) := by
    rw [Fintype.prod_prod_type, Finset.prod_comm]
    simp_rw [mul_assoc]
  rw [h1, h2, ← prod_mul_distrib]
  exact prod_eq_one fun j _ => mk_hsymm_mul_prod_one_sub α (β j * T)

end GlobalTheory.JSW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NegCycPowerBlockCrysDeRhamJumps
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory

noncomputable def negPowBlock {G LL : Type} [Group G] [Field LL] (χ : G →* LLˣ) (t : ℕ) :
    Representation LL G (Fin t → LL) where
  toFun g := LinearMap.pi fun c : Fin t =>
    (((χ g)⁻¹ ^ (c : ℕ) : LLˣ) : LL) • LinearMap.proj c
  map_one' := by ext; simp
  map_mul' g h := by
    refine LinearMap.ext fun v => funext fun c => ?_
    simp only [map_mul, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply,
      Module.End.mul_apply, smul_eq_mul, mul_inv, mul_pow, Units.val_mul]
    ring

noncomputable def snocSplit (LL : Type) [Field LL] (t : ℕ) :
    (Fin (t + 1) → LL) ≃ₗ[LL] ((Fin t → LL) × LL) where
  toFun v := (fun c => v c.castSucc, v (Fin.last t))
  invFun p := Fin.snoc (α := fun _ => LL) p.1 p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv v := Fin.snoc_init_self v
  right_inv p := by
    ext <;> simp

theorem negCycBlock_jumps : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (t : ℕ) (ρ : Representation ↥LL.1 ↥(GK K) (Fin t → ↥LL.1)), (∀ g v (c : Fin t), ρ g v c = (((cycLL (P.PD K) ↥LL.1 g)⁻¹ ^ (c : ℕ) : (↥LL.1)ˣ) : ↥LL.1) * v c) → IsCrys (P.PD K) ρ ∧ IsDR (P.PD K) ρ ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), multV (P.PD K) ρ τ a = if 0 ≤ a ∧ a < (t : ℤ) then 1 else 0 := by
  intro l _ P AI hT K LL t
  induction t with
  | zero =>
    intro ρ _
    refine ⟨?_, ?_, fun τ a => ?_⟩
    · unfold IsCrys
      rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton (M := Fin 0 → ↥LL.1), mul_zero]
    · unfold IsDR
      rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton (M := Fin 0 → ↥LL.1), mul_zero]
    · unfold multV
      rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton, if_neg (by omega)]
      simp
  | succ t ih =>
    intro ρ hρ
    obtain ⟨c1, d1, m1⟩ := ih (negPowBlock (cycLL (P.PD K) ↥LL.1) t) (fun _ _ _ => rfl)
    obtain ⟨c2, d2, m2⟩ := GlobalTheory.T.cyc_zpow_crys_dR_jump_alt l P AI hT K LL (-(t : ℤ))
    obtain ⟨hd, hc, hm⟩ := GlobalTheory.T.directSum_deRham_crystalline_jumps_add l P AI hT K LL _ ρ _
      (negPowBlock (cycLL (P.PD K) ↥LL.1) t) _ (charRep (cycLL (P.PD K) ↥LL.1 ^ (-(t : ℤ))))
      (snocSplit ↥LL.1 t) (by
        intro g v
        refine Prod.ext (funext fun c => ?_) ?_
        · exact hρ g v c.castSucc
        · refine (hρ g v (Fin.last t)).trans ?_
          change _ = (((cycLL (P.PD K) ↥LL.1 ^ (-(t : ℤ))) g : (↥LL.1)ˣ) : ↥LL.1) * v (Fin.last t)
          rw [MonoidHom.zpow_apply, Fin.val_last, zpow_neg, zpow_natCast, inv_pow])
    refine ⟨hc.2 ⟨c1, c2⟩, hd.2 ⟨d1, d2⟩, fun τ a => ?_⟩
    rw [hm, m1, m2]
    push_cast
    split_ifs <;> omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneMemOfFrobeniusLinkedBoundedSeriesIdeals
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.BK.GcdCore

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem powerSeries_coeff_norm_le_one_mul {f g : K⟦X⟧} (hf : ∀ n, ‖coeff n f‖ ≤ 1) (hg : ∀ n, ‖coeff n g‖ ≤ 1) (n : ℕ) :
    ‖coeff n (f * g)‖ ≤ 1 := by
  simpa using norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp)
    zero_le_one zero_le_one (f := f) (g := g) (by simpa using hf) (by simpa using hg) n

theorem powerSeries_coeff_norm_le_one_add {f g : K⟦X⟧} (hf : ∀ n, ‖coeff n f‖ ≤ 1) (hg : ∀ n, ‖coeff n g‖ ≤ 1) (n : ℕ) :
    ‖coeff n (f + g)‖ ≤ 1 := by
  rw [map_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf n) (hg n))

theorem powerSeries_coeff_norm_le_one_pow {f : K⟦X⟧} (hf : ∀ n, ‖coeff n f‖ ≤ 1) (m : ℕ) : ∀ n, ‖coeff n (f ^ m)‖ ≤ 1 := by
  induction m with
  | zero => intro n; rw [pow_zero, coeff_one]; split_ifs <;> simp
  | succ m ih => intro n; rw [pow_succ]; exact powerSeries_coeff_norm_le_one_mul ih hf n

theorem powerSeries_coeff_norm_le_one_X_pow (i : ℕ) : ∀ n, ‖coeff n ((X : K⟦X⟧) ^ i)‖ ≤ 1 := by
  intro n; rw [coeff_X_pow]; split_ifs <;> simp

theorem powerSeries_coeff_norm_le_one_frobeniusExpand (l : ℕ) [Fact l.Prime] {f : K⟦X⟧} (hf : ∀ n, ‖coeff n f‖ ≤ 1) :
    ∀ n, ‖coeff n (frob K l f)‖ ≤ 1 := by
  intro n; rw [coeff_frob]; split_ifs
  · exact hf _
  · simp

theorem coeff_norm_le_one_eisensteinPolynomialPowPlusPrime (l e : ℕ) (hl : ‖(l : K)‖ < 1) : ∀ n, ‖coeff n (E K l e)‖ ≤ 1 := by
  intro n
  rw [E, ← map_natCast (C : K →+* K⟦X⟧)]
  refine powerSeries_coeff_norm_le_one_add (powerSeries_coeff_norm_le_one_X_pow e) (fun m => ?_) n
  rw [coeff_C]; split_ifs
  · exact hl.le
  · simp

theorem powerSeries_coeff_norm_le_one_finset_sum {ι : Type} (s : Finset ι) (f : ι → K⟦X⟧) (hf : ∀ i ∈ s, ∀ n, ‖coeff n (f i)‖ ≤ 1) :
    ∀ n, ‖coeff n (∑ i ∈ s, f i)‖ ≤ 1 :=
  Finset.sum_induction f (fun g => ∀ n, ‖coeff n g‖ ≤ 1) (fun _ _ ha hb => powerSeries_coeff_norm_le_one_add ha hb)
    (fun n => by simp) hf

theorem sum_X_pow_mul_frob_frobSlice (l : ℕ) [Fact l.Prime] (z : K⟦X⟧) :
    z = ∑ i ∈ Finset.range l, (X : K⟦X⟧) ^ i * frob K l (frobSlice l i z) := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  ext n
  rw [map_sum]
  simp_rw [coeff_X_pow_mul', coeff_frob, coeff_frobSlice]
  rw [Finset.sum_eq_single (n % l)]
  · have h1 : n % l ≤ n := Nat.mod_le n l
    have h2 : l ∣ n - n % l := Nat.dvd_sub_mod n
    rw [if_pos h1, if_pos h2, Nat.mul_div_cancel' h2, Nat.sub_add_cancel h1]
  · intro i hi hne
    split_ifs with h1 h2
    · exfalso
      obtain ⟨c, hc⟩ := h2
      have hn : n = i + l * c := by omega
      apply hne
      rw [hn, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Finset.mem_range.1 hi)]
    · rfl
    · rfl
  · intro h; exact absurd (Finset.mem_range.2 (Nat.mod_lt n hl)) h

theorem one_mem_of_frobenius_stable_ideals_boundedPowerSeries (GEN : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (J : Set K⟦X⟧), (∀ x ∈ J, ∀ y ∈ J, x + y ∈ J) → (∀ x ∈ J, ∀ b : K⟦X⟧, (∃ c : ℝ, ∀ n, ‖coeff n b‖ ≤ c) → b * x ∈ J) → (∃ g ∈ J, (∀ n, ‖coeff n g‖ ≤ 1) ∧ ∃ n, ‖coeff n g‖ = 1) → ∃ Δ ∈ J, (∀ n, ‖coeff n Δ‖ ≤ 1) ∧ (∃ n, ‖coeff n Δ‖ = 1) ∧ ∀ h ∈ J, (∀ n, ‖coeff n h‖ ≤ 1) → ∃ q : K⟦X⟧, (∀ n, ‖coeff n q‖ ≤ 1) ∧ h = Δ * q)
  (CYCLE : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (l e a M N : ℕ) [Fact l.Prime] [NeZero a], 0 < e → (l : K) ≠ 0 → ‖(l : K)‖ < 1 → ∀ (Δ k k' : ZMod a → K⟦X⟧), (∀ τ n, ‖coeff n (Δ τ)‖ ≤ 1) → (∀ τ, ∃ n, ‖coeff n (Δ τ)‖ = 1) → (∀ τ n, ‖coeff n (k τ)‖ ≤ 1) → (∀ τ n, ‖coeff n (k' τ)‖ ≤ 1) → (∀ τ, k τ * k' τ = E K l e ^ N) → (∀ τ, Δ τ * k τ = E K l e ^ M * frob K l (Δ (τ - 1))) → ∀ τ, ‖constantCoeff (Δ τ)‖ = 1)
  (UNITA : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (f : K⟦X⟧), (∀ n, ‖coeff n f‖ ≤ 1) → ‖constantCoeff f‖ = 1 → ∃ g : K⟦X⟧, (∀ n, ‖coeff n g‖ ≤ 1) ∧ f * g = 1) :
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (l e a M₁ M₂ : ℕ) [Fact l.Prime] [NeZero a], 0 < e → (l : K) ≠ 0 → ‖(l : K)‖ < 1 → ∀ (J : ZMod a → Set K⟦X⟧), (∀ τ, ∀ x ∈ J τ, ∀ y ∈ J τ, x + y ∈ J τ) → (∀ τ, ∀ x ∈ J τ, ∀ b : K⟦X⟧, (∃ c : ℝ, ∀ n, ‖coeff n b‖ ≤ c) → b * x ∈ J τ) → (∀ τ, ∀ x ∈ J τ, ∃ c : ℝ, ∀ n, ‖coeff n x‖ ≤ c) → (∀ τ, ∃ g ∈ J τ, (∀ n, ‖coeff n g‖ ≤ 1) ∧ ∃ n, ‖coeff n g‖ = 1) → (∀ τ, ∀ h ∈ J (τ - 1), E K l e ^ M₁ * frob K l h ∈ J τ) → (∀ τ, ∀ h ∈ J τ, ∀ i < l, frobSlice l i (E K l e ^ M₂ * h) ∈ J (τ - 1)) → ∀ τ, (1 : K⟦X⟧) ∈ J τ := by
  intro K _ _ _ l e a M₁ M₂ _ _ he hl0 hl1 J hadd hmul _ hprim hphi hsl
  choose Δ hΔJ hΔ1 hΔp hΔdiv using fun τ => GEN K (J τ) (hadd τ) (hmul τ) (hprim τ)
  have hE := coeff_norm_le_one_eisensteinPolynomialPowPlusPrime (K := K) l e hl1

  have hk : ∀ τ, ∃ k : K⟦X⟧, (∀ n, ‖coeff n k‖ ≤ 1) ∧
      Δ τ * k = E K l e ^ M₁ * frob K l (Δ (τ - 1)) := by
    intro τ
    obtain ⟨q, hq1, hq⟩ := hΔdiv τ _ (hphi τ _ (hΔJ (τ - 1)))
      (powerSeries_coeff_norm_le_one_mul (powerSeries_coeff_norm_le_one_pow hE M₁) (powerSeries_coeff_norm_le_one_frobeniusExpand l (hΔ1 (τ - 1))))
    exact ⟨q, hq1, hq.symm⟩
  choose k hk1 hk using hk

  have hm : ∀ τ i, ∃ m : K⟦X⟧, i < l → (∀ n, ‖coeff n m‖ ≤ 1) ∧
      frobSlice l i (E K l e ^ M₂ * Δ τ) = Δ (τ - 1) * m := by
    intro τ i
    by_cases hi : i < l
    · have hs1 : ∀ n, ‖coeff n (frobSlice l i (E K l e ^ M₂ * Δ τ))‖ ≤ 1 := fun n => by
        rw [coeff_frobSlice]; exact powerSeries_coeff_norm_le_one_mul (powerSeries_coeff_norm_le_one_pow hE M₂) (hΔ1 τ) _
      obtain ⟨q, hq1, hq⟩ := hΔdiv (τ - 1) _ (hsl τ _ (hΔJ τ) i hi) hs1
      exact ⟨q, fun _ => ⟨hq1, hq⟩⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose m hm using hm
  set k' : ZMod a → K⟦X⟧ := fun τ => ∑ i ∈ Finset.range l, (X : K⟦X⟧) ^ i * frob K l (m τ i) with hk'def
  have hk'1 : ∀ τ n, ‖coeff n (k' τ)‖ ≤ 1 := fun τ =>
    powerSeries_coeff_norm_le_one_finset_sum _ _ fun i hi => powerSeries_coeff_norm_le_one_mul (powerSeries_coeff_norm_le_one_X_pow i) (powerSeries_coeff_norm_le_one_frobeniusExpand l (hm τ i (Finset.mem_range.1 hi)).1)
  have hk' : ∀ τ, E K l e ^ M₂ * Δ τ = frob K l (Δ (τ - 1)) * k' τ := by
    intro τ
    rw [sum_X_pow_mul_frob_frobSlice (K := K) l (E K l e ^ M₂ * Δ τ), hk'def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(hm τ i (Finset.mem_range.1 hi)).2, map_mul]
    ring
  have hne : ∀ τ, Δ τ ≠ 0 := fun τ h => by
    obtain ⟨n, hn⟩ := hΔp τ
    rw [h, map_zero, norm_zero] at hn
    exact zero_ne_one hn
  have hkk : ∀ τ, k τ * k' τ = E K l e ^ (M₁ + M₂) := by
    intro τ
    apply mul_left_cancel₀ (hne τ)
    calc Δ τ * (k τ * k' τ) = E K l e ^ M₁ * (frob K l (Δ (τ - 1)) * k' τ) := by
          rw [← mul_assoc, hk τ, mul_assoc]
      _ = Δ τ * E K l e ^ (M₁ + M₂) := by rw [← hk' τ, pow_add]; ring
  have hc := CYCLE K l e a M₁ (M₁ + M₂) he hl0 hl1 Δ k k' hΔ1 hΔp hk1 hk'1 hkk hk
  intro τ
  obtain ⟨g, hg1, hg⟩ := UNITA K (Δ τ) (hΔ1 τ) (hc τ)
  have := hmul τ _ (hΔJ τ) g ⟨1, hg1⟩
  rwa [mul_comm, hg] at this

theorem one_mem : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (l e a M₁ M₂ : ℕ) [Fact l.Prime] [NeZero a], 0 < e → (l : K) ≠ 0 → ‖(l : K)‖ < 1 → ∀ (J : ZMod a → Set K⟦X⟧), (∀ τ, ∀ x ∈ J τ, ∀ y ∈ J τ, x + y ∈ J τ) → (∀ τ, ∀ x ∈ J τ, ∀ b : K⟦X⟧, (∃ c : ℝ, ∀ n, ‖coeff n b‖ ≤ c) → b * x ∈ J τ) → (∀ τ, ∀ x ∈ J τ, ∃ c : ℝ, ∀ n, ‖coeff n x‖ ≤ c) → (∀ τ, ∃ g ∈ J τ, (∀ n, ‖coeff n g‖ ≤ 1) ∧ ∃ n, ‖coeff n g‖ = 1) → (∀ τ, ∀ h ∈ J (τ - 1), E K l e ^ M₁ * frob K l h ∈ J τ) → (∀ τ, ∀ h ∈ J τ, ∀ i < l, frobSlice l i (E K l e ^ M₂ * h) ∈ J (τ - 1)) → ∀ τ, (1 : K⟦X⟧) ∈ J τ :=
  one_mem_of_frobenius_stable_ideals_boundedPowerSeries GlobalTheory.T.exists_primitive_generator_boundedMultiple_set GlobalTheory.T.norm_constantCoeff_eq_one_of_eisenstein_frobenius_cycle GlobalTheory.T.exists_integral_inverse_powerSeries_of_unit_constantCoeff

end GlobalTheory.BK.GcdCore
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowSmulMemLatticeOfAcrisBoundStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_smul_mem_lattice_of_acris_bound : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (T : LocLat (Gl l) ℚ_[l] K O), l ≠ 2 → ∀ ε : OCb l, IsEps ε → ∀ (j n c : ℕ), 2 * j < l - 1 → ∀ (u : TW (OB l O) T) (x : ↥T.L.T) (w : TW (OCr l O) T), (l : O) ^ n • u = (1 : OB l O) ⊗ₜ[O] x → toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ j) • ((l : O) ^ c • u) = TWincl (toOB l O) T w → ∃ x' : ↥T.L.T, (l : O) ^ c • u = (1 : OB l O) ⊗ₜ[O] x' := by
  first | exact @GlobalTheory.BKGal.Count.count | exact GlobalTheory.BKGal.Count.count | (intros; apply GlobalTheory.BKGal.Count.count <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReciprocityAuxiliaryPlacesSecondHalfStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reciprocity_auxiliaryPlaces_secondHalf : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → Gen.ArchimedeanSignatureMatching → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → FirstHalf i s → Recip bkP i s := by
  first | exact @GlobalTheory.ResRecip.reciprocity | exact GlobalTheory.ResRecip.reciprocity | (intros; apply GlobalTheory.ResRecip.reciprocity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerFinrankEqDualStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residual_selmer_finrank_eq_dual : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → Gen.ArchimedeanSignatureMatching → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → EqDim bkP i s := by
  first | exact @GlobalTheory.ResDual.eqDim | exact GlobalTheory.ResDual.eqDim | (intros; apply GlobalTheory.ResDual.eqDim <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RootCancelPowEqSelfAcrisGaussNormStatement
section
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootCancel_pow_eq_self_acris_gaussNorm : ∀ (l : ℕ) [Fact l.Prime] (h s : ℕ), s < h → ∀ (w w' : Formalism.Per.Acris l) (ζ : Formalism.Per.Fl l) (o : ℕ) (ρ₀ : ℝ), (φc l)^[h] w' = (l : Formalism.Per.Acris l) ^ s * w' → w' ≠ 0 → φc l w * w' = w * φc l w' → (∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ w = gC l ρ w') → 0 < o → ζ ^ (l ^ o) = ζ → ζ ≠ 0 → (l : ℝ)⁻¹ ≤ ρ₀ → ρ₀ < 1 → gC l ρ₀ (w - tc l ζ * w') < gC l ρ₀ w' → ζ ^ l = ζ := by
  first | exact @GlobalTheory.PMon.Gauss.root_cancel_pow_eq_self | exact GlobalTheory.PMon.Gauss.root_cancel_pow_eq_self | (intros; apply GlobalTheory.PMon.Gauss.root_cancel_pow_eq_self <;> assumption)
end

