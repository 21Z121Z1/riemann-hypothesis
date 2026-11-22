import Formalism.CyclotomicNorms.Bundle0001

-- bundled from Formalism.CyclotomicNorms.NonsquarefreeBounds.Newton
section
open Finset Polynomial

noncomputable section

namespace Formalism.CyclotomicNorms

namespace NewtonPolygonValuation

variable {L : Type} [Field L] (v : AddValuation L (WithTop ℝ))

lemma val_prod {ι : Type*} (s : Finset ι) (g : ι → L) :
    v (∏ i ∈ s, g i) = ∑ i ∈ s, v (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [prod_insert ha, sum_insert ha, AddValuation.map_mul, ih]

lemma val_root_eq_zero {z : L} {N : ℕ} (hN : 0 < N) (hz : z ^ N = 1) : v z = 0 := by
  have h := congrArg v hz
  rw [AddValuation.map_pow, AddValuation.map_one] at h
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hz
    exact zero_ne_one hz
  have hne : v z ≠ ⊤ := (AddValuation.ne_top_iff v).2 hz0
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hne
  rw [← hr] at h ⊢
  rw [← WithTop.coe_nsmul] at h
  have h1 : N • r = 0 := by exact_mod_cast h
  rw [nsmul_eq_mul] at h1
  have hr0 : r = 0 := by
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 (by exact_mod_cast hN.ne')
    · exact h2
  rw [hr0]
  rfl

lemma val_sub_one_le {ζ : L} {N : ℕ} (hN : 0 < N) (hζ : ζ ^ N = 1) (i : ℕ) :
    v (ζ - 1) ≤ v (ζ ^ i - 1) := by
  rw [← geom_sum_mul, AddValuation.map_mul]
  have h0 : (0 : WithTop ℝ) ≤ v (∑ k ∈ range i, ζ ^ k) := by
    apply AddValuation.map_le_sum
    intro k _
    rw [AddValuation.map_pow, val_root_eq_zero v hN hζ, smul_zero]
  calc v (ζ - 1) = 0 + v (ζ - 1) := (zero_add _).symm
    _ ≤ _ := add_le_add h0 le_rfl

lemma val_zeta_sub_one {ℓ j : ℕ} (hℓ : ℓ.Prime) (hj : 1 ≤ j) (hv : v (ℓ : L) = wt 1) {z : L}
    (hz : IsPrimitiveRoot z (ℓ ^ j)) :
    v (z - 1) = wt (1 / ((ℓ ^ j).totient : ℝ)) := by
  classical
  have := Fact.mk hℓ
  have hpos : 0 < ℓ ^ j := pow_pos hℓ.pos j
  have : NeZero (ℓ ^ j) := ⟨hpos.ne'⟩
  have heq : ∀ μ ∈ primitiveRoots (ℓ ^ j) L, v (1 - μ) = v (z - 1) := by
    intro μ hμ
    rw [mem_primitiveRoots hpos] at hμ
    rw [AddValuation.map_sub_swap]
    apply le_antisymm
    · obtain ⟨i, -, hi⟩ := hμ.eq_pow_of_pow_eq_one hz.pow_eq_one
      rw [← hi]
      exact val_sub_one_le v hpos hμ.pow_eq_one i
    · obtain ⟨i, -, hi⟩ := hz.eq_pow_of_pow_eq_one hμ.pow_eq_one
      rw [← hi]
      exact val_sub_one_le v hpos hz.pow_eq_one i
  have hcyc := congrArg (eval 1) (cyclotomic_eq_prod_X_sub_primitiveRoots hz)
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [eval_one_cyclotomic_prime_pow, eval_prod] at hcyc
  simp only [eval_sub, eval_X, eval_C] at hcyc
  have h2 := congrArg v hcyc
  rw [hv, val_prod, sum_congr rfl heq, sum_const, hz.card_primitiveRoots] at h2
  have hne1 : z ≠ 1 := hz.ne_one (Nat.one_lt_pow (by omega) hℓ.one_lt)
  have hne : v (z - 1) ≠ ⊤ := (AddValuation.ne_top_iff v).2 (sub_ne_zero.2 hne1)
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hne
  rw [← hr] at h2 ⊢
  rw [← WithTop.coe_nsmul] at h2
  have h3 : (1 : ℝ) = ((ℓ ^ (k + 1)).totient : ℝ) * r := by
    have := WithTop.coe_injective h2
    rw [nsmul_eq_mul] at this
    exact this
  have hφ : (0 : ℝ) < ((ℓ ^ (k + 1)).totient : ℝ) := by exact_mod_cast Nat.totient_pos.2 hpos
  congr 1
  field_simp
  linarith

lemma val_sum_eq_of_lt {ι : Type*} [DecidableEq ι] {s : Finset ι} {g : ι → L} {i₀ : ι}
    (hi : i₀ ∈ s) (h0 : v (g i₀) ≠ ⊤) (hlt : ∀ i ∈ s.erase i₀, v (g i₀) < v (g i)) :
    v (∑ i ∈ s, g i) = v (g i₀) := by
  rw [← add_sum_erase s g hi]
  exact AddValuation.map_add_eq_of_lt_left v (AddValuation.map_lt_sum v h0 hlt)

lemma wt_lt_add {a : WithTop ℝ} {x y : ℝ} (h : ∀ r : ℝ, a = r → x < r + y) :
    (x : WithTop ℝ) < a + y := by
  induction a using WithTop.recTopCoe with
  | top => simp
  | coe r =>
    rw [← WithTop.coe_add]
    exact WithTop.coe_lt_coe.2 (h r rfl)

lemma val_term {x : L} {s : ℝ} (hx : v x = wt s) (a : L) (i : ℕ) :
    v (a * x ^ i) = v a + wt (i * s) := by
  rw [AddValuation.map_mul, AddValuation.map_pow, hx, ← WithTop.coe_nsmul, nsmul_eq_mul]

end NewtonPolygonValuation

open NewtonPolygonValuation

theorem evaluation_bound : Evaluation := by
  intro L _ v ℓ e w j F z hℓ he hv hcoef hunit hz hφw
  classical
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [pow_zero, IsPrimitiveRoot.one_right_iff] at hz
    subst hz
    have hw : w = 0 := by
      rw [pow_zero, Nat.totient_one, Nat.cast_one] at hφw
      have : e * w < 1 := by exact_mod_cast hφw
      rcases Nat.eq_zero_or_pos w with h | h
      · exact h
      · exact absurd this (by have := Nat.mul_le_mul he h; omega)
    subst hw
    obtain ⟨i, hi, hvi⟩ := hunit
    obtain rfl : i = 0 := by omega
    rw [sub_self, ← coeff_zero_eq_eval_zero, hvi]
    simp
  · set φ : ℝ := ((ℓ ^ j).totient : ℝ) with hφdef
    have hφpos : (0 : ℝ) < φ := by
      rw [hφdef]; exact_mod_cast Nat.totient_pos.2 (pow_pos hℓ.pos j)
    have hepos : (0 : ℝ) < e := by exact_mod_cast he
    set t : ℝ := 1 / φ with htdef
    have htpos : 0 < t := by positivity
    have hx : v (z - 1) = wt t := val_zeta_sub_one v hℓ hj hv hz
    have hex : ∃ i, i ≤ w ∧ v (F.coeff i) = wt 0 := by
      obtain ⟨i, hi, h⟩ := hunit; exact ⟨i, hi, h⟩
    set i₀ := Nat.find hex with hi₀def
    have hi₀w : i₀ ≤ w := (Nat.find_spec hex).1
    have hi₀v : v (F.coeff i₀) = wt 0 := (Nat.find_spec hex).2
    have hlow : ∀ i < i₀, wt (1 / e) ≤ v (F.coeff i) := by
      intro i hi
      have hn := Nat.find_min hex hi
      rcases hcoef i with h | h
      · exact absurd ⟨by omega, h⟩ hn
      · exact h
    have hnn : ∀ i, (0 : WithTop ℝ) ≤ v (F.coeff i) := by
      intro i
      rcases hcoef i with h | h
      · rw [h]; rfl
      · refine le_trans ?_ h
        exact WithTop.coe_le_coe.2 (by positivity)
    have hwt : (w : ℝ) * t < 1 / e := by
      have h1 : ((e * w : ℕ) : ℝ) < φ := hφw
      push_cast at h1
      rw [htdef, lt_div_iff₀ hepos]
      rw [mul_one_div, div_mul_eq_mul_div, div_lt_one hφpos]
      linarith
    have hne0 : F.coeff i₀ ≠ 0 := by
      rw [← AddValuation.ne_top_iff v, hi₀v]; exact WithTop.coe_ne_top
    have hmem : i₀ ∈ range (F.natDegree + 1) :=
      mem_range.2 (Nat.lt_succ_of_le (le_natDegree_of_ne_zero hne0))
    rw [eval_eq_sum_range]
    rw [val_sum_eq_of_lt v hmem ?_ ?_]
    · rw [val_term v hx, hi₀v, ← WithTop.coe_add, zero_add]
      apply WithTop.coe_le_coe.2
      rw [htdef, mul_one_div]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hi₀w) hφpos.le
    · rw [val_term v hx, hi₀v, ← WithTop.coe_add]; exact WithTop.coe_ne_top
    · intro i hi
      have hii : i ≠ i₀ := (mem_erase.1 hi).1
      rw [val_term v hx, val_term v hx, hi₀v, ← WithTop.coe_add, zero_add]
      apply wt_lt_add
      intro r hr
      rcases lt_or_gt_of_ne hii with h | h
      · have h1 := hlow i h
        rw [hr] at h1
        have h1' : 1 / (e : ℝ) ≤ r := WithTop.coe_le_coe.1 h1
        have : (i₀ : ℝ) * t ≤ w * t :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hi₀w) htpos.le
        have : (0 : ℝ) ≤ i * t := by positivity
        linarith
      · have h1 := hnn i
        rw [hr] at h1
        have h1' : (0 : ℝ) ≤ r := WithTop.coe_le_coe.1 h1
        have : (i₀ : ℝ) * t < i * t :=
          mul_lt_mul_of_pos_right (by exact_mod_cast h) htpos
        linarith

end Formalism.CyclotomicNorms
end
end

-- bundled from Formalism.CyclotomicNorms.NonsquarefreeBounds.SpanQuadraticOfImage
section
noncomputable section

open Module

namespace Formalism.CyclotomicNorms

namespace PrismSpan

theorem sum_single {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type}
    [∀ i, AddCommMonoid (X i)] (v : ∀ i, X i) : ∑ i, Pi.single i (v i) = v := by
  ext; simp

variable {k G : Type} [Field k] [Group G] {a : ℕ} {W : Fin a → Type}
  [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)]

def diag (ρ : ∀ i, Representation k G (W i)) : G →* (∀ i, Module.End k (W i)) where
  toFun g i := ρ i g
  map_one' := by funext i; exact map_one (ρ i)
  map_mul' g h := by funext i; exact map_mul (ρ i) g h

abbrev alg (ρ : ∀ i, Representation k G (W i)) : Subalgebra k (∀ i, Module.End k (W i)) :=
  (MonoidAlgebra.lift k (∀ i, Module.End k (W i)) G (diag ρ)).range

variable (ρ : ∀ i, Representation k G (W i))

theorem diag_mem (g : G) : diag ρ g ∈ alg ρ :=
  ⟨MonoidAlgebra.single g 1, by simp⟩

theorem pi_smul_single (E : ∀ j, Module.End k (W j)) (i : Fin a) (w : W i) :
    E • (Pi.single i w : ∀ j, W j) = Pi.single i (E i w) := by
  funext j
  show E j (Pi.single i w j) = _
  by_cases hj : j = i
  · subst hj; simp
  · simp [Pi.single_eq_of_ne hj]

theorem alg_smul_eq (c : k) (m : ∀ i, W i) : (algebraMap k (alg ρ) c) • m = c • m := by
  funext i
  show ((algebraMap k (alg ρ) c : ∀ i, Module.End k (W i))) i (m i) = c • m i
  simp

variable {ρ}

theorem proj_surj (hspan : ∀ i, Submodule.span k (Set.range (ρ i)) = ⊤) (i : Fin a)
    (X : Module.End k (W i)) : ∃ r ∈ alg ρ, r i = X := by
  have hX : X ∈ Submodule.span k (Set.range (ρ i)) := by rw [hspan i]; trivial
  induction hX using Submodule.span_induction with
  | mem x hx => obtain ⟨g, rfl⟩ := hx; exact ⟨diag ρ g, diag_mem ρ g, rfl⟩
  | zero => exact ⟨0, Subalgebra.zero_mem _, rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨r, hr, rfl⟩ := hx
    obtain ⟨s, hs, rfl⟩ := hy
    exact ⟨r + s, add_mem hr hs, rfl⟩
  | smul c x _ hx =>
    obtain ⟨r, hr, rfl⟩ := hx
    exact ⟨c • r, Subalgebra.smul_mem _ hr c, rfl⟩

theorem exists_end {V : Type} [AddCommGroup V] [Module k V] {v : V} (hv : v ≠ 0) (w : V) :
    ∃ X : Module.End k V, X v = w := by
  obtain ⟨μ, hμ⟩ := Module.Projective.exists_dual_ne_zero k hv
  exact ⟨(μ v)⁻¹ • μ.smulRight w, by simp [smul_smul, inv_mul_cancel₀ hμ]⟩

variable (ρ) in

def coordSub (i : Fin a) : Submodule (alg ρ) (∀ j, W j) where
  carrier := {v | ∀ j, j ≠ i → v j = 0}
  add_mem' {u v} hu hv j hj := by
    show u j + v j = 0
    rw [hu j hj, hv j hj, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' r v hv j hj := by
    show (r : ∀ i, Module.End k (W i)) j (v j) = 0
    rw [hv j hj, map_zero]

theorem single_mem (i : Fin a) (w : W i) : (Pi.single i w : ∀ j, W j) ∈ coordSub ρ i :=
  fun _ hj => Pi.single_eq_of_ne hj w

theorem coord_simple (hnt : ∀ i, Nontrivial (W i))
    (hspan : ∀ i, Submodule.span k (Set.range (ρ i)) = ⊤) (i : Fin a) :
    IsSimpleModule (alg ρ) (coordSub ρ i) := by
  rw [isSimpleModule_iff_isAtom]
  refine ⟨?_, fun N hN => ?_⟩
  · obtain ⟨w, hw⟩ := exists_ne (0 : W i)
    intro h
    have h1 : (Pi.single i w : ∀ j, W j) ∈ (⊥ : Submodule (alg ρ) (∀ j, W j)) :=
      h ▸ single_mem i w
    rw [Submodule.mem_bot] at h1
    exact hw (by simpa using congrFun h1 i)
  · by_contra hN0
    obtain ⟨v, hvN, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN0
    have hvi : v i ≠ 0 := by
      intro h
      apply hv0
      funext j
      by_cases hj : j = i
      · subst hj; exact h
      · exact hN.le hvN j hj
    refine hN.ne (le_antisymm hN.le fun u hu => ?_)
    obtain ⟨X, hX⟩ := exists_end (k := k) hvi (u i)
    obtain ⟨r, hr, rfl⟩ := proj_surj hspan i X
    have h2 : (⟨r, hr⟩ : alg ρ) • v = u := by
      funext j
      show r j (v j) = u j
      by_cases hj : j = i
      · subst hj; exact hX
      · rw [hN.le hvN j hj, hu j hj, map_zero]
    exact h2 ▸ N.smul_mem _ hvN

theorem semisimple (hnt : ∀ i, Nontrivial (W i))
    (hspan : ∀ i, Submodule.span k (Set.range (ρ i)) = ⊤) :
    IsSemisimpleModule (alg ρ) (∀ j, W j) := by
  apply IsSemisimpleModule.of_sSup_simples_eq_top
  refine eq_top_iff.mpr fun v _ => ?_
  rw [← sum_single v]
  exact Submodule.sum_mem _ fun i _ =>
    (le_sSup (show coordSub ρ i ∈ {m : Submodule (alg ρ) (∀ j, W j) | IsSimpleModule _ m} from
      coord_simple hnt hspan i) : coordSub ρ i ≤ _) (single_mem i (v i))

theorem off_diag (hspan : ∀ i, Submodule.span k (Set.range (ρ i)) = ⊤)
    (hne : ∀ i j, i ≠ j → ¬ ∃ T : W i ≃ₗ[k] W j, ∀ g x, T (ρ i g x) = ρ j g (T x))
    (φ : (∀ j, W j) →ₗ[alg ρ] (∀ j, W j)) {i j : Fin a} (hij : i ≠ j) (w : W i) :
    φ (Pi.single i w) j = 0 := by
  let ψ : W i →ₗ[k] W j :=
    { toFun := fun w => φ (Pi.single i w) j
      map_add' := fun x y => by
        show φ (Pi.single i (x + y)) j = φ (Pi.single i x) j + φ (Pi.single i y) j
        rw [Pi.single_add, map_add]; rfl
      map_smul' := fun c x => by
        show φ (Pi.single i (c • x)) j = c • φ (Pi.single i x) j
        rw [Pi.single_smul, ← alg_smul_eq ρ c, φ.map_smul, alg_smul_eq]; rfl }
  have hint : ∀ r ∈ alg ρ, ∀ x, ψ (r i x) = r j (ψ x) := by
    intro r hr x
    show φ (Pi.single i (r i x)) j = r j (φ (Pi.single i x) j)
    rw [← pi_smul_single r i x]
    exact congrFun (φ.map_smul ⟨r, hr⟩ (Pi.single i x)) j
  by_contra hw
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro u hu
    by_contra hu0
    obtain ⟨X, hX⟩ := exists_end (k := k) hu0 w
    obtain ⟨r, hr, rfl⟩ := proj_surj hspan i X
    apply hw
    show ψ w = 0
    rw [← hX, hint r hr, LinearMap.mem_ker.mp hu, map_zero]
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨Y, hY⟩ := exists_end (k := k) (show ψ w ≠ 0 from hw) y
    obtain ⟨r, hr, rfl⟩ := proj_surj hspan j Y
    exact ⟨r i w, by rw [hint r hr, hY]⟩
  exact hne i j hij ⟨LinearEquiv.ofBijective ψ ⟨hinj, hsurj⟩,
    fun g x => hint _ (diag_mem ρ g) x⟩

theorem on_diag (hspan : ∀ i, Submodule.span k (Set.range (ρ i)) = ⊤)
    (φ : (∀ j, W j) →ₗ[alg ρ] (∀ j, W j)) (i : Fin a) (X : Module.End k (W i)) (w : W i) :
    φ (Pi.single i (X w)) i = X (φ (Pi.single i w) i) := by
  obtain ⟨r, hr, rfl⟩ := proj_surj hspan i X
  rw [← pi_smul_single r i w]
  exact congrFun (φ.map_smul ⟨r, hr⟩ (Pi.single i w)) i

theorem comm (hspan : ∀ i, Submodule.span k (Set.range (ρ i)) = ⊤)
    (hne : ∀ i j, i ≠ j → ¬ ∃ T : W i ≃ₗ[k] W j, ∀ g x, T (ρ i g x) = ρ j g (T x))
    (φ : (∀ j, W j) →ₗ[alg ρ] (∀ j, W j)) (E : ∀ j, Module.End k (W j)) (m : ∀ j, W j) :
    φ (E • m) = E • φ m := by
  have key : ∀ i (w : W i), φ (Pi.single i (E i w)) = E • φ (Pi.single i w) := by
    intro i w
    funext j
    show _ = E j (φ (Pi.single i w) j)
    by_cases hij : i = j
    · subst hij; exact on_diag hspan φ i (E i) w
    · rw [off_diag hspan hne φ hij, off_diag hspan hne φ hij, map_zero]
  conv_lhs => rw [← sum_single m]
  conv_rhs => rw [← sum_single m]
  simp only [Finset.smul_sum, map_sum, pi_smul_single, key]

end PrismSpan

namespace PrismSpan

variable {k G : Type} [Field k] [Group G] {a : ℕ} {W : Fin a → Type}
  [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)]
  {La : Fin a → Type} [∀ i, AddCommGroup (La i)] [∀ i, Module k (La i)]

def post (x : ∀ i, La i →ₗ[k] W i) :
    (∀ i, Module.End k (W i)) →ₗ[k] (∀ i, La i →ₗ[k] W i) where
  toFun E i := E i ∘ₗ x i
  map_add' E F := by funext i; exact LinearMap.add_comp _ _ _
  map_smul' c E := by funext i; exact LinearMap.smul_comp _ _ _

def sr (i : Fin a) (w : W i) : Module.Dual k (La i) →ₗ[k] (∀ j, La j →ₗ[k] W j) where
  toFun ψ := Pi.single i (ψ.smulRight w)
  map_add' ψ ψ' := by
    rw [← Pi.single_add]; congr 1; ext; simp [add_smul]
  map_smul' c ψ := by
    rw [RingHom.id_apply, ← Pi.single_smul]; congr 1; ext; simp [smul_smul]

end PrismSpan

end Formalism.CyclotomicNorms
end
end

-- bundled from Formalism.CyclotomicNorms.NonsquarefreeBounds.SubstitutionBound
section
open Finset

noncomputable section

namespace Formalism.CyclotomicNorms

namespace SubstitutionExponents

variable {r : ℕ}

def weight (n : Fin r → ℕ) (d : Fin r →₀ ℕ) : ℕ := ∑ i, d i * n i

theorem prod_X_pow {k : Type*} [CommRing k] (n : Fin r → ℕ) (d : Fin r →₀ ℕ) :
    (d.prod fun s e => ((PowerSeries.X : PowerSeries k) ^ n s) ^ e) =
      PowerSeries.X ^ weight n d := by
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp_rw [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  simp only [weight, mul_comm]

theorem hasSubst_X_pow {k : Type*} [CommRing k] (n : Fin r → ℕ) (hn : ∀ j, n j ≠ 0) :
    MvPowerSeries.HasSubst (fun j => (PowerSeries.X : PowerSeries k) ^ n j) := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero (fun j => ?_)
  rw [map_pow]
  have : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries k) = 0 :=
    MvPowerSeries.constantCoeff_X _
  rw [this, zero_pow (hn j)]

theorem coeff_subst_weight {k : Type*} [CommRing k] (n : Fin r → ℕ) (hn : ∀ j, n j ≠ 0)
    (F : MvPowerSeries (Fin r) k) (m : ℕ) :
    PowerSeries.coeff m
        (MvPowerSeries.subst (fun j => (PowerSeries.X : PowerSeries k) ^ n j) F : PowerSeries k) =
      finsum (fun d => if weight n d = m then MvPowerSeries.coeff d F else 0) := by
  change MvPowerSeries.coeff (Finsupp.single () m) _ = _
  rw [MvPowerSeries.coeff_subst (hasSubst_X_pow n hn)]
  congr 1
  ext d
  rw [prod_X_pow, PowerSeries.coeff_coeToMvPowerSeries, PowerSeries.coeff_X_pow, smul_eq_mul]
  by_cases h : weight n d = m
  · simp [h]
  · rw [if_neg (Ne.symm h), if_neg h, mul_zero]

def revLex : (Fin r →₀ ℕ) → (Fin r →₀ ℕ) → Prop :=
  Finsupp.Lex (· > ·) (· < ·)

theorem revLex_wf : WellFounded (revLex (r := r)) :=
  Finsupp.Lex.wellFounded_of_finite _ wellFounded_lt

theorem sum_split (g : Fin r → ℕ) (j : Fin r) :
    ∑ i, g i = ∑ i ∈ univ.filter (· < j), g i + g j + ∑ i ∈ univ.filter (j < ·), g i := by
  rw [← Finset.sum_filter_add_sum_filter_not univ (· < j)]
  have h : univ.filter (fun i => ¬ i < j) = insert j (univ.filter (j < ·)) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_insert, not_lt]
    exact le_iff_eq_or_lt.trans (or_congr eq_comm Iff.rfl)
  rw [h, Finset.sum_insert (by simp), add_assoc]

theorem unique_of_min (n : Fin r → ℕ) (a : Fin r →₀ ℕ)
    (hn : ∀ j, ∑ i ∈ univ.filter (· < j), a i * n i < n j)
    (d : Fin r →₀ ℕ) (hmin : ¬ revLex d a) (hw : weight n d = weight n a) : d = a := by
  classical
  by_contra hne
  have hS : (univ.filter fun i => d i ≠ a i).Nonempty := by
    by_contra h
    apply hne
    ext i
    by_contra hi
    exact h ⟨i, by simp [hi]⟩
  set j := (univ.filter fun i => d i ≠ a i).max' hS with hj
  have hdj : d j ≠ a j := by
    have := Finset.max'_mem _ hS
    rw [← hj] at this
    simpa using this
  have habove : ∀ i, j < i → d i = a i := by
    intro i hi
    by_contra h
    have : i ≤ j := Finset.le_max' _ i (by simp [h])
    exact absurd hi (not_lt.2 this)
  have hlt : a j < d j := by
    rcases lt_or_gt_of_ne hdj with h | h
    · exact absurd ⟨j, fun i hi => habove i hi, h⟩ hmin
    · exact h
  have e1 := sum_split (fun i => d i * n i) j
  have e2 := sum_split (fun i => a i * n i) j
  have e3 : ∑ i ∈ univ.filter (j < ·), d i * n i = ∑ i ∈ univ.filter (j < ·), a i * n i :=
    Finset.sum_congr rfl (fun i hi => by rw [habove i (by simpa using hi)])
  have h4 := hn j
  have h5 : (a j + 1) * n j ≤ d j * n j := Nat.mul_le_mul_right _ hlt
  rw [add_mul, one_mul] at h5
  unfold weight at hw
  rw [e1, e2, e3] at hw
  omega

end SubstitutionExponents

end Formalism.CyclotomicNorms
end
end

