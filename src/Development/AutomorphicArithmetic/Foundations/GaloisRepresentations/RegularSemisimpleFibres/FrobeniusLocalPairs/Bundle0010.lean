import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0354
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle0004
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle0008
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle0005
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.Bundle0001

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.LiftVal
section
open ValuativeRel Matrix Polynomial GlobalTheory.DZA GlobalTheory.LBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

private theorem pow_finrank_aut {k K : Type} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K]
    (s : K ≃ₐ[k] K) : s ^ Module.finrank k K = 1 := by
  classical
  have h1 : Nat.card (⊤ : Subgroup (K ≃ₐ[k] K)) ∣ Module.finrank k K := by
    rw [← IntermediateField.finrank_fixedField_eq_card,
      ← Module.finrank_mul_finrank k (IntermediateField.fixedField (⊤ : Subgroup (K ≃ₐ[k] K))) K]
    exact dvd_mul_left _ _
  rw [Subgroup.card_top] at h1
  exact orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_natCard s).trans h1)

private theorem partial_twConj {k K : Type} [Field k] [Field K] [Algebra k K] (s : K ≃ₐ[k] K) (n : ℕ)
    (δ g : GL (Fin n) K) (m : ℕ) :
    (List.ofFn fun j : Fin m => GlobalTheory.LBC.galAct (s ^ (j : ℕ)) n (g⁻¹ * δ * GlobalTheory.LBC.galAct s n g)).prod =
      g⁻¹ * (List.ofFn fun j : Fin m => GlobalTheory.LBC.galAct (s ^ (j : ℕ)) n δ).prod * GlobalTheory.LBC.galAct (s ^ m) n g := by
  induction m with
  | zero => simp [GlobalTheory.LBC.galAct_one]
  | succ m ih =>
    rw [List.ofFn_succ', List.ofFn_succ', List.prod_concat, List.prod_concat]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih]
    have e : GlobalTheory.LBC.galAct (s ^ m) n (GlobalTheory.LBC.galAct s n g) = GlobalTheory.LBC.galAct (s ^ (m + 1)) n g := by
      rw [pow_succ, GlobalTheory.LBC.galAct_mul, MonoidHom.comp_apply]
    rw [map_mul, map_mul, map_inv, e]
    group

private theorem norm_tw {k K : Type} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] (s : K ≃ₐ[k] K)
    (n : ℕ) (δ g : GL (Fin n) K) :
    GlobalTheory.LBC.norm k s (g⁻¹ * δ * GlobalTheory.LBC.galAct s n g) = g⁻¹ * GlobalTheory.LBC.norm k s δ * g := by
  unfold GlobalTheory.LBC.norm
  rw [partial_twConj, pow_finrank_aut, GlobalTheory.LBC.galAct_one, MonoidHom.id_apply]

private theorem fb_eq_of_isFinNorm {F₀ F₁ : Type} [Field F₀] [Field F₁] [Algebra F₀ F₁] [Finite F₁]
    (sb : F₁ ≃ₐ[F₀] F₁) {n : ℕ} (fb : GL (Fin n) F₀ → ℂ) (hfb : ∀ a b, fb (b⁻¹ * a * b) = fb a)
    {δ : GL (Fin n) F₁} {γ γ' : GL (Fin n) F₀} (h : IsFinNorm sb δ γ) (h' : IsFinNorm sb δ γ') :
    fb γ' = fb γ := by
  have hc : IsConj γ' γ := GlobalTheory.Shin.isConj_of_isConj_incl F₀ F₁ n γ' γ (h'.trans h.symm)
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  have := hfb γ' c⁻¹
  rw [inv_inv] at this
  rw [← this, hc]

end UpperTheory.Gal.InertialTypesAlt.L

theorem UpperTheory.Gal.InertialTypesAlt.L.liftVal :
    UpperTheory.Gal.InertialTypesAlt.L.LiftVal := by
  intro F₀ F₁ _ _ _ _ _ sb _ n fb hfb
  haveI : FiniteDimensional F₀ F₁ := Module.Finite.of_finite
  refine ⟨fun δ γ h => ?_, fun δ x => ?_⟩
  · have hex : ∃ γ, GlobalTheory.DZA.IsFinNorm sb δ γ := ⟨γ, h⟩
    rw [GlobalTheory.DZA.normLift, dif_pos hex]
    exact UpperTheory.Gal.InertialTypesAlt.L.fb_eq_of_isFinNorm sb fb hfb h hex.choose_spec
  · have hiff : ∀ γ, GlobalTheory.DZA.IsFinNorm sb (x⁻¹ * δ * GlobalTheory.LBC.galAct sb n x) γ ↔ GlobalTheory.DZA.IsFinNorm sb δ γ := by
      intro γ
      have hc : IsConj (GlobalTheory.LBC.norm F₀ sb δ) (GlobalTheory.LBC.norm F₀ sb (x⁻¹ * δ * GlobalTheory.LBC.galAct sb n x)) := by
        rw [UpperTheory.Gal.InertialTypesAlt.L.norm_tw]
        refine isConj_iff.mpr ⟨x⁻¹, ?_⟩
        simp
      exact ⟨fun h => IsConj.trans h hc.symm, fun h => IsConj.trans h hc⟩
    have hfun : (fun γ => GlobalTheory.DZA.IsFinNorm sb (x⁻¹ * δ * GlobalTheory.LBC.galAct sb n x) γ) =
        fun γ => GlobalTheory.DZA.IsFinNorm sb δ γ := funext fun γ => propext (hiff γ)
    by_cases hex : ∃ γ, GlobalTheory.DZA.IsFinNorm sb δ γ
    · obtain ⟨γ, hγ⟩ := hex
      have h1 : ∃ γ, GlobalTheory.DZA.IsFinNorm sb δ γ := ⟨γ, hγ⟩
      have h2 : ∃ γ, GlobalTheory.DZA.IsFinNorm sb (x⁻¹ * δ * GlobalTheory.LBC.galAct sb n x) γ := ⟨γ, (hiff γ).2 hγ⟩
      rw [GlobalTheory.DZA.normLift, GlobalTheory.DZA.normLift, dif_pos h1, dif_pos h2]
      exact (UpperTheory.Gal.InertialTypesAlt.L.fb_eq_of_isFinNorm sb fb hfb ((hiff _).1 h2.choose_spec) h1.choose_spec).symm
    · have h2 : ¬ ∃ γ, GlobalTheory.DZA.IsFinNorm sb (x⁻¹ * δ * GlobalTheory.LBC.galAct sb n x) γ :=
        fun ⟨γ, hγ⟩ => hex ⟨γ, (hiff γ).1 hγ⟩
      rw [GlobalTheory.DZA.normLift, GlobalTheory.DZA.normLift, dif_neg hex, dif_neg h2]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.NormAdic
section
namespace UpperTheory.Gal.InertialTypesAlt.L

private theorem unit_of_sub_mem {A : Type} [CommRing A] (I : Ideal A) [IsAdicComplete I A]
    {x z : A} (hx : IsUnit x) (h : z - x ∈ I) : IsUnit z := by
  have hj := (Ideal.mem_jacobson_bot.mp (IsAdicComplete.le_jacobson_bot I h)) (↑hx.unit⁻¹ : A)
  have e : z = x * ((z - x) * ↑hx.unit⁻¹ + 1) := by
    linear_combination (-(z - x)) * hx.mul_val_inv
  rw [e]
  exact hx.mul hj

private theorem prod_one_add {A : Type} [CommRing A] (b : ℕ → A) (r : A) (d : ℕ) :
    ∃ c, ∏ i ∈ Finset.range d, (1 + b i * r) =
      1 + (∑ i ∈ Finset.range d, b i) * r + r ^ 2 * c := by
  induction d with
  | zero => exact ⟨0, by simp⟩
  | succ d ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c + (∑ i ∈ Finset.range d, b i) * b d + r * c * b d, ?_⟩
    rw [Finset.prod_range_succ, Finset.sum_range_succ, hc]
    ring

private theorem itN_mul {A : Type} [CommRing A] (τ : A ≃+* A) (d : ℕ) (y w : A) :
    itN τ d (y * w) = itN τ d y * itN τ d w := by
  have key : ∀ i, (⇑τ)^[i] (y * w) = (⇑τ)^[i] y * (⇑τ)^[i] w := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul]
  simp only [itN, key, Finset.prod_mul_distrib]

private theorem itN_fixed {A : Type} [CommRing A] (τ : A ≃+* A) (d : ℕ)
    (hd : ∀ x, τ^[d] x = x) (y : A) : τ (itN τ d y) = itN τ d y := by
  unfold itN
  rw [map_prod]
  simp only [← Function.iterate_succ_apply' (⇑τ)]
  cases d with
  | zero => simp
  | succ m =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ' (fun i => (⇑τ)^[i] y), hd y]
    rfl

private theorem step {A : Type} [CommRing A] (I : Ideal A) (τ : A ≃+* A) (d : ℕ)
    (hd : ∀ x, τ^[d] x = x) (a : A) (ha : ∑ i ∈ Finset.range d, τ^[i] a = 1)
    (x : A) (hτx : τ x = x) (n : ℕ) (hn : n ≠ 0) (y : A) (hu : IsUnit (itN τ d y))
    (h : itN τ d y - x ∈ I ^ n) :
    ∃ y', y' - y ∈ I ^ n ∧ itN τ d y' - x ∈ I ^ (n + 1) := by
  set N := itN τ d y with hN
  set v : A := ↑hu.unit⁻¹ with hv
  have hNv : N * v = 1 := hu.mul_val_inv
  have hNfix : τ N = N := itN_fixed τ d hd y
  have hvfix : τ v = v := by
    have h1 : τ N * τ v = 1 := by rw [← map_mul, hNv, map_one]
    rw [hNfix] at h1
    calc τ v = (N * v) * τ v := by rw [hNv, one_mul]
      _ = v * (N * τ v) := by ring
      _ = v := by rw [h1, mul_one]
  have hwfix : τ ((x - N) * v) = (x - N) * v := by rw [map_mul, map_sub, hτx, hNfix, hvfix]
  have hit : ∀ i (z : A), (⇑τ)^[i] z = ((τ : A →+* A) ^ i) z := by
    intro i z
    rw [RingHom.coe_pow]
    rfl
  have hwit : ∀ i, (⇑τ)^[i] ((x - N) * v) = (x - N) * v := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [Function.iterate_succ_apply', ih, hwfix]
  have hwI : (x - N) * v ∈ I ^ n := by
    apply Ideal.mul_mem_right
    rw [← neg_sub]
    exact neg_mem h
  obtain ⟨c, hc⟩ := prod_one_add (fun i => (⇑τ)^[i] a) ((x - N) * v) d
  beta_reduce at hc
  refine ⟨y * (1 + a * ((x - N) * v)), ?_, ?_⟩
  · have e : y * (1 + a * ((x - N) * v)) - y = (y * a) * ((x - N) * v) := by ring
    rw [e]
    exact Ideal.mul_mem_left _ _ hwI
  · have e1 : itN τ d (1 + a * ((x - N) * v)) = ∏ i ∈ Finset.range d, (1 + (⇑τ)^[i] a * ((x - N) * v)) := by
      unfold itN
      apply Finset.prod_congr rfl
      intro i _
      rw [hit, map_add, map_one, map_mul, ← hit, ← hit, hwit]
    rw [itN_mul, ← hN, e1, hc, ha]
    have e2 : N * (1 + 1 * ((x - N) * v) + ((x - N) * v) ^ 2 * c) - x = N * c * ((x - N) * v) ^ 2 := by
      linear_combination (x - N) * hNv
    rw [e2]
    apply Ideal.mul_mem_left
    have h2 : ((x - N) * v) ^ 2 ∈ I ^ (n * 2) := by
      rw [pow_mul]
      exact Ideal.pow_mem_pow hwI 2
    exact Ideal.pow_le_pow_right (by omega) h2

private theorem tau_pow_mem {A : Type} [CommRing A] (I : Ideal A) (τ : A ≃+* A)
    (hI : ∀ x ∈ I, τ x ∈ I) (n : ℕ) {z : A} (h : z ∈ I ^ n) : τ z ∈ I ^ n := by
  have h1 : Ideal.map τ I ≤ I := Ideal.map_le_iff_le_comap.mpr (fun x hx => hI x hx)
  have h2 : τ z ∈ Ideal.map τ (I ^ n) := Ideal.mem_map_of_mem τ h
  rw [Ideal.map_pow] at h2
  exact Ideal.pow_right_mono h1 n h2

private theorem iter_pow_mem {A : Type} [CommRing A] (I : Ideal A) (τ : A ≃+* A)
    (hI : ∀ x ∈ I, τ x ∈ I) (n i : ℕ) {z : A} (h : z ∈ I ^ n) : τ^[i] z ∈ I ^ n := by
  induction i with
  | zero => exact h
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact tau_pow_mem I τ hI n ih

private theorem itN_sub_mem {A : Type} [CommRing A] (I : Ideal A) (τ : A ≃+* A)
    (hI : ∀ x ∈ I, τ x ∈ I) (d n : ℕ) {u v : A} (h : u - v ∈ I ^ n) :
    itN τ d u - itN τ d v ∈ I ^ n := by
  have hs : ∀ i, (⇑τ)^[i] u - (⇑τ)^[i] v ∈ I ^ n := by
    intro i
    have e : ∀ j, (⇑τ)^[j] u - (⇑τ)^[j] v = (⇑τ)^[j] (u - v) := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ← map_sub, ih]
    rw [e]
    exact iter_pow_mem I τ hI n i h
  unfold itN
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    have e2 : (∏ i ∈ Finset.range d, (⇑τ)^[i] u) * (⇑τ)^[d] u - (∏ i ∈ Finset.range d, (⇑τ)^[i] v) * (⇑τ)^[d] v
        = (∏ i ∈ Finset.range d, (⇑τ)^[i] u - ∏ i ∈ Finset.range d, (⇑τ)^[i] v) * (⇑τ)^[d] u
          + (∏ i ∈ Finset.range d, (⇑τ)^[i] v) * ((⇑τ)^[d] u - (⇑τ)^[d] v) := by
      ring
    rw [e2]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ih) (Ideal.mul_mem_left _ _ (hs d))

private theorem mem_smul_top {A : Type} [CommRing A] (I : Ideal A) (n : ℕ) (z : A) :
    z ∈ (I ^ n • ⊤ : Submodule A A) ↔ z ∈ I ^ n := by
  simp

theorem normAdic : NormAdic := by
  intro A _ I _ τ d hd hI a ha x y hx hτx hy
  have hunit : ∀ n : ℕ, ∀ z : A, itN τ d z - x ∈ I ^ (n + 1) → IsUnit (itN τ d z) := by
    intro n z hz
    exact unit_of_sub_mem I hx (Ideal.pow_le_self (Nat.succ_ne_zero n) hz)
  have hstep : ∀ n : ℕ, ∀ z : A, itN τ d z - x ∈ I ^ (n + 1) →
      ∃ z', z' - z ∈ I ^ (n + 1) ∧ itN τ d z' - x ∈ I ^ (n + 1 + 1) := by
    intro n z hz
    exact step I τ d hd a ha x hτx (n + 1) (Nat.succ_ne_zero n) z (hunit n z hz) hz
  choose! g hg1 hg2 using hstep
  let f : ℕ → A := fun k => Nat.rec (motive := fun _ => A) y (fun k z => g k z) k
  have hf0 : f 0 = y := rfl
  have hfs : ∀ k, f (k + 1) = g k (f k) := fun k => rfl
  have hfN : ∀ k, itN τ d (f k) - x ∈ I ^ (k + 1) := by
    intro k
    induction k with
    | zero => simpa [hf0] using hy
    | succ k ih =>
      rw [hfs]
      exact hg2 k (f k) ih
  have hfd : ∀ k, f (k + 1) - f k ∈ I ^ (k + 1) := by
    intro k
    rw [hfs]
    exact hg1 k (f k) (hfN k)
  have hcauchy : ∀ m k, f m - f (m + k) ∈ I ^ m := by
    intro m k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : f m - f (m + (k + 1)) = (f m - f (m + k)) - (f (m + k + 1) - f (m + k)) := by
        rw [← add_assoc]
        ring
      rw [e]
      refine Ideal.sub_mem _ ih ?_
      exact Ideal.pow_le_pow_right (by omega) (hfd (m + k))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) (M := A) inferInstance (f := f) (by
    intro m n hmn
    rw [SModEq.sub_mem, mem_smul_top]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    exact hcauchy m k)
  refine ⟨L, ?_⟩
  have hzero := IsHausdorff.haus (I := I) (M := A) inferInstance (itN τ d L - x) (by
    intro n
    rw [SModEq.sub_mem, sub_zero, mem_smul_top]
    have h1 : itN τ d L - itN τ d (f n) ∈ I ^ n := by
      apply itN_sub_mem I τ hI d n
      have h0 := SModEq.sub_mem.mp (hL n)
      rw [mem_smul_top] at h0
      rw [← neg_sub]
      exact neg_mem h0
    have h2 : itN τ d (f n) - x ∈ I ^ n := Ideal.pow_le_pow_right (by omega) (hfN n)
    have e : itN τ d L - x = (itN τ d L - itN τ d (f n)) + (itN τ d (f n) - x) := by ring
    rw [e]
    exact Ideal.add_mem _ h1 h2)
  exact sub_eq_zero.mp hzero

end UpperTheory.Gal.InertialTypesAlt.L
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.OneField
section
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc
open GlobalTheory.SmGL hiding iwahori
open UpperTheory.Gal.InertialTypesAlt.L

section

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

private theorem sg_cont {σ : E ≃+* E} (hσ : Isom σ) : Continuous (sg σ : GL (Fin n) E → GL (Fin n) E) := by
  have hc : Continuous (σ : E → E) := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt, (IsValuativeTopology.hasBasis_nhds x).tendsto_iff
      (IsValuativeTopology.hasBasis_nhds (σ x))]
    intro γ _
    refine ⟨γ, trivial, fun z hz => ?_⟩
    simp only [Set.mem_setOf_eq] at hz ⊢
    rw [← map_sub, hσ]
    exact hz
  exact Continuous.units_map _ (continuous_id.matrix_map hc)

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem map_diag {F : Type} [Field F] (f : E →+* F) (u : Fin n → Eˣ) :
    Matrix.GeneralLinearGroup.map f (diagT E (Fin n) u) = diagT F (Fin n) fun i => Units.map (f : E →* F) (u i) := by
  ext i j
  simp only [Matrix.GeneralLinearGroup.map_apply, val_diagT, RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.diagonal_apply]
  split_ifs <;> simp

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem diag_comm (u v : Fin n → Eˣ) :
    diagT E (Fin n) u * diagT E (Fin n) v = diagT E (Fin n) v * diagT E (Fin n) u := by
  rw [← map_mul, ← map_mul, mul_comm]

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem diag_inj {u v : Fin n → Eˣ} (h : diagT E (Fin n) u = diagT E (Fin n) v) : u = v := by
  funext i
  have h1 := congrArg (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E) i i) h
  simp only [val_diagT, Matrix.diagonal_apply_eq] at h1
  exact Units.ext h1

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem sg_diag (σ : E ≃+* E) (p : Fin n → Eˣ) :
    sg σ (diagT E (Fin n) p) = diagT E (Fin n) (sgT σ p) := by
  exact map_diag (σ : E →+* E) p

private theorem cent_diag {σ : E ≃+* E} {q : ℕ} (hσ : Cyc σ q) {d : Fin n → Eˣ} (hd : Strict d) {δ y c : GL (Fin n) E}
    (hy : y⁻¹ * δ * sg σ y = diagT E (Fin n) d) (hc : c⁻¹ * δ * sg σ c = δ) : ∃ u, y⁻¹ * c * y = diagT E (Fin n) u := by
  have hc2 : δ * sg σ c = c * δ := by
    calc δ * sg σ c = c * (c⁻¹ * δ * sg σ c) := by group
      _ = c * δ := by rw [hc]
  have key : (y⁻¹ * c * y)⁻¹ * diagT E (Fin n) d * sg σ (y⁻¹ * c * y) = diagT E (Fin n) d := by
    rw [← hy]
    simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left]
    rw [← mul_assoc δ, hc2]
    simp only [mul_assoc, inv_mul_cancel_left]
  exact strictNormal E n σ q hσ d d hd hd _ key

private theorem diag_ball {r : ValueGroupWithZero E} {s : Fin n → Eˣ} (h : Near r s) : diagT E (Fin n) s ∈ ball n r := by
  intro i j
  rw [val_diagT]
  by_cases hij : i = j
  · subst hij
    simpa using h i
  · simp [Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij]

private theorem near_of_ball {r : ValueGroupWithZero E} {s : Fin n → Eˣ} (h : diagT E (Fin n) s ∈ ball n r) : Near r s := by
  intro i
  have h1 := h i i
  simpa [val_diagT, Matrix.diagonal_apply_eq] using h1

end

theorem UpperTheory.Gal.InertialTypesAlt.L.oneField :
    UpperTheory.Gal.InertialTypesAlt.L.OneField := by
  intro E _ _ _ _ n σ q hσ r hr0 hr1 _ _ μ hμ A hA δ y d hd hy H hH ν hν R hR hRd
  obtain ⟨K, hK, hKo, hKc⟩ := ballSub E n r hr0 hr1
  have hsupp := (suppE E n σ q hσ r hr0 hr1 A hA).2 δ y d hd hy
  have hδ : δ = y * diagT E (Fin n) d * (sg σ y)⁻¹ := by
    rw [← hy]
    group
  have hfix : ∀ w, (y * diagT E (Fin n) w * y⁻¹)⁻¹ * δ * sg σ (y * diagT E (Fin n) w * y⁻¹) = δ ↔
      sgT σ w = w := by
    intro w
    have e : (y * diagT E (Fin n) w * y⁻¹)⁻¹ * δ * sg σ (y * diagT E (Fin n) w * y⁻¹) =
        y * ((diagT E (Fin n) w)⁻¹ * diagT E (Fin n) d * diagT E (Fin n) (sgT σ w)) * (sg σ y)⁻¹ := by
      rw [hδ, map_mul, map_mul, map_inv, sg_diag]
      group
    rw [e]
    constructor
    · intro h
      conv_rhs at h => rw [hδ]
      have h2 : (diagT E (Fin n) w)⁻¹ * diagT E (Fin n) d * diagT E (Fin n) (sgT σ w) = diagT E (Fin n) d :=
        mul_left_cancel (mul_right_cancel h)
      have h3 : diagT E (Fin n) d * diagT E (Fin n) (sgT σ w) = diagT E (Fin n) d * diagT E (Fin n) w := by
        calc diagT E (Fin n) d * diagT E (Fin n) (sgT σ w)
            = diagT E (Fin n) w * ((diagT E (Fin n) w)⁻¹ * diagT E (Fin n) d * diagT E (Fin n) (sgT σ w)) := by
              group
          _ = diagT E (Fin n) w * diagT E (Fin n) d := by rw [h2]
          _ = diagT E (Fin n) d * diagT E (Fin n) w := diag_comm w d
      exact diag_inj (mul_left_cancel h3)
    · intro h
      rw [h, hδ, mul_assoc (diagT E (Fin n) w)⁻¹, diag_comm d w]
      group
  have hcen : ∀ c ∈ H, ∃ u, y⁻¹ * c * y = diagT E (Fin n) u :=
    fun c hc => cent_diag hσ hd hy ((hH c).1 hc)
  have hback : ∀ c u, y⁻¹ * c * y = diagT E (Fin n) u → c = y * diagT E (Fin n) u * y⁻¹ := by
    intro c u hu
    rw [← hu]
    group
  have hfixH : ∀ c ∈ H, ∀ u, y⁻¹ * c * y = diagT E (Fin n) u → sgT σ u = u := by
    intro c hc u hu
    apply (hfix u).1
    rw [← hback c u hu]
    exact (hH c).1 hc
  have hclosed : IsClosed (H : Set (GL (Fin n) E)) := by
    have hset : (H : Set (GL (Fin n) E)) = {c | c⁻¹ * δ * sg σ c = δ} := Set.ext hH
    rw [hset]
    exact isClosed_eq ((continuous_inv.mul continuous_const).mul (sg_cont hσ.isom)) continuous_const
  have hcomm : ∀ a ∈ H, ∀ b ∈ H, Commute a b := by
    intro a ha b hb
    obtain ⟨u, hu⟩ := hcen a ha
    obtain ⟨v, hv⟩ := hcen b hb
    rw [hback a u hu, hback b v hv]
    show y * diagT E (Fin n) u * y⁻¹ * (y * diagT E (Fin n) v * y⁻¹) =
      y * diagT E (Fin n) v * y⁻¹ * (y * diagT E (Fin n) u * y⁻¹)
    calc y * diagT E (Fin n) u * y⁻¹ * (y * diagT E (Fin n) v * y⁻¹)
        = y * (diagT E (Fin n) u * diagT E (Fin n) v) * y⁻¹ := by group
      _ = y * (diagT E (Fin n) v * diagT E (Fin n) u) * y⁻¹ := by rw [diag_comm u v]
      _ = y * diagT E (Fin n) v * y⁻¹ * (y * diagT E (Fin n) u * y⁻¹) := by group
  have hV : ∀ ρ ∈ R, ∀ h : H, h ∈ {h : H | y⁻¹ * ↑h * y ∈ ball n r} ↔
      (y * diagT E (Fin n) ρ)⁻¹ * ↑h * (y * diagT E (Fin n) ρ) ∈ K := by
    intro ρ _ h
    obtain ⟨u, hu⟩ := hcen h h.2
    have e : (y * diagT E (Fin n) ρ)⁻¹ * ↑h * (y * diagT E (Fin n) ρ) = y⁻¹ * ↑h * y := by
      calc (y * diagT E (Fin n) ρ)⁻¹ * ↑h * (y * diagT E (Fin n) ρ)
          = (diagT E (Fin n) ρ)⁻¹ * (y⁻¹ * ↑h * y) * diagT E (Fin n) ρ := by group
        _ = y⁻¹ * ↑h * y := by
          rw [hu, mul_assoc, diag_comm u ρ, inv_mul_cancel_left]
    rw [Set.mem_setOf_eq, e, ← SetLike.mem_coe, hK]
  have hS : ∀ g, g ∈ {g : GL (Fin n) E | g⁻¹ * δ * sg σ g ∈ elemSet r A} ↔
      ∃ ρ ∈ R, ∃ h ∈ H, ∃ κ ∈ K, g = h * (y * diagT E (Fin n) ρ) * κ := by
    intro g
    rw [Set.mem_setOf_eq, hsupp g]
    constructor
    · rintro ⟨u, hu, κ, hκ, rfl⟩
      obtain ⟨ρ, hρR, p, s, hp, hs, rfl⟩ := (hR u).1 hu
      refine ⟨ρ, hρR, y * diagT E (Fin n) p * y⁻¹, (hH _).2 ((hfix p).2 hp), diagT E (Fin n) s * κ, ?_, ?_⟩
      · refine K.mul_mem ?_ ?_
        · rw [← SetLike.mem_coe, hK]
          exact diag_ball hs
        · rw [← SetLike.mem_coe, hK]
          exact hκ
      · rw [map_mul, map_mul, diag_comm ρ p]
        group
    · rintro ⟨ρ, hρR, h, hh, κ, hκ, rfl⟩
      obtain ⟨w, hw⟩ := hcen h hh
      have hw' := hfixH h hh w hw
      refine ⟨w * ρ, (hR _).2 ⟨ρ, hρR, w, 1, hw', fun i => by simp, by rw [mul_one, mul_comm]⟩, κ, ?_, ?_⟩
      · rw [← hK]
        exact hκ
      · rw [map_mul, hback h w hw]
        group
  have hD : ∀ i ∈ R, ∀ j ∈ R, (∃ h ∈ H, ∃ κ ∈ K, y * diagT E (Fin n) i = h * (y * diagT E (Fin n) j) * κ) →
      i = j := by
    rintro i hi j hj ⟨h, hh, κ, hκ, he⟩
    obtain ⟨w, hw⟩ := hcen h hh
    have hw' := hfixH h hh w hw
    have hk : κ = diagT E (Fin n) (w⁻¹ * j⁻¹ * i) := by
      calc κ = (h * (y * diagT E (Fin n) j))⁻¹ * (y * diagT E (Fin n) i) := by
            rw [he]
            group
        _ = diagT E (Fin n) (w⁻¹ * j⁻¹ * i) := by
          rw [hback h w hw, mul_comm w⁻¹ j⁻¹]
          simp only [map_mul, map_inv]
          group
    refine hRd i hi j hj ⟨w, w⁻¹ * j⁻¹ * i, hw', near_of_ball ?_, by group⟩
    rw [← hk, ← hK]
    exact hκ
  have key := cosetSum (GL (Fin n) E) μ hμ K H hKo hKc hclosed hcomm ν hν (Fin n → Eˣ) R
    (fun ρ => y * diagT E (Fin n) ρ) {h : H | y⁻¹ * ↑h * y ∈ ball n r}
    {g : GL (Fin n) E | g⁻¹ * δ * sg σ g ∈ elemSet r A} hV hS hD
  rw [hK] at key
  exact key
end

