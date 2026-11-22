import Formalism.NormUnitaryBounds.Statement

-- bundled from Formalism.NormUnitaryBounds.DetPolynomialWeights.NormMul
section
open MvPolynomial Finset

noncomputable section

namespace Formalism.NormUnitaryCountingLemmas

namespace NMul

theorem vandermonde {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℕ) (m : ℕ) :
    ∑ l ∈ finsuppAntidiag (univ : Finset ι) m, ∏ k, (c k).choose (l k) =
      (∑ k, c k).choose m := by
  have h1 : (∑ k, c k).choose m = PowerSeries.coeff m
      (((∏ k, (1 + Polynomial.X : Polynomial ℕ) ^ (c k) : Polynomial ℕ)) : PowerSeries ℕ) := by
    rw [Polynomial.coeff_coe, Finset.prod_pow_eq_pow_sum, Polynomial.coeff_one_add_X_pow,
      Nat.cast_id]
  have h2 : (((∏ k, (1 + Polynomial.X : Polynomial ℕ) ^ (c k) : Polynomial ℕ)) : PowerSeries ℕ)
      = ∏ k, (((1 + Polynomial.X : Polynomial ℕ) ^ (c k) : Polynomial ℕ) : PowerSeries ℕ) :=
    map_prod (Polynomial.coeToPowerSeries.ringHom (R := ℕ)) _ _
  rw [h1, h2, PowerSeries.coeff_prod]
  refine sum_congr rfl fun l _ => prod_congr rfl fun k _ => ?_
  rw [Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow, Nat.cast_id]

theorem weight_blockWt {N n : ℕ} (a : Fin N × Fin n →₀ ℕ) (j : Fin N) :
    Finsupp.weight (blockWt N n) a j = blockDeg a j := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [blockWt, blockDeg, Finset.sum_apply, Fintype.sum_prod_type, Pi.smul_apply,
    Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single j (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

theorem blockDeg_of_mem {N n : ℕ} {ν : Fin N → ℕ} {F : MvPolynomial (Fin N × Fin n) ℂ}
    (hF : F ∈ weightedHomogeneousSubmodule ℂ (blockWt N n) ν) {a : Fin N × Fin n →₀ ℕ}
    (ha : a ∈ F.support) (j : Fin N) : blockDeg a j = ν j := by
  rw [mem_weightedHomogeneousSubmodule] at hF
  have := hF (mem_support_iff.1 ha)
  rw [← weight_blockWt, this]

theorem blockDeg_add {N n : ℕ} (a b : Fin N × Fin n →₀ ℕ) (j : Fin N) :
    blockDeg (a + b) j = blockDeg a j + blockDeg b j := by
  simp [blockDeg, sum_add_distrib]

theorem bweight_pos {N n : ℕ} (e : Fin N × Fin n →₀ ℕ) : 0 < bweight e := by
  unfold bweight
  positivity

theorem fact_add (x y : ℕ) :
    ((x + y).factorial : ℝ) = ((x + y).choose x : ℝ) * x.factorial * y.factorial := by
  rw [Nat.choose_symm_add]
  exact_mod_cast (Nat.add_choose_mul_factorial_mul_factorial x y).symm

theorem bweight_add {N n : ℕ} (a b : Fin N × Fin n →₀ ℕ) :
    bweight (a + b) * ∏ j, ((blockDeg (a + b) j).choose (blockDeg a j) : ℝ) =
      bweight a * bweight b * ∏ j, ∏ k, (((a + b) (j, k)).choose (a (j, k)) : ℝ) := by
  unfold bweight
  rw [← prod_mul_distrib, ← prod_mul_distrib, ← prod_mul_distrib]
  refine prod_congr rfl fun j _ => ?_
  rw [blockDeg_add]
  simp only [Finsupp.coe_add, Pi.add_apply]
  push_cast
  rw [fact_add (blockDeg a j) (blockDeg b j),
    prod_congr rfl (fun k _ => fact_add (a (j, k)) (b (j, k))), prod_mul_distrib,
    prod_mul_distrib]
  have h1 : (0 : ℝ) < ((blockDeg a j + blockDeg b j).choose (blockDeg a j) : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_right _ _)
  have h2 : (0 : ℝ) < (blockDeg a j).factorial := by positivity
  have h3 : (0 : ℝ) < (blockDeg b j).factorial := by positivity
  field_simp

def Dc {N n : ℕ} (ν : Fin N → ℕ) (c : Fin N × Fin n →₀ ℕ) : ℝ :=
  ∏ j, ((blockDeg c j).choose (ν j) : ℝ)

def Pc {N n : ℕ} (c a : Fin N × Fin n →₀ ℕ) : ℝ :=
  ∏ j, ∏ k, ((c (j, k)).choose (a (j, k)) : ℝ)

theorem comb {N n : ℕ} (ν : Fin N → ℕ) (sF sG : Finset (Fin N × Fin n →₀ ℕ))
    (hF : ∀ a ∈ sF, ∀ j, blockDeg a j = ν j) (c : Fin N × Fin n →₀ ℕ) :
    ∑ p ∈ (sF ×ˢ sG).filter (fun p => p.1 + p.2 = c), ∏ j, ∏ k, (c (j, k)).choose (p.1 (j, k)) ≤
      ∏ j, (blockDeg c j).choose (ν j) := by
  classical
  have hR : ∏ j, (blockDeg c j).choose (ν j) =
      ∑ x ∈ Fintype.piFinset (fun j => finsuppAntidiag (univ : Finset (Fin n)) (ν j)),
        ∏ j, ∏ k, (c (j, k)).choose (x j k) := by
    calc ∏ j, (blockDeg c j).choose (ν j)
        = ∏ j, ∑ l ∈ finsuppAntidiag (univ : Finset (Fin n)) (ν j), ∏ k, (c (j, k)).choose (l k) :=
          prod_congr rfl fun j _ => (vandermonde (fun k => c (j, k)) (ν j)).symm
      _ = _ := Finset.prod_univ_sum _ _
  rw [hR]
  let ι : (Fin N × Fin n →₀ ℕ) × (Fin N × Fin n →₀ ℕ) → (Fin N → Fin n →₀ ℕ) :=
    fun p j => Finsupp.equivFunOnFinite.symm (fun k => p.1 (j, k))
  have hinj : Set.InjOn ι ((sF ×ˢ sG).filter (fun p => p.1 + p.2 = c)) := by
    intro p hp q hq hpq
    rw [mem_coe, mem_filter] at hp hq
    have h1 : p.1 = q.1 := by
      ext ⟨j, k⟩
      have := congrArg (fun x => x j k) hpq
      simpa [ι] using this
    have h2 : p.2 = q.2 := by
      have := hp.2.trans hq.2.symm
      rw [h1] at this
      exact add_left_cancel this
    exact Prod.ext h1 h2
  calc ∑ p ∈ (sF ×ˢ sG).filter (fun p => p.1 + p.2 = c), ∏ j, ∏ k, (c (j, k)).choose (p.1 (j, k))
      = ∑ p ∈ (sF ×ˢ sG).filter (fun p => p.1 + p.2 = c),
          (fun x : Fin N → Fin n →₀ ℕ => ∏ j, ∏ k, (c (j, k)).choose (x j k)) (ι p) := by
        simp [ι]
    _ = ∑ x ∈ ((sF ×ˢ sG).filter (fun p => p.1 + p.2 = c)).image ι,
          ∏ j, ∏ k, (c (j, k)).choose (x j k) := (sum_image (f := fun x : Fin N → Fin n →₀ ℕ =>
          ∏ j, ∏ k, (c (j, k)).choose (x j k)) hinj).symm
    _ ≤ _ := by
        apply sum_le_sum_of_subset
        intro x hx
        rw [mem_image] at hx
        obtain ⟨p, hp, rfl⟩ := hx
        rw [Fintype.mem_piFinset]
        intro j
        rw [mem_finsuppAntidiag]
        refine ⟨?_, subset_univ _⟩
        rw [mem_filter, mem_product] at hp
        rw [← hF _ hp.1.1 j]
        simp [ι, blockDeg]

theorem key_c {N n : ℕ} {ν : Fin N → ℕ} {F G : MvPolynomial (Fin N × Fin n) ℂ}
    (hF : ∀ a ∈ F.support, ∀ j, blockDeg a j = ν j) (c : Fin N × Fin n →₀ ℕ) :
    ‖∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
        coeff p.1 F * coeff p.2 G‖ ^ 2 * bweight c ≤
      ∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
        (‖coeff p.1 F‖ ^ 2 * bweight p.1) * (‖coeff p.2 G‖ ^ 2 * bweight p.2) := by
  classical
  rcases ((F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c)).eq_empty_or_nonempty
    with hA | hA
  · simp [hA]
  have hmem : ∀ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
      p.1 ∈ F.support ∧ p.2 ∈ G.support ∧ p.1 + p.2 = c := by
    intro p hp
    rw [mem_filter, mem_product] at hp
    exact ⟨hp.1.1, hp.1.2, hp.2⟩
  have hDpos : 0 < Dc ν c := by
    obtain ⟨p0, hp0⟩ := hA
    obtain ⟨h1, _, h3⟩ := hmem p0 hp0
    refine prod_pos fun j _ => ?_
    have : ν j ≤ blockDeg c j := by
      rw [← h3, ← hF _ h1 j, blockDeg_add]
      exact Nat.le_add_right _ _
    exact_mod_cast Nat.choose_pos this
  have hPpos : ∀ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
      0 < Pc c p.1 := by
    intro p hp
    obtain ⟨_, _, h3⟩ := hmem p hp
    refine prod_pos fun j _ => prod_pos fun k _ => ?_
    have : p.1 (j, k) ≤ c (j, k) := by
      rw [← h3]
      simp
    exact_mod_cast Nat.choose_pos this
  have hW : ∀ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
      bweight c = bweight p.1 * bweight p.2 * Pc c p.1 / Dc ν c := by
    intro p hp
    obtain ⟨h1, _, h3⟩ := hmem p hp
    have := bweight_add p.1 p.2
    rw [h3] at this
    have e : ∏ j, ((blockDeg c j).choose (blockDeg p.1 j) : ℝ) = Dc ν c :=
      prod_congr rfl fun j _ => by rw [hF _ h1 j]
    rw [e] at this
    rw [eq_div_iff hDpos.ne']
    exact this
  have hsumP : ∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c), Pc c p.1 ≤
      Dc ν c := by
    have := comb ν F.support G.support hF c
    unfold Pc Dc
    exact_mod_cast this
  have hgpos : ∀ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
      0 < Pc c p.1 / Dc ν c := fun p hp => div_pos (hPpos p hp) hDpos
  have hsumg : ∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
      Pc c p.1 / Dc ν c ≤ 1 := by
    rw [← sum_div, div_le_one hDpos]
    exact hsumP
  have hsumgpos : 0 < ∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
      Pc c p.1 / Dc ν c := sum_pos hgpos hA
  have hsed := sq_sum_div_le_sum_sq_div _ (fun p => ‖coeff p.1 F * coeff p.2 G‖) hgpos
  have h1 : ‖∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
        coeff p.1 F * coeff p.2 G‖ ^ 2 ≤
      ∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
        ‖coeff p.1 F * coeff p.2 G‖ ^ 2 / (Pc c p.1 / Dc ν c) := by
    calc _ ≤ (∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
          ‖coeff p.1 F * coeff p.2 G‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ _ := le_div_self (sq_nonneg _) hsumgpos hsumg
      _ ≤ _ := hsed
  calc _ ≤ (∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
        ‖coeff p.1 F * coeff p.2 G‖ ^ 2 / (Pc c p.1 / Dc ν c)) * bweight c :=
        mul_le_mul_of_nonneg_right h1 (bweight_pos c).le
    _ = _ := by
      rw [sum_mul]
      refine sum_congr rfl fun p hp => ?_
      have hP := hPpos p hp
      rw [hW p hp, norm_mul]
      field_simp

theorem coeff_mul_eq {N n : ℕ} (F G : MvPolynomial (Fin N × Fin n) ℂ)
    (c : Fin N × Fin n →₀ ℕ) :
    coeff c (F * G) = ∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
      coeff p.1 F * coeff p.2 G := by
  classical
  rw [coeff_mul]
  symm
  refine sum_subset (fun p hp => ?_) (fun p hp hnot => ?_)
  · rw [mem_filter] at hp
    exact mem_antidiagonal.2 hp.2
  · by_cases h1 : coeff p.1 F = 0
    · simp [h1]
    by_cases h2 : coeff p.2 G = 0
    · simp [h2]
    have h3 : p.1 + p.2 = c := mem_antidiagonal.1 hp
    exact (hnot (mem_filter.2 ⟨mem_product.2 ⟨mem_support_iff.2 h1, mem_support_iff.2 h2⟩,
      h3⟩)).elim

theorem normSq_mul {N n : ℕ} (ν : Fin N → ℕ) (F G : MvPolynomial (Fin N × Fin n) ℂ)
    (hF : F ∈ weightedHomogeneousSubmodule ℂ (blockWt N n) ν) :
    bnormSq (F * G) ≤ bnormSq F * bnormSq G := by
  classical
  have hF' : ∀ a ∈ F.support, ∀ j, blockDeg a j = ν j := fun a ha j => blockDeg_of_mem hF ha j
  have hnn : ∀ p : (Fin N × Fin n →₀ ℕ) × (Fin N × Fin n →₀ ℕ),
      0 ≤ (‖coeff p.1 F‖ ^ 2 * bweight p.1) * (‖coeff p.2 G‖ ^ 2 * bweight p.2) := fun p =>
    mul_nonneg (mul_nonneg (sq_nonneg _) (bweight_pos _).le)
      (mul_nonneg (sq_nonneg _) (bweight_pos _).le)
  calc bnormSq (F * G) = ∑ c ∈ (F * G).support, ‖coeff c (F * G)‖ ^ 2 * bweight c := rfl
    _ ≤ ∑ c ∈ (F * G).support, ∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
          (‖coeff p.1 F‖ ^ 2 * bweight p.1) * (‖coeff p.2 G‖ ^ 2 * bweight p.2) := by
        refine sum_le_sum fun c _ => ?_
        rw [coeff_mul_eq]
        exact key_c hF' c
    _ = ∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 ∈ (F * G).support),
          (‖coeff p.1 F‖ ^ 2 * bweight p.1) * (‖coeff p.2 G‖ ^ 2 * bweight p.2) :=
        sum_fiberwise_eq_sum_filter _ _ _ _
    _ ≤ ∑ p ∈ F.support ×ˢ G.support,
          (‖coeff p.1 F‖ ^ 2 * bweight p.1) * (‖coeff p.2 G‖ ^ 2 * bweight p.2) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p _ _ => hnn p)
    _ = bnormSq F * bnormSq G := by
        rw [bnormSq, bnormSq, Finset.sum_mul_sum, Finset.sum_product]

end NMul

end Formalism.NormUnitaryCountingLemmas
end
end

-- bundled from Formalism.NormUnitaryBounds.DetPolynomialWeights.ShearCoefficients
section
open MvPolynomial

noncomputable section

namespace Formalism.NormUnitaryCountingLemmas

namespace ShearCoefficients

variable {R : Type*} [CommRing R]

lemma mem_H_iff {N n : ℕ} (ν : Fin N → ℕ) (F : MvPolynomial (Fin N × Fin n) R) :
    F ∈ H R ν ↔ F.IsWeightedHomogeneous (blockWt N n) ν ∧
      ∀ i j : Fin N, i < j → shear R i j F = Polynomial.C F := by
  simp only [H, Submodule.mem_inf, mem_weightedHomogeneousSubmodule, Submodule.mem_iInf,
    LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply,
    IsScalarTower.toAlgHom_apply, sub_eq_zero]
  rfl

lemma weight_mapDomain {σ τ M : Type*} [AddCommMonoid M] (w : τ → M) (f : σ → τ)
    (d : σ →₀ ℕ) :
    Finsupp.weight w (Finsupp.mapDomain f d) = Finsupp.weight (w ∘ f) d := by
  classical
  simp only [Finsupp.weight_apply]
  rw [Finsupp.sum_mapDomain_index] <;> simp [add_smul]

lemma isWeightedHomogeneous_rename {σ τ M : Type*} [AddCommMonoid M] {w : τ → M} {f : σ → τ}
    {m : M} {F : MvPolynomial σ R} (hF : F.IsWeightedHomogeneous (w ∘ f) m) :
    (rename f F).IsWeightedHomogeneous w m := by
  refine IsWeightedHomogeneous.induction_on
    (motive := fun p _ => (rename f p).IsWeightedHomogeneous w m) ?_ ?_ ?_ hF
  · simpa using isWeightedHomogeneous_zero R w m
  · intro p q _ _ hp hq
    rw [map_add]; exact hp.add hq
  · intro d r hr
    rw [rename_monomial]
    exact isWeightedHomogeneous_monomial _ _ _ (by rw [weight_mapDomain, hr])

lemma shear_rename_perm {N n : ℕ} (i j : Fin N) (σ : Equiv.Perm (Fin n))
    (F : MvPolynomial (Fin N × Fin n) R) :
    shear R i j (rename (fun p : Fin N × Fin n => (p.1, σ p.2)) F) =
      Polynomial.map (rename (R := R) (fun p : Fin N × Fin n => (p.1, σ p.2))).toRingHom
        (shear R i j F) := by
  have key : (shear R i j).comp (rename (fun p : Fin N × Fin n => (p.1, σ p.2))) =
      (Polynomial.mapAlgHom (rename (fun p : Fin N × Fin n => (p.1, σ p.2)))).comp
        (shear R i j) := by
    apply MvPolynomial.algHom_ext
    intro p
    by_cases h : p.1 = j <;> simp [shear, h]
  have h := congrArg (fun φ => φ F) key
  simpa [Polynomial.coe_mapAlgHom] using h

theorem perm : NormUnitaryPermutationInvariance := by
  intro R _ N n ν σ F hF
  rw [mem_H_iff] at hF ⊢
  refine ⟨isWeightedHomogeneous_rename hF.1, fun i j hij => ?_⟩
  rw [shear_rename_perm, hF.2 i j hij, Polynomial.map_C]
  rfl

def CoeffHom {σ M : Type*} [AddCommMonoid M] (wt : σ → M) (m : M)
    (P : Polynomial (MvPolynomial σ R)) : Prop :=
  ∀ k, (P.coeff k).IsWeightedHomogeneous wt m

section CoeffHom

variable {σ M : Type*} [AddCommMonoid M] {wt : σ → M}

lemma CoeffHom.add {m : M} {P Q : Polynomial (MvPolynomial σ R)} (hP : CoeffHom wt m P)
    (hQ : CoeffHom wt m Q) : CoeffHom wt m (P + Q) := by
  intro k; rw [Polynomial.coeff_add]; exact (hP k).add (hQ k)

lemma CoeffHom.zero (m : M) : CoeffHom (R := R) wt m 0 := by
  intro k; rw [Polynomial.coeff_zero]; exact isWeightedHomogeneous_zero R wt m

lemma CoeffHom.mul {a b : M} {P Q : Polynomial (MvPolynomial σ R)} (hP : CoeffHom wt a P)
    (hQ : CoeffHom wt b Q) : CoeffHom wt (a + b) (P * Q) := by
  intro k
  rw [Polynomial.coeff_mul]
  exact IsWeightedHomogeneous.sum _ _ _ (fun x _ => (hP x.1).mul (hQ x.2))

lemma CoeffHom.C {m : M} {r : MvPolynomial σ R} (h : r.IsWeightedHomogeneous wt m) :
    CoeffHom wt m (Polynomial.C r) := by
  intro k
  rw [Polynomial.coeff_C]
  split_ifs
  · exact h
  · exact isWeightedHomogeneous_zero R wt m

lemma CoeffHom.X : CoeffHom (R := R) wt 0 Polynomial.X := by
  intro k
  rw [Polynomial.coeff_X]
  split_ifs
  · exact isWeightedHomogeneous_one R wt
  · exact isWeightedHomogeneous_zero R wt 0

lemma CoeffHom.one : CoeffHom (R := R) wt 0 1 := by
  simpa using CoeffHom.C (R := R) (isWeightedHomogeneous_one R wt)

lemma CoeffHom.pow {a : M} {P : Polynomial (MvPolynomial σ R)} (h : CoeffHom wt a P) (e : ℕ) :
    CoeffHom wt (e • a) (P ^ e) := by
  induction e with
  | zero => simpa using CoeffHom.one (R := R) (wt := wt)
  | succ e ih => rw [pow_succ, succ_nsmul]; exact ih.mul h

lemma CoeffHom.prod {ι : Type*} (s : Finset ι) (P : ι → Polynomial (MvPolynomial σ R))
    (a : ι → M) (h : ∀ x ∈ s, CoeffHom wt (a x) (P x)) :
    CoeffHom wt (∑ x ∈ s, a x) (∏ x ∈ s, P x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using CoeffHom.one (R := R) (wt := wt)
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx]
    exact (h x (Finset.mem_insert_self _ _)).mul
      (ih fun y hy => h y (Finset.mem_insert_of_mem hy))

end CoeffHom

lemma coeffHom_shear_X {N n : ℕ} (i j : Fin N) (p : Fin N × Fin n) :
    CoeffHom (R := R) (coordWt N n) (coordWt N n p)
      (Polynomial.C (X p) +
        (if p.1 = j then Polynomial.X * Polynomial.C (X (i, p.2)) else 0)) := by
  refine CoeffHom.add (CoeffHom.C (isWeightedHomogeneous_X R _ p)) ?_
  split_ifs
  · have h := (CoeffHom.X (R := R) (wt := coordWt N n)).mul
      (CoeffHom.C (isWeightedHomogeneous_X R (coordWt N n) (i, p.2)))
    rw [zero_add] at h
    exact h
  · exact CoeffHom.zero _

lemma coeffHom_shear_monomial {N n : ℕ} (i j : Fin N) (d : (Fin N × Fin n) →₀ ℕ) (r : R) :
    CoeffHom (coordWt N n) (Finsupp.weight (coordWt N n) d) (shear R i j (monomial d r)) := by
  rw [shear, aeval_monomial, Finsupp.weight_apply, Finsupp.prod, Finsupp.sum,
    ← zero_add (∑ a ∈ d.support, d a • coordWt N n a)]
  refine CoeffHom.mul ?_ (CoeffHom.prod _ _ _ fun p _ => (coeffHom_shear_X i j p).pow _)
  rw [Polynomial.algebraMap_apply]
  exact CoeffHom.C (isWeightedHomogeneous_C _ _)

lemma comp_coeff_shear {N n : ℕ} (i j : Fin N) (w : Fin n → ℕ)
    (F : MvPolynomial (Fin N × Fin n) R) (k : ℕ) :
    weightedHomogeneousComponent (coordWt N n) w ((shear R i j F).coeff k) =
      (shear R i j (weightedHomogeneousComponent (coordWt N n) w F)).coeff k := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial d r =>
    rw [weightedHomogeneousComponent_of_mem (coeffHom_shear_monomial i j d r k),
      weightedHomogeneousComponent_of_mem
        (isWeightedHomogeneous_monomial (coordWt N n) d r rfl)]
    split_ifs <;> simp
  | add p q hp hq =>
    rw [map_add, map_add, Polynomial.coeff_add, map_add, hp, hq, map_add, Polynomial.coeff_add]

theorem weight : NormUnitaryWeight := by
  classical
  intro R _ N n ν F hF w
  rw [mem_H_iff] at hF ⊢
  refine ⟨?_, fun i j hij => ?_⟩
  · intro d hd
    rw [coeff_weightedHomogeneousComponent] at hd
    split_ifs at hd
    · exact hF.1 hd
    · exact absurd rfl hd
  · refine Polynomial.ext fun k => ?_
    rw [← comp_coeff_shear, hF.2 i j hij, Polynomial.coeff_C, Polynomial.coeff_C]
    split_ifs <;> simp

end ShearCoefficients

end Formalism.NormUnitaryCountingLemmas
end
end

