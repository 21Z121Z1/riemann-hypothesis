import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LangXRoot
section
namespace GlobalTheory.PMonE.LangIsogenyConstruction

open Polynomial

section Lang
variable {k V : Type} [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]

noncomputable def langX (q : ℕ) (a : ℕ → k) : ℕ → k[X]
  | 0 => C (a 0) * X ^ q
  | (i + 1) => (langX q a i) ^ q + C (a (i + 1)) * X ^ q

theorem langX_dvd (q : ℕ) (hq : 1 < q) (a : ℕ → k) (i : ℕ) : (X : k[X]) ^ q ∣ langX q a i := by
  induction i with
  | zero => exact Dvd.intro_left _ rfl
  | succ i ih =>
    exact dvd_add (ih.trans (dvd_pow_self _ (by omega))) (Dvd.intro_left _ rfl)

theorem langX_ne (q : ℕ) (hq : 1 < q) (a : ℕ → k) (i : ℕ) (h : ∃ j ≤ i, a j ≠ 0) :
    langX q a i ≠ 0 := by
  induction i with
  | zero =>
    obtain ⟨j, hj, ha⟩ := h
    obtain rfl : j = 0 := by omega
    simp [langX, ha]
  | succ i ih =>
    intro h0
    have h0' : (langX q a i) ^ q + C (a (i + 1)) * X ^ q = 0 := h0
    have h1 : (langX q a i) ^ q = - (C (a (i + 1)) * X ^ q) := eq_neg_of_add_eq_zero_left h0'
    have hd : (X : k[X]) ^ (q * q) ∣ (langX q a i) ^ q := by
      rw [pow_mul]; exact pow_dvd_pow_of_dvd (langX_dvd q hq a i) q
    have hc := (X_pow_dvd_iff.1 hd) q (by nlinarith)
    rw [h1] at hc
    have ha : a (i + 1) = 0 := by simpa using hc
    have hX : langX q a i = 0 := by
      rw [ha] at h1
      simp only [map_zero, zero_mul, neg_zero] at h1
      exact pow_eq_zero_iff (by omega) |>.1 h1
    refine ih ?_ hX
    obtain ⟨j, hj, haj⟩ := h
    refine ⟨j, ?_, haj⟩
    by_contra hji
    have : j = i + 1 := by omega
    exact haj (this ▸ ha)

theorem langX_root (q : ℕ) (hq : 1 < q) (a : ℕ → k) (i : ℕ) (h : langX q a i ≠ 0) :
    ∃ y : k, y ≠ 0 ∧ (langX q a i).eval y = y := by
  obtain ⟨T, hT⟩ := langX_dvd q hq a i
  have hT0 : T ≠ 0 := by
    rintro rfl
    exact h (by simpa using hT)
  have hdeg : 0 < (X ^ (q - 1) * T).degree := by
    rw [degree_mul, degree_X_pow]
    have h0 : 0 ≤ T.degree := zero_le_degree_iff.2 hT0
    have h1 : (0 : WithBot ℕ) < ((q - 1 : ℕ) : WithBot ℕ) := by
      exact_mod_cast (by omega : 0 < q - 1)
    exact add_pos_of_pos_of_nonneg h1 h0
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root (X ^ (q - 1) * T - C 1)
    (by rw [degree_sub_C hdeg]; exact hdeg.ne')
  have hy' : y ^ (q - 1) * T.eval y = 1 := by
    have h2 : (X ^ (q - 1) * T - C 1).eval y = 0 := hy
    simp only [eval_sub, eval_mul, eval_pow, eval_X, eval_C] at h2
    exact sub_eq_zero.1 h2
  refine ⟨y, ?_, ?_⟩
  · rintro rfl
    rw [zero_pow (by omega)] at hy'
    simp at hy'
  · rw [hT]
    simp only [eval_mul, eval_pow, eval_X]
    have h3 : y ^ q = y * y ^ (q - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [h3, mul_assoc, hy', mul_one]

theorem as_root (q : ℕ) (hq : 1 < q) (c : k) : ∃ z : k, z ^ q - z = c := by
  have hdeg : (X ^ q - (X + C c) : k[X]).degree = q := by
    rw [degree_sub_eq_left_of_degree_lt, degree_X_pow]
    rw [degree_X_pow, degree_X_add_C]
    exact_mod_cast hq
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (X ^ q - (X + C c) : k[X]) (by
    rw [hdeg]; exact_mod_cast (by omega : q ≠ 0))
  have h2 : (X ^ q - (X + C c) : k[X]).eval z = 0 := hz
  simp only [eval_sub, eval_add, eval_pow, eval_X, eval_C] at h2
  exact ⟨z, by linear_combination h2⟩

def langQ (U : Submodule k V) (F : V → V) (v : V) (r : ℕ) : Prop :=
  ∃ u ∈ U, ∃ a : ℕ → k, F^[r] v = u + ∑ i ∈ Finset.range r, a i • F^[i] v

theorem lang_span [FiniteDimensional k V] (q : ℕ) (hq : 1 < q) (F : V →+ V)
    (hF : ∀ (a : k) (v : V), F (a • v) = a ^ q • F v) (hinj : Function.Injective F) :
    Submodule.span k {v : V | F v = v} = ⊤ := by
  classical
  set U := Submodule.span k {v : V | F v = v} with hU
  have hfix : ∀ w, F w = w → w ∈ U := fun w hw => Submodule.subset_span hw
  have h2 : ∀ u ∈ U, ∃ u' ∈ U, F u' - u' = u := by
    intro u hu
    induction hu using Submodule.closure_induction with
    | zero => exact ⟨0, U.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨x', hx', ex⟩ := hx
      obtain ⟨y', hy', ey⟩ := hy
      exact ⟨x' + y', U.add_mem hx' hy', by rw [map_add, ← ex, ← ey]; abel⟩
    | smul_mem c w hw =>
      obtain ⟨z, hz⟩ := as_root q hq c
      refine ⟨z • w, U.smul_mem _ (hfix w hw), ?_⟩
      rw [hF, show F w = w from hw, ← sub_smul, hz]
  have h3 : ∀ u ∈ U, ∃ u' ∈ U, F u' = u := by
    intro u hu
    induction hu using Submodule.closure_induction with
    | zero => exact ⟨0, U.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨x', hx', ex⟩ := hx
      obtain ⟨y', hy', ey⟩ := hy
      exact ⟨x' + y', U.add_mem hx' hy', by rw [map_add, ← ex, ← ey]⟩
    | smul_mem c w hw =>
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c (by omega : 0 < q)
      refine ⟨z • w, U.smul_mem _ (hfix w hw), ?_⟩
      rw [hF, show F w = w from hw, hz]
  have h4 : ∀ x, F x ∈ U → x ∈ U := by
    intro x hx
    obtain ⟨u', hu', e⟩ := h3 _ hx
    rw [← hinj e]; exact hu'
  have h4' : ∀ (n : ℕ) (x : V), (⇑F)^[n] x ∈ U → x ∈ U := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      rw [Function.iterate_succ_apply'] at hx
      exact ih x (h4 _ hx)
  by_contra hne
  obtain ⟨v, hv⟩ : ∃ v, v ∉ U := by
    by_contra hall
    push Not at hall
    exact hne (eq_top_iff.2 fun x _ => hall x)
  have hex : ∃ r, langQ U (⇑F) v r := by
    let N : ℕ →o Submodule k V :=
      ⟨fun j => Submodule.span k (Set.range fun i : Fin j => (⇑F)^[(i : ℕ)] v), by
        intro j j' h
        refine Submodule.span_mono ?_
        rintro _ ⟨i, rfl⟩
        exact ⟨Fin.castLE h i, rfl⟩⟩
    obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.2 inferInstance N
    have hmem : (⇑F)^[n] v ∈ N (n + 1) := Submodule.subset_span ⟨Fin.last n, rfl⟩
    rw [← hn (n + 1) (by omega)] at hmem
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hmem
    refine ⟨n, 0, U.zero_mem, fun i => if h : i < n then c ⟨i, h⟩ else 0, ?_⟩
    rw [zero_add, ← hc, Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [i.2]
  obtain ⟨r, ⟨u, hu, a, ha⟩, hmin⟩ : ∃ r, langQ U (⇑F) v r ∧ ∀ j < r, ¬ langQ U (⇑F) v j :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · exfalso
      rw [h0] at ha
      simp only [Function.iterate_zero, id_eq, Finset.range_zero, Finset.sum_empty, add_zero] at ha
      exact hv (ha ▸ hu)
    · exact ⟨r - 1, by omega⟩
  by_cases hall : ∀ j ≤ s, a j = 0
  · have h0 : ∑ i ∈ Finset.range (s + 1), a i • (⇑F)^[i] v = 0 :=
      Finset.sum_eq_zero fun i hi => by
        rw [hall i (by simpa [Nat.lt_succ_iff] using hi), zero_smul]
    rw [h0, add_zero] at ha
    exact hv (h4' (s + 1) v (ha ▸ hu))
  · push Not at hall
    obtain ⟨y, hy0, hy⟩ := langX_root q hq a s (langX_ne q hq a s hall)
    obtain ⟨x, hxdef⟩ : ∃ x : ℕ → k, x = fun i => (langX q a i).eval y := ⟨_, rfl⟩
    have hx0 : x 0 = y ^ q * a 0 := by
      rw [hxdef]
      show (C (a 0) * X ^ q : k[X]).eval y = _
      simp only [eval_mul, eval_C, eval_pow, eval_X]
      ring
    have hxs : ∀ i, x (i + 1) = (x i) ^ q + y ^ q * a (i + 1) := by
      intro i
      rw [hxdef]
      show ((langX q a i) ^ q + C (a (i + 1)) * X ^ q : k[X]).eval y =
        ((langX q a i).eval y) ^ q + y ^ q * a (i + 1)
      simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
      ring
    have hxy : x s = y := by rw [hxdef]; exact hy
    obtain ⟨z, hz⟩ : ∃ z : V, z = ∑ i ∈ Finset.range (s + 1), x i • (⇑F)^[i] v := ⟨_, rfl⟩
    have hFz : F z - z = y ^ q • u := by
      have e1 : F z = ∑ i ∈ Finset.range s, (x i) ^ q • (⇑F)^[i + 1] v +
          y ^ q • (⇑F)^[s + 1] v := by
        rw [hz, map_sum, Finset.sum_range_succ]
        congr 1
        · refine Finset.sum_congr rfl fun i _ => ?_
          rw [hF, Function.iterate_succ_apply']
        · rw [hF, Function.iterate_succ_apply', hxy]
      have e2 : z = x 0 • v + ∑ i ∈ Finset.range s, x (i + 1) • (⇑F)^[i + 1] v := by
        rw [hz, Finset.sum_range_succ', add_comm]; rfl
      have e3 : ∑ i ∈ Finset.range (s + 1), a i • (⇑F)^[i] v =
          a 0 • v + ∑ i ∈ Finset.range s, a (i + 1) • (⇑F)^[i + 1] v := by
        rw [Finset.sum_range_succ', add_comm]; rfl
      rw [sub_eq_iff_eq_add, e1, ha, e3]
      conv_rhs => rw [e2]
      simp only [hx0, hxs, add_smul, Finset.sum_add_distrib, smul_add, Finset.smul_sum, smul_smul]
      abel
    obtain ⟨u', hu', e'⟩ := h2 (y ^ q • u) (U.smul_mem _ hu)
    have hzU : z ∈ U := by
      have h5 : F (z - u') = z - u' := by
        rw [map_sub, sub_eq_sub_iff_sub_eq_sub, hFz, e']
      have h6 := U.add_mem (hfix _ h5) hu'
      simpa using h6
    apply hmin s (by omega)
    refine ⟨y⁻¹ • z, U.smul_mem _ hzU, fun i => - (y⁻¹ * x i), ?_⟩
    rw [hz, Finset.sum_range_succ, hxy, smul_add, smul_smul, inv_mul_cancel₀ hy0, one_smul,
      Finset.smul_sum]
    simp only [neg_smul, Finset.sum_neg_distrib, smul_smul]
    abel

theorem lang_basis [FiniteDimensional k V] (q : ℕ) (hq : 1 < q) (F : V →+ V)
    (hF : ∀ (a : k) (v : V), F (a • v) = a ^ q • F v) (hinj : Function.Injective F) :
    ∃ b : Module.Basis (Fin (Module.finrank k V)) k V, ∀ i, F (b i) = b i := by
  classical
  have hs : ⊤ ≤ Submodule.span k {v : V | F v = v} := (lang_span q hq F hF hinj).ge
  let b' := Module.Basis.ofSpan hs
  haveI : Finite _ := Module.Finite.finite_basis b'
  letI := Fintype.ofFinite ((linearIndepOn_empty k id).extend (Set.empty_subset {v : V | F v = v}))
  let e := Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b').symm
  refine ⟨b'.reindex e, fun i => ?_⟩
  have h1 : b' (e.symm i) ∈ {v : V | F v = v} := Module.Basis.ofSpan_subset hs ⟨e.symm i, rfl⟩
  simpa using h1

end Lang

end GlobalTheory.PMonE.LangIsogenyConstruction
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeCosetTranslateMemOfCover
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem det_one_add_uniformizer_smul_ne_zero {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {r : ℕ} {ϖ : O} (hϖ : Irreducible ϖ)
    (a : Matrix (Fin r) (Fin r) O) : (1 + ϖ • a).det ≠ 0 := by
  intro h
  have hres : IsLocalRing.residue O ϖ = 0 :=
    (IsLocalRing.residue_eq_zero_iff ϖ).2 ((IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.not_isUnit)
  have hm : (IsLocalRing.residue O).mapMatrix (1 + ϖ • a) = 1 := by
    ext i j
    simp [Matrix.one_apply, hres, apply_ite (IsLocalRing.residue O)]
  have h1 : IsLocalRing.residue O ((1 + ϖ • a).det) = 1 := by
    rw [RingHom.map_det, hm, Matrix.det_one]
  rw [h, map_zero] at h1
  exact zero_ne_one h1

theorem exists_inv_integral_of_not_mem {O K : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] {ϖ : O}
    (hϖ : Irreducible ϖ) (y : K) (hy : ¬ ∃ c : O, y = algebraMap O K ϖ * algebraMap O K c) :
    ∃ u : O, algebraMap O K u * y = 1 := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy ⟨0, by simp⟩
  rcases ValuationRing.isInteger_or_isInteger O y with ⟨a, ha⟩ | ⟨u, hu⟩
  · have hau : IsUnit a := by
      by_contra hna
      have hmem : a ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal a).2 hna
      rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
      obtain ⟨c, rfl⟩ := hmem
      exact hy ⟨c, by rw [← ha, map_mul]⟩
    obtain ⟨v, rfl⟩ := hau
    refine ⟨(v⁻¹ : Oˣ), ?_⟩
    rw [← ha, ← map_mul]
    simp
  · exact ⟨u, by rw [hu]; exact inv_mul_cancel₀ hy0⟩

theorem coset_translate_mem_of_cover (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O)
    (hϖ : Irreducible ϖ) (N : ℕ) (x : Matrix (Fin r ⊕ Fin t) (Fin r) K) (g : GL (Fin r) K)
    (z₀ : Matrix (Fin r ⊕ Fin t) (Fin r) O)
    (hx : x * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O)
      (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z₀).map (algebraMap O K))
    (hcov : ∀ z : Matrix (Fin r ⊕ Fin t) (Fin r) O, ∃ (g' : GL (Fin r) K)
      (z' : Matrix (Fin r ⊕ Fin t) (Fin r) O), (x + (ϖ ^ N • z).map (algebraMap O K)) *
      (g' : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O)
      (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z').map (algebraMap O K))
    (z : Matrix (Fin r ⊕ Fin t) (Fin r) O) : ∃ z' : Matrix (Fin r ⊕ Fin t) (Fin r) O,
      (x + (ϖ ^ N • z).map (algebraMap O K)) * (g : Matrix (Fin r) (Fin r) K) =
      ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z').map
        (algebraMap O K) := by
  set ι := algebraMap O K with hι
  have hsmul : ∀ (c : O) {m n : Type} (A : Matrix m n O), (c • A).map ι = c • A.map ι := by
    intro c m n A
    exact Matrix.map_smul _ _ (fun a => by simp [hι, Algebra.smul_def]) A
  have hadd : ∀ {m n : Type} (A B : Matrix m n O), (A + B).map ι = A.map ι + B.map ι :=
    fun A B => Matrix.map_add _ (map_add ι) A B
  have hrow : ∀ (A : Matrix (Fin r ⊕ Fin t) (Fin r) K) (G : Matrix (Fin r) (Fin r) K),
      (A * G).toRows₁ = A.toRows₁ * G := fun A G => rfl
  set x₁ := x.toRows₁ with hx₁

  have hinv : ∀ w : Matrix (Fin r) (Fin r) O, (x₁ + (ϖ ^ N • w).map ι).det ≠ 0 := by
    intro w
    obtain ⟨g', z', h⟩ := hcov (Matrix.fromRows w 0)
    have h1 := congrArg Matrix.toRows₁ h
    rw [hrow] at h1
    have e1 : (x + (ϖ ^ N • Matrix.fromRows w (0 : Matrix (Fin t) (Fin r) O)).map ι).toRows₁ =
        x₁ + (ϖ ^ N • w).map ι := by
      ext i j; rfl
    have e2 : Matrix.toRows₁ (((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) +
        ϖ • z').map ι) = (1 + ϖ • Matrix.toRows₁ z').map ι := by
      ext i j; rfl
    rw [e1, e2] at h1
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, show ((1 + ϖ • Matrix.toRows₁ z').map ι).det = ι (1 + ϖ • Matrix.toRows₁ z').det from
      (RingHom.map_det ι _).symm] at h2
    intro h0
    rw [h0, zero_mul] at h2
    exact det_one_add_uniformizer_smul_ne_zero hϖ _
      ((injective_iff_map_eq_zero ι).1 (IsFractionRing.injective O K) _ h2.symm)

  have hdet : IsUnit x₁.det := by
    have := hinv 0
    rw [smul_zero, Matrix.map_zero _ (map_zero ι), add_zero] at this
    exact isUnit_iff_ne_zero.2 this
  set B := x₁⁻¹ with hB
  have hxB : x₁ * B = 1 := Matrix.mul_nonsing_inv _ hdet
  have hC : ∀ i j, ∃ c : O, ι (ϖ ^ N) * B i j = ι ϖ * ι c := by
    intro i j
    by_contra hne
    obtain ⟨u, hu⟩ := exists_inv_integral_of_not_mem hϖ (ι (ϖ ^ N) * B i j) hne
    apply hinv (Matrix.single j i (-u))
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨fun k => B k j, ?_, ?_⟩
    · intro h0
      have := congrFun h0 i
      simp only [Pi.zero_apply] at this
      rw [this, mul_zero, mul_zero] at hu
      exact zero_ne_one hu
    · funext k
      rw [Matrix.add_mulVec]
      have h1 : Matrix.mulVec x₁ (fun k => B k j) k = (1 : Matrix (Fin r) (Fin r) K) k j := by
        rw [← hxB]; rfl
      have h2 : Matrix.mulVec ((ϖ ^ N • Matrix.single j i (-u)).map ι) (fun k => B k j) k =
          if k = j then -(ι u * (ι (ϖ ^ N) * B i j)) else 0 := by
        simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.smul_apply, Matrix.single_apply]
        by_cases hk : k = j
        · subst hk
          rw [Finset.sum_eq_single i (fun b _ hb => by simp [Ne.symm hb])
            (fun h => absurd (Finset.mem_univ i) h)]
          simp [Algebra.smul_def]
          ring
        · simp [hk, Ne.symm hk]
      rw [Pi.add_apply, h1, h2, hu, Matrix.one_apply]
      split_ifs <;> simp

  choose C hC' using hC
  set Cm : Matrix (Fin r) (Fin r) O := Matrix.of C with hCmdef
  have hCm : ι (ϖ ^ N) • B = ι ϖ • Cm.map ι := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, hCmdef, Matrix.of_apply]
    exact hC' i j
  have hx1 : x₁ * (g : Matrix (Fin r) (Fin r) K) = (1 + ϖ • Matrix.toRows₁ z₀).map ι := by
    have h1 := congrArg Matrix.toRows₁ hx
    rw [hrow] at h1
    rw [h1]
    ext i j; rfl
  have hg : (g : Matrix (Fin r) (Fin r) K) = B * (1 + ϖ • Matrix.toRows₁ z₀).map ι := by
    rw [← hx1, ← Matrix.mul_assoc, hB, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  have key : ϖ ^ N • (g : Matrix (Fin r) (Fin r) K) =
      ϖ • (Cm * (1 + ϖ • Matrix.toRows₁ z₀)).map ι := by
    rw [hg, Matrix.map_mul, ← Matrix.smul_mul, ← Matrix.smul_mul, ← algebraMap_smul K (ϖ ^ N) B,
      ← algebraMap_smul K ϖ (Cm.map ι), hCm]
  refine ⟨z₀ + z * (Cm * (1 + ϖ • Matrix.toRows₁ z₀)), ?_⟩
  rw [Matrix.add_mul, hx, hsmul, Matrix.smul_mul, ← Matrix.mul_smul, key]
  simp only [hadd, hsmul, Matrix.map_mul, smul_add, add_assoc, Matrix.mul_smul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LaurentDegenerationFirstOrderKernel
section
open Polynomial

namespace GlobalTheory

theorem laurent_degeneration_abstract (k : Type) [Field k] (K : Type) [Field K] [Algebra k K] (σ : K)
    (O : K → Prop) (π0 π1 : K →ₗ[k] k) (h0 : ∀ z, O z → π0 (σ * z) = 0)
    (h1 : ∀ z, π1 (σ * z) = π0 z) (hone : π0 1 = 1)
    (hnorm : ∀ (a : ℕ) (y : Fin a → K), y ≠ 0 → ∃ (f : K) (c0 : Fin a), f * y c0 = 1 ∧ ∀ c, O (f * y c))
    (a e : ℕ) (V : Submodule k (Fin a → k)) (U : Type) [AddCommGroup U] [Module k U]
    (t u : V →ₗ[k] U) (he : e ≤ 1)
    (H : ∀ x0 x1 : Fin (e + 1) → V, (∀ j, t (x0 j) = 0 ∧ t (x1 j) = u (x0 j)) →
      ¬ LinearIndependent k x0)
    (y : Fin (e + 1) → Fin a → K)
    (hy : ∀ j (π : K →ₗ[k] k), ∃ x x' : V, (∀ c, x.1 c = π (y j c)) ∧
      (∀ c, x'.1 c = π (σ * y j c)) ∧ t x = u x') :
    ¬ LinearIndependent K y := by
  let P : (Fin a → K) → Prop := fun z => ∀ (π : K →ₗ[k] k), ∃ x x' : V, (∀ c, x.1 c = π (z c)) ∧
      (∀ c, x'.1 c = π (σ * z c)) ∧ t x = u x'
  have Psmul : ∀ (f : K) z, P z → P (f • z) := by
    intro f z hz π
    obtain ⟨x, x', h, h', h''⟩ := hz (π ∘ₗ LinearMap.mulLeft k f)
    refine ⟨x, x', fun c => by simpa using h c, fun c => ?_, h''⟩
    rw [h' c]
    simp [mul_left_comm]
  have Psub : ∀ z w, P z → P w → P (z - w) := by
    intro z w hz hw π
    obtain ⟨x, x', h, h', h''⟩ := hz π
    obtain ⟨v, v', g, g', g''⟩ := hw π
    refine ⟨x - v, x' - v', fun c => by simp [h c, g c], fun c => by simp [h' c, g' c, mul_sub],
      by simp [h'', g'']⟩
  have key : ∀ z, P z → z ≠ 0 → ∃ (f : K) (c0 : Fin a) (x0 x1 : V), f * z c0 = 1 ∧
      (∀ c, x0.1 c = π0 (f * z c)) ∧ t x0 = 0 ∧ t x1 = u x0 := by
    intro z hz hz0
    obtain ⟨f, c0, hf, hO⟩ := hnorm a z hz0
    have hP := Psmul f z hz
    obtain ⟨x, x', h, h', h''⟩ := hP π0
    obtain ⟨v, v', g, g', g''⟩ := hP π1
    have hx' : x' = 0 := by
      ext c
      rw [h' c]
      simpa using h0 _ (hO c)
    have hv' : v' = x := by
      ext c
      rw [g' c, h c, h1]
    refine ⟨f, c0, x, v, hf, fun c => by simpa using h c, by rw [h'', hx', map_zero],
      by rw [g'', hv']⟩
  intro hli
  obtain rfl | rfl : e = 0 ∨ e = 1 := by omega
  · obtain ⟨f, c0, x0, x1, hf, hx, ht, ht'⟩ := key (y 0) (hy 0) (hli.ne_zero 0)
    refine H (fun _ => x0) (fun _ => x1) (fun _ => ⟨ht, ht'⟩) ?_
    have hne : x0 ≠ 0 := by
      intro h
      have := hx c0
      rw [h, hf, hone] at this
      simp at this
    exact (linearIndependent_unique_iff (ι := Fin 1) (v := fun _ => x0)).2 hne
  · obtain ⟨f, c0, x0, x1, hf, hx, ht, ht'⟩ := key (y 0) (hy 0) (hli.ne_zero 0)
    have hw : y 1 - (y 1 c0 * f) • y 0 ≠ 0 := by
      intro h
      have hy2 : y = ![y 0, y 1] := by
        ext i : 1
        fin_cases i <;> rfl
      rw [hy2, LinearIndependent.pair_iff] at hli
      have := (hli (-(y 1 c0 * f)) 1 (by rw [← h]; simp [sub_eq_neg_add])).2
      exact one_ne_zero this
    obtain ⟨g, c1, z0, z1, hg, hz, hs, hs'⟩ :=
      key _ (Psub _ _ (hy 1) (Psmul (y 1 c0 * f) _ (hy 0))) hw
    have e1 : x0.1 c0 = 1 := by rw [hx, hf, hone]
    have e2 : z0.1 c0 = 0 := by
      rw [hz]
      simp [mul_assoc, hf]
    have e3 : z0.1 c1 = 1 := by rw [hz, hg, hone]
    refine H ![x0, z0] ![x1, z1] (fun j => by fin_cases j <;> simp [ht, ht', hs, hs']) ?_
    rw [LinearIndependent.pair_iff]
    intro s r h
    have a0 := congrArg (fun v : V => v.1 c0) h
    have a1 := congrArg (fun v : V => v.1 c1) h
    simp [e1, e2] at a0
    simp [a0, e3] at a1
    exact ⟨a0, a1⟩

theorem laurent_vector_normalise (k : Type) [Field k] (a : ℕ) (y : Fin a → HahnSeries ℤ k)
    (hy : y ≠ 0) : ∃ (f : HahnSeries ℤ k) (c0 : Fin a), f * y c0 = 1 ∧
      ∀ c, (f * y c).coeff (-1) = 0 := by
  classical
  have hne : (Finset.univ.filter fun c => y c ≠ 0).Nonempty := by
    obtain ⟨c, hc⟩ := Function.ne_iff.1 hy
    exact ⟨c, by simpa using hc⟩
  obtain ⟨c0, hc0, hmin⟩ := Finset.exists_min_image _ (fun c => (y c).order) hne
  have h0 : y c0 ≠ 0 := by simpa using hc0
  refine ⟨(y c0)⁻¹, c0, inv_mul_cancel₀ h0, fun c => ?_⟩
  by_cases hc : y c = 0
  · simp [hc]
  · have h1 := hmin c (by simpa using hc)
    have h2 := HahnSeries.order_mul (inv_ne_zero h0) h0
    rw [inv_mul_cancel₀ h0, HahnSeries.order_one] at h2
    apply HahnSeries.coeff_eq_zero_of_lt_order
    rw [HahnSeries.order_mul (inv_ne_zero h0) hc]
    omega

noncomputable def laurentCoeffForm (k : Type) [Field k] (n : ℤ) :
    letI : Algebra k (HahnSeries ℤ k) := HahnSeries.instAlgebra
    HahnSeries ℤ k →ₗ[k] k :=
  HahnSeries.coeff.linearMap n

theorem laurent_degeneration : ∀ (k : Type) [Field k], ∃ (K : Type) (_ : Field K) (_ : Algebra k K) (σ : K), ∀ (a e : ℕ) (V : Submodule k (Fin a → k)) (U : Type) [AddCommGroup U] [Module k U] (t u : V →ₗ[k] U), e ≤ 1 → (∀ x0 x1 : Fin (e + 1) → V, (∀ j, t (x0 j) = 0 ∧ t (x1 j) = u (x0 j)) → ¬ LinearIndependent k x0) → ∀ y : Fin (e + 1) → Fin a → K, (∀ j (π : K →ₗ[k] k), ∃ x x' : V, (∀ c, x.1 c = π (y j c)) ∧ (∀ c, x'.1 c = π (σ * y j c)) ∧ t x = u x') → ¬ LinearIndependent K y := by
  intro k _
  letI : Algebra k (HahnSeries ℤ k) := HahnSeries.instAlgebra
  refine ⟨HahnSeries ℤ k, inferInstance, this, HahnSeries.single 1 1, ?_⟩
  intro a e V U _ _ t u
  have hs : ∀ (z : HahnSeries ℤ k) (n : ℤ),
      (HahnSeries.single (1 : ℤ) (1 : k) * z).coeff (n + 1) = z.coeff n := by
    intro z n
    rw [HahnSeries.coeff_single_mul_add, one_mul]
  refine laurent_degeneration_abstract k (HahnSeries ℤ k) (HahnSeries.single 1 1)
    (fun z => z.coeff (-1) = 0) (laurentCoeffForm k 0) (laurentCoeffForm k 1) ?_ ?_ ?_
    (laurent_vector_normalise k) a e V U t u
  · intro z hz
    exact (hs z (-1)).trans hz
  · intro z
    exact hs z 0
  · show (1 : HahnSeries ℤ k).coeff 0 = 1
    simp

end GlobalTheory
end

