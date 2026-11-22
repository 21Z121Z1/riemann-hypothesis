import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPosSmulEqOfLinearIndependentCone
section
open Finset

namespace GlobalTheory

theorem exists_pos_smul_eq_of_linearIndependent_cone {L : Type} [AddCommGroup L] {m m' : ℕ}
    (δ : Fin m → L) (γ : Fin m' → L) (i : Fin m) (k : ℕ)
    (a : Fin m' → ℕ) (hδ : LinearIndependent ℤ δ) (hk : 0 < k) (hsum : k • δ i = ∑ j, a j • γ j)
    (hγ : ∀ j, 0 < a j → ∃ (k' : ℕ) (b : Fin m → ℕ), 0 < k' ∧ k' • γ j = ∑ l, b l • δ l) :
    ∃ (j : Fin m') (p r : ℕ), 0 < p ∧ 0 < r ∧ p • δ i = r • γ j := by
  classical
  have hγ' : ∀ j, ∃ (k' : ℕ) (b : Fin m → ℕ), 0 < k' ∧ (0 < a j → k' • γ j = ∑ l, b l • δ l) := by
    intro j
    by_cases hj : 0 < a j
    · obtain ⟨k', b, hk', h⟩ := hγ j hj
      exact ⟨k', b, hk', fun _ => h⟩
    · exact ⟨1, 0, one_pos, fun h => absurd h hj⟩
  choose kk b hkk hb using hγ'
  let c : Fin m' → ℕ := fun j => ∏ j' ∈ univ.erase j, kk j'
  let K : ℕ := ∏ j, kk j
  have hcK : ∀ j, c j * kk j = K := fun j => by
    rw [mul_comm]; exact Finset.mul_prod_erase _ _ (mem_univ j)
  have hcpos : ∀ j, 0 < c j := fun j => Finset.prod_pos (fun j' _ => hkk j')
  have hKpos : 0 < K := Finset.prod_pos (fun j _ => hkk j)
  have hterm : ∀ j, (K * a j) • γ j = (a j * c j) • ∑ l, b j l • δ l := by
    intro j
    by_cases hj : 0 < a j
    · rw [← hb j hj, smul_smul, ← hcK j]; congr 1; ring
    · have : a j = 0 := Nat.eq_zero_of_not_pos hj
      simp [this]
  have key : (K * k) • δ i = ∑ l, (∑ j, a j * c j * b j l) • δ l := by
    calc (K * k) • δ i = K • (k • δ i) := mul_smul _ _ _
      _ = ∑ j, (K * a j) • γ j := by rw [hsum, Finset.smul_sum]; simp_rw [smul_smul]
      _ = ∑ j, (a j * c j) • ∑ l, b j l • δ l := Finset.sum_congr rfl (fun j _ => hterm j)
      _ = ∑ l, (∑ j, a j * c j * b j l) • δ l := by
          simp_rw [Finset.smul_sum, smul_smul, Finset.sum_smul]
          rw [Finset.sum_comm]
  let N : Fin m → ℕ := fun l => ∑ j, a j * c j * b j l
  let g : Fin m → ℤ := fun l => (N l : ℤ) - (if l = i then ((K * k : ℕ) : ℤ) else 0)
  have hg : ∑ l, g l • δ l = 0 := by
    simp only [g, sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_eq',
      mem_univ, if_true, natCast_zsmul]
    rw [key]; exact sub_self _
  have hg0 := Fintype.linearIndependent_iff.mp hδ g hg
  have hN : ∀ l, N l = if l = i then K * k else 0 := by
    intro l
    have := hg0 l
    simp only [g] at this
    split_ifs at this ⊢ <;> omega
  have hNi : N i ≠ 0 := by rw [hN i, if_pos rfl]; exact (Nat.mul_pos hKpos hk).ne'
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hNi
  have haj : 0 < a j := Nat.pos_of_ne_zero (fun h => hj (by simp [h]))
  have hbji : 0 < b j i := Nat.pos_of_ne_zero (fun h => hj (by simp [h]))
  have hbjl : ∀ l, l ≠ i → b j l = 0 := by
    intro l hl
    have h0 : N l = 0 := by rw [hN l, if_neg hl]
    have := (Finset.sum_eq_zero_iff.mp h0) j (mem_univ j)
    rcases Nat.mul_eq_zero.mp this with h | h
    · rcases Nat.mul_eq_zero.mp h with h | h
      · omega
      · exact absurd h (hcpos j).ne'
    · exact h
  have hγj : kk j • γ j = b j i • δ i := by
    rw [hb j haj, Finset.sum_eq_single i]
    · intro l _ hl; rw [hbjl l hl, zero_smul]
    · intro h; exact absurd (mem_univ i) h
  exact ⟨j, b j i, kk j, hbji, hkk j, hγj.symm⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeDvdNatCastMem
section
namespace GlobalTheory.PrimeDvdNatCastMem

theorem exists_prime_dvd_natCast_mem {O : Type} [CommRing O] (P : Ideal O) [hP : Ideal.IsPrime P]
    (m : ℕ) : m ≠ (0 : ℕ) → (↑m : O) ∈ P → ∃ (p : ℕ), Nat.Prime p ∧ p ∣ m ∧ (↑p : O) ∈ P := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm0 hm
    by_cases h1 : m = 1
    · subst h1
      exact absurd ((Ideal.eq_top_iff_one P).2 (by simpa using hm)) hP.ne_top
    · obtain ⟨q, hq, k, hk⟩ := Nat.exists_prime_and_dvd h1
      have hk0 : k ≠ 0 := by
        rintro rfl
        exact hm0 (by simpa using hk)
      have hmul : (q : O) * (k : O) ∈ P := by
        have := hm
        rw [hk, Nat.cast_mul] at this
        exact this
      rcases hP.mem_or_mem hmul with h | h
      · exact ⟨q, hq, ⟨k, hk⟩, h⟩
      · have hlt : k < m := by
          have h2 := hq.two_le
          have h3 : 0 < k := Nat.pos_of_ne_zero hk0
          rw [hk]
          nlinarith
        obtain ⟨p, hp, hpk, hpP⟩ := ih k hlt hk0 h
        exact ⟨p, hp, hk ▸ Dvd.dvd.mul_left hpk q, hpP⟩

end GlobalTheory.PrimeDvdNatCastMem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeMemHeightOneSpectrum
section
namespace GlobalTheory.PrimeInHeightOneSpectrum

theorem exists_prime_natCast_mem {R : Type} [CommRing R] (P : Ideal R) [hP : P.IsPrime] :
    ∀ n : ℕ, n ≠ 0 → (n : R) ∈ P → ∃ p : ℕ, Nat.Prime p ∧ (p : R) ∈ P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hmem
    have h1 : n ≠ 1 := by
      rintro rfl
      exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr (by simpa using hmem))
    have hpr : Nat.Prime n.minFac := Nat.minFac_prime h1
    obtain ⟨m, hm⟩ := Nat.minFac_dvd n
    have hmul : ((n.minFac : R) * (m : R)) ∈ P := by
      rw [← Nat.cast_mul, ← hm]; exact hmem
    rcases hP.mem_or_mem hmul with h | h
    · exact ⟨_, hpr, h⟩
    · have hm0 : m ≠ 0 := by rintro rfl; simp at hm; exact hn hm
      have hlt : m < n := by
        rw [hm]
        have := hpr.two_le
        calc m = 1 * m := (one_mul m).symm
          _ < n.minFac * m := Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pos_of_ne_zero hm0)
      exact ih m hlt hm0 h

theorem exists_prime_mem_heightOneSpectrum {K : Type} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ (p : ℕ), Nat.Prime p ∧ (↑p : NumberField.RingOfIntegers K) ∈
      IsDedekindDomain.HeightOneSpectrum.asIdeal v := by
  haveI := v.isPrime
  exact exists_prime_natCast_mem v.asIdeal (Ideal.absNorm v.asIdeal)
    (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot) (Ideal.absNorm_mem _)

theorem target : ∀ {K : Type} [inst : Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
    ∃ (p : ℕ), Nat.Prime p ∧ (↑p : NumberField.RingOfIntegers K) ∈
      IsDedekindDomain.HeightOneSpectrum.asIdeal v :=
  fun v => exists_prime_mem_heightOneSpectrum v

end GlobalTheory.PrimeInHeightOneSpectrum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimitiveElementComplete
section
open IsLocalRing Polynomial

namespace GlobalTheory

theorem residue_eval_map_eq_aeval {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R]
    [IsLocalRing R] (φ : A →+* R) [IsLocalHom φ] (P : A[X]) (x : R) :
    letI := (ResidueField.map φ).toAlgebra
    residue R ((P.map φ).eval x) = aeval (residue R x) (P.map (residue A)) := by
  letI := (ResidueField.map φ).toAlgebra
  rw [aeval_def, eval₂_map, eval_map, hom_eval₂]
  congr 1

theorem exists_hensel_generator_of_residue_finite : ∀ {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] (φ : A →+* R) [IsLocalHom φ], (ResidueField.map φ).Finite → CharZero (ResidueField A) → ∃ (θ : R) (q : Polynomial A), q.Monic ∧ (q.map φ).eval θ = 0 ∧ IsUnit ((q.derivative.map φ).eval θ) ∧ (∀ r : R, ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R) ∧ ∀ P : Polynomial A, P.natDegree < q.natDegree → (P.map φ).eval θ ∈ maximalIdeal R → ∀ i, P.coeff i ∈ maximalIdeal A := by
  intro A R _ _ _ _ _ φ _ hfin hchar
  letI := (ResidueField.map φ).toAlgebra
  haveI : FiniteDimensional (ResidueField A) (ResidueField R) := hfin
  haveI : Algebra.IsSeparable (ResidueField A) (ResidueField R) := inferInstance
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (ResidueField A) (ResidueField R)
  have hint : IsIntegral (ResidueField A) α := Algebra.IsIntegral.isIntegral α
  set p := minpoly (ResidueField A) α with hp
  have hpm : p.Monic := minpoly.monic hint
  have hlift : p ∈ lifts (residue A) :=
    (lifts_iff_coeff_lifts p).2 fun n => residue_surjective (p.coeff n)
  obtain ⟨q, hqmap, hqdeg, hqm⟩ := lifts_and_degree_eq_and_monic hlift hpm
  have hqnat : q.natDegree = p.natDegree := natDegree_eq_of_degree_eq hqdeg
  obtain ⟨θ₀, hθ₀⟩ := residue_surjective (R := R) α
  have hmon : (q.map φ).Monic := hqm.map φ
  have h1 : (q.map φ).eval θ₀ ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff, residue_eval_map_eq_aeval, hqmap, hθ₀]
    exact minpoly.aeval _ _
  have hder : ∀ x : R, residue R x = α → IsUnit ((q.derivative.map φ).eval x) := by
    intro x hx
    rw [← residue_ne_zero_iff_isUnit, residue_eval_map_eq_aeval, ← derivative_map, hqmap, hx]
    have hsep : (minpoly (ResidueField A) α).Separable :=
      Algebra.IsSeparable.isSeparable (ResidueField A) α
    exact hsep.aeval_derivative_ne_zero (minpoly.aeval _ _)
  have h2 : IsUnit ((q.map φ).derivative.eval θ₀) := by
    rw [derivative_map]; exact hder θ₀ hθ₀
  obtain ⟨θ, hroot, hθθ₀⟩ :=
    (IsAdicComplete.henselianRing R (maximalIdeal R)).is_henselian _ hmon θ₀ h1 (h2.map _)
  have hθ : residue R θ = α := by
    rw [← hθ₀, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact hθθ₀
  refine ⟨θ, q, hqm, hroot, hder θ hθ, ?_, ?_⟩
  · intro r
    have hr : residue R r ∈ Algebra.adjoin (ResidueField A) {α} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
        IntermediateField.mem_toSubalgebra, hα]
      exact IntermediateField.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hr
    obtain ⟨pb, hpb⟩ := hr
    obtain ⟨P, hP⟩ := map_surjective (residue A) residue_surjective pb
    refine ⟨P, ?_⟩
    rw [← residue_eq_zero_iff, map_sub, residue_eval_map_eq_aeval, hP, hθ, sub_eq_zero]
    exact hpb.symm
  · intro P hdeg hmem i
    rw [← residue_eq_zero_iff, residue_eval_map_eq_aeval, hθ] at hmem
    have hz : P.map (residue A) = 0 := by
      by_contra hne
      have := minpoly.degree_le_of_ne_zero (ResidueField A) α hne hmem
      have h3 := natDegree_le_natDegree this
      have h4 : (P.map (residue A)).natDegree ≤ P.natDegree := natDegree_map_le
      rw [← hp] at h3
      omega
    rw [← residue_eq_zero_iff, ← coeff_map, hz, coeff_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimitiveElementUnramified
section
open IsLocalRing Polynomial

namespace GlobalTheory

open IsLocalRing Polynomial in
private lemma residue_eval_map_eq {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R]
    [IsLocalRing R] (φ : A →+* R) [IsLocalHom φ] (P : A[X]) (x : R) :
    residue R ((P.map φ).eval x) =
      (P.map (residue A)).eval₂ (ResidueField.map φ) (residue R x) := by
  rw [eval_map, hom_eval₂, eval₂_map]
  congr 1

open IsLocalRing Polynomial in

theorem _root_.GlobalTheory.exists_hensel_generator_of_residue_finite_unramified : ∀ {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] (φ : A →+* R) [IsLocalHom φ], ((residue R).comp φ).Finite → ((residue R).comp φ).FormallyUnramified → ∃ (θ : R) (q : Polynomial A), q.Monic ∧ (q.map φ).eval θ = 0 ∧ IsUnit ((q.derivative.map φ).eval θ) ∧ (∀ r : R, ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R) ∧ ∀ P : Polynomial A, P.natDegree < q.natDegree → (P.map φ).eval θ ∈ maximalIdeal R → ∀ i, P.coeff i ∈ maximalIdeal A := by
  intro A R _ _ _ _ _ φ _ hfin hunr
  have hcomp : (residue R).comp φ = (ResidueField.map φ).comp (residue A) :=
    RingHom.ext fun a => (ResidueField.map_residue φ a).symm
  rw [hcomp] at hfin hunr
  letI : Algebra (ResidueField A) (ResidueField R) := (ResidueField.map φ).toAlgebra
  haveI : Module.Finite (ResidueField A) (ResidueField R) := hfin.of_comp_finite
  haveI : Algebra.FormallyUnramified (ResidueField A) (ResidueField R) := hunr.of_comp
  haveI : Algebra.IsSeparable (ResidueField A) (ResidueField R) :=
    Algebra.FormallyUnramified.isSeparable _ _
  set pb := Field.powerBasisOfFiniteOfSeparable (ResidueField A) (ResidueField R)
  set f := minpoly (ResidueField A) pb.gen with hf
  have hfmonic : f.Monic := minpoly.monic pb.isIntegral_gen
  have hfroot : aeval pb.gen f = 0 := minpoly.aeval _ _
  have hfder : aeval pb.gen (derivative f) ≠ 0 :=
    (Algebra.IsSeparable.isSeparable _ pb.gen).aeval_derivative_ne_zero hfroot
  obtain ⟨q, hqf, hqdeg, hqmonic⟩ := lifts_and_natDegree_eq_and_monic
    ((mem_lifts f).2 (map_surjective (residue A) residue_surjective f)) hfmonic
  obtain ⟨θ₀, hθ₀⟩ := residue_surjective pb.gen
  have key : ∀ (P : A[X]) (x : R), residue R x = pb.gen →
      residue R ((P.map φ).eval x) = aeval pb.gen (P.map (residue A)) := by
    intro P x hx
    rw [residue_eval_map_eq, hx]
    rfl
  obtain ⟨θ, hroot, hθ⟩ := HenselianRing.is_henselian (I := maximalIdeal R) (q.map φ)
    (hqmonic.map φ) θ₀
    (by rw [← residue_eq_zero_iff, key _ _ hθ₀, hqf, hfroot])
    (by
      rw [derivative_map]
      change IsUnit (residue R _)
      rw [key _ _ hθ₀, ← derivative_map, hqf]
      exact isUnit_iff_ne_zero.2 hfder)
  have hθres : residue R θ = pb.gen := by
    rw [← hθ₀, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hθ
  refine ⟨θ, q, hqmonic, hroot, ?_, ?_, ?_⟩
  · rw [← residue_ne_zero_iff_isUnit, key _ _ hθres, ← derivative_map, hqf]
    exact hfder
  · intro r
    obtain ⟨g, hg⟩ := pb.exists_eq_aeval' (residue R r)
    obtain ⟨P, hP⟩ := map_surjective (residue A) residue_surjective g
    refine ⟨P, ?_⟩
    rw [← residue_eq_zero_iff, map_sub, key _ _ hθres, hP, hg, sub_self]
  · intro P hdeg hmem i
    rw [← residue_eq_zero_iff, key _ _ hθres] at hmem
    have hzero : P.map (residue A) = 0 := by
      by_contra hne
      have h1 := minpoly.degree_le_of_ne_zero (ResidueField A) pb.gen hne hmem
      have h2 := natDegree_le_natDegree h1
      have h3 : (P.map (residue A)).natDegree ≤ P.natDegree := natDegree_map_le
      rw [← hf, ← hqdeg] at h2
      omega
    rw [← residue_eq_zero_iff, ← coeff_map, hzero, coeff_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRatAddMulOfMemAdjoin
section
namespace GlobalTheory.RatCoordsAdjoin

theorem exists_rat_add_mul_of_mem_adjoin {E : Type} [Field E] [NumberField E] (d : ℕ) (s : E)
    (hs : s ^ 2 = -(d : E)) {x : E} (hx : x ∈ IntermediateField.adjoin ℚ ({s} : Set E)) :
    ∃ a b : ℚ, x = (a : E) + (b : E) * s := by
  have halg : IsAlgebraic ℚ s := Algebra.IsAlgebraic.isAlgebraic s
  have hx' : x ∈ Algebra.adjoin ℚ ({s} : Set E) := by
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (F := ℚ) (S := ({s} : Set E))
      (by intro y hy; rw [Set.mem_singleton_iff.mp hy]; exact halg)]
    exact hx
  clear hx
  induction hx' using Algebra.adjoin_induction with
  | mem y hy => exact ⟨0, 1, by rw [Set.mem_singleton_iff.mp hy]; simp⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨c, e, rfl⟩ := hz
    exact ⟨a + c, b + e, by push_cast; ring⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨c, e, rfl⟩ := hz
    exact ⟨a * c - b * e * d, a * e + b * c, by
      push_cast; linear_combination ((b : E) * (e : E)) * hs⟩

end GlobalTheory.RatCoordsAdjoin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRootNormSubPowLe
section
universe u_1

namespace GlobalTheory.RootNormPowerBound

open Polynomial

theorem pow_card_le_norm_eval_prod {K : Type u_1} [NormedField K] (x : K) (c : ℝ) (hc : 0 ≤ c)
    (s : Multiset K) (hs : ∀ a ∈ s, c ≤ ‖a - x‖) :
    c ^ Multiset.card s ≤ ‖Polynomial.eval x (s.map fun a => X - C a).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.card_cons, pow_succ, Multiset.map_cons, Multiset.prod_cons, eval_mul, norm_mul, mul_comm]
    have ha : c ≤ ‖eval x (X - C a)‖ := by
      rw [eval_sub, eval_X, eval_C, norm_sub_rev]
      exact hs a (Multiset.mem_cons_self a s)
    exact mul_le_mul ha (ih fun t ht => hs t (Multiset.mem_cons_of_mem ht)) (pow_nonneg hc _)
      (norm_nonneg _)

theorem exists_root_norm_sub_pow_le {K : Type u_1} [inst : NormedField K] [IsAlgClosed K]
    (p : Polynomial K) (hp : (0 : ℕ) < Polynomial.natDegree p) (x : K) :
    ∃ b ∈ Polynomial.roots p,
      ‖Polynomial.leadingCoeff p‖ * ‖b - x‖ ^ Polynomial.natDegree p ≤ ‖Polynomial.eval x p‖ := by
  have hsp : p.Splits := IsAlgClosed.splits p
  have hcard := hsp.natDegree_eq_card_roots
  have hne : p.roots ≠ 0 := by
    intro h
    rw [h, Multiset.card_zero] at hcard
    omega
  obtain ⟨b, hb, hmin⟩ := Multiset.exists_min_image (fun a => ‖a - x‖) hne
  refine ⟨b, hb, ?_⟩
  conv_rhs => rw [hsp.eq_prod_roots]
  rw [eval_mul, eval_C, norm_mul, hcard]
  exact mul_le_mul_of_nonneg_left (pow_card_le_norm_eval_prod x _ (norm_nonneg _) _ hmin) (norm_nonneg _)

end GlobalTheory.RootNormPowerBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSaturated
section
universe u_1

namespace GlobalTheory.SaturatedNotDvd

theorem exists_saturated {A : Type u_1} [CommRing A] [IsDomain A] {x a b : A} (hx : Prime x)
    (hb : ¬ x ∣ b) {I : Ideal A} (hI : I ≠ ⊥) (h : ∀ r ∈ I, ∃ s ∈ I, a * r = b * s) :
    ∃ K : Ideal A, K ≠ ⊥ ∧ (∀ u, x * u ∈ K → u ∈ K) ∧ ∀ r ∈ K, ∃ s ∈ K, a * r = b * s := by
  let K : Ideal A :=
    { carrier := {u | ∃ k : ℕ, x ^ k * u ∈ I}
      add_mem' := by
        rintro u v ⟨k, hk⟩ ⟨l, hl⟩
        refine ⟨k + l, ?_⟩
        have e : x ^ (k + l) * (u + v) = x ^ l * (x ^ k * u) + x ^ k * (x ^ l * v) := by ring
        rw [e]
        exact I.add_mem (I.mul_mem_left _ hk) (I.mul_mem_left _ hl)
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c u ⟨k, hk⟩
        refine ⟨k, ?_⟩
        have e : x ^ k * (c • u) = c * (x ^ k * u) := by rw [smul_eq_mul]; ring
        rw [e]
        exact I.mul_mem_left _ hk }
  refine ⟨K, ?_, ?_, ?_⟩
  · intro hK
    apply hI
    rw [eq_bot_iff] at hK ⊢
    intro r hr
    exact hK (show ∃ k : ℕ, x ^ k * r ∈ I from ⟨0, by simpa using hr⟩)
  · rintro u ⟨k, hk⟩
    exact ⟨k + 1, by rw [pow_succ, mul_assoc]; exact hk⟩
  · rintro r ⟨k, hk⟩
    obtain ⟨s, hs, hrs⟩ := h _ hk
    have hdvd : x ^ k ∣ b * s := ⟨a * r, by rw [← hrs]; ring⟩
    obtain ⟨s', hs'⟩ := hx.pow_dvd_of_dvd_mul_left k hb hdvd
    refine ⟨s', ⟨k, by rw [← hs']; exact hs⟩, ?_⟩
    have hxk : x ^ k ≠ 0 := pow_ne_zero _ hx.ne_zero
    apply mul_left_cancel₀ hxk
    calc x ^ k * (a * r) = a * (x ^ k * r) := by ring
      _ = b * s := hrs
      _ = b * (x ^ k * s') := by rw [hs']
      _ = x ^ k * (b * s') := by ring

theorem exists_not_dvd {A : Type u_1} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] {x : A}
    (hx : ¬ IsUnit x) {K : Ideal A} (hK : K ≠ ⊥) (hs : ∀ u, x * u ∈ K → u ∈ K) :
    ∃ u ∈ K, ¬ x ∣ u := by
  by_contra hall
  push_neg at hall
  apply hK
  apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {x}) K (IsNoetherian.noetherian K)
  · intro u hu
    obtain ⟨u', rfl⟩ := hall u hu
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self x) (hs u' hu)
  · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact (Ideal.span_singleton_le_iff_mem _).2 ((IsLocalRing.mem_maximalIdeal x).2 hx)

theorem main : (let d1 : (A : Type u_1) → [CommRing A] → Prop := @(fun (A : Type u_1) [CommRing A] ↦ ∀ (a b : A) (I : Ideal A), b ≠ (0 : A) → I ≠ ⊥ → (∀ r ∈ I, ∃ s ∈ I, a * r = b * s) → b ∣ a); ∀ {A : Type u_1} [inst : CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] {x : A}, Prime x → d1 (A ⧸ Ideal.span {x}) → ∀ {a b : A}, ¬x ∣ b → ∀ {I : Ideal A}, I ≠ ⊥ → (∀ r ∈ I, ∃ s ∈ I, a * r = b * s) → b ∣ a) := by
  intro d1 A _ _ _ _ x hx hd a b hb I hI h
  have hd' : ∀ (a b : A ⧸ Ideal.span {x}) (I : Ideal (A ⧸ Ideal.span {x})), b ≠ 0 → I ≠ ⊥ →
      (∀ r ∈ I, ∃ s ∈ I, a * r = b * s) → b ∣ a := hd
  obtain ⟨K, hK, hsat, hKa⟩ := exists_saturated hx hb hI h
  obtain ⟨u₀, hu₀, hxu⟩ := exists_not_dvd hx.not_unit hK hsat
  have hz : ∀ y : A, Ideal.Quotient.mk (Ideal.span {x}) y = 0 ↔ x ∣ y := fun y => by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have step : ∀ a : A, (∀ r ∈ K, ∃ s ∈ K, a * r = b * s) →
      ∃ c d : A, a = b * c + x * d ∧ ∀ r ∈ K, ∃ s ∈ K, d * r = b * s := by
    intro a ha
    have hdiv : Ideal.Quotient.mk (Ideal.span {x}) b ∣ Ideal.Quotient.mk (Ideal.span {x}) a := by
      refine hd' _ _ (K.map (Ideal.Quotient.mk (Ideal.span {x}))) (fun h0 => hb ((hz b).1 h0)) ?_ ?_
      · intro hbot
        have hm := Ideal.mem_map_of_mem (Ideal.Quotient.mk (Ideal.span {x})) hu₀
        rw [hbot, Ideal.mem_bot] at hm
        exact hxu ((hz _).1 hm)
      · intro r hr
        obtain ⟨r', hr', rfl⟩ :=
          (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hr
        obtain ⟨s, hs, hrs⟩ := ha r' hr'
        exact ⟨_, Ideal.mem_map_of_mem _ hs, by rw [← map_mul, ← map_mul, hrs]⟩
    obtain ⟨c', hc'⟩ := hdiv
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c'
    have hxd : x ∣ a - b * c := (hz _).1 (by rw [map_sub, map_mul, hc', sub_self])
    obtain ⟨d, hdd⟩ := hxd
    refine ⟨c, d, by linear_combination hdd, ?_⟩
    intro r hr
    obtain ⟨s, hs, hrs⟩ := ha r hr
    have h1 : b * (s - c * r) = x * (d * r) := by linear_combination r * hdd - hrs
    have h2 : x ∣ s - c * r := (hx.dvd_or_dvd ⟨_, h1⟩).resolve_left hb
    obtain ⟨w, hw⟩ := h2
    have hwK : w ∈ K := hsat w (hw ▸ K.sub_mem hs (K.mul_mem_left c hr))
    refine ⟨w, hwK, ?_⟩
    apply mul_left_cancel₀ hx.ne_zero
    rw [← h1, hw]; ring
  have iter : ∀ n : ℕ, ∀ a : A, (∀ r ∈ K, ∃ s ∈ K, a * r = b * s) →
      ∃ c y : A, a = b * c + x ^ n * y := by
    intro n
    induction n with
    | zero => intro a _; exact ⟨0, a, by simp⟩
    | succ n ih =>
      intro a ha
      obtain ⟨c, d, rfl, hd2⟩ := step a ha
      obtain ⟨c', y, rfl⟩ := ih d hd2
      exact ⟨c + x * c', y, by ring⟩
  have hne : Ideal.span {x} ≠ ⊤ := fun h => hx.not_unit (Ideal.span_singleton_eq_top.1 h)
  have hk := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := A ⧸ Ideal.span {b})
    (Ideal.span {x}) hne
  have hmem : Ideal.Quotient.mk (Ideal.span {b}) a ∈
      (⨅ i : ℕ, Ideal.span {x} ^ i • ⊤ : Submodule A (A ⧸ Ideal.span {b})) := by
    rw [Submodule.mem_iInf]
    intro n
    obtain ⟨c, y, hcy⟩ := iter n a hKa
    have : Ideal.Quotient.mk (Ideal.span {b}) a
        = x ^ n • Ideal.Quotient.mk (Ideal.span {b}) y := by
      change _ = Ideal.Quotient.mk (Ideal.span {b}) (x ^ n * y)
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
      exact ⟨c, by rw [hcy]; ring⟩
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self x) n)
      Submodule.mem_top
  rw [hk, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hmem
  exact hmem

end GlobalTheory.SaturatedNotDvd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCastNotMemOfPrimeNe
section
namespace GlobalTheory.NatCastNotMemPrime

theorem natCast_notMem_of_prime_ne {A : Type} [inst : CommRing A] (P : Ideal A)
    [hP : Ideal.IsPrime P] {p l : ℕ} (hp : Nat.Prime p) (hl : Nat.Prime l) (hne : l ≠ p)
    (hpP : (↑p : A) ∈ P) : (↑l : A) ∉ P := by
  intro hlP
  have hcop : Nat.Coprime l p := (Nat.coprime_primes hl hp).2 hne
  have hc : IsCoprime (l : A) (p : A) := Nat.Coprime.cast hcop
  obtain ⟨a, b, hab⟩ := hc
  apply hP.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact P.add_mem (P.mul_mem_left a hlP) (P.mul_mem_left b hpP)

end GlobalTheory.NatCastNotMemPrime
end

