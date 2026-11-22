import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.QaWeightRowInd
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.SubYGenCoefHom
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.MemInvariantSectionsIffIntegral

-- bundled from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.BlockSubstitutionBlockEmb
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

section LC

variable {K σ ρ : Type} [Field K]

private theorem coeff_lcoef_eq (L : MvPolynomial ρ K →ₗ[K] K) (f : MvPolynomial σ (MvPolynomial ρ K))
    (w : σ →₀ ℕ) : coeff w (lcoef L f) = L (coeff w f) :=
  coeff_sum_monomial_linear L f w

theorem qa_lcoef_monomial (L : MvPolynomial ρ K →ₗ[K] K) (u : σ →₀ ℕ) (b : MvPolynomial ρ K) :
    lcoef L (monomial u b) = monomial u (L b) := by
  classical
  ext w
  rw [coeff_lcoef_eq, coeff_monomial, coeff_monomial]
  split_ifs <;> simp

theorem qa_lcoef_C (L : MvPolynomial ρ K →ₗ[K] K) (b : MvPolynomial ρ K) :
    lcoef L (C b : MvPolynomial σ (MvPolynomial ρ K)) = C (L b) := by
  classical
  ext w
  rw [coeff_lcoef_eq, coeff_C, coeff_C]
  split_ifs <;> simp

theorem qa_lcoef_mapC_mul (L : MvPolynomial ρ K →ₗ[K] K) (G : MvPolynomial σ K)
    (h : MvPolynomial σ (MvPolynomial ρ K)) : lcoef L (map C G * h) = G * lcoef L h := by
  classical
  ext w
  rw [coeff_lcoef_eq, coeff_mul, coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [coeff_map, coeff_lcoef_eq, MvPolynomial.C_mul', map_smul, smul_eq_mul]

theorem qa_eval_lcoef (L : MvPolynomial ρ K →ₗ[K] K) (x : σ → K) (h : MvPolynomial σ (MvPolynomial ρ K)) :
    eval x (lcoef L h) = L (eval (fun i => C (x i)) h) := by
  classical
  rw [show lcoef L h = ∑ u ∈ h.support, monomial u (L (coeff u h)) from rfl, map_sum]
  conv_rhs => rw [h.as_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [eval_monomial, eval_monomial]
  rw [show (u.prod fun n e => (C (x n) : MvPolynomial ρ K) ^ e) = C (u.prod fun n e => x n ^ e) by
    simp [Finsupp.prod, map_prod, map_pow]]
  rw [mul_comm (coeff u h), MvPolynomial.C_mul', map_smul, smul_eq_mul, mul_comm]

theorem qa_lcoef_rowAct {k n : ℕ} (L : MvPolynomial ρ K →ₗ[K] K) (g : Matrix (Fin k) (Fin k) K)
    (h : MvPolynomial (Fin k × Fin n) (MvPolynomial ρ K)) :
    lcoef L (rowAct (MvPolynomial ρ K) (g.map C) h) = rowAct K g (lcoef L h) := by
  classical
  have key : ∀ P : MvPolynomial (Fin k × Fin n) K,
      rowAct (MvPolynomial ρ K) (g.map C) (map C P) = map C (rowAct K g P) := by
    intro P
    have e := MvPolynomial.ringHom_ext
      (f := ((rowAct (MvPolynomial ρ K) (n := n) (g.map C)).toRingHom.comp (map C) :
        MvPolynomial (Fin k × Fin n) K →+* MvPolynomial (Fin k × Fin n) (MvPolynomial ρ K)))
      (g := ((map C).comp (rowAct K (n := n) g).toRingHom :
        MvPolynomial (Fin k × Fin n) K →+* MvPolynomial (Fin k × Fin n) (MvPolynomial ρ K)))
      (fun a => by simp [rowAct]) (fun i => by simp [rowAct, Matrix.map_apply, map_sum])
    simpa using RingHom.congr_fun e P
  conv_lhs => rw [h.as_sum]
  conv_rhs => rw [h.as_sum]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hm : (monomial u (coeff u h) : MvPolynomial (Fin k × Fin n) (MvPolynomial ρ K)) =
      map C (monomial u 1) * C (coeff u h) := by
    rw [map_monomial, map_one, mul_comm, C_mul_monomial, mul_one]
  have hr1 : rowAct (MvPolynomial ρ K) (n := n) (g.map C) (C (coeff u h)) = C (coeff u h) := by simp [rowAct]
  have hr2 : rowAct K (n := n) g (C (L (coeff u h))) = C (L (coeff u h)) := by simp [rowAct]
  rw [hm, map_mul, key, hr1, qa_lcoef_mapC_mul, qa_lcoef_mapC_mul, qa_lcoef_C, map_mul, hr2]

end LC

section S2

variable {K : Type} [Field K] {r : ℕ}

theorem qa_blockEmb_C {S : Type} {k n : ℕ} (b : S) (a : K) : blockEmb K (k := k) (n := n) b (C a) = C a := by
  simp [blockEmb]

theorem qa_blockEmb_X {S : Type} {k n : ℕ} (b : S) (x : Fin k × Fin n) : blockEmb K b (X x) = X (b, x) := by
  simp [blockEmb]

theorem block_substitution_C (a : K) : sub2 K r (C a) = C (C a) := by
  simp [sub2]

theorem block_substitution_X (b : Bool) (x : Fin (r + 1 + 1) × Fin (r + 1 + 1)) :
    sub2 K r (X (b, x)) = map (blockEmb K (k := r) (n := r) b).toRingHom (subY K r (X x)) := by
  simp [sub2]

theorem block_substitution_blockEmb (b : Bool) (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K) :
    sub2 K r (blockEmb K b v) = map (blockEmb K (k := r) (n := r) b).toRingHom (subY K r v) := by
  induction v using MvPolynomial.induction_on
  next a =>
    rw [qa_blockEmb_C, block_substitution_C]
    simp [subY, qa_blockEmb_C]
  next p q hp hq =>
    rw [map_add, map_add, hp, hq, map_add, map_add]
  next p x hp =>
    rw [map_mul, map_mul, hp, qa_blockEmb_X, block_substitution_X, map_mul, map_mul]

theorem qa_blockEmb_comp_C (b : Bool) :
    ((blockEmb K (k := r) (n := r) b).toRingHom).comp C = (C : K →+* MvPolynomial (Bool × (Fin r × Fin r)) K) := RingHom.ext fun a => by simp [qa_blockEmb_C]

theorem qa_lamOf_apply (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K)
    (x : MvPolynomial (Bool × (Fin (r + 1 + 1) × Fin (r + 1 + 1))) K) : lamOf K r L x = lcoef L (sub2 K r x) := rfl

theorem qa_eval_map_block (b : Bool)
    (h : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) K)) :
    eval (fun i => (C (idPoint K (r + 1 + 1) (r + 1 + 1) i) : MvPolynomial (Bool × (Fin r × Fin r)) K))
        (map (blockEmb K (k := r) (n := r) b).toRingHom h) =
      blockEmb K b (eval (idPoint (MvPolynomial (Fin r × Fin r) K) (r + 1 + 1) (r + 1 + 1)) h) := by
  rw [MvPolynomial.eval_map]
  show _ = (blockEmb K (k := r) (n := r) b).toRingHom
    (MvPolynomial.eval₂ (RingHom.id _) (idPoint (MvPolynomial (Fin r × Fin r) K) (r + 1 + 1) (r + 1 + 1)) h)
  rw [MvPolynomial.eval₂_comp_left, RingHom.comp_id]
  congr 1
  funext i
  simp only [idPoint, Function.comp_apply]
  split_ifs <;> simp

end S2

theorem lamCoeffP : LamCoeffP := by
  classical
  intro K _ r L v t u
  rw [qa_lamOf_apply, map_mul, block_substitution_blockEmb, block_substitution_blockEmb, coeff_lcoef_eq, coeff_mul, map_sum]
  simp only [coeff_map]
  rfl

theorem lamMulP : LamMulP := by
  classical
  intro K _ r Q L F s t hF
  rw [qa_lamOf_apply, map_mul (blockEmb K true) F s, map_mul (sub2 K r), map_mul (sub2 K r),
    block_substitution_blockEmb, block_substitution_blockEmb, block_substitution_blockEmb, hF,
    map_mul (map (blockEmb K (k := r) (n := r) true).toRingHom), map_C, MvPolynomial.map_map,
    qa_blockEmb_comp_C, ← qa_lcoef_mapC_mul]
  congr 1
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  ring

theorem lamEvalP : LamEvalP := by
  classical
  intro K _ r L v t
  rw [qa_lamOf_apply, map_mul, block_substitution_blockEmb, block_substitution_blockEmb, qa_eval_lcoef, map_mul,
    qa_eval_map_block, qa_eval_map_block]
  rfl

theorem lamEquivP : LamEquivP := by
  intro K _ r L g v t
  have hcomm : ∀ (b : Bool) (P : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) K)),
      map (blockEmb K (k := r) (n := r) b).toRingHom
          (rowAct (MvPolynomial (Fin r × Fin r) K) (n := r + 1 + 1) (g.map C) P) =
        rowAct (MvPolynomial (Bool × (Fin r × Fin r)) K) (n := r + 1 + 1) (g.map C)
          (map (blockEmb K (k := r) (n := r) b).toRingHom P) := by
    intro b P
    have e := MvPolynomial.ringHom_ext
      (f := ((map (blockEmb K (k := r) (n := r) b).toRingHom).comp
          (rowAct (MvPolynomial (Fin r × Fin r) K) (n := r + 1 + 1) (g.map C)).toRingHom :
        MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) K) →+*
          MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K)))
      (g := ((rowAct (MvPolynomial (Bool × (Fin r × Fin r)) K) (n := r + 1 + 1) (g.map C)).toRingHom.comp
          (map (blockEmb K (k := r) (n := r) b).toRingHom) :
        MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) K) →+*
          MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K)))
      (fun c => by simp [rowAct]) (fun i => by simp [rowAct, Matrix.map_apply, map_sum, qa_blockEmb_C])
    simpa using RingHom.congr_fun e P
  rw [qa_lamOf_apply, qa_lamOf_apply, map_mul (sub2 K r), map_mul (sub2 K r), block_substitution_blockEmb,
    block_substitution_blockEmb, block_substitution_blockEmb, block_substitution_blockEmb, qa_subY_rowAct, qa_subY_rowAct, hcomm, hcomm,
    ← map_mul (rowAct (MvPolynomial (Bool × (Fin r × Fin r)) K) (n := r + 1 + 1) (g.map C)), qa_lcoef_rowAct]

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.BlockSubstitutionEmbedding
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf.QB

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

def th (K : Type) [Field K] (r : ℕ) (b : Bool) :
    MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K →ₐ[K]
      MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K) :=
  (mapAlgHom (blockEmb K (k := r) (n := r) b)).comp (subY K r)

theorem blockEmb_X (K : Type) [Field K] {k n : ℕ} (b : Bool) (x : Fin k × Fin n) :
    blockEmb K b (X x) = (X (b, x) : MvPolynomial (Bool × (Fin k × Fin n)) K) := by
  show rename _ (X x) = _
  rw [rename_X]

theorem th_C (K : Type) [Field K] (r : ℕ) (b : Bool) (a : K) : th K r b (C a) = C (C a) := by
  rw [th, AlgHom.comp_apply, subY_C, mAH_C, algHom_C, algebraMap_eq]

theorem th_X_mid (K : Type) [Field K] (r : ℕ) (b : Bool) (a : Fin (r + 1 + 1)) (j : Fin r) :
    th K r b (X (a, midI r j)) = ∑ i : Fin r, C (X (b, (i, j))) * X (a, midI r i) := by
  rw [th, AlgHom.comp_apply, mAH_subY_mid]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [blockEmb_X]

theorem th_X_none (K : Type) [Field K] (r : ℕ) (b : Bool) (a t : Fin (r + 1 + 1)) (h : midOf t = none) :
    th K r b (X (a, t)) = X (a, t) := by
  rw [th, AlgHom.comp_apply, mAH_subY_none r _ a t h]

theorem th_coeff (K : Type) [Field K] (r : ℕ) (b : Bool) (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)
    (u : Fin (r + 1 + 1) × Fin (r + 1 + 1) →₀ ℕ) :
    coeff u (th K r b v) = blockEmb K b (coeff u (subY K r v)) := by
  rw [th, AlgHom.comp_apply, mAH_coeff]

theorem block_substitution_embedding (K : Type) [Field K] (r : ℕ) (b : Bool) (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K) :
    sub2 K r (blockEmb K b v) = th K r b v := by
  have : (sub2 K r).comp (blockEmb K (k := r + 1 + 1) (n := r + 1 + 1) b) = th K r b := by
    apply algHom_ext
    intro w
    rw [AlgHom.comp_apply, blockEmb_X]
    unfold sub2
    rw [aeval_X]
    rfl
  exact AlgHom.congr_fun this v

theorem lam_eq (K : Type) [Field K] (r : ℕ) (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K)
    (v t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K) :
    lamOf K r L (blockEmb K true v * blockEmb K false t) = lcoef L (th K r true v * th K r false t) := by
  unfold lamOf
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, block_substitution_embedding, block_substitution_embedding]

section Psi

variable {K B σ : Type} [Field K] [CommRing B] [Algebra K B]

def psiB (B : Type) [CommRing B] [Algebra K B] (ψ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K) :
    MvPolynomial σ B →+* MvPolynomial σ B :=
  eval₂Hom C (fun w => map (algebraMap K B) (ψ (X w)))

theorem psiB_C (ψ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K) (b : B) : psiB B ψ (C b) = C b := by
  show eval₂ _ _ (C b) = _
  rw [eval₂_C]

theorem psiB_X (ψ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K) (w : σ) :
    psiB B ψ (X w) = map (algebraMap K B) (ψ (X w)) := by
  show eval₂ _ _ (X w) = _
  rw [eval₂_X]

theorem psiB_map (ψ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K) (G : MvPolynomial σ K) :
    psiB B ψ (map (algebraMap K B) G) = map (algebraMap K B) (ψ G) := by
  have : (psiB B ψ).comp (map (algebraMap K B)) = (map (algebraMap K B)).comp (ψ : MvPolynomial σ K →+* MvPolynomial σ K) := by
    apply ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, RingHom.coe_coe, map_C, psiB_C, algHom_C, algebraMap_eq]
    · intro w
      simp only [RingHom.comp_apply, RingHom.coe_coe, map_X, psiB_X]
  exact RingHom.congr_fun this G

theorem lcoef_C_mul_map (L : B →ₗ[K] K) (b : B) (G : MvPolynomial σ K) :
    lcoef L (C b * map (algebraMap K B) G) = L b • G := by
  ext u
  rw [coeff_lcoef, coeff_C_mul, coeff_map, coeff_smul, smul_eq_mul, mul_comm b, ← Algebra.smul_def, map_smul,
    smul_eq_mul, mul_comm]

theorem lcoef_comm (ψ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K) (L : B →ₗ[K] K) (h : MvPolynomial σ B) :
    ψ (lcoef L h) = lcoef L (psiB B ψ h) := by
  induction h using MvPolynomial.induction_on' with
  | monomial u b =>
    have e : (monomial u b : MvPolynomial σ B) = C b * map (algebraMap K B) (monomial u 1) := by
      rw [map_monomial, map_one, C_mul_monomial, mul_one]
    rw [e, lcoef_C_mul_map, map_mul, psiB_map, psiB_C, lcoef_C_mul_map, map_smul]
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]

theorem hom_eq_on {S : Type} [CommRing S] (f g : MvPolynomial σ K →+* S) (hC : ∀ a, f (C a) = g (C a))
    (hX : ∀ w, f (X w) = g (X w)) (v : MvPolynomial σ K) : f v = g v := by
  rw [ringHom_ext hC hX]

end Psi

theorem pow_exp_inj {K : Type} [Field K] [Infinite K] (a b : ℕ) (h : ∀ c : K, c ≠ 0 → c ^ a = c ^ b) : a = b := by
  have h1 : (Polynomial.X ^ (a + 1) : Polynomial K) = Polynomial.X ^ (b + 1) := by
    apply Polynomial.funext
    intro c
    simp only [Polynomial.eval_pow, Polynomial.eval_X]
    by_cases hc : c = 0
    · rw [hc, zero_pow (Nat.succ_ne_zero _), zero_pow (Nat.succ_ne_zero _)]
    · rw [pow_succ, pow_succ, h c hc]
  have h2 := congrArg Polynomial.natDegree h1
  rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X_pow] at h2
  omega

section Scale

variable {K : Type} [Field K]

theorem sc_monomial {σ : Type} (d : σ → K) (u : σ →₀ ℕ) (a : K) :
    aeval (fun w => C (d w) * X w) (monomial u a) = monomial u (a * u.prod fun w e => d w ^ e) := by
  rw [aeval_monomial]
  simp only [mul_pow]
  rw [Finsupp.prod_mul]
  have hC : (u.prod fun v e => (C (d v) : MvPolynomial σ K) ^ e) = C (u.prod fun v e => d v ^ e) := by
    rw [map_finsuppProd]; simp only [map_pow]
  rw [hC, monomial_eq, C_mul, algebraMap_eq]
  ring

theorem sc_coeff {σ : Type} (d : σ → K) (f : MvPolynomial σ K) (m : σ →₀ ℕ) :
    coeff m (aeval (fun w => C (d w) * X w) f) = coeff m f * m.prod fun w e => d w ^ e := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [sc_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · rw [h]
    · rw [zero_mul]
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq, add_mul]

def scCol (K : Type) [Field K] (k : ℕ) (t0 : Fin k) (c : K) :
    MvPolynomial (Fin k × Fin k) K →ₐ[K] MvPolynomial (Fin k × Fin k) K :=
  aeval (fun w => C (if w.2 = t0 then c else 1) * X w)

theorem scCol_X {k : ℕ} (t0 : Fin k) (c : K) (w : Fin k × Fin k) :
    scCol K k t0 c (X w) = C (if w.2 = t0 then c else 1) * X w := by
  unfold scCol
  rw [aeval_X]

theorem sc_prod {k : ℕ} (t0 : Fin k) (c : K) (m : Fin k × Fin k →₀ ℕ) :
    (m.prod fun w e => (if w.2 = t0 then c else 1) ^ e) = c ^ (Finsupp.weight (colW k k) m t0) := by
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type, lccomp_weight_colW_apply,
    ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Finset.prod_eq_single t0]
  · simp
  · intro t _ ht
    simp [ht]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem scCol_coeff {k : ℕ} (t0 : Fin k) (c : K) (f : MvPolynomial (Fin k × Fin k) K) (m : Fin k × Fin k →₀ ℕ) :
    coeff m (scCol K k t0 c f) = coeff m f * c ^ (Finsupp.weight (colW k k) m t0) := by
  unfold scCol
  rw [sc_coeff, sc_prod]

theorem scCol_of_hom {k : ℕ} (t0 : Fin k) (c : K) (f : MvPolynomial (Fin k × Fin k) K) (ν : Fin k → ℕ)
    (hf : IsWeightedHomogeneous (colW k k) f ν) : scCol K k t0 c f = c ^ ν t0 • f := by
  ext m
  rw [scCol_coeff, coeff_smul, smul_eq_mul, mul_comm]
  by_cases h : coeff m f = 0
  · rw [h, mul_zero, mul_zero]
  · rw [hf h]

theorem wt_of_scale [Infinite K] {k : ℕ} (t0 : Fin k) (n : ℕ) (f : MvPolynomial (Fin k × Fin k) K)
    (h : ∀ c : K, c ≠ 0 → scCol K k t0 c f = c ^ n • f) (m : Fin k × Fin k →₀ ℕ) (hm : coeff m f ≠ 0) :
    Finsupp.weight (colW k k) m t0 = n := by
  apply pow_exp_inj (K := K)
  intro c hc
  have := congrArg (coeff m) (h c hc)
  rw [scCol_coeff, coeff_smul, smul_eq_mul, mul_comm] at this
  exact mul_right_cancel₀ hm this

theorem colAdd_trivial {k : ℕ} (l j : Fin k) (c : K) (f : MvPolynomial (Fin k × Fin k) K)
    (hf : ∀ m, coeff m f ≠ 0 → Finsupp.weight (colW k k) m j = 0) : colAdd K l j c f = f := by
  classical
  have e : colAdd K l j c f = ∑ m ∈ f.support, colAdd K l j c (monomial m (coeff m f)) := by
    conv_lhs => rw [f.as_sum]
    rw [map_sum]
  rw [e]
  conv_rhs => rw [f.as_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  unfold colAdd
  rw [aeval_monomial, monomial_eq, algebraMap_eq]
  congr 1
  apply Finsupp.prod_congr
  intro w hw
  have hwj : w.2 ≠ j := by
    intro h
    have h0 := hf m (mem_support_iff.1 hm)
    rw [lccomp_weight_colW_apply] at h0
    have h1 := Finset.sum_eq_zero_iff.1 h0 w.1 (Finset.mem_univ _)
    have e2 : w = (w.1, j) := Prod.ext rfl h
    apply Finsupp.mem_support_iff.1 hw
    rw [e2]
    exact h1
  rw [if_neg hwj]

end Scale

end Formalism.MainNotions.flipOneThree.Pf.QB

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudA
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem cloudOne_of (h : ContractionStandardLattice) : CloudOne := by
  intro p n' R mm hmm a ccl P Q lam hlam h0 hl hmid h8
  obtain ⟨abelian₂, hK, hE, hI, nb, s, s', ka, hnb, hka, hs, hs', h24⟩ := h p n' R mm hmm a ccl P Q lam hlam h0 hl hmid h8
  have := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  have hm1 : 1 ≤ mm + 1 := by omega
  have hloA : Antitone (lam - wtPQ (mm + 1) P Q) := caLo_anti mm ccl P Q lam hlam h0 hl hmid
  have hloA' : Antitone (dualWt (lam - wtPQ (mm + 1) P Q)) := cc_dualWt_anti _ hloA
  have hmuA : Antitone (wtPQ (mm + 1) P Q) := wtPQ_anti _ _ _ hm1
  have hmpA : Antitone (wtPQ (mm + 1) (P + 2 * ccl) (Q + 2 * ccl)) := wtPQ_anti _ _ _ hm1
  have hzeA : Antitone (wtPQ (mm + 1) (2 * ccl) (2 * ccl)) := wtPQ_anti _ _ _ hm1
  have hlo0 : (lam - wtPQ (mm + 1) P Q) 0 = (ccl : ℤ) := by
    rw [lo_val mm ccl P Q lam h0 hl, if_pos rfl]
  have hloL : (lam - wtPQ (mm + 1) P Q) (Fin.last (mm + 1)) = -(ccl : ℤ) := by
    rw [lo_val mm ccl P Q lam h0 hl, if_neg (caLast_ne_zero mm), if_pos rfl]
  have hloL' : dualWt (lam - wtPQ (mm + 1) P Q) (Fin.last (mm + 1)) = -(ccl : ℤ) := by
    unfold dualWt
    rw [Fin.rev_last, hlo0]
  refine ⟨abelian₂, hK, ?_, ?_⟩
  · rintro Λ ⟨g, hg, rfl⟩ v hv t ht
    rw [mem_invariant_sections_iff_integral hinj _ _ hmpA g hg]
    have hv0 := (mem_invariant_sections_iff_integral hinj _ lam hlam g hg v).1 hv
    have ht0 := (mem_invariant_sections_iff_integral hinj _ _ hloA' g hg t).1 ht
    have hvK : v ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf lam) :=
      la_nablaLTw_le _ lam g hg v (H0_le_twisted_nabla _ lam hlam g hg hv)
    have htK : t ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))) :=
      la_nablaLTw_le _ _ g hg t (H0_le_twisted_nabla _ _ hloA' g hg ht)
    have h3 := hI _ hv0 _ ht0
    rw [map_smul, map_smul, smul_mul_smul_comm, map_smul, hE g hg v hvK t htK, ← zpow_add₀ hg.ne_zero] at h3
    have he : lam (Fin.last (mm + 1)) + dualWt (lam - wtPQ (mm + 1) P Q) (Fin.last (mm + 1)) =
        wtPQ (mm + 1) (P + 2 * ccl) (Q + 2 * ccl) (Fin.last (mm + 1)) := by
      rw [hl, hloL', wtPQ_last]
      push_cast
      ring
    rwa [he] at h3
  · intro g hg
    have hgi : IsUnit (g⁻¹).det := Matrix.isUnit_nonsing_inv_det g hg
    refine ⟨nb, g.det ^ (2 * ccl) • rowAct R.Kf g⁻¹ (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl)))),
      fun b => g.det ^ ccl • rowAct R.Kf g⁻¹ (s b), fun a' => g.det ^ ccl • rowAct R.Kf g⁻¹ (s' a'), ka, hnb, hka, ?_, ?_⟩
    · intro a' b F hF
      have hF0 : rowAct R.Kf g F ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (wtPQ (mm + 1) P Q)) :=
        dualWeylRowStable R.Kf _ _ _ g F hF
      have e1 : F * (g.det ^ ccl • rowAct R.Kf g⁻¹ (s b)) = g.det ^ ccl • rowAct R.Kf g⁻¹ (rowAct R.Kf g F * s b) := by
        rw [map_mul, rowAct_cancel_inv g hg, mul_smul_comm]
      have hsK := intO_le (O := R.O) _ _ _ (hs b).1
      have hsK' := intO_le (O := R.O) _ _ _ (hs' a').1
      have hv : rowAct R.Kf g F * s b ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf lam) := by
        have h4 := dualWeyl_mul R.Kf _ _ _ _ hF0 hsK
        rw [← nuOf_add _ _ hmuA hloA] at h4
        have e : wtPQ (mm + 1) P Q + (lam - wtPQ (mm + 1) P Q) = lam := by abel
        rwa [e] at h4
      show abelian₂ (blockEmb R.Kf true (F * (g.det ^ ccl • rowAct R.Kf g⁻¹ (s b))) *
        blockEmb R.Kf false (g.det ^ ccl • rowAct R.Kf g⁻¹ (s' a'))) = _
      rw [e1, map_smul, map_smul, smul_mul_smul_comm, map_smul, hE g⁻¹ hgi _ hv _ hsK', h24 a' b _ hF0]
      split_ifs
      · rw [map_smul, map_mul, rowAct_cancel_inv g hg, smul_smul, smul_mul_assoc, smul_smul]
        congr 1
        ring
      · rw [map_zero, smul_zero]
    · intro c hc
      have hgD : IsUnit (g * lb_D (mm + 1 + 1) 1 c).det := by
        rw [Matrix.det_mul]
        exact hg.mul (lb_D_det _ 1 c hc)
      have hzR : Row0 (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl)))) (2 * ccl + 2 * ccl) := by
        have h5 := highest_weight_first_entry (K := R.Kf) (mm + 1) _ (nuOf_anti _ hzeA)
        have h6 : nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl)) 0 = 2 * ccl + 2 * ccl := by
          unfold nuOf
          rw [wtPQ_zero, wtPQ_last]
          omega
        rwa [h6] at h5
      have hcz := core_id g hg c hc (2 * ccl) (2 * ccl) _ hzR
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [mem_invariant_sections_iff_integral hinj _ _ hzeA _ hgD, wtPQ_last, hcz]
        exact hw_int _ _ (nuOf_anti _ hzeA)
      · rintro ⟨z', hz', he⟩
        have h7 := (mem_invariant_sections_iff_integral hinj _ _ hzeA _ hgD z').1 hz'
        rw [wtPQ_last] at h7
        apply hw_prim (O := R.O) (K := R.Kf) hinj R.w R.w_mem (mm + 1 + 1) (nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl)))
        refine ⟨_, h7, ?_⟩
        rw [← hcz, he, smulO_eq R.w z', map_smul, smulO_eq R.w, smul_comm]
      · intro b
        have hR : Row0 (s b) (ccl + ccl) := by rw [← two_mul]; exact (hs b).2
        rw [mem_invariant_sections_iff_integral hinj _ _ hloA _ hgD, hloL, core_id g hg c hc ccl ccl _ hR]
        exact (hs b).1
      · intro a'
        have hR : Row0 (s' a') (ccl + ccl) := by rw [← two_mul]; exact (hs' a').2
        rw [mem_invariant_sections_iff_integral hinj _ _ hloA' _ hgD, hloL', core_id g hg c hc ccl ccl _ hR]
        exact (hs' a').1

end Formalism.MainNotions.flipOneThree.Pf

end
end

