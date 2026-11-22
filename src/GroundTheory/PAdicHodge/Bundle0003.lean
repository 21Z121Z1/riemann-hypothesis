import Mathlib
import GroundTheory.PAdicHodge.Admissible
import GroundTheory.PAdicHodge.BdRSeries
import GroundTheory.PAdicHodge.PerfectoidField

-- bundled from GroundTheory.PAdicHodge.AdmissibleField
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open TensorProduct Module

section Field

variable (G F B : Type*) [Group G] [Field F] [Field B] [Algebra F B] [MulSemiringAction G B]

theorem isRegular_of_field : IsRegular G F B where
  image_fixedPoints := by
    let := IsFractionRing.mulSemiringAction G B (FractionRing B)
    have hmap : ∀ (g : G) (b : B), g • algebraMap B (FractionRing B) b =
        algebraMap B (FractionRing B) (g • b) := fun g b =>
      IsFractionRing.ringEquivOfRingEquiv_algebraMap _ b
    have hinj := IsFractionRing.injective B (FractionRing B)
    ext y
    constructor
    · rintro ⟨b, hb, rfl⟩ g
      rw [hmap, hb g]
    · intro hy
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors B) y
      have hs : (s : B) ≠ 0 := nonZeroDivisors.ne_zero s.2
      have e : IsLocalization.mk' (FractionRing B) a s =
          algebraMap B (FractionRing B) (a * (s : B)⁻¹) := by
        rw [IsLocalization.mk'_eq_iff_eq_mul, ← map_mul, mul_assoc, inv_mul_cancel₀ hs, mul_one]
      refine ⟨a * (s : B)⁻¹, fun g => hinj ?_, e.symm⟩
      rw [← hmap, ← e]
      exact hy g
  isUnit_of_mem_span b hb _ := hb.isUnit

end Field

section Coeff

variable (G F K B : Type*) [Group G] [Field F] [Field K] [CommRing B] [Algebra F K] [Algebra K B]
  [Algebra F B] [IsScalarTower F K B] [MulSemiringAction G B] [SMulCommClass G F B]
  [SMulCommClass G K B]
variable {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V)

def DBK : Submodule K (B ⊗[F] V) where
  carrier := {x | ∀ g : G, baseChangeRep B ρ g x = x}
  add_mem' {x y} hx hy g := by rw [map_add, hx g, hy g]
  zero_mem' g := map_zero _
  smul_mem' k x hx g := by
    change baseChangeRep B ρ g (k • x) = k • x
    rw [← algebraMap_smul B k x, baseChangeRep_smul, hx g, smul_algebraMap]

variable {G F K B ρ} in
theorem mem_DBK {x : B ⊗[F] V} : x ∈ DBK G F K B ρ ↔ ∀ g : G, baseChangeRep B ρ g x = x :=
  Iff.rfl

theorem coe_DBK : (DBK G F K B ρ : Set (B ⊗[F] V)) = DB B ρ := rfl

def toInvariantRing : K →+* invariantRing G F B where
  toFun k := ⟨algebraMap K B k, fun g => smul_algebraMap g k⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a b)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a b)

variable {G F K B}

omit [Algebra F K] [IsScalarTower F K B] in
@[simp]
theorem coe_toInvariantRing (k : K) : (toInvariantRing G F K B k : B) = algebraMap K B k := rfl

omit [Algebra F K] [IsScalarTower F K B] in
theorem toInvariantRing_bijective [Nontrivial B]
    (hK : ∀ b : B, (∀ g : G, g • b = b) → ∃ k : K, algebraMap K B k = b) :
    Function.Bijective (toInvariantRing G F K B) := by
  refine ⟨fun a b hab => (algebraMap K B).injective ?_, fun e => ?_⟩
  · simpa using congrArg Subtype.val hab
  · obtain ⟨k, hk⟩ := hK e e.2
    exact ⟨k, Subtype.ext hk⟩

theorem invariantRing_eq_range
    (hK : ∀ b : B, (∀ g : G, g • b = b) → ∃ k : K, algebraMap K B k = b) :
    invariantRing G F B = (IsScalarTower.toAlgHom F K B).range := by
  ext b
  constructor
  · intro hb
    obtain ⟨k, hk⟩ := hK b hb
    exact ⟨k, hk⟩
  · rintro ⟨k, rfl⟩ g
    exact smul_algebraMap g k

theorem rank_DBK [Nontrivial B]
    (hK : ∀ b : B, (∀ g : G, g • b = b) → ∃ k : K, algebraMap K B k = b) :
    Module.rank K (DBK G F K B ρ) = Module.rank (invariantRing G F B) (DB B ρ) := by
  let j : DBK G F K B ρ ≃+ DB B ρ :=
    { toFun := fun x => ⟨x, x.2⟩
      invFun := fun x => ⟨x, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  refine rank_eq_of_equiv_equiv (toInvariantRing G F K B) j (toInvariantRing_bijective hK) ?_
  intro k x
  apply Subtype.ext
  change k • (x : B ⊗[F] V) =
    ((toInvariantRing G F K B k : invariantRing G F B) : B) • (x : B ⊗[F] V)
  rw [coe_toInvariantRing, algebraMap_smul]

theorem finrank_DBK [Nontrivial B]
    (hK : ∀ b : B, (∀ g : G, g • b = b) → ∃ k : K, algebraMap K B k = b) :
    finrank K (DBK G F K B ρ) = finrank (invariantRing G F B) (DB B ρ) := by
  simp only [Module.finrank, rank_DBK ρ hK]

variable [IsDomain B]

theorem IsRegular.finiteDimensional_DBK (h : IsRegular G F B)
    (hK : ∀ b : B, (∀ g : G, g • b = b) → ∃ k : K, algebraMap K B k = b) [FiniteDimensional F V] :
    FiniteDimensional K (DBK G F K B ρ) := by
  let := h.field
  have := h.free ρ
  have := h.finite ρ
  have : Module.Free K (DBK G F K B ρ) := Module.Free.of_divisionRing K (DBK G F K B ρ)
  exact Module.rank_lt_aleph0_iff.1 (by rw [rank_DBK ρ hK]; exact Module.rank_lt_aleph0_iff.2 ‹_›)

theorem IsRegular.finrank_DBK_le (h : IsRegular G F B)
    (hK : ∀ b : B, (∀ g : G, g • b = b) → ∃ k : K, algebraMap K B k = b) [FiniteDimensional F V] :
    finrank K (DBK G F K B ρ) ≤ finrank F V := by
  rw [finrank_DBK ρ hK]
  exact h.finrank_le ρ

theorem isAdmissible_iff_finrank_DBK
    (hK : ∀ b : B, (∀ g : G, g • b = b) → ∃ k : K, algebraMap K B k = b) :
    IsAdmissible B ρ ↔ finrank K (DBK G F K B ρ) = finrank F V := by
  rw [finrank_DBK ρ hK]
  rfl

end Coeff

end GroundTheory.PAdicHodge
end

-- bundled from GroundTheory.PAdicHodge.LogMul
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open PowerSeries

section Formal

theorem exp_subst_log : (exp ℚ).subst (log ℚ) = (1 + X : ℚ⟦X⟧) := by
  have hS : HasSubst (log ℚ) := HasSubst.log
  set F : ℚ⟦X⟧ := (exp ℚ).subst (log ℚ) with hF
  set G : ℚ⟦X⟧ := mk (fun n => algebraMap ℚ ℚ ((-1) ^ n)) with hG
  have h1 : (1 + X : ℚ⟦X⟧) * G = 1 := one_add_X_mul_geom
  have hF' : d⁄dX ℚ F = F * G := by
    rw [hF, derivative_subst hS, derivative_exp, deriv_log]
  have hG' : d⁄dX ℚ G = -(G * G) := by
    have h := congrArg (d⁄dX ℚ) h1
    rw [Derivation.leibniz, derivative_one, map_add, derivative_one, derivative_X, zero_add,
      smul_eq_mul, smul_eq_mul, mul_one] at h
    calc d⁄dX ℚ G = G * ((1 + X) * d⁄dX ℚ G) := by
          rw [← mul_assoc, mul_comm G, h1, one_mul]
      _ = -(G * G) := by
          rw [show (1 + X) * d⁄dX ℚ G = -G from eq_neg_of_add_eq_zero_left h]
          ring
  have hc : constantCoeff F = 1 := by
    have h0 : MvPowerSeries.constantCoeff (log ℚ) = 0 := constantCoeff_log
    have hz := constantCoeff_subst_eq_zero h0 (exp ℚ - 1) (by simp [constantCoeff_exp])
    have hsub : (exp ℚ - 1 : ℚ⟦X⟧).subst (log ℚ) = F - 1 := by
      rw [hF, ← coe_substAlgHom hS, map_sub, map_one]
    rw [hsub, map_sub, map_one, sub_eq_zero] at hz
    exact hz
  have hGc : constantCoeff G = 1 := by
    rw [hG, ← coeff_zero_eq_constantCoeff_apply, coeff_mk]
    simp
  have hH : F * G = 1 := by
    apply derivative.ext
    · rw [Derivation.leibniz, hF', hG', derivative_one, smul_eq_mul, smul_eq_mul]
      ring
    · rw [map_mul, hc, hGc, map_one, mul_one]
  calc F = F * ((1 + X) * G) := by rw [h1, mul_one]
    _ = (F * G) * (1 + X) := by ring
    _ = 1 + X := by rw [hH, one_mul]

end Formal

section Nilpotent

variable {S : Type*} [CommRing S] [Algebra ℚ S]

theorem truncEval_pow_eq_zero {n : ℕ} {s : S} (hs : s ^ n = 0) {g : ℚ⟦X⟧}
    (hg : constantCoeff g = 0) : (truncEval s hs g) ^ n = 0 := by
  obtain ⟨h, rfl⟩ := X_dvd_iff.2 hg
  rw [← map_pow, mul_pow, map_mul, map_pow, truncEval_X, hs, zero_mul]

theorem truncEval_subst {n : ℕ} {s : S} (hs : s ^ n = 0) {g : ℚ⟦X⟧} (hg : constantCoeff g = 0)
    (f : ℚ⟦X⟧) :
    truncEval s hs (f.subst g) = truncEval (truncEval s hs g) (truncEval_pow_eq_zero hs hg) f := by
  have hS := HasSubst.of_constantCoeff_zero' hg
  have key := truncEval_unique ((truncEval s hs).comp (substAlgHom hS)) (truncEval s hs g)
    (truncEval_pow_eq_zero hs hg) (by rw [AlgHom.comp_apply, coe_substAlgHom, subst_X hS])
  rw [← key, AlgHom.comp_apply, coe_substAlgHom]

theorem truncEval_exp {n : ℕ} {s : S} (hs : s ^ n = 0) :
    truncEval s hs (exp ℚ) = IsNilpotent.exp s := by
  rw [truncEval_eq_sum, IsNilpotent.exp_eq_sum hs]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_exp, Algebra.smul_def, one_div]
  simp

theorem isNilpotent_truncEval_log {n : ℕ} {s : S} (hs : s ^ n = 0) :
    IsNilpotent (truncEval s hs (log ℚ)) :=
  ⟨n, truncEval_pow_eq_zero hs constantCoeff_log⟩

theorem exp_truncEval_log {n : ℕ} {s : S} (hs : s ^ n = 0) :
    IsNilpotent.exp (truncEval s hs (log ℚ)) = 1 + s := by
  rw [← truncEval_exp (truncEval_pow_eq_zero hs constantCoeff_log),
    ← truncEval_subst hs (g := log ℚ) constantCoeff_log,
    exp_subst_log, map_add, map_one, truncEval_X]

theorem eq_zero_of_exp_eq_one {c : S} (hc : IsNilpotent c) (h : IsNilpotent.exp c = 1) : c = 0 := by
  obtain ⟨k, hk⟩ := hc
  set w : S := ∑ i ∈ Finset.range k, ((i + 1).factorial : ℚ)⁻¹ • c ^ i with hw
  have hexp : IsNilpotent.exp c = 1 + c * w := by
    rw [IsNilpotent.exp_eq_sum (pow_eq_zero_of_le (Nat.le_succ k) hk), Finset.sum_range_succ',
      hw, Finset.mul_sum]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, pow_succ, mul_comm c]
  have hw1 : IsUnit w := by
    rcases k with _ | k
    · have : Subsingleton S := subsingleton_of_zero_eq_one (by simpa using hk.symm)
      exact isUnit_of_subsingleton w
    · have hsplit : w = 1 + c * ∑ i ∈ Finset.range k, ((i + 2).factorial : ℚ)⁻¹ • c ^ i := by
        rw [hw, Finset.sum_range_succ', Finset.mul_sum]
        simp only [pow_zero, zero_add, Nat.factorial_one, Nat.cast_one, inv_one, one_smul]
        rw [add_comm]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_smul_comm, pow_succ, mul_comm c]
      rw [hsplit]
      exact IsNilpotent.isUnit_one_add ⟨k + 1, by rw [mul_pow, hk, zero_mul]⟩
  have h0 : c * w = 0 := by
    have := hexp.symm.trans h
    rwa [add_eq_left] at this
  simpa using (hw1.mul_left_eq_zero).1 h0

theorem eq_of_exp_eq {a b : S} (ha : IsNilpotent a) (hb : IsNilpotent b)
    (h : IsNilpotent.exp a = IsNilpotent.exp b) : a = b := by
  have hnb : IsNilpotent (-b) := hb.neg
  have h1 : IsNilpotent.exp (a + -b) = 1 := by
    rw [IsNilpotent.exp_add_of_commute (Commute.all _ _) ha hnb, h,
      IsNilpotent.exp_mul_exp_neg_self hb]
  have h2 := eq_zero_of_exp_eq_one (Commute.isNilpotent_add (Commute.all _ _) ha hnb) h1
  rw [← sub_eq_add_neg, sub_eq_zero] at h2
  exact h2

theorem truncEval_log_mul {l m n : ℕ} {x y z : S} (hx : x ^ l = 0) (hy : y ^ m = 0)
    (hz : z ^ n = 0) (hxyz : 1 + z = (1 + x) * (1 + y)) :
    truncEval z hz (log ℚ) = truncEval x hx (log ℚ) + truncEval y hy (log ℚ) := by
  have hnx := isNilpotent_truncEval_log hx
  have hny := isNilpotent_truncEval_log hy
  apply eq_of_exp_eq (isNilpotent_truncEval_log hz) (Commute.isNilpotent_add (Commute.all _ _) hnx hny)
  rw [IsNilpotent.exp_add_of_commute (Commute.all _ _) hnx hny, exp_truncEval_log,
    exp_truncEval_log, exp_truncEval_log, hxyz]

end Nilpotent

section Complete

variable {B : Type*} [CommRing B] [Algebra ℚ B] {I : Ideal B} [IsAdicComplete I B]

theorem mk_seriesEval_eq_truncEval {z : B} (hz : z ∈ I) (f : ℚ⟦X⟧) (n : ℕ) :
    Ideal.Quotient.mk (I ^ n) (seriesEval I z hz f) =
      truncEval (Ideal.Quotient.mk (I ^ n) z) (pow_mk_eq_zero I hz n) f :=
  IsAdicComplete.mk_liftAlgHom I
    (fun n => truncEval (Ideal.Quotient.mk (I ^ n) z) (pow_mk_eq_zero I hz n))
    (fun hle => factorₐ_comp_truncEval I hz hle) n f

theorem logOnePlus_mul {x y z : B} (hx : x ∈ I) (hy : y ∈ I) (hz : z ∈ I)
    (hxyz : 1 + z = (1 + x) * (1 + y)) :
    logOnePlus I z hz = logOnePlus I x hx + logOnePlus I y hy := by
  refine eq_of_forall_sub_mem_pow I fun n => ?_
  rw [← Ideal.Quotient.eq, map_add, logOnePlus, logOnePlus, logOnePlus,
    mk_seriesEval_eq_truncEval, mk_seriesEval_eq_truncEval, mk_seriesEval_eq_truncEval]
  exact truncEval_log_mul _ _ _ (by rw [← map_one (Ideal.Quotient.mk (I ^ n)), ← map_add, hxyz,
    map_mul, map_add, map_add, map_one])

end Complete

end GroundTheory.PAdicHodge
end
end

-- bundled from GroundTheory.PAdicHodge.PerfectoidCharP
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace IsPerfectoidField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

theorem charZero_or_charP (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p] :
    CharZero K ∨ CharP K p := by
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hq | hq
  · right
    have hq' : Fact (ringChar K).Prime := ⟨hq⟩
    by_contra hne
    have hpq : p ≠ ringChar K := fun h => hne (h ▸ ringChar.charP K)

    have hpz : ((p : ZMod (ringChar K))) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      exact hpq ((Nat.prime_dvd_prime_iff_eq hq (Fact.out : p.Prime)).1 hdvd).symm
    have hferm := ZMod.pow_card_sub_one_eq_one hpz
    have hK : (p : K) ^ (ringChar K - 1) = 1 := by
      have := congrArg (ZMod.castHom (dvd_refl (ringChar K)) K) hferm
      simpa using this
    have hn := congrArg norm hK
    rw [norm_pow, norm_one] at hn
    have hlt := IsPerfectoidField.norm_natCast_lt_one (K := K) (p := p)
    have hpos : ringChar K - 1 ≠ 0 := by have := hq.two_le; omega
    have : ‖(p : K)‖ = 1 :=
      (pow_eq_one_iff_of_nonneg (norm_nonneg _) hpos).1 hn
    linarith
  · left
    have : CharP K 0 := by rw [← hq]; exact ringChar.charP K
    exact CharP.charP_to_charZero K

theorem of_finiteDimensional_of_charP (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p] [CharP K p]
    (L : Type*) [NontriviallyNormedField L] [IsUltrametricDist L] [NormedAlgebra K L]
    [FiniteDimensional K L] : IsPerfectoidField L p := by
  have := IsPerfectoidField.completeSpace (K := K) p
  have : CompleteSpace L := FiniteDimensional.complete K L
  have : PerfectRing K p := IsPerfectoidField.perfectRing p
  have : PerfectField K := PerfectRing.toPerfectField K p
  have : PerfectField L := Algebra.IsAlgebraic.perfectField (K := K)
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have : PerfectRing L p := PerfectField.toPerfectRing p
  refine IsPerfectoidField.of_perfectRing p fun r hr => ?_
  obtain ⟨x, hx1, hx2⟩ := IsPerfectoidField.exists_norm_mem_Ioo (K := K) (p := p) r hr
  exact ⟨algebraMap K L x, by rwa [norm_algebraMap'], by rwa [norm_algebraMap']⟩

end IsPerfectoidField

end GroundTheory.PAdicHodge
end
end

