import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0020

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedEqOneOfLe
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.TupHecke

section General

variable {L : Type} [Field L] [NumberField L]

abbrev FI (L : Type) [Field L] [NumberField L] : Type := (FiniteAdeleRing (𝓞 L) L)ˣ

def sing (P : HeightOneSpectrum (𝓞 L)) : (P.adicCompletion L)ˣ →* FI L := Units.map (finiteSingle L P)

def cmp (P : HeightOneSpectrum (𝓞 L)) : FI L →* (P.adicCompletion L)ˣ :=
  Units.map { toFun := fun a => a P, map_one' := rfl, map_mul' := fun _ _ => rfl }

variable (L) in

def incl : FI L →* Ideles L := Units.map (MonoidHom.inr (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

variable (L) in

def finP : Ideles L →* FI L := Units.map (MonoidHom.snd (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

theorem cmp_val (P : HeightOneSpectrum (𝓞 L)) (u : FI L) :
    (cmp P u : P.adicCompletion L) = (u : FiniteAdeleRing (𝓞 L) L) P := rfl

theorem incl_sing (P : HeightOneSpectrum (𝓞 L)) (x) : incl L (sing P x) = localIdele L P x := rfl

theorem finitePart_incl (u : FI L) : finP L (incl L u) = u := rfl

theorem finitePart_localIdele (P : HeightOneSpectrum (𝓞 L)) (x) : finP L (localIdele L P x) = sing P x := rfl

theorem finitePart_infIdele (w : InfinitePlace L) (x) : finP L (infIdele L w x) = 1 := rfl

open Classical in
theorem cmp_sing_self (P : HeightOneSpectrum (𝓞 L)) (x) : cmp P (sing P x) = x := by
  apply Units.ext
  show Function.update (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L)) P x P = x
  exact Function.update_self (β := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) P _ _

open Classical in
theorem cmp_sing_ne {P Q : HeightOneSpectrum (𝓞 L)} (h : P ≠ Q) (x) : cmp P (sing Q x) = 1 := by
  apply Units.ext
  show Function.update (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L)) Q x P = 1
  exact Function.update_of_ne (β := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) h _ _

theorem fi_ext {u u' : FI L} (h : ∀ P, cmp P u = cmp P u') : u = u' :=
  Units.ext (FiniteAdeleRing.ext _ fun P => congrArg Units.val (h P))

open Classical in
theorem cmp_prod (T : Finset (HeightOneSpectrum (𝓞 L))) (x : ∀ Q : HeightOneSpectrum (𝓞 L), (Q.adicCompletion L)ˣ)
    (P : HeightOneSpectrum (𝓞 L)) : cmp P (∏ Q ∈ T, sing Q (x Q)) = if P ∈ T then x P else 1 := by
  rw [map_prod]
  split_ifs with h
  · rw [Finset.prod_eq_single_of_mem P h fun Q _ hQ => cmp_sing_ne hQ.symm _, cmp_sing_self]
  · exact Finset.prod_eq_one fun Q hQ => cmp_sing_ne (by rintro rfl; exact h hQ) _

theorem valued_eq_one_of_le {P : HeightOneSpectrum (𝓞 L)} (x : (P.adicCompletion L)ˣ)
    (h : Valued.v (x : P.adicCompletion L) ≤ 1) (h' : Valued.v ((x⁻¹ : (P.adicCompletion L)ˣ) : P.adicCompletion L) ≤ 1) :
    Valued.v (x : P.adicCompletion L) = 1 := by
  refine le_antisymm h ?_
  have e : Valued.v (x : P.adicCompletion L) * Valued.v ((x⁻¹ : (P.adicCompletion L)ˣ) : P.adicCompletion L) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  exact e.symm.le.trans (mul_le_of_le_one_right' h')

theorem finite_nonunit (u : FI L) : {P | ¬ IsUnitAt P (cmp P u)}.Finite := by
  have h1 := Filter.eventually_cofinite.1 (u : FiniteAdeleRing (𝓞 L) L).2
  have h2 := Filter.eventually_cofinite.1 ((u⁻¹ : FI L) : FiniteAdeleRing (𝓞 L) L).2
  refine (h1.union h2).subset fun P hP => ?_
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hn
  exact hP (valued_eq_one_of_le _ hn.1 hn.2)

theorem finite_nat {N : ℕ} (hN : 0 < N) :
    {P : HeightOneSpectrum (𝓞 L) | Valued.v (N : P.adicCompletion L) ≠ 1}.Finite := by
  refine (finite_nonunit (Units.map (algebraMap L (FiniteAdeleRing (𝓞 L) L)).toMonoidHom
    (Units.mk0 (N : L) (Nat.cast_ne_zero.2 hN.ne')))).subset fun P hP h => hP ?_
  rw [← map_natCast (algebraMap L (P.adicCompletion L))]
  exact h

def Cong (N : ℕ) (u : FI L) : Prop :=
  ∀ P, IsUnitAt P (cmp P u) ∧ Valued.v ((cmp P u : P.adicCompletion L) - 1) ≤ Valued.v (N : P.adicCompletion L)

variable {G : Type} [CommGroup G]

theorem eq_one_of_local {N : ℕ} (hN : 0 < N) (ψ : FI L →* G) (hψ : ∀ u, Cong N u → ψ u = 1) (u : FI L)
    (h : ∀ P, ψ (sing P (cmp P u)) = 1) : ψ u = 1 := by
  classical
  set T := ((finite_nonunit u).union (finite_nat (L := L) hN)).toFinset with hT
  have e : u = (∏ Q ∈ T, sing Q (cmp Q u)) * ((∏ Q ∈ T, sing Q (cmp Q u))⁻¹ * u) := by simp
  rw [e, map_mul, map_prod, Finset.prod_eq_one fun Q _ => h Q, one_mul]
  refine hψ _ fun P => ?_
  rw [map_mul, map_inv, cmp_prod]
  split_ifs with hP
  · simp [IsUnitAt]
  · simp only [hT, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hP
    rw [inv_one, one_mul, hP.2]
    exact ⟨hP.1, Valuation.map_sub_le _ hP.1.le (by simp)⟩

theorem cong_sing {N : ℕ} {P : HeightOneSpectrum (𝓞 L)} {x : (P.adicCompletion L)ˣ} (h : IsUnitAt P x)
    (h' : Valued.v ((x : P.adicCompletion L) - 1) ≤ Valued.v (N : P.adicCompletion L)) : Cong N (sing P x) := by
  intro Q
  by_cases e : Q = P
  · subst e
    rw [cmp_sing_self]
    exact ⟨h, h'⟩
  · rw [cmp_sing_ne e]
    simp [IsUnitAt]

theorem local_of_global {N : ℕ} (hN : 0 < N) (ψ : FI L →* G) (hψ : ∀ u, Cong N u → ψ u = 1)
    (P : HeightOneSpectrum (𝓞 L)) (h : ∀ k : Lˣ, ψ (sing P (atFin P k)) = 1) (x : (P.adicCompletion L)ˣ) :
    ψ (sing P x) = 1 := by
  have hx0 : Valued.v (x : P.adicCompletion L) ≠ 0 := by simp
  have hN0 := GlobalTheory.AdLat.valued_natCast_ne_zero P hN
  obtain ⟨n, hn⟩ := GlobalTheory.Idele.exists_exp_neg_lt (mul_ne_zero hx0 hN0)
  have hd : DenseRange (algebraMap L (P.adicCompletion L)) := HeightOneSpectrum.denseRange_algebraMap (K := L) P
  have ho : IsOpen ((fun y : P.adicCompletion L => (x : P.adicCompletion L) - y) ⁻¹'
      {z | Valued.v z ≤ WithZero.exp (-(n : ℤ))}) :=
    (GlobalTheory.Idele.isOpen_valued_le (K := L) P (-(n : ℤ))).preimage (by fun_prop)
  obtain ⟨k, hk⟩ := hd.exists_mem_open ho ⟨x, by simp⟩
  have hk1 : Valued.v ((x : P.adicCompletion L) - algebraMap L _ k) <
    Valued.v (x : P.adicCompletion L) * Valued.v (N : P.adicCompletion L) := lt_of_le_of_lt hk hn
  have hk2 : Valued.v (algebraMap L (P.adicCompletion L) k) = Valued.v (x : P.adicCompletion L) := by
    have := Valuation.map_sub_eq_of_lt_left Valued.v
      (hk1.trans_le (mul_le_of_le_one_right' (GlobalTheory.AdLat.valued_natCast_le_one P N)))
    rwa [sub_sub_cancel] at this
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [map_zero, map_zero] at hk2
    exact hx0 hk2.symm
  have e : x = atFin P (Units.mk0 k hk0) * ((atFin P (Units.mk0 k hk0))⁻¹ * x) := by simp
  have ev : ((atFin P (Units.mk0 k hk0) : (P.adicCompletion L)ˣ) : P.adicCompletion L) = algebraMap L _ k := rfl
  have hk3 : algebraMap L (P.adicCompletion L) k ≠ 0 := by simpa using hk0
  rw [e, map_mul, map_mul, h, one_mul]
  refine hψ _ (cong_sing ?_ ?_)
  · unfold IsUnitAt
    rw [Units.val_mul, Units.val_inv_eq_inv_val, ev, map_mul, map_inv₀, hk2, inv_mul_cancel₀ hx0]
  · rw [Units.val_mul, Units.val_inv_eq_inv_val, ev]
    have e2 : (algebraMap L (P.adicCompletion L) k)⁻¹ * x - 1 =
      (algebraMap L (P.adicCompletion L) k)⁻¹ * (x - algebraMap L _ k) := by field_simp
    rw [e2, map_mul, map_inv₀, hk2, inv_mul_le_iff₀ (zero_lt_iff.2 hx0)]
    exact hk1.le

theorem continuous_finP {N : ℕ} (hN : 0 < N) (ψ : FI L →* ℂˣ) (hψ : ∀ u, Cong N u → ψ u = 1) :
    Continuous (ψ.comp (finP L)) := by
  classical
  obtain ⟨T, hT⟩ : ∃ T : Finset (HeightOneSpectrum (𝓞 L)), ∀ P, P ∉ T → Valued.v (N : P.adicCompletion L) = 1 :=
    ⟨(finite_nat (L := L) hN).toFinset, fun P hP => by simpa using hP⟩
  choose n hn using fun P : HeightOneSpectrum (𝓞 L) =>
    GlobalTheory.Idele.exists_exp_neg_lt (GlobalTheory.AdLat.valued_natCast_ne_zero P hN)
  have ho := (GlobalTheory.Mem.UnitOpen.unit_open_and_congr_open L).2 T (T.sup n)
  have h1 := ho.mem_nhds (x := (1 : Ideles L)) ⟨one_mem _, fun v _ => by
    have : ((1 : Ideles L) : AdeleRing (𝓞 L) L).2 v = 1 := rfl
    rw [this, sub_self, map_zero]
    exact zero_le⟩
  have h2 : (fun _ => (1 : ℂˣ)) =ᶠ[nhds (1 : Ideles L)] (ψ.comp (finP L)) := by
    filter_upwards [h1] with a ha
    have hu : ∀ P, IsUnitAt P (cmp P (finP L a)) := ha.1
    refine (hψ (finP L a) fun P => ⟨hu P, ?_⟩).symm
    by_cases hP : P ∈ T
    · refine le_trans (ha.2 P hP) (le_trans ?_ (hn P).le)
      rw [WithZero.exp_le_exp]
      have := Finset.le_sup (f := n) hP
      omega
    · rw [hT P hP]
      exact Valuation.map_sub_le _ (hu P).le (by simp)
  exact continuous_of_continuousAt_one _ (continuousAt_const.congr h2)

theorem apply_eq_apply_finitePart_of_pow_eq_one [IsTotallyComplex L] (ψ : Ideles L →* G) {n : ℕ} (hn : 0 < n) (h : ∀ a, ψ a ^ n = 1)
    (a : Ideles L) : ψ a = ψ (incl L (finP L a)) := by
  have hroot : ∀ (w : InfinitePlace L) (z : w.Completion), ∃ y, y ^ n = z := fun w z => by
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (e z) hn
    exact ⟨e.symm y, by rw [← map_pow, hy, e.symm_apply_apply]⟩
  choose y hy using fun w => hroot w ((a : AdeleRing (𝓞 L) L).1 w)
  let Y : AdeleRing (𝓞 L) L := (y, 1)
  have e : Y ^ n = ((a * (incl L (finP L a))⁻¹ : Ideles L) : AdeleRing (𝓞 L) L) := by
    refine Prod.ext (funext fun w => (hy w).trans (mul_one _).symm) ?_
    exact (one_pow n).trans (congrArg Prod.snd a.mul_inv).symm
  have hu : IsUnit Y := (isUnit_pow_iff hn.ne').1 (e ▸ Units.isUnit _)
  obtain ⟨b, hb⟩ := hu
  have e2 : b ^ n = a * (incl L (finP L a))⁻¹ := Units.ext (by rw [Units.val_pow_eq_pow_val, hb, e])
  have := h b
  rwa [← map_pow, e2, map_mul, map_inv, mul_inv_eq_one] at this

theorem eq_self_of_fix (φ : FiniteAdeleRing (𝓞 L) L →+* FiniteAdeleRing (𝓞 L) L)
    (h1 : ∀ x : L, φ (algebraMap L _ x) = algebraMap L _ x)
    (h2 : ∀ z : FiniteAdeleRing (𝓞 L) L, (∀ P, Valued.v (z P) ≤ 1) → ∀ P, Valued.v (φ z P) ≤ 1)
    (z : FiniteAdeleRing (𝓞 L) L) : φ z = z := by
  rw [← sub_eq_zero]
  refine (GlobalTheory.AdLat.integral_finiteAdele_complete_separated L).1 _ fun N hN => ?_
  obtain ⟨x, a, ha, rfl⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat L N hN).1 z
  refine ⟨φ a - a, fun v => sub_mem (h2 a ha v) (ha v), ?_⟩
  rw [map_add, h1, map_nsmul, smul_sub]
  abel

end General

end GlobalTheory.Mem.TupHecke
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedPowSubOneLtOne
section
open NumberField IsDedekindDomain Formalism.L2.Host IsLocalRing Polynomial

namespace GlobalTheory.Mem.WildChar

theorem le_exp_neg_one_of_lt_one {g : WithZero (Multiplicative ℤ)} (hy : g < 1) :
    g ≤ WithZero.exp (-1 : ℤ) := by
  by_cases hg : g = 0
  · rw [hg]; exact zero_le
  · rw [← WithZero.exp_log hg] at hy ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hy
    rw [WithZero.exp_le_exp]
    omega

theorem val_pow_sub_pow_le {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation K Γ) {a b : K} (ha : w a ≤ 1) (hb : w b ≤ 1) (m : ℕ) :
    w (a ^ m - b ^ m) ≤ w (a - b) := by
  first
  | exact @_root_.GlobalTheory.ValuationPowSubPow.valuation_pow_sub_pow_le
  | exact _root_.GlobalTheory.ValuationPowSubPow.valuation_pow_sub_pow_le
  | (apply _root_.GlobalTheory.ValuationPowSubPow.valuation_pow_sub_pow_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.ValuationPowSubPow.valuation_pow_sub_pow_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ValuationPowSubPow.valuation_pow_sub_pow_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ValuationPowSubPow.valuation_pow_sub_pow_le ..)

theorem val_pow_sub_one_le {K : Type*} [Field K] (w : Valuation K (WithZero (Multiplicative ℤ)))
    {u : K} (hu : w u ≤ 1) (hu1 : w (u - 1) < 1) {q : ℕ} (hq : w (q : K) < 1) :
    w (u ^ q - 1) ≤ w (u - 1) * WithZero.exp (-1 : ℤ) := by
  rw [← mul_geom_sum, map_mul]
  refine mul_le_mul_right (le_exp_neg_one_of_lt_one ?_) _
  have e : ∑ i ∈ Finset.range q, u ^ i = (q : K) + ∑ i ∈ Finset.range q, (u ^ i - 1 ^ i) := by
    simp
  rw [e]
  refine Valuation.map_add_lt _ hq (Valuation.map_sum_lt _ one_ne_zero fun i _ => ?_)
  exact (val_pow_sub_pow_le w hu (map_one w).le i).trans_lt hu1

theorem val_pow_pow_sub_one_le {K : Type*} [Field K] (w : Valuation K (WithZero (Multiplicative ℤ)))
    {u : K} (hu : w u ≤ 1) (hu1 : w (u - 1) < 1) {q : ℕ} (hq : w (q : K) < 1) (n : ℕ) :
    w (u ^ (q ^ n) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  induction n with
  | zero => simpa using hu1.le
  | succ n ih =>
    have h1 : w (u ^ (q ^ n)) ≤ 1 := by rw [map_pow]; exact pow_le_one' hu _
    have h2 : w (u ^ (q ^ n) - 1) < 1 := by
      have := val_pow_sub_pow_le w hu (map_one w).le (q ^ n)
      rw [one_pow] at this
      exact this.trans_lt hu1
    rw [pow_succ, pow_mul]
    refine (val_pow_sub_one_le w h1 h2 hq).trans ((mul_le_mul_left ih _).trans (le_of_eq ?_))
    rw [← WithZero.exp_add]
    congr 1
    push_cast
    ring

variable {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))

theorem valued_algebraMap_lt_one {y : 𝓞 L} :
    Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) y) < 1 ↔ y ∈ v.asIdeal := by
  have h3 : Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) y)
      = v.valuation L (algebraMap (𝓞 L) L y) :=
    ReciprocityTheory.Aut.adic_valued_algebraMap v (algebraMap (𝓞 L) L y)
  rw [h3]
  exact HeightOneSpectrum.valuation_lt_one_iff_mem v _

theorem valued_absNorm_lt_one :
    Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion L) < 1 := by
  rw [← map_natCast (algebraMap (𝓞 L) (v.adicCompletion L)), valued_algebraMap_lt_one]
  exact Ideal.absNorm_mem v.asIdeal

theorem one_lt_absNorm : 1 < Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

theorem valued_pow_sub_one_lt_one {x : v.adicCompletion L} (hx : Valued.v x = 1) :
    Valued.v (x ^ (Ideal.absNorm v.asIdeal - 1) - 1) < 1 := by
  obtain ⟨y, hy⟩ := ReciprocityTheory.Aut.adic_exists_approx v x hx.le
  have hy1 : Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) y) = 1 := by
    rw [← hx]
    apply Valuation.map_eq_of_sub_lt
    rw [Valuation.map_sub_swap, hx]
    exact hy
  have hnot : y ∉ v.asIdeal := by
    rw [← valued_algebraMap_lt_one, hy1]; exact lt_irrefl _
  have hmem : y ^ (Ideal.absNorm v.asIdeal - 1) - 1 ∈ v.asIdeal := by
    haveI := v.isMaximal
    letI := Ideal.Quotient.field v.asIdeal
    haveI : Finite (𝓞 L ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
    letI := Fintype.ofFinite (𝓞 L ⧸ v.asIdeal)
    rw [← Ideal.Quotient.eq, map_pow, map_one, Ideal.absNorm_apply, Submodule.cardQuot_apply,
      Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one _ (fun h => hnot (Ideal.Quotient.eq_zero_iff_mem.1 h))
  rw [← valued_algebraMap_lt_one, map_sub, map_pow, map_one] at hmem
  rw [← sub_add_sub_cancel _
    (algebraMap (𝓞 L) (v.adicCompletion L) y ^ (Ideal.absNorm v.asIdeal - 1))]
  exact Valuation.map_add_lt _ ((val_pow_sub_pow_le _ hx.le hy1.le _).trans_lt hy) hmem

theorem mem_maximalIdeal_iff (a : v.adicCompletionIntegers L) :
    a ∈ maximalIdeal (v.adicCompletionIntegers L) ↔ Valued.v (a : v.adicCompletion L) < 1 := by
  rw [mem_maximalIdeal, mem_nonunits_iff,
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  have h : Valued.v (a : v.adicCompletion L) ≤ 1 := a.2
  exact ⟨fun h' => lt_of_le_of_ne h h', fun h' => h'.ne⟩

theorem exists_rootOfUnity_congr {x : v.adicCompletion L} (hx : Valued.v x = 1) :
    ∃ ζ : v.adicCompletion L, ζ ^ (Ideal.absNorm v.asIdeal - 1) = 1 ∧ Valued.v (ζ - x) < 1 := by
  have hc : IsAdicComplete (maximalIdeal (v.adicCompletionIntegers L))
      (v.adicCompletionIntegers L) := by
    refine NormIntegers.isAdicComplete_of_fg (C := v.adicCompletion L) ⟨?_, ?_, ?_⟩
      (IsNoetherian.noetherian _) (maximalIdeal.isMaximal _).ne_top
    · exact FaithfulSMul.algebraMap_injective _ _
    · intro x
      have : ‖(x : v.adicCompletion L)‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.2 x.2
      exact_mod_cast this
    · intro x hx
      have : ‖x‖ ≤ 1 := by exact_mod_cast hx
      exact ⟨⟨x, Valued.toNormedField.norm_le_one_iff.1 this⟩, rfl⟩
  have hq := one_lt_absNorm v
  let a : v.adicCompletionIntegers L := ⟨x, hx.le⟩
  obtain ⟨ζ, h1, h2⟩ := HenselianRing.is_henselian (I := maximalIdeal (v.adicCompletionIntegers L))
    (X ^ (Ideal.absNorm v.asIdeal - 1) - C 1) (monic_X_pow_sub_C _ (by omega)) a
    (by
      rw [mem_maximalIdeal_iff]
      simpa [a] using valued_pow_sub_one_lt_one v hx)
    (by
      apply IsUnit.map
      rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
      have h3 : Valued.v (((Ideal.absNorm v.asIdeal - 1 : ℕ)) : v.adicCompletion L) = 1 := by
        rw [Nat.cast_sub hq.le, Nat.cast_one, Valuation.map_sub_swap]
        exact Valuation.map_one_sub_of_lt _ (valued_absNorm_lt_one v)
      simp [a, derivative_X_pow, hx, h3])
  refine ⟨ζ, ?_, ?_⟩
  · have h4 : ζ ^ (Ideal.absNorm v.asIdeal - 1) = 1 := by
      simpa [sub_eq_zero] using h1
    have h5 := congrArg (algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L)) h4
    rw [map_pow, map_one] at h5
    exact h5
  · have h6 := (mem_maximalIdeal_iff v _).1 h2
    rw [AddSubgroupClass.coe_sub] at h6
    exact h6

theorem orders_on_units : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)), (χ.TameAt v → ∀ x, IsUnitAt v x → χ.loc v x ^ (Ideal.absNorm v.asIdeal - 1) = 1) ∧ ((∀ x : (v.adicCompletion L)ˣ, x ^ (Ideal.absNorm v.asIdeal - 1) = 1 → χ.loc v x = 1) → ∀ x, IsUnitAt v x → ∃ n : ℕ, χ.loc v x ^ (Ideal.absNorm v.asIdeal ^ n) = 1) := by
  intro L _ _ χ v
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · rw [← map_pow]
    refine h _ (GlobalTheory.Mem.UnrAe.isUnitAt_pow hx _) ?_
    rw [Units.val_pow_eq_pow_val]
    simpa using le_exp_neg_one_of_lt_one (valued_pow_sub_one_lt_one v hx)
  · obtain ⟨n, hn⟩ := GlobalTheory.Mem.UnrAe.exists_levelLe χ v
    have hx' : Valued.v (x : v.adicCompletion L) = 1 := hx
    obtain ⟨ζ, h1, h2⟩ := exists_rootOfUnity_congr v hx'
    have hζ : Valued.v ζ = 1 := by
      rw [← hx']
      apply Valuation.map_eq_of_sub_lt
      rwa [hx']
    have h0 : ζ ≠ 0 := by
      rintro rfl
      simp at hζ
    let z : (v.adicCompletion L)ˣ := Units.mk0 ζ h0
    have hz : χ.loc v z = 1 := h z (Units.ext (by simpa [z] using h1))
    have hu : IsUnitAt v (x * z⁻¹) := by
      simp [IsUnitAt, z, hx', hζ]
    have hu1 : Valued.v (((x * z⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1) < 1 := by
      have e : ((x * z⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1 = (x - ζ) * ζ⁻¹ := by
        simp [z, sub_mul, h0]
      rw [e, map_mul, map_inv₀, hζ, inv_one, mul_one, Valuation.map_sub_swap]
      exact h2
    refine ⟨n, ?_⟩
    have h3 := hn _ (GlobalTheory.Mem.UnrAe.isUnitAt_pow hu (Ideal.absNorm v.asIdeal ^ n)) (by
      rw [Units.val_pow_eq_pow_val]
      exact val_pow_pow_sub_one_le _ (le_of_eq hu) hu1 (valued_absNorm_lt_one v) n)
    rwa [map_pow, map_mul, map_inv, hz, inv_one, mul_one] at h3

end GlobalTheory.Mem.WildChar
end

