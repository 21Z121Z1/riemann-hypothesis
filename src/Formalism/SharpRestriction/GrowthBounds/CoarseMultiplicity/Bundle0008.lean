import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0007
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.PairedLiftAtOfIdentity
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0004

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.CharZeroOfW
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees MvPolynomial

theorem p_not_unit {O : Type} [CommRing O] {p : ℕ} {w : O} (hw : Irreducible w) (hpw : w ^ 2 = (p : O)) :
    ¬ IsUnit (p : O) := by
  rw [← hpw]
  intro h
  exact hw.not_isUnit (isUnit_of_mul_isUnit_left (by rwa [pow_two] at h))

theorem charZero_of_w {O : Type} [CommRing O] [IsDomain O] {p : ℕ} (hp : p.Prime) {w : O} (hw : Irreducible w)
    (hpw : w ^ 2 = (p : O)) : CharZero O := by
  have hp0 : (p : O) ≠ 0 := by rw [← hpw]; exact pow_ne_zero _ hw.ne_zero
  have hpu := p_not_unit hw hpw
  obtain ⟨c, hc⟩ := CharP.exists O
  rcases CharP.char_is_prime_or_zero O c with h | h
  · exfalso
    have hc0 : (c : O) = 0 := CharP.cast_eq_zero O c
    by_cases hcp : c = p
    · exact hp0 (hcp ▸ hc0)
    · have hcop : Nat.Coprime c p := (Nat.coprime_primes h hp).2 hcp
      obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
      have h1 : ((a * c + b * p : ℤ) : O) = 1 := by rw [hab]; simp
      push_cast at h1
      rw [hc0, mul_zero, zero_add] at h1
      exact hpu (IsUnit.of_mul_eq_one_right _ h1)
  · subst h
    exact CharP.charP_to_charZero O

def KapAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (w : O),
    Irreducible w → w ^ 2 = (X.p : O) → D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
      Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
      ∃ κ : O, κ ≠ 0 ∧ vLEO X.p κ (((X.m + 2) * lgSeg X j : ℕ) : ℝ) ∧
        ∀ μ, HomExp C0 CE1 CE2 X j b μ →
          zSeg (KK O) X j * (X.p : KK O) ^ padicValNat X.p (Nblk C0 CE1 CE2 X j b) * (Rblk C0 CE1 CE2 X j b : KK O) *
            (∏ v : BV C0 CE1 CE2 X j, ((baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v)).factorial : KK O) *
              ((symLev X.p C0 CE1 CE2 X j v).factorial : KK O) ^ (μ v)) =
          algebraMap O (KK O) κ * (specConst X.p (X.seg C0 CE1 CE2 j) b : KK O)

theorem lev_pow (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) :
    ∃ t, (X.seg C0 CE1 CE2 j).P X.p i = X.p ^ (t + 1) := by
  obtain ⟨s, ⟨-, -, -, h4⟩, h5⟩ := get_spec X.TT j i
  have hlt : (segDists X.TT j).get i < segG X.TT j := h5 ▸ h4
  refine ⟨segG X.TT j - (segDists X.TT j).get i - 1, ?_⟩
  show X.p ^ (segG X.TT j - (segDists X.TT j).get i) = _
  congr 1
  omega

theorem oddVar_data (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    (hb : Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b) (v : BV C0 CE1 CE2 X j)
    (hv : IsOddVar C0 CE1 CE2 X j v) :
    (∃ t, symLev X.p C0 CE1 CE2 X j v = X.p ^ (t + 1)) ∧
      baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v) < symLev X.p C0 CE1 CE2 X j v := by
  rcases v with ⟨a, c⟩ | ⟨l, bo⟩
  · have h : (a : ℕ) < 2 * segS X.TT j := hv
    simp only [symLev, symVar, dif_pos h]
    refine ⟨lev_pow C0 CE1 CE2 X j _, ?_⟩
    rw [baseExp_odd]
    simp only [Fin.succ_ne_zero, and_false, if_false, add_zero]
    split_ifs
    · exact (hb.1.1 _ _).1
    · exact (hb.1.1 _ _).2
  · have h : (l : ℕ) < (X.seg C0 CE1 CE2 j).t := hv
    simp only [symLev, symVar, dif_pos h]
    refine ⟨lev_pow C0 CE1 CE2 X j _, ?_⟩
    rw [baseExp_odd]
    have hz : ¬ ((uTop (X.seg C0 CE1 CE2 j) ⟨l, h⟩ : ℕ) < (X.seg C0 CE1 CE2 j).sigma) := by
      show ¬ ((X.seg C0 CE1 CE2 j).sigma + (l : ℕ) < (X.seg C0 CE1 CE2 j).sigma)
      omega
    simp only [hz, false_and, if_false, add_zero]
    split_ifs
    · exact (hb.1.1 _ _).1
    · exact (hb.1.1 _ _).2

theorem endVar_data (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    (v : BV C0 CE1 CE2 X j) (hv : ¬ IsOddVar C0 CE1 CE2 X j v) :
    symLev X.p C0 CE1 CE2 X j v = 1 ∧ baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v) = 0 := by
  rcases v with ⟨a, c⟩ | ⟨l, bo⟩
  · have h : ¬ (a : ℕ) < 2 * segS X.TT j := hv
    simp only [symLev, symVar, dif_neg h]
    exact ⟨trivial, baseExp_end C0 CE1 CE2 X j b _ _⟩
  · have h : ¬ (l : ℕ) < (X.seg C0 CE1 CE2 j).t := hv
    simp only [symLev, symVar, dif_neg h]
    exact ⟨trivial, baseExp_end C0 CE1 CE2 X j b _ _⟩

theorem factAt_of {D : Formalism.BasicNotions.D7} (h52 : Formalism.MainNotions.CovariantDegrees.FactorialUnitDecomposition D) {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ}
    (hK : KapAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) : FactAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  classical
  intro X _ O _ _ _ w hw h2 hD1 hH hc j b hb
  have hp : X.p.Prime := hD1.1
  have hpO := p_not_unit hw h2
  have hO : CharZero O := charZero_of_w hp hw h2
  have : CharZero (KK O) := charZero_of_injective_algebraMap (IsFractionRing.injective O (KK O))
  obtain ⟨κ, hκ0, hκv, hκ⟩ := hK X O w hw h2 hD1 hH hc j b hb
  have ht : ∀ v : BV C0 CE1 CE2 X j, ∃ t, IsOddVar C0 CE1 CE2 X j v → symLev X.p C0 CE1 CE2 X j v = X.p ^ (t + 1) := by
    intro v
    by_cases hv : IsOddVar C0 CE1 CE2 X j v
    · obtain ⟨t, ht⟩ := (oddVar_data C0 CE1 CE2 X j b hb v hv).1
      exact ⟨t, fun _ => ht⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose t ht using ht
  obtain ⟨T, q, hT, hfa⟩ := fact_abs h52 hp hD1.2.1 (BV C0 CE1 CE2 X j) (IsOddVar C0 CE1 CE2 X j) t
    (fun v => baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v)) (fun v => symLev X.p C0 CE1 CE2 X j v)
    (fun v hv => ⟨ht v hv, (oddVar_data C0 CE1 CE2 X j b hb v hv).2⟩)
    (fun v hv => endVar_data C0 CE1 CE2 X j b v hv) X.c
  have hq : ∀ ν, ∃ y : O, ν ∈ T → ((q ν : ℚ) : KK O) = algebraMap O (KK O) y := by
    intro ν
    by_cases hν : ν ∈ T
    · obtain ⟨y, hy⟩ := rat_int (O := O) (K := KK O) hp hpO (q ν) 0 (by simpa using (hT ν hν).2.2)
      exact ⟨y, fun _ => by rw [hy, pow_zero, one_mul]⟩
    · exact ⟨0, fun h => absurd h hν⟩
  choose qO hqO using hq
  refine ⟨κ, T, qO, hκ0, hκv, fun ν hν => ⟨(hT ν hν).1, (hT ν hν).2.1⟩, ?_⟩
  intro μ hμ
  obtain ⟨h, hh, heq⟩ := hfa μ
  obtain ⟨y, hy⟩ := rat_int (O := O) (K := KK O) hp hpO h X.c hh
  refine ⟨w ^ X.c * y, ?_⟩
  have hg : algebraMap O (KK O) (gEv T qO μ) =
      ((∑ ν ∈ T, q ν * ((ν.prod fun k i => (μ k).choose i : ℕ) : ℚ) : ℚ) : KK O) := by
    unfold gEv
    rw [map_sum, Rat.cast_sum]
    refine Finset.sum_congr rfl fun ν hν => ?_
    rw [map_mul, ← hqO ν hν, map_natCast, Rat.cast_mul, Rat.cast_natCast]
  have heqK := congrArg (fun x : ℚ => (x : KK O)) heq
  simp only [Rat.cast_mul, Rat.cast_prod, Rat.cast_natCast, Rat.cast_add, Rat.cast_one, Rat.cast_pow] at heqK
  have hsplit : (∏ x : BV C0 CE1 CE2 X j,
      ((baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j x)).factorial : KK O) * ((μ x).factorial : KK O) *
        ((symLev X.p C0 CE1 CE2 X j x).factorial : KK O) ^ (μ x)) =
      (∏ v : BV C0 CE1 CE2 X j, ((baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v)).factorial : KK O) *
        ((symLev X.p C0 CE1 CE2 X j v).factorial : KK O) ^ (μ v)) * ∏ v : BV C0 CE1 CE2 X j, ((μ v).factorial : KK O) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v _ => by ring
  have hmu : (expFact μ : KK O) = ∏ v : BV C0 CE1 CE2 X j, ((μ v).factorial : KK O) := by
    unfold expFact
    rw [Finsupp.prod_fintype _ _ (fun _ => rfl)]
    push_cast
    rfl
  have hW : (algebraMap O (KK O) (w ^ X.c)) ^ 2 = (X.p : KK O) ^ X.c := by
    rw [← map_pow, ← pow_mul, mul_comm, pow_mul, h2, map_pow, map_natCast]
  have hk := hκ μ hμ
  rw [expFact_ioExp, hg, hmu, map_add, map_one, map_mul, map_mul, Nat.cast_mul, Nat.cast_prod]
  rw [hsplit] at heqK
  linear_combination (zSeg (KK O) X j * (X.p : KK O) ^ padicValNat X.p (Nblk C0 CE1 CE2 X j b) *
      (Rblk C0 CE1 CE2 X j b : KK O)) * heqK +
    ((∏ v : BV C0 CE1 CE2 X j, ((μ v).factorial : KK O)) * (1 + (h : KK O))) * hk +
    (algebraMap O (KK O) κ * (specConst X.p (X.seg C0 CE1 CE2 j) b : KK O) *
      (∏ v : BV C0 CE1 CE2 X j, ((μ v).factorial : KK O))) * hy -
    (algebraMap O (KK O) κ * (specConst X.p (X.seg C0 CE1 CE2 j) b : KK O) *
      (∏ v : BV C0 CE1 CE2 X j, ((μ v).factorial : KK O)) * algebraMap O (KK O) y) * hW

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.DivDerZero
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.CovariantDegrees

section Y

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero (KK O)] {N r : ℕ} [NeZero r]

theorem ycond_op (D : Formalism.BasicNotions.D7) (LL LL' : ChainLetters N) (hv : LL'.vec = LL.vec) (j : ℕ) {M M' : WithTop ℤ} (n : ℕ)
    (hM : M + ((n : ℤ) : WithTop ℤ) ≤ M') (al be : Fin N × Fin r →₀ ℕ)
    (hn : vecDeg (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} al +
      covDeg (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} be ≤ n)
    {y : MvPolynomial (Fin N × Fin r) (KK O)} (hy : y ∈ YCond (KK O) (r := r) LL j M) :
    monomial al 1 * divDer be y ∈ YCond (KK O) (r := r) LL' j M' := by
  cases M' with
  | top => rw [PolBridge.ycond_top]; exact Submodule.mem_top
  | coe M' =>
    cases M with
    | top => simp at hM
    | coe M =>
      rw [PolBridge.mem_ycond_iff D] at hy ⊢
      rw [hv]
      have h1 := flt_op_lam1S (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} y al be n hn
      refine h1.trans ?_
      have h2 : M + (n : ℤ) ≤ M' := by exact_mod_cast hM
      calc lam1S (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} y + ((n : ℤ) : WithBot ℤ)
          ≤ ((M : ℤ) : WithBot ℤ) + ((n : ℤ) : WithBot ℤ) := by gcongr
        _ = ((M + (n : ℤ) : ℤ) : WithBot ℤ) := by norm_cast
        _ ≤ _ := by exact_mod_cast h2

theorem divDer_zero {R : Type} [CommSemiring R] {σ : Type} (F : MvPolynomial σ R) : divDer 0 F = F := by
  unfold divDer
  conv_rhs => rw [F.as_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp

theorem intPol_cth {σ : Type} (v : σ) (n : ℕ) {y : MvPolynomial σ (KK O)} (hy : y ∈ IntPol O σ) :
    cth v n y ∈ IntPol O σ := by
  rw [mem_integral_poly_iff_coeff] at hy ⊢
  intro m
  obtain ⟨o, ho⟩ := hy m
  exact ⟨o * (((m v).choose n : ℕ) : O), by rw [coeff_cth, ho, map_mul, map_natCast]⟩

theorem intPol_mul {σ : Type} {x y : MvPolynomial σ (KK O)} (hx : x ∈ IntPol O σ) (hy : y ∈ IntPol O σ) :
    x * y ∈ IntPol O σ := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a * b, by simp⟩

theorem intPol_X {σ : Type} (v : σ) : (X v : MvPolynomial σ (KK O)) ∈ IntPol O σ := ⟨X v, by simp⟩

theorem yjtZ_cth (D : Formalism.BasicNotions.D7) (LL : ChainLetters N) {q : ℕ} (J : Fin q → ℕ) {thr thr' : Fin q → WithTop ℤ} (n : ℕ)
    (hthr : ∀ k, thr k + ((n : ℤ) : WithTop ℤ) ≤ thr' k) (v : Fin N × Fin r)
    {y : MvPolynomial (Fin N × Fin r) (KK O)} (hy : y ∈ YjtZ O (r := r) LL J thr) :
    cth v n y ∈ YjtZ O (r := r) LL J thr' := by
  classical
  obtain ⟨⟨hy1, hy2⟩, hy3⟩ := hy
  refine ⟨⟨?_, ?_⟩, intPol_cth v n hy3⟩
  · unfold chPol Formalism.MainNotions.G.Pol at hy1 ⊢
    rw [SetLike.mem_coe, mem_restrictSupport_iff] at hy1 ⊢
    intro m hm
    apply hy1
    rw [Finset.mem_coe, mem_support_iff] at hm ⊢
    intro h0
    exact hm (by rw [coeff_cth, h0, zero_mul])
  · rw [SetLike.mem_coe, Submodule.mem_iInf] at hy2 ⊢
    intro k
    refine ycond_op D LL LL rfl (J k) n (hthr k) _ _ ?_ (hy2 k)
    by_cases hn : n = 0
    · subst hn; simp [vecDeg, covDeg]
    · simp only [vecDeg, covDeg, Finsupp.support_single_ne_zero _ hn, Finset.sum_singleton, Finsupp.single_eq_same]
      split_ifs with h1 h2 <;> first | omega | (exfalso; simp_all)

theorem yjtZ_X (D : Formalism.BasicNotions.D7) (LL LL' : ChainLetters N) (hv : LL'.vec = LL.vec) (a : Fin N) (c : Fin r)
    (hd : ∀ i, LL'.deg i = LL.deg i + if i = a then 1 else 0)
    {q : ℕ} (J : Fin q → ℕ) {thr thr' : Fin q → WithTop ℤ} (n : ℕ) (hn : LL.vec a = true → 1 ≤ n)
    (hthr : ∀ k, thr k + ((n : ℤ) : WithTop ℤ) ≤ thr' k)
    {y : MvPolynomial (Fin N × Fin r) (KK O)} (hy : y ∈ YjtZ O (r := r) LL J thr) :
    X (a, c) * y ∈ YjtZ O (r := r) LL' J thr' := by
  classical
  obtain ⟨⟨hy1, hy2⟩, hy3⟩ := hy
  refine ⟨⟨?_, ?_⟩, intPol_mul (intPol_X _) hy3⟩
  · unfold chPol Formalism.MainNotions.G.Pol at hy1 ⊢
    rw [SetLike.mem_coe, mem_restrictSupport_iff] at hy1 ⊢
    intro m hm
    rw [Finset.mem_coe, support_X_mul, Finset.mem_map] at hm
    obtain ⟨m0, hm0, rfl⟩ := hm
    have h0 := hy1 hm0
    intro i
    have h1 := h0 i
    simp only [multideg, addLeftEmbedding_apply, Finsupp.add_apply] at h1 ⊢
    rw [Finset.sum_add_distrib, h1, hd i, add_comm]
    congr 1
    by_cases hi : i = a
    · subst hi
      simp [Finsupp.single_apply]
    · have : ∀ x : Fin r, (Finsupp.single (a, c) 1 : Fin N × Fin r →₀ ℕ) (i, x) = 0 := by
        intro x
        rw [Finsupp.single_apply, if_neg]
        intro h
        exact hi (congrArg Prod.fst h).symm
      simp [this, hi]
  · rw [SetLike.mem_coe, Submodule.mem_iInf] at hy2 ⊢
    intro k
    have h := ycond_op D LL LL' hv (J k) n (hthr k) (Finsupp.single (a, c) 1) 0 ?_ (hy2 k)
    · rwa [divDer_zero] at h
    · simp only [vecDeg, covDeg, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton,
        Finsupp.single_eq_same, Finsupp.support_zero, Finset.sum_empty, add_zero]
      split_ifs with h1
      · exact hn h1.2
      · omega

end Y

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.RestRawTail1Of
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

def topStart (X : Loc) (j : Fin (numSeg X.TT)) : X.TT := ⟨segStart X.TT j, (start_mem X.TT j).1⟩

abbrev RHH (O : Type) [CommRing O] [IsDomain O] (X : Loc) := MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) (KK O)

def kSkey (O : Type) [CommRing O] [IsDomain O] (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) : RHH O X :=
  ∑ a : Fin (X.m + 1), MvPolynomial.X ((topStart X j, true), a) ^ (X.p ^ (segDists X.TT j).get i) * MvPolynomial.X ((topOdd X j i, false), a)

def kWkey (O : Type) [CommRing O] [IsDomain O] (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j))
    (c : Fin (X.m + 1)) : RHH O X :=
  MvPolynomial.X ((topOdd X j i, true), c) * MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ (segDists X.TT j).get i) -
    MvPolynomial.X ((topOdd X j i, true), 0) * MvPolynomial.X ((topStart X j, true), c) ^ (X.p ^ (segDists X.TT j).get i)

def locC (O : Type) [CommRing O] [IsDomain O] (X : Loc) (c : Fin (X.m + 1)) : RHH O X :=
  ∏ j : Fin (numSeg X.TT), MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ segG X.TT j - 1) -
    ∏ j : Fin (numSeg X.TT), MvPolynomial.X ((topStart X j, true), c) ^ (X.p ^ segG X.TT j - 1)

def locR (O : Type) [CommRing O] [IsDomain O] (X : Loc) (j0 : Fin (numSeg X.TT)) : RHH O X :=
  MvPolynomial.X ((topStart X j0, true), 0) * ∏ c : Fin X.m, locC O X c.succ

def CoarseMultiplicityBoundAtIdentity : Prop :=
  ∀ (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X →
    ∀ (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)),
      (∀ g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g →
        InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (kSkey O X j i) 1 ∧
        ∀ c : Fin X.m, InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (kWkey O X j i c.succ) 1) ∧
      liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) 1 (kSkey O X j i) =
        S.w • (MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ (segDists X.TT j).get i) * MvPolynomial.X ((topOdd X j i, false), 0) +
          S.w ^ (X.p ^ (segDists X.TT j).get i - 1) • (∑ c : Fin X.m,
            MvPolynomial.X ((topStart X j, true), c.succ) ^ (X.p ^ (segDists X.TT j).get i) *
              MvPolynomial.X ((topOdd X j i, false), c.succ) : RHH O X) : RHH O X) ∧
      ∀ c : Fin X.m, liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) 1 (kWkey O X j i c.succ) =
        S.w • (MvPolynomial.X ((topOdd X j i, true), c.succ) * MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ (segDists X.TT j).get i) -
          S.w ^ (X.p ^ (segDists X.TT j).get i - 1) •
            (MvPolynomial.X ((topOdd X j i, true), 0) *
              MvPolynomial.X ((topStart X j, true), c.succ) ^ (X.p ^ (segDists X.TT j).get i) : RHH O X) : RHH O X)

def LocalBoundAtIdentity : Prop :=
  ∀ (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → 2 ≤ numSeg X.TT →
    (∀ (j0 : Fin (numSeg X.TT)) (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')), IsGLW g →
      ratPlane X.p X.n' 1 g ≠ ratPlane X.p X.n' 1 1 →
      InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (locR O X j0) 1) ∧
    ∀ c : Fin X.m, liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) 1 (locC O X c.succ) =
      ∏ j : Fin (numSeg X.TT), MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ segG X.TT j - 1) -
        S.w ^ (∑ j : Fin (numSeg X.TT), (X.p ^ segG X.TT j - 1)) •
          (∏ j : Fin (numSeg X.TT), MvPolynomial.X ((topStart X j, true), c.succ) ^ (X.p ^ segG X.TT j - 1) : RHH O X)

def AsmRTAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  CoarseMultiplicityBoundAtIdentity → LocalBoundAtIdentity → RawTailAt1 C0 CYb Cde Ck CD Cb CE1 CE2 Cc

def RestAsmRT : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => AsmRTAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

theorem restRawTail1_of (h3 : CoarseMultiplicityBoundAtIdentity) (h4 : LocalBoundAtIdentity) (hA : RestAsmRT) : RestRawTail1 :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h => h h3 h4) hA

section Fac

variable {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra (WF X.p X.n') O]

structure IsFac (w : O) (f : RHH O X) (o : ℕ) (sg : RHH O X) : Prop where
  inA : InA f
  ord : ∀ g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g →
    InWjRg X.p X.n' O w 1 (hhLetters X.TT) g f o
  sym : InWj w (liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 f - (w ^ o) • sg) (o + 1)
  sgInt : InA sg

theorem isGLW_one' (k : ℕ) : IsGLW (1 : Matrix (Fin k) (Fin k) (WF X.p X.n')) := by
  unfold IsGLW
  rw [Matrix.det_one]
  exact isUnit_one

theorem IsFac.mul {w : O} {f f' sg sg' : RHH O X} {o o' : ℕ} (h : IsFac w f o sg) (h' : IsFac w f' o' sg') :
    IsFac w (f * f') (o + o') (sg * sg') where
  inA := by
    have := inWj_mul ((inA_iff_wj w).1 h.inA) ((inA_iff_wj w).1 h'.inA)
    exact (inA_iff_wj w).2 this
  ord := fun g hg => inWjRg_mul (h.ord g hg) (h'.ord g hg)
  sym := by
    have e : liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 (f * f') - (w ^ (o + o')) • (sg * sg') =
        (liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 f - (w ^ o) • sg) *
            liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 f' +
          ((w ^ o) • sg) * (liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 f' - (w ^ o') • sg') := by
      rw [map_mul, pow_add, mul_smul_mul_comm]
      ring
    rw [e]
    have a1 := inWj_mul h.sym (h'.ord 1 (isGLW_one' _))
    have a2 := inWj_mul (wj_smul_pow ((inA_iff_wj w).1 h.sgInt) o) h'.sym
    have e1 : o + 1 + o' = o + o' + 1 := by ring
    have e2 : 0 + o + (o' + 1) = o + o' + 1 := by ring
    rw [e1] at a1
    rw [e2] at a2
    exact (wjSub w (o + o' + 1)).add_mem a1 a2
  sgInt := by
    have := inWj_mul ((inA_iff_wj w).1 h.sgInt) ((inA_iff_wj w).1 h'.sgInt)
    exact (inA_iff_wj w).2 this

end Fac

end Formalism.MainNotions.ColumnSystems.Pf
end
end

