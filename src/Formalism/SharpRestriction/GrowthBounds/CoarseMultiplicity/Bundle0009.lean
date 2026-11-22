import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0008
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.SymVarInlFst
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.MemIntPolOfCoeff
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0006
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0004

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.BlockWithThresholds
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.CovariantDegrees

section GlobalTheory

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero (KK O)] {N r : ℕ} [NeZero r]

abbrev blockWithThresholds (D : BlockData N) (thr : Fin D.T.q → WithTop ℤ) : BlockData N :=
  { D with T := { D.T with thr := thr } }

abbrev SSt (O : Type) [CommRing O] [IsDomain O] (r : ℕ) [NeZero r] (D : BlockData N) (thr : Fin D.T.q → WithTop ℤ) :
    Submodule O (MvPolynomial (BVar N r D.T.t) (KK O)) :=
  (blockWithThresholds D thr).SSZ O (r := r)

structure TieOK (D : BlockData N) : Prop where
  lt : ∀ i, D.T.pos i + 1 < N
  inj : ∀ i i', D.T.pos i = D.T.pos i' → i = i'
  sep : ∀ i i', D.T.pos i + 1 ≠ D.T.pos i'
  uW : ∀ i, D.T.pos i ≠ (D.uPos : ℕ) ∧ D.T.pos i + 1 ≠ (D.uPos : ℕ)
  vecE : ∀ i (h : D.T.pos i + 1 < N), D.LL.vec ⟨D.T.pos i + 1, h⟩ = false

def tailP (O : Type) [CommRing O] [IsDomain O] (r : ℕ) (D : BlockData N) (jp : ℕ)
    (y : MvPolynomial (Fin N × Fin r) (KK O)) (g : MvPolynomial (BVar N r D.T.t) (KK O)) :
    MvPolynomial (BVar N r D.T.t) (KK O) :=
  D.Eplus O (r := r) ^ jp * (∏ i, X (scalZ N r D.T.t (Fin.castSucc i)) ^ D.T.z i) *
    X (scalZ N r D.T.t (Fin.last D.T.t)) ^ D.zPlus * rename (chainEmb N r D.T.t) y * g

theorem gen_mem (D : BlockData N) (thr : Fin D.T.q → WithTop ℤ) {j : Fin D.T.t → ℕ} {jp : ℕ} (hL : D.LevelOK j jp)
    {y : MvPolynomial (Fin N × Fin r) (KK O)} (hy : y ∈ YjtZ O (r := r) (D.lettersAt j jp) D.T.J thr)
    {g : MvPolynomial (BVar N r D.T.t) (KK O)} (hg : g ∈ XiPolZ O N r D.T.t (D.B - jp)) :
    (∏ i, D.Ehat O (r := r) i ^ j i) * tailP O r D jp y g ∈ SSt O r D thr := by
  unfold SSt BlockData.SSZ
  apply Submodule.subset_span
  refine Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨jp, Set.mem_iUnion.2 ⟨hL, ⟨y, hy, g, hg, ?_⟩⟩⟩⟩
  unfold tailP
  simp only [mul_assoc]
  rfl

theorem SSt_mono (D : BlockData N) {thr thr' : Fin D.T.q → WithTop ℤ} (h : ∀ k, thr k ≤ thr' k) :
    SSt O r D thr ≤ SSt O r D thr' := by
  unfold SSt BlockData.SSZ
  apply Submodule.span_mono
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨j, jp, hL, hx⟩ := hx
  obtain ⟨y, hy, g0, hg0, rfl⟩ := hx
  exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨jp, Set.mem_iUnion.2 ⟨hL,
    ⟨y, ⟨yjt_mono' _ _ h hy.1, hy.2⟩, g0, hg0, rfl⟩⟩⟩⟩

def IsMult (O : Type) [CommRing O] [IsDomain O] (r : ℕ) [NeZero r] (vec : Fin N → Bool) {q : ℕ} (J : Fin q → ℕ)
    (aW aE : Fin N) (q0 : MvPolynomial (Fin N × Fin r) (KK O)) : Prop :=
  ∀ (deg : Fin N → ℕ) (thr : Fin q → WithTop ℤ) (y : MvPolynomial (Fin N × Fin r) (KK O)),
    y ∈ YjtZ O (r := r) ⟨vec, deg⟩ J thr →
    q0 * y ∈ YjtZ O (r := r) ⟨vec, fun a => deg a + if a = aW ∨ a = aE then 1 else 0⟩ J
      (fun k => thr k + ((1 : ℤ) : WithTop ℤ))

theorem IsMult.pow {vec : Fin N → Bool} {q : ℕ} {J : Fin q → ℕ} {aW aE : Fin N}
    {q0 : MvPolynomial (Fin N × Fin r) (KK O)} (h : IsMult O r vec J aW aE q0) (l : ℕ) (deg : Fin N → ℕ)
    (thr : Fin q → WithTop ℤ) (y : MvPolynomial (Fin N × Fin r) (KK O)) (hy : y ∈ YjtZ O (r := r) ⟨vec, deg⟩ J thr) :
    q0 ^ l * y ∈ YjtZ O (r := r) ⟨vec, fun a => deg a + if a = aW ∨ a = aE then l else 0⟩ J
      (fun k => thr k + ((l : ℤ) : WithTop ℤ)) := by
  induction l with
  | zero =>
    simpa using hy
  | succ l ih =>
    have h1 := h _ _ _ ih
    rw [pow_succ', mul_assoc]
    have e1 : (fun a => (deg a + if a = aW ∨ a = aE then l else 0) + if a = aW ∨ a = aE then 1 else 0) =
        fun a => deg a + if a = aW ∨ a = aE then l + 1 else 0 := by
      funext a
      split_ifs <;> omega
    have e2 : (fun k => thr k + ((l : ℤ) : WithTop ℤ) + ((1 : ℤ) : WithTop ℤ)) =
        fun k => thr k + (((l + 1 : ℕ) : ℤ) : WithTop ℤ) := by
      funext k
      rw [add_assoc]
      norm_cast
    rw [e1, e2] at h1
    exact h1

theorem isMult_XX (D7 : Formalism.BasicNotions.D7) (vec : Fin N → Bool) {q : ℕ} (J : Fin q → ℕ) (aW aE : Fin N) (hne : aW ≠ aE)
    (hE : vec aE = false) (c c' : Fin r) : IsMult O r vec J aW aE (X (aW, c) * X (aE, c')) := by
  intro deg thr y hy
  have h1 := yjtZ_X (O := O) D7 ⟨vec, deg⟩ ⟨vec, fun a => deg a + if a = aE then 1 else 0⟩ rfl aE c' (fun _ => rfl) J
    (thr := thr) (thr' := thr) 0 (fun h => by simp [hE] at h) (fun k => by simp) hy
  have h2 := yjtZ_X (O := O) D7 ⟨vec, fun a => deg a + if a = aE then 1 else 0⟩
    ⟨vec, fun a => deg a + if a = aW ∨ a = aE then 1 else 0⟩ rfl aW c
    (fun i => by
      show deg i + _ = deg i + _ + _
      by_cases h1 : i = aW
      · subst h1; simp [hne]
      · simp [h1]) J (thr := thr) (thr' := fun k => thr k + ((1 : ℤ) : WithTop ℤ)) 1 (fun _ => le_rfl)
    (fun k => by norm_cast) h1
  rw [mul_assoc]
  exact h2

theorem IsMult.neg {vec : Fin N → Bool} {q : ℕ} {J : Fin q → ℕ} {aW aE : Fin N}
    {q0 : MvPolynomial (Fin N × Fin r) (KK O)} (h : IsMult O r vec J aW aE q0) : IsMult O r vec J aW aE (-q0) := by
  intro deg thr y hy
  rw [neg_mul]
  exact Submodule.neg_mem _ (h deg thr y hy)

theorem IsMult.sum {vec : Fin N → Bool} {q : ℕ} {J : Fin q → ℕ} {aW aE : Fin N} {ι : Type} (s : Finset ι)
    {q0 : ι → MvPolynomial (Fin N × Fin r) (KK O)} (h : ∀ i ∈ s, IsMult O r vec J aW aE (q0 i)) :
    IsMult O r vec J aW aE (∑ i ∈ s, q0 i) := by
  intro deg thr y hy
  rw [Finset.sum_mul]
  exact Submodule.sum_mem _ fun i hi => h i hi deg thr y hy

end GlobalTheory

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.KeyOne
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

theorem liftSubst_one_X {p f : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF p f) O] (w : O) (r : ℕ)
    {ι : Type} {k : ℕ} (LL : LiftLetters ι) (v : ι × Fin k) :
    liftSubst p f O w r LL (1 : Matrix (Fin k) (Fin k) (WF p f)) (X v) =
      C (algebraMap O (KK O) (dW O w LL r v.1 v.2)) * X v := by
  unfold liftSubst
  rw [MvPolynomial.aeval_X, sigMat_one, inv_one]
  by_cases hv : LL.vec v.1 <;> simp [hv, Matrix.one_apply, dW] <;> split_ifs <;> simp_all

theorem liftSubst_one_hh {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (x : X.TT × Bool) (b : Fin (X.m + 1)) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) (1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'))
        (MvPolynomial.X (x, b)) =
      (if (x.2 = true ∧ 1 ≤ (b : ℕ)) ∨ (x.2 = false ∧ (b : ℕ) < 1) then
        C (algebraMap O (KK O) w) * MvPolynomial.X (x, b) else MvPolynomial.X (x, b)) := by
  rw [liftSubst_one_X]
  have hd : dW O w (hhLetters X.TT) 1 x b =
      if (x.2 = true ∧ 1 ≤ (b : ℕ)) ∨ (x.2 = false ∧ (b : ℕ) < 1) then w else 1 := rfl
  rw [hd]
  split_ifs <;> simp

private theorem liftSubst_X_true_zero_eq_X {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [Algebra (WF X.p X.n') O] (w : O) (y : X.TT) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) (1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'))
      (MvPolynomial.X ((y, true), (0 : Fin (X.m + 1)))) = MvPolynomial.X ((y, true), 0) := by
  rw [liftSubst_one_hh]
  simp

private theorem liftSubst_X_true_succ_eq_C_mul_X {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [Algebra (WF X.p X.n') O] (w : O) (y : X.TT) (c : Fin X.m) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) (1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'))
      (MvPolynomial.X ((y, true), c.succ)) =
        C (algebraMap O (KK O) w) * MvPolynomial.X ((y, true), c.succ) := by
  rw [liftSubst_one_hh]
  simp

private theorem liftSubst_X_false_zero_eq_C_mul_X {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [Algebra (WF X.p X.n') O] (w : O) (y : X.TT) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) (1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'))
      (MvPolynomial.X ((y, false), (0 : Fin (X.m + 1)))) =
        C (algebraMap O (KK O) w) * MvPolynomial.X ((y, false), 0) := by
  rw [liftSubst_one_hh]
  simp

private theorem liftSubst_X_false_succ_eq_X {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [Algebra (WF X.p X.n') O] (w : O) (y : X.TT) (c : Fin X.m) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) (1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'))
      (MvPolynomial.X ((y, false), c.succ)) = MvPolynomial.X ((y, false), c.succ) := by
  rw [liftSubst_one_hh]
  simp

theorem key3One_S {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 (kSkey O X j i) =
      w • (MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ (segDists X.TT j).get i) * MvPolynomial.X ((topOdd X j i, false), 0) +
        w ^ (X.p ^ (segDists X.TT j).get i - 1) • (∑ c : Fin X.m,
          MvPolynomial.X ((topStart X j, true), c.succ) ^ (X.p ^ (segDists X.TT j).get i) *
            MvPolynomial.X ((topOdd X j i, false), c.succ) : RHH O X) : RHH O X) := by
  have hq1 : 1 ≤ X.p ^ (segDists X.TT j).get i := Nat.one_le_pow _ _ (Fact.out : X.p.Prime).pos
  unfold kSkey
  rw [map_sum, Fin.sum_univ_succ]
  simp only [map_mul, map_pow, liftSubst_X_true_zero_eq_X, liftSubst_X_true_succ_eq_C_mul_X, liftSubst_X_false_zero_eq_C_mul_X, liftSubst_X_false_succ_eq_X]
  rw [Algebra.smul_def, Algebra.smul_def, MvPolynomial.algebraMap_apply,
    MvPolynomial.algebraMap_apply, map_pow, map_pow]
  obtain ⟨q', hq'⟩ : ∃ q', X.p ^ (segDists X.TT j).get i = q' + 1 :=
    ⟨_, (Nat.sub_add_cancel hq1).symm⟩
  rw [hq', Nat.add_sub_cancel]
  have hsum : ∑ c : Fin X.m, (C (algebraMap O (KK O) w) * MvPolynomial.X ((topStart X j, true), c.succ)) ^
      (q' + 1) * MvPolynomial.X ((topOdd X j i, false), c.succ) =
      C (algebraMap O (KK O) w) ^ (q' + 1) * ∑ c : Fin X.m,
        MvPolynomial.X ((topStart X j, true), c.succ) ^ (q' + 1) * MvPolynomial.X ((topOdd X j i, false), c.succ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hsum]
  ring

theorem key_lift_identity_lower {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) (c : Fin X.m) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 (kWkey O X j i c.succ) =
      w • (MvPolynomial.X ((topOdd X j i, true), c.succ) * MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ (segDists X.TT j).get i) -
        w ^ (X.p ^ (segDists X.TT j).get i - 1) •
          (MvPolynomial.X ((topOdd X j i, true), 0) *
            MvPolynomial.X ((topStart X j, true), c.succ) ^ (X.p ^ (segDists X.TT j).get i) : RHH O X) : RHH O X) := by
  have hq1 : 1 ≤ X.p ^ (segDists X.TT j).get i := Nat.one_le_pow _ _ (Fact.out : X.p.Prime).pos
  unfold kWkey
  simp only [map_sub, map_mul, map_pow, liftSubst_X_true_zero_eq_X, liftSubst_X_true_succ_eq_C_mul_X]
  rw [Algebra.smul_def, Algebra.smul_def, MvPolynomial.algebraMap_apply,
    MvPolynomial.algebraMap_apply, map_pow, map_pow]
  obtain ⟨q', hq'⟩ : ∃ q', X.p ^ (segDists X.TT j).get i = q' + 1 :=
    ⟨_, (Nat.sub_add_cancel hq1).symm⟩
  rw [hq', Nat.add_sub_cancel]
  ring

theorem loc4One {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (c : Fin X.m) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 (locC O X c.succ) =
      ∏ j : Fin (numSeg X.TT), MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ segG X.TT j - 1) -
        w ^ (∑ j : Fin (numSeg X.TT), (X.p ^ segG X.TT j - 1)) •
          (∏ j : Fin (numSeg X.TT), MvPolynomial.X ((topStart X j, true), c.succ) ^ (X.p ^ segG X.TT j - 1) : RHH O X) := by
  unfold locC
  simp only [map_sub, map_prod, map_pow, liftSubst_X_true_zero_eq_X, liftSubst_X_true_succ_eq_C_mul_X]
  rw [Algebra.smul_def, MvPolynomial.algebraMap_apply, map_pow, map_pow,
    ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  congr 1
  exact Finset.prod_congr rfl fun j _ => mul_pow _ _ _

def CoarseMultiplicityOrderBound : Prop :=
  ∀ (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X →
    ∀ (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)),
      ∀ g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g →
        InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (kSkey O X j i) 1 ∧
        ∀ c : Fin X.m, InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (kWkey O X j i c.succ) 1

def LocalOrderBound : Prop :=
  ∀ (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → 2 ≤ numSeg X.TT →
    ∀ (j0 : Fin (numSeg X.TT)) (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')), IsGLW g →
      ratPlane X.p X.n' 1 g ≠ ratPlane X.p X.n' 1 1 →
      InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (locR O X j0) 1

theorem third_key_of_order (h : CoarseMultiplicityOrderBound) : CoarseMultiplicityBoundAtIdentity := by
  intro X _ O _ _ _ _ S hSq hD j i
  exact ⟨fun g hg => h X O S hSq hD j i g hg, key3One_S S.w j i, fun c => key_lift_identity_lower S.w j i c⟩

theorem local_fourth_of_order (h : LocalOrderBound) : LocalBoundAtIdentity := by
  intro X _ O _ _ _ _ S hSq hD hn
  exact ⟨fun j0 g hg hr => h X O S hSq hD hn j0 g hg hr, fun c => loc4One S.w c⟩

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.LeadingExponentHomogeneous
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory MvPolynomial

theorem nat_split {O : Type} [CommRing O] [IsLocalRing O] {p : ℕ} (hp : p.Prime) (hpO : ¬ IsUnit (p : O)) {n : ℕ}
    (hn : n ≠ 0) : ∃ u : Oˣ, (n : O) = (p : O) ^ (n.factorization p) * u := by
  have hcop : Nat.Coprime (ordCompl[p] n) p := (Nat.coprime_ordCompl hp hn).symm
  have hunit : IsUnit ((ordCompl[p] n : ℕ) : O) := by
    by_contra hu
    have h1 := Nat.gcd_eq_gcd_ab (ordCompl[p] n) p
    rw [hcop] at h1
    have h2 : (1 : O) = ((ordCompl[p] n : ℕ) : O) * ((Nat.gcdA (ordCompl[p] n) p : ℤ) : O) +
        (p : O) * ((Nat.gcdB (ordCompl[p] n) p : ℤ) : O) := by
      have := congrArg (Int.cast : ℤ → O) h1
      simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_one, Int.cast_one] at this
      exact this
    have hm1 : ((ordCompl[p] n : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := hu
    have hm2 : (p : O) ∈ IsLocalRing.maximalIdeal O := hpO
    have h3 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      rw [h2]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hm1) (Ideal.mul_mem_right _ _ hm2)
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h3)
  refine ⟨hunit.unit, ?_⟩
  rw [IsUnit.unit_spec, ← Nat.cast_pow, ← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self]

theorem kap_transport {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} (hp : p.Prime) {w : O}
    (hw : Irreducible w) (h2 : w ^ 2 = (p : O)) {A B : ℕ} (hA : A ≠ 0) (hB : B ≠ 0) (E D : ℕ)
    (hlo : B.factorization p ≤ E + A.factorization p) (hhi : E + A.factorization p ≤ D + B.factorization p) :
    ∃ κ : O, κ ≠ 0 ∧ vLEO p κ (D : ℝ) ∧ (p : O) ^ E * (A : O) = κ * (B : O) := by
  have hpO := p_not_unit hw h2
  obtain ⟨uA, huA⟩ := nat_split hp hpO hA
  obtain ⟨uB, huB⟩ := nat_split hp hpO hB
  have hp0 : (p : O) ≠ 0 := by rw [← h2]; exact pow_ne_zero _ hw.ne_zero
  set n := E + A.factorization p - B.factorization p with hn
  have h1 : (p : O) ^ n ≠ 0 := pow_ne_zero _ hp0
  have hκ : (p : O) ^ n * uA * ((uB⁻¹ : Oˣ) : O) ≠ 0 := mul_ne_zero (mul_ne_zero h1 uA.ne_zero) (Units.ne_zero _)
  refine ⟨(p : O) ^ n * uA * ((uB⁻¹ : Oˣ) : O), hκ, ?_, ?_⟩
  · rw [vLEO_iff hw h2 hκ, dvr_order_mul (mul_ne_zero h1 uA.ne_zero) (Units.ne_zero _), dvr_order_mul h1 uA.ne_zero,
      dvr_order_pow hp0, dvr_order_unit_eq_zero uA.isUnit, dvr_order_unit_eq_zero (Units.isUnit _)]
    have hv : dvrOrderNat (p : O) = 2 := by rw [← h2, dvr_order_pow hw.ne_zero, nv_irr hw]
    rw [hv]
    have : (n : ℝ) ≤ D := by exact_mod_cast (by omega : n ≤ D)
    push_cast
    linarith
  · rw [huA, huB]
    have hu : ((uB⁻¹ : Oˣ) : O) * uB = 1 := by simp
    have hpw : (p : O) ^ E * (p : O) ^ A.factorization p = (p : O) ^ n * (p : O) ^ B.factorization p := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    linear_combination (uA : O) * hpw - ((p : O) ^ n * (p : O) ^ B.factorization p * uA) * hu

section

variable (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT))

def lvW (ℓ : ℕ) : BV C0 CE1 CE2 X j → ℕ := fun v => if symLev X.p C0 CE1 CE2 X j v = ℓ then 1 else 0

def lvL (ℓ : ℕ) : Fin (2 * segS X.TT j + 1 + 1) → ℕ :=
  fun a => if symLev X.p C0 CE1 CE2 X j (Sum.inl (a, 0)) = ℓ then 1 else 0

theorem lev_balanced (ℓ : ℕ) : Balanced X.m (X.seg C0 CE1 CE2 j) (lvW C0 CE1 CE2 X j ℓ) (lvL C0 CE1 CE2 X j ℓ) := by
  refine ⟨fun a c => rfl, ?_, ?_⟩
  · intro l
    have hi := (uTop (X.seg C0 CE1 CE2 j) l).2
    have e0 : finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ)) =
        Fin.castSucc (⟨2 * (uTop (X.seg C0 CE1 CE2 j) l).val, by omega⟩ : Fin (2 * segS X.TT j + 1)) :=
      Fin.ext (Nat.min_eq_left (by omega))
    have e1 : finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) + 1) =
        Fin.castSucc (⟨2 * (uTop (X.seg C0 CE1 CE2 j) l).val + 1, by omega⟩ : Fin (2 * segS X.TT j + 1)) :=
      Fin.ext (Nat.min_eq_left (by omega))
    unfold lvW lvL
    rw [sl_Z, sl_Z, e0, e1, symbol_level_lower_letter, sl_E]
  · unfold lvW lvL
    rw [symbol_level_last, symbol_level_last, sl_U, sl_xi]

theorem lev_const (b : SegBlock (segS X.TT j) X.m) (μ μ' : BV C0 CE1 CE2 X j →₀ ℕ) (hμ : HomExp C0 CE1 CE2 X j b μ)
    (hμ' : HomExp C0 CE1 CE2 X j b μ') (f : ℕ → ℕ) :
    ∏ v, f (symLev X.p C0 CE1 CE2 X j v) ^ μ v = ∏ v, f (symLev X.p C0 CE1 CE2 X j v) ^ μ' v := by
  classical
  have key : ∀ ν : BV C0 CE1 CE2 X j →₀ ℕ, HomExp C0 CE1 CE2 X j b ν →
      ∏ v, f (symLev X.p C0 CE1 CE2 X j v) ^ ν v =
        ∏ ℓ ∈ Finset.univ.image (symLev X.p C0 CE1 CE2 X j), f ℓ ^ (OmB X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j)
          (segAPlus X.TT X.aT j) b (lvW C0 CE1 CE2 X j ℓ) (lvL C0 CE1 CE2 X j ℓ)) := by
    intro ν hν
    rw [← Finset.prod_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image (symLev X.p C0 CE1 CE2 X j))
      (g := symLev X.p C0 CE1 CE2 X j) (fun v _ => Finset.mem_image_of_mem _ (Finset.mem_univ v))]
    refine Finset.prod_congr rfl fun ℓ _ => ?_
    rw [← hν _ _ (lev_balanced C0 CE1 CE2 X j ℓ), ← Finset.prod_pow_eq_pow_sum, Finset.prod_filter]
    refine Finset.prod_congr rfl fun v _ => ?_
    unfold lvW
    split_ifs with h
    · rw [h, mul_one]
    · rw [mul_zero, pow_zero]
  rw [key μ hμ, key μ' hμ']

def mu0F (b : SegBlock (segS X.TT j) X.m) : BV C0 CE1 CE2 X j → ℕ
  | Sum.inl (a, c) => if c = 0 then Fin.lastCases (motive := fun _ => ℕ) (X.seg C0 CE1 CE2 j).bPlus
      (fun a' => (segChain X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b).deg a') a else 0
  | Sum.inr (l, false) => Fin.lastCases (motive := fun _ => ℕ) (segAPlus X.TT X.aT j - b.oPlus)
      (fun l' => coarseA X.p (X.seg C0 CE1 CE2 j) b (uTop (X.seg C0 CE1 CE2 j) l') -
        b.o (uTop (X.seg C0 CE1 CE2 j) l')) l
  | Sum.inr (_, true) => 0

def mu0 (b : SegBlock (segS X.TT j) X.m) : BV C0 CE1 CE2 X j →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (mu0F C0 CE1 CE2 X j b)

theorem leading_exponent_homogeneous (b : SegBlock (segS X.TT j) X.m) : HomExp C0 CE1 CE2 X j b (mu0 C0 CE1 CE2 X j b) := by
  classical
  intro ω ωL hB
  obtain ⟨h1, -, -⟩ := hB
  show ∑ v, mu0F C0 CE1 CE2 X j b v * ω v = _
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
  have a1 : ∀ a : Fin (2 * segS X.TT j + 1 + 1), ∑ c : Fin X.m, mu0F C0 CE1 CE2 X j b (Sum.inl (a, c)) * ω (Sum.inl (a, c)) =
      Fin.lastCases (motive := fun _ => ℕ) (X.seg C0 CE1 CE2 j).bPlus
        (fun a' => (segChain X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b).deg a') a * ωL a := by
    intro a
    rw [Finset.sum_eq_single (0 : Fin X.m)]
    · simp only [mu0F, if_true, h1]
    · intro c _ hc
      simp only [mu0F, if_neg hc, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have a2 : ∀ l : Fin ((X.seg C0 CE1 CE2 j).t + 1), ∑ β : Bool, mu0F C0 CE1 CE2 X j b (Sum.inr (l, β)) * ω (Sum.inr (l, β)) =
      Fin.lastCases (motive := fun _ => ℕ) (segAPlus X.TT X.aT j - b.oPlus)
        (fun l' => coarseA X.p (X.seg C0 CE1 CE2 j) b (uTop (X.seg C0 CE1 CE2 j) l') -
          b.o (uTop (X.seg C0 CE1 CE2 j) l')) l * ω (Sum.inr (l, false)) := by
    intro l
    rw [Fintype.sum_bool]
    simp only [mu0F, zero_mul, zero_add]
  rw [Finset.sum_congr rfl fun a _ => a1 a, Finset.sum_congr rfl fun l _ => a2 l]
  have s1 : ∑ a : Fin (2 * segS X.TT j + 1 + 1), Fin.lastCases (motive := fun _ => ℕ) (X.seg C0 CE1 CE2 j).bPlus
        (fun a' => (segChain X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b).deg a') a * ωL a =
      ∑ a' : Fin (2 * segS X.TT j + 1), (segChain X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b).deg a' *
        ωL (Fin.castSucc a') + (X.seg C0 CE1 CE2 j).bPlus * ωL (Fin.last _) := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
  have s2 : ∑ l : Fin ((X.seg C0 CE1 CE2 j).t + 1), Fin.lastCases (motive := fun _ => ℕ) (segAPlus X.TT X.aT j - b.oPlus)
        (fun l' => coarseA X.p (X.seg C0 CE1 CE2 j) b (uTop (X.seg C0 CE1 CE2 j) l') -
          b.o (uTop (X.seg C0 CE1 CE2 j) l')) l * ω (Sum.inr (l, false)) =
      ∑ l' : Fin (X.seg C0 CE1 CE2 j).t, (coarseA X.p (X.seg C0 CE1 CE2 j) b (uTop (X.seg C0 CE1 CE2 j) l') -
          b.o (uTop (X.seg C0 CE1 CE2 j) l')) * ω (Sum.inr (Fin.castSucc l', false)) +
        (segAPlus X.TT X.aT j - b.oPlus) * ω (Sum.inr (Fin.last _, false)) := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
  rw [s1, s2]
  unfold OmB
  ring

def PhiB (b : SegBlock (segS X.TT j) X.m) : ℕ :=
  Rblk C0 CE1 CE2 X j b * ∏ v : BV C0 CE1 CE2 X j, (baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v)).factorial *
    (symLev X.p C0 CE1 CE2 X j v).factorial ^ (mu0 C0 CE1 CE2 X j b v)

end

def KapNumAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
      Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
      (facSeg X j).factorization X.p ≤ (X.m + 1) * lgSeg X j +
          (∏ x : X.TT × Bool, (cdeg C0 CE1 CE2 X j b x).factorial).factorization X.p +
          (PhiB C0 CE1 CE2 X j b).factorization X.p ∧
      (∏ x : X.TT × Bool, (cdeg C0 CE1 CE2 X j b x).factorial).factorization X.p +
          (PhiB C0 CE1 CE2 X j b).factorization X.p ≤ lgSeg X j + (facSeg X j).factorization X.p

theorem facSeg_ne (X : Loc) (j : Fin (numSeg X.TT)) : facSeg X j ≠ 0 := by
  have : 0 < facSeg X j := by
    unfold facSeg
    positivity
  omega

theorem PhiB_ne (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m) :
    PhiB C0 CE1 CE2 X j b ≠ 0 := by
  have : 0 < PhiB C0 CE1 CE2 X j b := by
    unfold PhiB Rblk
    positivity
  omega

theorem kapAt_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hN : KapNumAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    KapAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  classical
  intro X _ O _ _ _ w hw h2 hD1 hH hc j b hb
  have hp : X.p.Prime := hD1.1
  have hO : CharZero O := charZero_of_w hp hw h2
  have : CharZero (KK O) := charZero_of_injective_algebraMap (IsFractionRing.injective O (KK O))
  obtain ⟨n1, n2⟩ := hN X hD1 hH hc j b hb
  set sp := specConst X.p (X.seg C0 CE1 CE2 j) b with hsp
  have hsp0 : sp ≠ 0 := specConst_ne _ _ _
  have hc0 : (∏ x : X.TT × Bool, (cdeg C0 CE1 CE2 X j b x).factorial) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun x _ => Nat.factorial_ne_zero _
  have hvN : padicValNat X.p (Nblk C0 CE1 CE2 X j b) =
      (∏ x : X.TT × Bool, (cdeg C0 CE1 CE2 X j b x).factorial).factorization X.p + sp.factorization X.p := by
    rw [← Nat.factorization_def _ hp]
    unfold Nblk
    rw [Nat.factorization_mul hc0 hsp0]
    rfl
  have hBf : (facSeg X j * sp).factorization X.p = (facSeg X j).factorization X.p + sp.factorization X.p := by
    rw [Nat.factorization_mul (facSeg_ne X j) hsp0]
    rfl
  obtain ⟨κ, hκ0, hκv, hκ⟩ := kap_transport hp hw h2 (PhiB_ne C0 CE1 CE2 X j b) (mul_ne_zero (facSeg_ne X j) hsp0)
    ((X.m + 1) * lgSeg X j + padicValNat X.p (Nblk C0 CE1 CE2 X j b)) ((X.m + 2) * lgSeg X j)
    (by rw [hBf, hvN]; omega) (by
      rw [hBf, hvN]
      have : (X.m + 2) * lgSeg X j = (X.m + 1) * lgSeg X j + lgSeg X j := by ring
      omega)
  refine ⟨κ, hκ0, hκv, ?_⟩
  intro μ hμ
  have hΦ : Rblk C0 CE1 CE2 X j b * ∏ v : BV C0 CE1 CE2 X j,
      (baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v)).factorial * (symLev X.p C0 CE1 CE2 X j v).factorial ^ (μ v) =
      PhiB C0 CE1 CE2 X j b := by
    unfold PhiB
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      lev_const C0 CE1 CE2 X j b μ _ hμ (leading_exponent_homogeneous C0 CE1 CE2 X j b) Nat.factorial]
  have hΦK := congrArg (fun n : ℕ => (n : KK O)) hΦ
  simp only [Nat.cast_mul, Nat.cast_prod, Nat.cast_pow] at hΦK
  have hκK := congrArg (algebraMap O (KK O)) hκ
  simp only [map_mul, map_pow, map_natCast, Nat.cast_mul] at hκK
  have hf0 : (facSeg X j : KK O) ≠ 0 := Nat.cast_ne_zero.2 (facSeg_ne X j)
  unfold zSeg
  rw [mul_assoc (_ * _) _ _, hΦK, div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff hf0, ← pow_add, hκK]
  ring

end Formalism.MainNotions.ColumnSystems.Pf
end
end

