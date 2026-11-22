import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0155
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0082
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightTensor
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0236
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0204
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0243
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0244
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0013
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.Bundle0001
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0232
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0240
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0242

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogDerivQExpansionMulPrimePowCongr
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory.Glue.DlPow

open scoped MatrixGroups in

theorem _root_.GlobalTheory.Glue.DlPow.isAlgebraic_of_tower {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    {ε : Ω →+* ℂ} (X : _root_.GlobalTheory.KZ.Tower Ω ε) :
    Algebra.IsAlgebraic ℚ Ω := by
  refine ⟨fun c => ?_⟩
  obtain ⟨D, hD, hint⟩ := X.bdd (algebraMap Ω X.K c)
  obtain ⟨k, hk⟩ := hint 0
  have hc : (algebraMap Ω (HahnSeries ℚ Ω) c).coeff 0 = c := by
    rw [HahnSeries.algebraMap_apply']
    simp
  rw [AlgHom.commutes, hc] at hk
  have h1 : IsAlgebraic ℚ ((D : Ω) ^ k * c) := (hk.tower_top (A := ℚ)).isAlgebraic
  have hD' : ((D : ℚ) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hD.ne')
  have hc' : c = algebraMap ℚ Ω (((D : ℚ) ^ k)⁻¹) * ((D : Ω) ^ k * c) := by
    rw [← mul_assoc, ← map_natCast (algebraMap ℚ Ω), ← map_pow, ← map_mul, inv_mul_cancel₀ hD',
      map_one, one_mul]
  rw [hc']
  exact (isAlgebraic_algebraMap _).mul h1

open scoped MatrixGroups in
private lemma prim_pow_succ {Ω : Type} [Field Ω] {A : ValuationSubring Ω}
    {P : HahnSeries ℚ Ω} (hP : _root_.GlobalTheory.Glue.Prim A P) (k : ℕ) :
    _root_.GlobalTheory.Glue.Prim A (P ^ (k + 1)) := by
  induction k with
  | zero => rwa [zero_add, pow_one]
  | succ k ih =>
    rw [pow_succ]
    exact _root_.GlobalTheory.Glue.Prim.mul A _ _ ih hP

open scoped MatrixGroups in
private lemma theta_pow_succ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : ℚ)
    (P : HahnSeries ℚ Ω) (k : ℕ) :
    _root_.GlobalTheory.Glue.theta s (P ^ (k + 1)) =
      HahnSeries.C ((k + 1 : ℕ) : Ω) * P ^ k * _root_.GlobalTheory.Glue.theta s P := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, (_root_.GlobalTheory.Glue.theta_leibniz_add_const s _ _).1, ih]
    push_cast
    simp only [map_add, map_natCast, map_one]
    ring

open scoped MatrixGroups in
private lemma theta_one_coeff_mem_of_integral_den_one {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    (A : ValuationSubring Ω) {P : HahnSeries ℚ Ω} (hP : ∀ r, P.coeff r ∈ A)
    (hden : ∀ r, P.coeff r ≠ 0 → r.den = 1) (r : ℚ) :
    (_root_.GlobalTheory.Glue.theta 1 P).coeff r ∈ A := by
  show algebraMap ℚ Ω (1 * r) * P.coeff r ∈ A
  by_cases h : P.coeff r = 0
  · rw [h, mul_zero]
    exact zero_mem A
  · refine mul_mem ?_ (hP r)
    rw [one_mul, ← Rat.coe_int_num_of_den_eq_one (hden r h), map_intCast]
    exact intCast_mem A _

open scoped MatrixGroups in
private lemma hahnSeries_coeff_mul_mem_valuationSubring {Ω : Type} [Field Ω] (A : ValuationSubring Ω)
    {x y : HahnSeries ℚ Ω} (hx : ∀ r, x.coeff r ∈ A) (hy : ∀ r, y.coeff r ∈ A) (r : ℚ) :
    (x * y).coeff r ∈ A := by
  rw [HahnSeries.coeff_mul]
  exact sum_mem fun ij _ => mul_mem (hx _) (hy _)

open scoped MatrixGroups in
private lemma hahnSeries_coeff_pow_mem_valuationSubring {Ω : Type} [Field Ω] (A : ValuationSubring Ω)
    {x : HahnSeries ℚ Ω} (hx : ∀ r, x.coeff r ∈ A) (k : ℕ) (r : ℚ) : (x ^ k).coeff r ∈ A := by
  induction k generalizing r with
  | zero =>
    rw [pow_zero, HahnSeries.coeff_one]
    split_ifs
    · exact one_mem A
    · exact zero_mem A
  | succ k ih =>
    rw [pow_succ]
    exact hahnSeries_coeff_mul_mem_valuationSubring A ih hx r

open scoped MatrixGroups in

theorem _root_.GlobalTheory.Glue.DlPow.isDl_mul_lpow_cong : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : _root_.GlobalTheory.KZ.Tower Ω ε)
    (A : ValuationSubring Ω) (l : ℕ) [Fact l.Prime], (l : Ω) ∈ A.nonunits →
    ∀ (n : ℕ) (f u : X.K), f ≠ 0 → u ≠ 0 →
      X.sl (_root_.GlobalTheory.KZ.ofSL ModularGroup.T) u = u →
      ∀ φ φ' : HahnSeries ℚ Ω, _root_.GlobalTheory.Glue.IsDl X A l n 1 f φ →
        _root_.GlobalTheory.Glue.IsDl X A l n 1 (f * u ^ (l ^ n)) φ' →
          ∀ r, _root_.GlobalTheory.Glue.CgA A l n (φ.coeff r) (φ'.coeff r) := by
  intro Ω _ _ _ ε X A l _ hl n f u hf hu hT φ φ' hφ hφ' r
  have hj : ∃ g : ℂ → ℂ, DifferentiableOn ℂ g _root_.GlobalTheory.KZ.Hs ∧
      X.an X.jK = ↑g := by
    obtain ⟨g, h1, h2⟩ := X.j_hol
    exact ⟨g, h2, h1⟩
  have hden : ∀ x : X.K,
      X.sl (_root_.GlobalTheory.KZ.ofSL ModularGroup.T) x = x →
        ∀ s, (X.exp x).coeff s ≠ 0 → s.den = 1 := by
    intro x hx s hs
    have hmem : x ∈ _root_.GlobalTheory.Glue.KT X 1 := by
      rw [_root_.GlobalTheory.Glue.KT.mem_def, pow_one]
      exact hx
    simpa using (_root_.GlobalTheory.Glue.KTExp.mem_KT_iff ε X 1 one_pos x).1 hmem s hs
  have hu0 : _root_.GlobalTheory.Glue.IsDl X A l n 1 (u ^ (l ^ n)) 0 := by
    obtain ⟨a, b, κ, S, hκ, hab, hPa, hPb, hb, -⟩ :=
      _root_.GlobalTheory.exists_prim_frac_level_one ε X hj l A hl u hu
    have hbT := hb ModularGroup.T
    have haT : X.sl (_root_.GlobalTheory.KZ.ofSL ModularGroup.T) a = a := by
      have h1 := congrArg (X.sl (_root_.GlobalTheory.KZ.ofSL ModularGroup.T)) hab
      rw [map_mul, map_mul, hT, hbT, AlgEquiv.commutes, hab] at h1
      exact (mul_left_cancel₀ ((map_ne_zero _).2 hκ) h1).symm
    obtain ⟨k, hk⟩ : ∃ k, l ^ n = k + 1 :=
      ⟨l ^ n - 1, (Nat.succ_pred_eq_of_pos (pow_pos (Fact.out : l.Prime).pos n)).symm⟩
    have hl' : (l : Ω) ^ n = ((k + 1 : ℕ) : Ω) := by rw [← Nat.cast_pow, hk]
    have hPaA := hPa.1
    have hPbA := hPb.1
    unfold _root_.GlobalTheory.Glue.IsDl
    refine ⟨fun s => by simpa using zero_mem A, a ^ (l ^ n), b ^ (l ^ n), κ ^ (l ^ n),
      pow_ne_zero _ hκ, by rw [map_pow, ← mul_pow, ← mul_pow, hab], ?_, ?_, fun s => ?_⟩
    · rw [map_pow, hk]
      exact prim_pow_succ hPa k
    · rw [map_pow, hk]
      exact prim_pow_succ hPb k
    · rw [map_pow, map_pow, hk, theta_pow_succ, theta_pow_succ]
      set P := X.exp a
      set Q := X.exp b
      set W := P ^ k * Q ^ k *
        (_root_.GlobalTheory.Glue.theta 1 P * Q - P * _root_.GlobalTheory.Glue.theta 1 Q)
      have hW : W.coeff s ∈ A := by
        have hθP := theta_one_coeff_mem_of_integral_den_one A hPaA (hden a haT)
        have hθQ := theta_one_coeff_mem_of_integral_den_one A hPbA (hden b hbT)
        refine hahnSeries_coeff_mul_mem_valuationSubring A
          (hahnSeries_coeff_mul_mem_valuationSubring A (hahnSeries_coeff_pow_mem_valuationSubring A hPaA k)
            (hahnSeries_coeff_pow_mem_valuationSubring A hPbA k)) (fun t => ?_) s
        rw [HahnSeries.coeff_sub]
        exact sub_mem (hahnSeries_coeff_mul_mem_valuationSubring A hθP hPbA t)
          (hahnSeries_coeff_mul_mem_valuationSubring A hPaA hθQ t)
      have hexp : HahnSeries.C ((k + 1 : ℕ) : Ω) * P ^ k * _root_.GlobalTheory.Glue.theta 1 P *
          Q ^ (k + 1) -
          P ^ (k + 1) * (HahnSeries.C ((k + 1 : ℕ) : Ω) * Q ^ k * _root_.GlobalTheory.Glue.theta 1 Q) =
          HahnSeries.C ((k + 1 : ℕ) : Ω) * W := by
        simp only [W]
        ring
      unfold _root_.GlobalTheory.Glue.CgA
      refine ⟨-W.coeff s, neg_mem hW, ?_⟩
      rw [hexp, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, zero_mul, zero_mul,
        HahnSeries.coeff_zero, hl', smul_eq_mul]
      ring
  have h := (_root_.GlobalTheory.Glue.isDl_calc ε X hj l A hl n 1 f (u ^ (l ^ n)) φ 0).1
    hφ hu0
  simpa using _root_.GlobalTheory.Glue.isDl_unique ε X hj l A hl n 1 _ _ _ h hφ' r

end GlobalTheory.Glue.DlPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LowestKTypeOfIrreducibleGeneratedModule
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.LowestType

open GlobalTheory.TensorHW

variable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

noncomputable def zc (p q : ℕ) : Mat p q :=
  Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => 0))

lemma zc_eq : zc p q = ∑ i : Fin p, Eab (Sum.inl i) (Sum.inl i) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [zc, Eab, Matrix.sum_apply, Matrix.single_apply, Matrix.diagonal_apply]
  by_cases h : a = b
  · subst h; simp [Finset.filter_eq']
  · rw [if_neg h, eq_comm]
    simp only [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x - ⟨rfl, rfl⟩
    exact h rfl

lemma act_zc (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (x : V) :
    act (zc p q) x = ∑ i : Fin p, act (Eab (Sum.inl i) (Sum.inl i)) x := by
  rw [zc_eq, map_sum, LinearMap.sum_apply]

lemma zc_comm {X : Mat p q} (hX : IsKC X) : zc p q * X = X * zc p q := by
  ext a b
  rw [zc, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rcases a with a | a <;> rcases b with b | b
  · simp
  · simp [hX (.inl a) (.inr b) (by simp [sameBlock])]
  · simp [hX (.inr a) (.inl b) (by simp [sameBlock])]
  · simp

lemma kstable_eig {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsLieAct act) (t : ℂ) :
    KStable act (Module.End.eigenspace (act (zc p q)) t) := by
  intro X hX w hw
  rw [Module.End.mem_eigenspace_iff] at hw ⊢
  have h := hL (zc p q) X
  rw [zc_comm hX, sub_self, map_zero, eq_comm, sub_eq_zero] at h
  have h2 := LinearMap.congr_fun h w
  simp only [Module.End.mul_apply] at h2
  rw [h2, hw, map_smul]

lemma kstable_inf {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {A B : Submodule ℂ V}
    (hA : KStable act A) (hB : KStable act B) : KStable act (A ⊓ B) :=
  fun X hX w hw => ⟨hA X hX w hw.1, hB X hX w hw.2⟩

lemma wt_eig {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {μ : Ix p q → ℚ} {x : V}
    (hx : x ∈ wtSub act μ) :
    x ∈ Module.End.eigenspace (act (zc p q)) ((∑ i : Fin p, μ (Sum.inl i) : ℚ) : ℂ) := by
  rw [Module.End.mem_eigenspace_iff, act_zc]
  simp only [mem_wt.1 hx]
  rw [← Finset.sum_smul]
  push_cast
  rfl

lemma eig_le (f : Module.End ℂ V) (c : ℂ) (N : ℕ → Submodule ℂ V) (hN : (⨆ m, N m) = ⊤)
    (h : ∀ m : ℕ, N m ≤ f.eigenspace (c + m)) (t : ℂ) :
    f.eigenspace t ≤ ⨆ m : ℕ, ⨆ _ : c + m = t, N m := by
  intro x hx
  have h1 : (⊤ : Submodule ℂ V) ≤ (⨆ m : ℕ, ⨆ _ : c + m = t, N m) ⊔ ⨆ s, ⨆ _ : s ≠ t, f.eigenspace s := by
    rw [← hN]
    refine iSup_le fun m => ?_
    by_cases hm : c + m = t
    · exact le_sup_of_le_left (le_iSup₂_of_le m hm le_rfl)
    · exact le_sup_of_le_right (le_iSup₂_of_le (c + m) hm (h m))
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (h1 (Submodule.mem_top : x ∈ ⊤))
  have ha' : a ∈ f.eigenspace t := by
    refine (iSup₂_le fun m hm => ?_ : (⨆ m : ℕ, ⨆ _ : c + m = t, N m) ≤ f.eigenspace t) ha
    rw [← hm]; exact h m
  have hb' : b ∈ f.eigenspace t := by
    simpa using Submodule.sub_mem _ hx ha'
  have hd := Module.End.eigenspaces_iSupIndep f t
  have : b = 0 := (Submodule.disjoint_def.1 hd) b hb' hb
  simpa [this] using ha

lemma eig_mem (f : Module.End ℂ V) (c : ℂ) (N : ℕ → Submodule ℂ V) (hN : (⨆ m, N m) = ⊤)
    (h : ∀ m : ℕ, N m ≤ f.eigenspace (c + m)) (t : ℂ) {x : V} (hx : x ∈ f.eigenspace t) (h0 : x ≠ 0) :
    ∃ m : ℕ, t = c + m ∧ x ∈ N m := by
  have h1 := eig_le f c N hN h t hx
  by_cases hm : ∃ m : ℕ, c + m = t
  · obtain ⟨m, rfl⟩ := hm
    refine ⟨m, rfl, (iSup₂_le fun k hk => ?_ : (⨆ k : ℕ, ⨆ _ : c + k = c + m, N k) ≤ N m) h1⟩
    have : k = m := by exact_mod_cast add_left_cancel hk
    rw [this]
  · refine absurd ?_ h0
    exact (iSup₂_le fun k hk => absurd ⟨k, hk⟩ hm : (⨆ k : ℕ, ⨆ _ : c + k = t, N k) ≤ ⊥) h1

lemma eig_unique {f : Module.End ℂ V} {s t : ℂ} {x : V} (hs : x ∈ f.eigenspace s)
    (ht : x ∈ f.eigenspace t) (h0 : x ≠ 0) : s = t := by
  rw [Module.End.mem_eigenspace_iff] at hs ht
  exact smul_left_injective ℂ h0 (hs.symm.trans ht)

def rk : Ix p q → ℕ := Sum.elim (fun i => i.1) (fun j => p + j.1)

lemma rk_inj : Function.Injective (rk : Ix p q → ℕ) := by
  rintro (a | a) (b | b) h <;> simp only [rk, Sum.elim_inl, Sum.elim_inr] at h
  · rw [Fin.ext h]
  · have := a.2; omega
  · have := b.2; omega
  · rw [Fin.ext (add_left_cancel h)]

lemma same_equiv : Equivalence (sameBlock : Ix p q → Ix p q → Prop) := by
  refine ⟨same_refl, ?_, ?_⟩
  · rintro (a | a) (b | b) h <;> simp_all [sameBlock]
  · rintro (a | a) (b | b) (c | c) h h' <;> simp_all [sameBlock]

lemma pos_of_rk {a b : Ix p q} (h : sameBlock a b) (hr : rk a < rk b) : posC a b := by
  rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock, rk, posC]

lemma hw_irr {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsLieAct act) {W : Submodule ℂ V}
    (hW : KStable act W) (hirr : ∀ N : Submodule ℂ V, N ≤ W → KStable act N → N = ⊥ ∨ N = W)
    {μ : Ix p q → ℚ} {v : V} (hv : v ∈ W) (hh : IsHW act μ v) :
    (∀ x ∈ W, x ∈ wtSub act μ → ∃ c : ℂ, x = c • v) ∧
    ∀ (ν : Ix p q → ℚ), ∀ x ∈ W, x ≠ 0 → x ∈ wtSub act ν →
      ν = μ ∨ ∑ a, (rk a : ℚ) * μ a < ∑ a, (rk a : ℚ) * ν a := by
  obtain ⟨U, hvU, hS, hmin, h1, h2⟩ := GlobalTheory.ExtremalGen.exists_generated p q V act hL sameBlock same_equiv rk rk_inj μ v hh.2.1
    (fun a b hab hr => by
      have := hh.2.2
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, SetLike.mem_coe] at this
      exact this a b (pos_of_rk hab hr))
  have hUW : U ≤ W := hmin W hv fun a b hab _ x hx => hW _ (isKC_Eab (same_equiv.symm hab)) x hx
  have hU : U = W := by
    refine (hirr U hUW fun X hX w hw => kc_ind act U w (fun a b hab => hS a b hab w hw) hX).resolve_left ?_
    rintro rfl
    exact hh.1 (by simpa using hvU)
  subst hU
  exact ⟨h1, h2⟩

theorem lowest : ∀ (p q : ℕ) (M : GKMod p q) (Λ : Ix p q → ℚ) (W : Submodule ℂ M.V), IrrGK M → FiniteDimensional ℂ W → KStable M.act W → (∀ N : Submodule ℂ M.V, N ≤ W → KStable M.act N → N = ⊥ ∨ N = W) → (∃ e ∈ W, IsHW M.act Λ e) → (∀ e ∈ W, KilledByLower M.act e) → genSub M.act (W : Set M.V) = ⊤ → IsLowestType M Λ W ∧ Module.finrank ℂ ↥(hwSub M.act Λ) = 1 ∧ ∃ N : ℕ → Submodule ℂ M.V, (∀ m, FiniteDimensional ℂ (N m)) ∧ (⨆ m, N m) = ⊤ ∧ ∀ m : ℕ, ∀ x ∈ N m, ∑ i : Fin p, M.act (Eab (Sum.inl i) (Sum.inl i)) x = (((∑ i : Fin p, Λ (Sum.inl i) : ℚ) : ℂ) + m) • x := by
  intro p q M Λ W hM hfd hW hirr hex hlow hgen
  obtain ⟨e, heW, he⟩ := hex
  set c : ℂ := ((∑ i : Fin p, Λ (Sum.inl i) : ℚ) : ℂ) with hc
  have hWc : W ≤ Module.End.eigenspace (M.act (zc p q)) c := by
    rcases hirr _ inf_le_left (kstable_inf hW (kstable_eig M.lie c)) with h | h
    · exact absurd ((Submodule.eq_bot_iff _).1 h e ⟨heW, wt_eig he.2.1⟩) he.1
    · exact h.ge.trans inf_le_right
  obtain ⟨N, hN0, hNfd, hNtop, hN⟩ := GlobalTheory.FockGrade.exists_grading p q M.V M.act M.lie W c hfd hW hlow
    (fun x hx => by rw [← act_zc]; exact Module.End.mem_eigenspace_iff.1 (hWc hx))
  rw [hgen] at hNtop
  have hNe : ∀ m : ℕ, N m ≤ Module.End.eigenspace (M.act (zc p q)) (c + m) := fun m x hx => by
    rw [Module.End.mem_eigenspace_iff, act_zc]; exact hN m x hx
  have hcW : Module.End.eigenspace (M.act (zc p q)) c ≤ W := by
    intro x hx
    by_cases h0 : x = 0
    · rw [h0]; exact W.zero_mem
    obtain ⟨m, hm, hxm⟩ := eig_mem _ c N hNtop hNe c hx h0
    have : m = 0 := by exact_mod_cast left_eq_add.1 hm
    rwa [this, hN0] at hxm
  have hline := hw_irr M.lie hW hirr heW he
  refine ⟨⟨hM, hfd, hW, hirr, ⟨e, heW, he⟩, fun x => ⟨fun hx => ⟨W, hfd, hx, hW, ?_⟩, ?_⟩, hlow, hgen, ?_⟩, ?_,
    N, hNfd, hNtop, hN⟩
  · intro ν w hw hh
    rcases hline.2 ν w hw hh.1 hh.2.1 with h | h
    · exact h
    rcases (hw_irr M.lie hW hirr hw hh).2 Λ e heW he.1 he.2.1 with h' | h'
    · exact h'.symm
    · exact absurd h (not_lt.2 h'.le)
  · rintro ⟨W', hfd', hx, hW', hall⟩
    have h1 := GlobalTheory.WeightDecomp.mem_iSup_inf_wtSub p q M.V M.act W' (fun a y hy => hW' _ (isKC_Eab (same_refl a)) y hy) x hx (M.wts x)
    refine (iSup_le fun μ y hy => ?_ : (⨆ μ : Ix p q → ℚ, W' ⊓ wtSub M.act μ) ≤ W) h1
    by_cases h0 : y = 0
    · rw [h0]; exact W.zero_mem
    have hy2 := wt_eig hy.2
    have := hfd'
    obtain ⟨ν, v, hv, hh⟩ := GlobalTheory.ExistsHW.exists_highestWeight p q M _
      (Submodule.finiteDimensional_of_le inf_le_left) (kstable_inf hW' (kstable_eig M.lie
        ((∑ i : Fin p, μ (Sum.inl i) : ℚ) : ℂ)))
      (fun h => h0 ((Submodule.eq_bot_iff _).1 h y ⟨hy.1, hy2⟩))
    obtain rfl := hall ν v hv.1 hh
    have := eig_unique hv.2 (wt_eig hh.2.1) hh.1
    rw [this] at hy2
    exact hcW hy2
  · intro μ x h0 hx
    obtain ⟨m, hm, hxm⟩ := eig_mem _ c N hNtop hNe _ (wt_eig hx) h0
    refine ⟨m, by rw [hc] at hm; exact_mod_cast hm, ?_, fun hxW => ?_⟩
    · rintro rfl
      rwa [hN0] at hxm
    · have := eig_unique (hWc hxW) (hNe m hxm) h0
      exact_mod_cast left_eq_add.1 this
  · have : hwSub M.act Λ = Submodule.span ℂ {e} := by
      refine le_antisymm (fun x hx => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 he.2)
      obtain ⟨a, rfl⟩ := hline.1 x (hcW (wt_eig hx.1)) hx.1
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e)
    rw [this]
    exact finrank_span_singleton he.1

end GlobalTheory.LowestType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanSquareOrthoProductThetaEqProdStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.meanSquare_orthoProductTheta_eq_prod : ∀ (D : D7) (T : Tor D) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ T.abelian₂ = AddSubgroup.closure {w₁, w₂}) → (∀ i j, coordB D T b i (embV D T (b j)) = if i = j then 1 else 0) → (∀ z : VC D N N', z = ∑ j, coordB D T b j z • embV D T (b j)) → ∀ g : ℂ → ℂ, Continuous g → (∀ ω ∈ T.abelian₂, ∀ z, ‖U1 T.abelian₂ ω g z‖ = ‖g z‖) → normSq D T (LaB D T b) (pullB D T b g) = nrm1Sq T.abelian₂ g ^ r := by
  first | exact @GlobalTheory.PullNorm.normSq_pullB | exact GlobalTheory.PullNorm.normSq_pullB | (intros; apply GlobalTheory.PullNorm.normSq_pullB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemISupInfWeightSubmoduleOfDiagonalStableStatement
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_iSup_inf_weightSubmodule_of_diagonal_stable : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V), (∀ a, ∀ x ∈ N, act (Eab a a) x ∈ N) → ∀ x ∈ N, x ∈ (⨆ μ : Ix p q → ℚ, wtSub act μ) → x ∈ ⨆ μ : Ix p q → ℚ, N ⊓ wtSub act μ := by
  first | exact @GlobalTheory.WeightDecomp.mem_iSup_inf_wtSub | exact GlobalTheory.WeightDecomp.mem_iSup_inf_wtSub | (intros; apply GlobalTheory.WeightDecomp.mem_iSup_inf_wtSub <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MonomialDerivCauchyBoundGaussianGrowthStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monomialDeriv_cauchy_bound_gaussianGrowth : ∀ (D : D7) (N N' : ℕ) (G : VC D N N' → ℂ) (S A B : ℝ), 0 < A → 1 ≤ B → 0 ≤ S → Differentiable ℂ G → (∀ z, ‖G z‖ ^ 2 ≤ S * Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / A)) → ∀ α : Mono D N N', (∀ k, (α k : ℝ) ≤ 2 * B) → ‖(α.prod fun _ n => (n.factorial : ℂ)) * taylor D G α‖ ^ 2 ≤ S * (2 * Real.exp 1 * Real.pi * B / A) ^ (α.sum fun _ n => n) := by
  first | exact @GlobalTheory.GaussCauchy.monomial_deriv_bound | exact GlobalTheory.GaussCauchy.monomial_deriv_bound | (intros; apply GlobalTheory.GaussCauchy.monomial_deriv_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NabIndepAndDelIndepLocalConditions
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

namespace GlobalTheory.TestLat

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}

theorem isBasisAt_inv_mul (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) (Fin n → K)) (B B' : GL (Fin n) K)
    (h : IsBasisAt w M B) (h' : IsBasisAt w M B') : IsBasisAt w (colLat 1) (B'⁻¹ * B) := by
  rw [← isBasisAt_gLat w B', ← colLat_mul, mul_one, mul_inv_cancel_left]
  exact h'.symm.trans h

theorem indep_of_stable (lam : ι → DomWeight n) (w : HeightOneSpectrum (𝓞 K)) (T : Submodule (𝓞 K) (Pol K ι n))
    (hT : ∀ g : ι → GL (Fin n) K, (∀ τ, IsBasisAt w (colLat 1) (g τ)) → ∀ F ∈ T, actP lam g F ∈ T)
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (B B' : ι → GL (Fin n) K)
    (h : ∀ τ, IsBasisAt w (M τ) (B τ)) (h' : ∀ τ, IsBasisAt w (M τ) (B' τ)) (F : Pol K ι n) :
    actP lam B⁻¹ F ∈ T ↔ actP lam B'⁻¹ F ∈ T := by
  constructor
  · intro hF
    have := hT (B'⁻¹ * B) (fun τ => isBasisAt_inv_mul w (M τ) (B τ) (B' τ) (h τ) (h' τ)) _ hF
    rwa [← polyAction_mul, mul_inv_cancel_right] at this
  · intro hF
    have := hT (B⁻¹ * B') (fun τ => isBasisAt_inv_mul w (M τ) (B' τ) (B τ) (h' τ) (h τ)) _ hF
    rwa [← polyAction_mul, mul_inv_cancel_right] at this

theorem nabIndep_and_delIndep : NabIndep ∧ DelIndep :=
  ⟨fun K _ _ ι _ n lam w M B B' h h' F =>
      indep_of_stable lam w _ (GlobalTheory.T.polyAction_mem_locP_nabStd_of_isBasisAt K ι n lam w) M B B' h h' F,
    fun K _ _ ι _ n lam w M B B' h h' F =>
      indep_of_stable lam w _ (GlobalTheory.T.polyAction_mem_locP_delStd_of_isBasisAt K ι n lam w) M B B' h h' F⟩

end GlobalTheory.TestLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NegRankMulLogLeLogCovolumeHermitianStatement
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.neg_rank_mul_log_le_log_covolume_hermitian : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (v₀ : InfinitePlace K), IsConjAt v₀ → ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) K) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), IsRatHerm (cmMax K) H X → ∀ (s : ℕ), 0 < s → ∀ L : Submodule (𝓞 K) (Fin d → K), L.FG → (∀ x ∈ L, ∀ y ∈ L, (s : K) * (star x ⬝ᵥ H *ᵥ y) ∈ (algebraMap (𝓞 K) K).range) → -((Formalism.HN.rkK L : ℝ) * Real.log s) ≤ lcv X L := by
  first | exact @GlobalTheory.neg_rank_mul_log_le_lcv | exact GlobalTheory.neg_rank_mul_log_le_lcv | (intros; apply GlobalTheory.neg_rank_mul_log_le_lcv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniquenessStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oddThetaFunction_existence_uniqueness : ∀ (Λ : AddSubgroup ℂ), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) → (Differentiable ℂ (sgStar Λ) ∧ deriv (sgStar Λ) 0 = 1 ∧ (∀ z, sgStar Λ (-z) = -sgStar Λ z) ∧ ∀ ω ∈ Λ, ∀ z, U1 Λ ω (sgStar Λ) z = (if ω / 2 ∈ Λ then 1 else -1) * sgStar Λ z) ∧ (∀ z, sgStar Λ z = 0 ↔ z ∈ Λ) ∧ (∀ G : ℂ → ℂ, Differentiable ℂ G → (∀ ω ∈ Λ, ∀ z, U1 Λ ω G z = (if ω / 2 ∈ Λ then 1 else -1) * G z) → ∀ z, G z = deriv G 0 * sgStar Λ z) ∧ (∀ u v : ℂ, u ∉ Λ → v ∉ Λ → (wpF Λ u - wpF Λ v) * (sgStar Λ u ^ 2 * sgStar Λ v ^ 2) = -(sgStar Λ (u + v) * sgStar Λ (u - v))) ∧ ∀ c : ℂ, c ≠ 0 → ∀ z, sgStar (Λ.map (AddMonoidHom.mulLeft c)) (c * z) = c * sgStar Λ z := by
  first | exact @GlobalTheory.OddTheta.sgStar_laws | exact GlobalTheory.OddTheta.sgStar_laws | (intros; apply GlobalTheory.OddTheta.sgStar_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthoProductThetaMemThetaSpaceOfLatticeStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthoProductTheta_mem_thetaSpace_of_lattice : ∀ (D : D7) (T : Tor D) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (g : ℂ → ℂ), (∀ z w : VC D N N', ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j) = ∑ k, coordB D T b k z * (starRingEnd ℂ) (coordB D T b k w)) → (∀ x : VC D N N', x ∈ LaB D T b ↔ ∀ k, coordB D T b k x ∈ T.abelian₂) → Differentiable ℂ g → (∀ ω ∈ T.abelian₂, ∃ m : ℤ, q1 D T.abelian₂ ω = m ∧ ∀ z, (-1 : ℂ) ^ m * U1 T.abelian₂ ω g z = g z) → pullB D T b g ∈ ThSp D T (LaB D T b) := by
  first | exact @GlobalTheory.ProdTheta.pullB_mem_ThSp | exact GlobalTheory.ProdTheta.pullB_mem_ThSp | (intros; apply GlobalTheory.ProdTheta.pullB_mem_ThSp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthonormalBasisGaloisMapStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthonormalBasis_galois_map : ∀ (D : D7) (σ : D.host.E ≃ₐ[ℚ] D.host.E), (∀ a : D.host.K, σ (a : D.host.E) = (a : D.host.E)) → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → OnB D (fun j => (b j).map σ) := by
  first | exact @GlobalTheory.NormSum.onB_map_aut | exact GlobalTheory.NormSum.onB_map_aut | (intros; apply GlobalTheory.NormSum.onB_map_aut <;> assumption)
end

