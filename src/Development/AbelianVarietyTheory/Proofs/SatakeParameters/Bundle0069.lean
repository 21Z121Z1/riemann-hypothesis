import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0060
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0064
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0063
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0065
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008
import ReciprocityTheory.Hypotheses.GalCoh
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0066
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaCharMulInvEqOne

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCofactorTwistDualWeyl
section
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

namespace GlobalTheory.ValCmp

theorem initMinor_mem_dualWeyl_ind (R : Type) [CommRing R] {r n s : ℕ} (hs : s ≤ n) (I : Fin s → Fin r) :
    initMinor R I hs ∈ dualWeyl R r n (fun t => if t.val < s then 1 else 0) := by
  have h := bidetMem R r n 1 (fun _ => s) (fun _ => hs) (fun _ => I)
  have e1 : bideterminant R (fun _ : Fin 1 => s) (fun _ => hs) (fun _ => I) = initMinor R I hs := by
    simp [bideterminant]
  have e2 : (shapeDeg (fun _ : Fin 1 => s) : Fin n → ℕ) = fun t => if t.val < s then 1 else 0 := by
    funext t
    by_cases ht : t.val < s <;> simp [shapeDeg, ht]
  rwa [e1, e2] at h

private lemma one_mem_dualWeyl_zero (R : Type) [CommRing R] (r n : ℕ) :
    (1 : MvPolynomial (Fin r × Fin n) R) ∈ dualWeyl R r n 0 := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule]
  exact ⟨isWeightedHomogeneous_one R _, fun l j _ => by rw [map_one, map_one]⟩

private lemma mul_mem_dualWeyl_add (R : Type) [CommRing R] {r n : ℕ} {ν₁ ν₂ : Fin n → ℕ}
    {f g : MvPolynomial (Fin r × Fin n) R} (hf : f ∈ dualWeyl R r n ν₁) (hg : g ∈ dualWeyl R r n ν₂) :
    f * g ∈ dualWeyl R r n (ν₁ + ν₂) := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule] at hf hg ⊢
  refine ⟨hf.1.mul hg.1, fun l j hlj => ?_⟩
  rw [map_mul, map_mul, hf.2 l j hlj, hg.2 l j hlj]

theorem prod_mem_dualWeyl_sum (R : Type) [CommRing R] {r n : ℕ} {ι : Type} (S : Finset ι) (w : ι → Fin n → ℕ)
    (g : ι → MvPolynomial (Fin r × Fin n) R) (hg : ∀ k, g k ∈ dualWeyl R r n (w k)) :
    ∏ k ∈ S, g k ∈ dualWeyl R r n (∑ k ∈ S, w k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using one_mem_dualWeyl_zero R r n
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact mul_mem_dualWeyl_add R (hg a) ih

theorem exists_cofAct_initMinor (R : Type) [CommRing R] [IsDomain R] {n s : ℕ} (hs : s ≤ n) (I : Fin s → Fin n) :
    ∃ g ∈ dualWeyl R n n (fun t => if 0 < s ∧ t.val < n - s then 1 else 0),
      (genM R n).det ^ (s - 1) * g = cofAct R n (initMinor R I hs) := by
  classical
  rcases Nat.eq_zero_or_pos s with rfl | h1
  · refine ⟨1, ?_, ?_⟩
    · convert one_mem_dualWeyl_zero R n n using 2
      funext t
      simp
    · simp [initMinor]
  by_cases hI : Function.Injective I
  · obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin n), ∀ a, σ (Fin.castLE hs a) = I a := by
      let e : {x // x ∈ Set.range (Fin.castLE hs)} ≃ {x // x ∈ Set.range I} :=
        (Equiv.ofInjective _ (Fin.castLE_injective hs)).symm.trans (Equiv.ofInjective I hI)
      refine ⟨e.extendSubtype, fun a => ?_⟩
      rw [Equiv.extendSubtype_apply_of_mem e _ ⟨a, rfl⟩]
      simp only [e, Equiv.trans_apply]
      rw [Equiv.ofInjective_symm_apply]
      rfl
    obtain ⟨ε, hε⟩ := cofAct_initMinor R n s hs h1 σ
    have hIσ : (fun a : Fin s => σ (Fin.castLE hs a)) = I := funext hσ
    rw [hIσ] at hε
    refine ⟨(ε : ℤ) • initMinor R (fun a : Fin (n - s) => σ (Fin.rev (Fin.castLE (Nat.sub_le n s) a)))
      (Nat.sub_le n s), ?_, ?_⟩
    · have hm := initMinor_mem_dualWeyl_ind R (Nat.sub_le n s)
        (fun a : Fin (n - s) => σ (Fin.rev (Fin.castLE (Nat.sub_le n s) a)))
      have hw : (fun t : Fin n => if 0 < s ∧ t.val < n - s then 1 else 0) =
          fun t : Fin n => if t.val < n - s then 1 else 0 := by
        funext t
        simp [h1]
      rw [hw]
      exact zsmul_mem hm _
    · rw [hε, mul_smul_comm]
  · refine ⟨0, zero_mem _, ?_⟩
    simp only [Function.Injective, not_forall, exists_prop] at hI
    obtain ⟨a, b, hab, hne⟩ := hI
    have h0 : initMinor R I hs = 0 := by
      unfold initMinor
      exact Matrix.det_zero_of_row_eq hne (by funext q; simp [hab])
    rw [h0, map_zero, mul_zero]

theorem nuDual_shapeDeg {m K : ℕ} (sz : Fin K → ℕ) :
    nuDual (shapeDeg sz : Fin (m + 1) → ℕ) =
      ∑ k, fun t : Fin (m + 1) => if 0 < sz k ∧ t.val < m + 1 - sz k then 1 else 0 := by
  funext t
  have key : ∀ k, ((if t.rev.val < sz k then 1 else 0) +
      (if 0 < sz k ∧ t.val < m + 1 - sz k then 1 else 0) : ℕ) =
        if (0 : Fin (m + 1)).val < sz k then 1 else 0 := by
    intro k
    have := t.isLt
    rw [Fin.val_rev]
    split_ifs <;> (try simp only [Fin.val_zero] at *) <;> omega
  have hsum : ∑ k, (if t.rev.val < sz k then 1 else 0) +
      ∑ k, (if 0 < sz k ∧ t.val < m + 1 - sz k then 1 else 0) =
        ∑ k, (if (0 : Fin (m + 1)).val < sz k then 1 else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => key k
  simp only [nuDual, shapeDeg, Finset.sum_apply, Finset.card_filter]
  omega

private lemma card_filter_fin_val_lt_eq_of_le {N a : ℕ} (h : a ≤ N) :
    (Finset.univ.filter fun i : Fin N => i.val < a).card = a := by
  have e : (Finset.univ.filter fun i : Fin N => i.val < a) = Finset.univ.map (Fin.castLEEmb h) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.castLEEmb_apply]
    constructor
    · intro hi
      exact ⟨⟨i.val, hi⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact j.isLt
  rw [e, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem sum_shapeDeg_sub {m K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ m + 1) :
    ∑ i, (shapeDeg sz : Fin (m + 1) → ℕ) i - (shapeDeg sz : Fin (m + 1) → ℕ) 0 = ∑ k, (sz k - 1) := by
  have h1 : ∑ i, (shapeDeg sz : Fin (m + 1) → ℕ) i = ∑ k, sz k := by
    simp only [shapeDeg, Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.card_filter]
    exact card_filter_fin_val_lt_eq_of_le (hsz k)
  have h0 : (shapeDeg sz : Fin (m + 1) → ℕ) 0 = ∑ k, (if (0 : Fin (m + 1)).val < sz k then 1 else 0) := by
    simp only [shapeDeg, Finset.card_filter]
  have h2 : ∑ k, (sz k - 1) + ∑ k, (if (0 : Fin (m + 1)).val < sz k then 1 else 0) = ∑ k, sz k := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by
      split_ifs <;> (try simp only [Fin.val_zero] at *) <;> omega
  rw [h1, h0]
  omega

theorem exists_cofRel_dualWeyl : ∀ (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν → ν (Fin.last m) = 0 → ∀ f ∈ dualWeyl R (m + 1) (m + 1) ν, ∃ g ∈ dualWeyl R (m + 1) (m + 1) (nuDual ν), CofRel R m ν f g := by
  intro R _ _ m ν _ _ f hf
  obtain ⟨b, ⟨_, hspan, _⟩, hb⟩ := sSBasis R (m + 1) (m + 1) ν
  rw [← hspan] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨K, sz, hsz, I, hsh, -, hbi⟩ := (hb i).2.2
    rw [hbi]
    choose g hg hgeq using fun k => exists_cofAct_initMinor R (hsz k) (I k)
    refine ⟨∏ k, g k, ?_, ?_⟩
    · have hm := prod_mem_dualWeyl_sum R Finset.univ _ g hg
      rwa [← nuDual_shapeDeg sz, hsh] at hm
    · show (genM R (m + 1)).det ^ (∑ i, ν i - ν 0) * ∏ k, g k = cofAct R (m + 1) (bideterminant R sz hsz I)
      rw [← hsh, sum_shapeDeg_sub sz hsz, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib, bideterminant,
        map_prod]
      exact Finset.prod_congr rfl fun k _ => hgeq k
  | zero => exact ⟨0, zero_mem _, by simp [CofRel]⟩
  | add x y _ _ hx hy =>
    obtain ⟨g₁, h₁, e₁⟩ := hx
    obtain ⟨g₂, h₂, e₂⟩ := hy
    refine ⟨g₁ + g₂, add_mem h₁ h₂, ?_⟩
    unfold CofRel at e₁ e₂ ⊢
    rw [mul_add, e₁, e₂, map_add]
  | smul a x _ hx =>
    obtain ⟨g, h, e⟩ := hx
    refine ⟨a • g, Submodule.smul_mem _ a h, ?_⟩
    unfold CofRel at e ⊢
    rw [mul_smul_comm, e, map_smul]

end GlobalTheory.ValCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCofactorTwistHighestWeight
section
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

namespace GlobalTheory.ValCmp

theorem sum_mul_sub_succ : ∀ (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν →
    ∑ s : Fin m, s.val * (ν s.castSucc - ν s.succ) + m * ν (Fin.last m) + ν 0 = ∑ i, ν i := by
  intro m
  induction m with
  | zero => intro ν _; simp
  | succ m ih =>
    intro ν hν
    have h := ih (fun i => ν i.castSucc) (fun a b hab => hν (by simpa using hab))
    rw [Fin.sum_univ_castSucc (f := ν), ← h, Fin.sum_univ_castSucc]
    have hle : ν (Fin.last (m + 1)) ≤ ν (Fin.last m).castSucc := hν (Fin.le_last _)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    simp only [Fin.val_castSucc, Fin.val_last, Fin.succ_last, Fin.castSucc_zero, Fin.succ_castSucc, hd,
      Nat.add_sub_cancel_left]
    ring

noncomputable def revInitMinor (R : Type) [CommRing R] (n k : ℕ) : MP R n :=
  if h : k ≤ n then initMinor R (fun a : Fin k => Fin.rev (Fin.castLE h a)) h else 1

def antiDiagGL (R : Type) [CommRing R] (n : ℕ) : GL (Fin n) R where
  val := Matrix.of fun a b => if b = a.rev then 1 else 0
  inv := Matrix.of fun a b => if b = a.rev then 1 else 0
  val_inv := by
    ext a b
    rw [Matrix.mul_apply, Finset.sum_eq_single a.rev (fun j _ hj => by simp [hj]) (by simp)]
    simp [Matrix.one_apply, eq_comm]
  inv_val := by
    ext a b
    rw [Matrix.mul_apply, Finset.sum_eq_single a.rev (fun j _ hj => by simp [hj]) (by simp)]
    simp [Matrix.one_apply, eq_comm]

theorem dwAct_antiDiag_X (R : Type) [CommRing R] (n : ℕ) (a s : Fin n) :
    Formalism.UG.dwAct R n n (antiDiagGL R n) (X (a, s)) = X (a.rev, s) := by
  have : (((antiDiagGL R n)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
      Matrix.of fun a b => if b = a.rev then 1 else 0 := rfl
  rw [Formalism.UG.dwAct, this, rowAct, aeval_X, Finset.sum_eq_single a.rev (fun j _ hj => by simp [hj]) (by simp)]
  simp

theorem dwAct_antiDiag_lpMinor (R : Type) [CommRing R] (n k : ℕ) (h h' : k ≤ n) :
    Formalism.UG.dwAct R n n (antiDiagGL R n) (lpMinor R k h h') = revInitMinor R n k := by
  rw [revInitMinor, dif_pos h, lpMinor, initMinor, AlgHom.map_det]
  congr 1
  ext a b : 2
  simp [dwAct_antiDiag_X]

theorem cofAct_lpMinor (R : Type) [CommRing R] [IsDomain R] (n k : ℕ) (h h' : k + 1 ≤ n) : ∃ ε : ℤˣ,
    cofAct R n (lpMinor R (k + 1) h h') = (ε : ℤ) • ((genM R n).det ^ k * revInitMinor R n (n - (k + 1))) := by
  obtain ⟨ε, hε⟩ := cofAct_initMinor R n (k + 1) h (by omega) 1
  refine ⟨ε, ?_⟩
  rw [revInitMinor, dif_pos (Nat.sub_le _ _)]
  exact hε

theorem exists_cofRel_hw : ∀ (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν → ν (Fin.last m) = 0 → ∃ g ∈ weyl R (m + 1) (m + 1) le_rfl (nuDual ν), CofRel R m ν (hw R le_rfl ν) g := by
  intro R _ _ m ν hν h0
  have hmem : hw R le_rfl (nuDual ν) ∈ weyl R (m + 1) (m + 1) le_rfl (nuDual ν) :=
    Submodule.subset_span ⟨[], rfl⟩
  have hJ := Formalism.UG.Final.WeylGLStable R (m + 1) (m + 1) le_rfl (nuDual ν) (antiDiagGL R (m + 1)) _ hmem
  have hnext : ∀ (μ : Fin (m + 1) → ℕ) (s : Fin m), nuNext μ s.castSucc = μ s.succ := by
    intro μ s
    have : s.castSucc.val + 1 < m + 1 := by simp
    rw [nuNext, dif_pos this]
    rfl
  have e1 : Formalism.UG.dwAct R (m + 1) (m + 1) (antiDiagGL R (m + 1)) (hw R le_rfl (nuDual ν)) =
      ∏ s : Fin m, revInitMinor R (m + 1) (m + 1 - (s.val + 1)) ^ (ν s.castSucc - ν s.succ) := by
    rw [hw, map_prod, Fin.prod_univ_castSucc]
    simp only [map_pow, dwAct_antiDiag_lpMinor, hnext]
    have : nuDual ν (Fin.last m) = 0 := by simp [nuDual]
    rw [this, Nat.zero_sub, pow_zero, mul_one, ← Equiv.prod_comp Fin.revPerm]
    refine Finset.prod_congr rfl fun s _ => ?_
    have h1 : ν s.castSucc ≤ ν 0 := hν (Fin.zero_le _)
    have h2 : ν s.succ ≤ ν s.castSucc := hν (Fin.castSucc_lt_succ).le
    have hs := s.isLt
    congr 1
    · congr 1
      simp [Fin.val_rev]
      omega
    · simp only [nuDual, Fin.revPerm_apply, Fin.rev_castSucc, Fin.rev_succ, Fin.rev_rev]
      omega
  choose ε hε using fun s : Fin m =>
    cofAct_lpMinor R (m + 1) s.val (by have := s.isLt; omega) (by have := s.isLt; omega)
  refine ⟨(∏ s : Fin m, (ε s : ℤ) ^ (ν s.castSucc - ν s.succ)) • _, Submodule.smul_of_tower_mem _ _ hJ, ?_⟩
  have hsum : ∑ i, ν i - ν 0 = ∑ s : Fin m, s.val * (ν s.castSucc - ν s.succ) := by
    have := sum_mul_sub_succ m ν hν
    rw [h0] at this
    omega
  rw [CofRel, e1, hsum, hw, map_prod, Fin.prod_univ_castSucc, h0, Nat.zero_sub, pow_zero, map_one, mul_one]
  simp only [map_pow, hnext, Fin.val_castSucc, hε, zsmul_eq_mul, mul_pow, Finset.prod_mul_distrib, ← pow_mul,
    Finset.prod_pow_eq_pow_sum]
  push_cast
  ring

end GlobalTheory.ValCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIdeleClassGroupHomOpenKernel
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

noncomputable section

open scoped nonZeroDivisors

namespace GlobalTheory.IdeleClass

variable (E : Type) [Field E] [NumberField E]

theorem localIdele_snd_self' (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ) :
    ((localIdele E v x : Ideles E) : AdeleRing (𝓞 E) E).2 v = x := by
  classical
  show (Pi.mulSingle v (x : v.adicCompletion E) : ∀ w : HeightOneSpectrum (𝓞 E), w.adicCompletion E) v = x
  convert Pi.mulSingle_eq_same v (x : v.adicCompletion E)

theorem localIdele_snd_ne' (v w : HeightOneSpectrum (𝓞 E)) (h : w ≠ v) (x : (v.adicCompletion E)ˣ) :
    ((localIdele E v x : Ideles E) : AdeleRing (𝓞 E) E).2 w = 1 := by
  classical
  show (Pi.mulSingle v (x : v.adicCompletion E) : ∀ w : HeightOneSpectrum (𝓞 E), w.adicCompletion E) w = 1
  convert Pi.mulSingle_eq_of_ne h (x : v.adicCompletion E)

theorem classHom_val (a : Ideles E) :
    ((((GlobalTheory.Mem.UnitIndex.idealHom E).comp (GlobalTheory.Mem.UnitIndex.finIdele E)).toHomUnits a :
      (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E) =
      GlobalTheory.Idele.idealOf (GlobalTheory.Mem.UnitIndex.finIdele E a) := rfl

theorem finIdele_apply (a : Ideles E) (v : HeightOneSpectrum (𝓞 E)) :
    ((GlobalTheory.Mem.UnitIndex.finIdele E a : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) v =
      (a : AdeleRing (𝓞 E) E).2 v := rfl

theorem classHom_eq_one_of_mem_unitIdl {a : Ideles E} (ha : a ∈ GlobalTheory.Mem.Chr.unitIdl E) :
    GlobalTheory.Mem.UnitIndex.classHom E a = 1 := by
  have h : GlobalTheory.Idele.idealOf (GlobalTheory.Mem.UnitIndex.finIdele E a) = 1 := by
    rw [← GlobalTheory.Idele.smul_one_eq]
    exact (GlobalTheory.Idele.smul_eq_self_iff _ (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E))).2 fun v => ha v
  have hu : ((GlobalTheory.Mem.UnitIndex.idealHom E).comp (GlobalTheory.Mem.UnitIndex.finIdele E)).toHomUnits a = 1 :=
    Units.ext (by rw [classHom_val, h]; rfl)
  show ClassGroup.mk E _ = 1
  rw [hu, map_one]

theorem unitIdl_le_ker : GlobalTheory.Mem.Chr.unitIdl E ≤ (GlobalTheory.Mem.UnitIndex.classHom E).ker :=
  fun _ ha => classHom_eq_one_of_mem_unitIdl E ha

theorem infConn_le_unitIdl : infConn E ≤ GlobalTheory.Mem.Chr.unitIdl E := by
  rintro _ ⟨y, -, rfl⟩ v
  show Valued.v (1 : v.adicCompletion E) = 1
  exact map_one _

theorem diagUnits_range_le_ker : (diagUnits E).range ≤ (GlobalTheory.Mem.UnitIndex.classHom E).ker := by
  rintro _ ⟨k, rfl⟩
  have hd : GlobalTheory.Mem.UnitIndex.finIdele E (diagUnits E k) =
      FiniteAdeleRing.unitEmbedding (𝓞 E) E k := Units.ext rfl
  show ClassGroup.mk E _ = 1
  rw [ClassGroup.mk_eq_one_iff, classHom_val, hd, GlobalTheory.Idele.idealOf_unitEmbedding,
    FractionalIdeal.coe_spanSingleton]
  exact ⟨⟨(k : E), rfl⟩⟩

theorem localIdele_mem_unitIdl (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ)
    (hx : IsUnitAt v x) : localIdele E v x ∈ GlobalTheory.Mem.Chr.unitIdl E := by
  intro w
  by_cases hw : w = v
  · subst hw
    rw [localIdele_snd_self']
    exact hx
  · rw [localIdele_snd_ne' E v w hw]
    exact map_one _

open Classical in
theorem ord_vw_localIdele_unif (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ)
    (hx : IsUnifAt v x) (w : HeightOneSpectrum (𝓞 E)) :
    GlobalTheory.Idele.ord_vw (GlobalTheory.Mem.UnitIndex.finIdele E (localIdele E v x)) w =
      if v = w then 1 else 0 := by
  rw [GlobalTheory.Idele.ord_vw, finIdele_apply]
  by_cases hw : w = v
  · subst hw
    rw [localIdele_snd_self', if_pos rfl]
    have hx' : Valued.v (x : w.adicCompletion E) = WithZero.exp (-1) := hx
    rw [hx', WithZero.log_exp]
    rfl
  · rw [localIdele_snd_ne' E v w hw, if_neg (Ne.symm hw), map_one]
    rfl

theorem classHom_localIdele_unif (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ)
    (hx : IsUnifAt v x) :
    GlobalTheory.Mem.UnitIndex.classHom E (localIdele E v x) =
      ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ := by
  classical
  have hv : ((v.asIdeal : FractionalIdeal (𝓞 E)⁰ E)) ≠ 0 := by simpa using v.ne_bot
  have h : GlobalTheory.Idele.idealOf (GlobalTheory.Mem.UnitIndex.finIdele E (localIdele E v x)) =
      (v.asIdeal : FractionalIdeal (𝓞 E)⁰ E) := by
    refine GlobalTheory.Idele.eq_of_count_eq (GlobalTheory.Idele.idealOf_ne_zero _) hv fun w => ?_
    rw [GlobalTheory.Idele.count_idealOf, ord_vw_localIdele_unif E v x hx w,
      FractionalIdeal.count_maximal]
  have hu : ((GlobalTheory.Mem.UnitIndex.idealHom E).comp (GlobalTheory.Mem.UnitIndex.finIdele E)).toHomUnits
      (localIdele E v x) =
      FractionalIdeal.mk0 E ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ :=
    Units.ext (by rw [classHom_val, h, FractionalIdeal.coe_mk0])
  show ClassGroup.mk E _ = _
  rw [hu, ClassGroup.mk_mk0]

end GlobalTheory.IdeleClass

namespace GlobalTheory

theorem exists_ideleClassHom : ∀ (E : Type) [Field E] [NumberField E], ∃ cl : Ideles E →* ClassGroup (𝓞 E), IsOpen (cl.ker : Set (Ideles E)) ∧ (diagUnits E).range ⊔ infConn E ≤ cl.ker ∧ (∀ (v : HeightOneSpectrum (𝓞 E)) x, IsUnitAt v x → cl (localIdele E v x) = 1) ∧ ∀ (v : HeightOneSpectrum (𝓞 E)) x, IsUnifAt v x → cl (localIdele E v x) = ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ := by
  intro E _ _
  refine ⟨GlobalTheory.Mem.UnitIndex.classHom E,
    Subgroup.isOpen_mono (GlobalTheory.IdeleClass.unitIdl_le_ker E) GlobalTheory.Mem.UnitOpen.isOpen_unitIdl,
    sup_le (GlobalTheory.IdeleClass.diagUnits_range_le_ker E)
      ((GlobalTheory.IdeleClass.infConn_le_unitIdl E).trans (GlobalTheory.IdeleClass.unitIdl_le_ker E)),
    fun v x hx => GlobalTheory.IdeleClass.classHom_eq_one_of_mem_unitIdl E
      (GlobalTheory.IdeleClass.localIdele_mem_unitIdl E v x hx),
    fun v x hx => GlobalTheory.IdeleClass.classHom_localIdele_unif E v x hx⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueEmbeddingReadsGaloisElementStatement
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_embeddingReadsGaloisElement : ∀ {R : Ranks} (H : Host R) {l : ℕ} [Fact l.Prime] (K LL : FinExt l) (c : H.E →+* ↥K.1) (κ : H.E →+* ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1), ∃! g : R.GG, Reads H c κ τ g := by
  first | exact @GlobalTheory.HTW.Rec.existsUnique_reads | exact GlobalTheory.HTW.Rec.existsUnique_reads | (intros; apply GlobalTheory.HTW.Rec.existsUnique_reads <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueEmbeddingRestrictsToWachLetterUnramiStatement
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_embeddingRestrictsToWachLetter_unramified : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL), K.1 ≤ MaximalUnramifiedExtension l → ∀ a, ∃! τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, Over W τ a := by
  first | exact @GlobalTheory.HTW.Rec.existsUnique_over | exact GlobalTheory.HTW.Rec.existsUnique_over | (intros; apply GlobalTheory.HTW.Rec.existsUnique_over <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodCoefficientRingIntegersPadicFiniteExtensionStatement
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodCoefficientRing_integers_padicFiniteExtension : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), GoodO (Qp := ℚ_[l]) ↥LL.1 ↥(OL LL) := by
  first | exact @GlobalTheory.HTW.Rec.goodO_finExt_integers | exact GlobalTheory.HTW.Rec.goodO_finExt_integers | (intros; apply GlobalTheory.HTW.Rec.goodO_finExt_integers <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.H1H2LocalDualityStatement
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hOneTwo_of_localFiniteness_tateDuality_eulerChar : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ D : D7, HOneTwo D := by
  first | exact @GlobalTheory.HOneTwoLevel.hOneTwo_holds | exact GlobalTheory.HOneTwoLevel.hOneTwo_holds | (intros; apply GlobalTheory.HOneTwoLevel.hOneTwo_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HarrisTaylorOrderSplitAlmostAllPrimesStatement
section
open NumberField
open GlobalTheory.UPel.HT.Gen
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylorOrder_split_almost_all_primes : ∀ (G : GDatum), ∃ M : ℕ, 0 < M ∧ ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ M → Nonempty ((G.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 G.F] Matrix (Fin G.m) (Fin G.m) (𝓞 G.F ⊗[ℤ] ℤ_[p])) := by
  first | (exact @GlobalTheory.UPel.HT.Gen.SplitAE.splitAE) | (exact GlobalTheory.UPel.HT.Gen.SplitAE.splitAE) | (intros; apply GlobalTheory.UPel.HT.Gen.SplitAE.splitAE  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralDivUniformizerOfRedZeroStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_div_uniformizer_of_red_zero : ∀ (X : Fields) (Pr : Primes X), X.Ok → Pr.Ok → ∀ w ∈ Pr.vGs, ∀ a : X.E, IntAt w a → redP w a = 0 → IntAt w (a / (qOf w : X.E)) := by
  first | exact @GlobalTheory.TypePrimeUnif.intAt_div_qOf | exact GlobalTheory.TypePrimeUnif.intAt_div_qOf | (intros; apply GlobalTheory.TypePrimeUnif.intAt_div_qOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralGlReductionModPrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_gl_reduction_mod_prime : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (P : HeightOneSpectrum (𝓞 E)) (κ : Sp E n ≃ₗ[E] Sp E n), κ ∈ GLint E n P → ∃ h : GL (Fin n) (𝓞 E ⧸ P.asIdeal), ∀ x ∈ stdAt E n P, redV P (κ x) = h.1.mulVec (redV P x) := by
  first | exact @GlobalTheory.exists_GL_redV_of_mem_GLint | exact GlobalTheory.exists_GL_redV_of_mem_GLint | (intros; apply GlobalTheory.exists_GL_redV_of_mem_GLint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsCrystallineJumpsOfIsIsoMatrixGaloisRepresentatStatement
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCrystalline_jumps_of_isIsoMatrixGaloisRepresentation : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (T : Lat K LL) {r : ℕ} (M : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1), IsMatRep T M → (IsCrys (P.PD K) (matRep M) → IsCrys (P.PD K) T.ρ) ∧ ∀ τ u, multV (P.PD K) T.ρ τ u = multV (P.PD K) (matRep M) τ u := by
  first | exact @GlobalTheory.HTW.Rec.isCrys_multV_of_isMatRep | exact GlobalTheory.HTW.Rec.isCrys_multV_of_isMatRep | (intros; apply GlobalTheory.HTW.Rec.isCrys_multV_of_isMatRep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaCharMulInvEqOneStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lambda_char_mul_inv_eq_one : ∀ (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ), q ≠ 0 → (q : 𝓞 E) ∈ P.asIdeal → ∀ (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r t j n : ℕ), r + j * t ≤ n → ∀ g ∈ LocE.JG P q k₀ r t n 0, LocE.lamGB q ψ₀ χ k₀ r t j n 0 g.toLinearMap * LocE.lamGB q ψ₀ χ k₀ r t j n 0 (g⁻¹).toLinearMap = 1 := by
  first | exact @GlobalTheory.lamGB_mul_lamGB_inv | exact GlobalTheory.lamGB_mul_lamGB_inv | (intros; apply GlobalTheory.lamGB_mul_lamGB_inv <;> assumption)
end

