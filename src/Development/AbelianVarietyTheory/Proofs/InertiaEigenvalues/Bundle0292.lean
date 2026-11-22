import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0239
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0233
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0272
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0273
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0229
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionCoinvariantsTwistedCyclotomicGenerator
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0274
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0256
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0260
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0127
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIntegersTensorEqLetterwiseProductAinf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XiGradedPieceIsoTwistedOC

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerEpsilonRootPowSubZetaExpMemFiltration
section
noncomputable section

namespace GlobalTheory.ExpImage

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped Formalism.Per

theorem eq_of_pow_eq_of_nilpotent {Q : Type*} [CommRing Q] {a b : Q} {N : ℕ} (hN : IsUnit (N : Q))
    (hb : IsUnit b) (hn : IsNilpotent (a - b)) (h : a ^ N = b ^ N) : a = b := by
  have h1 := (Commute.all a b).geom_sum₂_mul N
  rw [h, sub_self] at h1
  have h2 : IsNilpotent ((∑ i ∈ Finset.range N, a ^ i * b ^ (N - 1 - i)) - N * b ^ (N - 1)) := by
    have e : (N : Q) * b ^ (N - 1) = ∑ i ∈ Finset.range N, b ^ i * b ^ (N - 1 - i) := by
      rw [Finset.sum_congr rfl (g := fun _ => b ^ (N - 1))]
      · simp
      · intro i hi
        rw [← pow_add]
        congr 1
        have := Finset.mem_range.1 hi
        omega
    rw [e, ← Finset.sum_sub_distrib, ← mem_nilradical]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [← sub_mul]
    obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow a b i
    rw [hc, mul_assoc]
    exact Ideal.mul_mem_right _ _ (mem_nilradical.2 hn)
  have h3 := h2.isUnit_add_right_of_commute (hN.mul (hb.pow (N - 1))) (Commute.all _ _)
  rw [sub_add_cancel] at h3
  exact sub_eq_zero.1 ((h3.mul_right_eq_zero).1 h1)

theorem nilpotent_exp_nsmul {Q : Type*} [CommRing Q] [Module ℚ Q] {x : Q} (hx : IsNilpotent x) (n : ℕ) :
    IsNilpotent.exp ((n : Q) * x) = IsNilpotent.exp x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, IsNilpotent.exp_add_of_commute (Commute.all _ _)
      ((Commute.all _ _).isNilpotent_mul_left hx) hx, ih, pow_succ]

theorem pow_eq_mul_exp {K Q : Type*} [Field K] [CharZero K] [CommRing Q] [Algebra K Q] {a z t : Q}
    {M N : ℕ} (m : ℕ) (hN : N ≠ 0) (ht : t ^ M = 0) (hz : z ^ N = 1) (hn : IsNilpotent (a - z))
    (ha : a ^ N = ∑ j ∈ Finset.range M, algebraMap K Q ((j.factorial : K)⁻¹) * t ^ j) :
    a ^ m = z ^ m * ∑ j ∈ Finset.range M,
      algebraMap K Q (((m : K) / (N : K)) ^ j / (j.factorial : K)) * t ^ j := by
  letI : Algebra ℚ Q := ((algebraMap K Q).comp (algebraMap ℚ K)).toAlgebra
  have hE : ∀ c : K, IsNilpotent.exp (algebraMap K Q c * t) =
      ∑ j ∈ Finset.range M, algebraMap K Q (c ^ j / (j.factorial : K)) * t ^ j := by
    intro c
    rw [IsNilpotent.exp_eq_sum (k := M) (by rw [mul_pow, ht, mul_zero])]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, mul_pow, ← mul_assoc, ← map_pow, div_eq_inv_mul, map_mul]
    congr 2
    change algebraMap K Q (algebraMap ℚ K _) = _
    simp
  have hN' : (N : K) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hx : IsNilpotent (algebraMap K Q (N : K)⁻¹ * t) :=
    (Commute.all _ _).isNilpotent_mul_left ⟨M, ht⟩
  have hk : ∀ k : ℕ, IsNilpotent.exp (algebraMap K Q (N : K)⁻¹ * t) ^ k =
      ∑ j ∈ Finset.range M, algebraMap K Q (((k : K) / (N : K)) ^ j / (j.factorial : K)) * t ^ j := by
    intro k
    rw [← nilpotent_exp_nsmul hx, ← hE, div_eq_mul_inv, map_mul, map_natCast, mul_assoc]
  have hu : IsUnit z := IsUnit.of_pow_eq_one hz hN
  have e : a = z * IsNilpotent.exp (algebraMap K Q (N : K)⁻¹ * t) := by
    refine eq_of_pow_eq_of_nilpotent (N := N) ?_ (hu.mul hx.isUnit_exp) ?_ ?_
    · have := (IsUnit.mk0 _ hN').map (algebraMap K Q)
      rwa [map_natCast] at this
    · have h1 := (Commute.all z _).isNilpotent_mul_left hx.isNilpotent_exp_sub_one
      have h2 := (Commute.all _ _).isNilpotent_sub hn h1
      convert h2 using 1
      ring
    · rw [mul_pow, hz, one_mul, hk, ha]
      simp [div_self hN']
  rw [e, mul_pow, hk]

variable {l : ℕ} [Fact l.Prime]

def filZero (P : LocPrime l) : Subalgebra ℚ_[l] P.R.BdR where
  carrier := {x | x ∈ FilB P 0}
  mul_mem' hx hy := FilB_zero_mul hx hy
  add_mem' hx hy := (FilB P 0).add_mem hx hy
  algebraMap_mem' c := qB_mem c

def filIdeal (P : LocPrime l) (M : ℕ) : Ideal ↥(filZero P) where
  carrier := {x | (x : P.R.BdR) ∈ FilB P (M : ℤ)}
  zero_mem' := (FilB P (M : ℤ)).zero_mem
  add_mem' hx hy := (FilB P (M : ℤ)).add_mem hx hy
  smul_mem' c _ hx := FilB_zero_mul c.2 hx

theorem epsT_pow {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) :
    epsT AI s ^ l ^ s = WittVector.teichmuller l AI.ε := by
  rw [epsT, ← map_pow]
  congr 1
  induction s with
  | zero => simp [LocAinf.εroot]
  | succ n ih =>
    rw [pow_succ', pow_mul, ← ih, LocAinf.εroot, Function.iterate_succ_apply',
      frobeniusEquiv_symm_pow_p]
    rfl

theorem ζQ_pow (P : LocPrime l) (s : ℕ) : P.ζQ s ^ l ^ s = 1 := by
  induction s with
  | zero => simp [P.ζQ_zero]
  | succ n ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]

theorem oB_mem_zero {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (x : Om l) :
    oB P x ∈ FilB P 0 := by
  obtain ⟨y, h1, -⟩ := T.om x
  exact (GlobalTheory.ThetaTie.fil_zero T _).2 ⟨y, h1.symm⟩

theorem epsT_sub_mem {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (s : ℕ) :
    io AI (epsT AI s) - oB P (P.ζQ s) ∈ FilB P 1 := by
  obtain ⟨y, h1, h2⟩ := T.om (P.ζQ s)
  refine (GlobalTheory.ThetaTie.fil_nat T 1 _).2 ⟨GlobalTheory.MemLoc.aDp l (epsT AI s) - y, ?_, ?_⟩
  · rw [← (GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l).2.1, map_sub, h2, (GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l).2.2.2.1, epsT,
      WittVector.fontaineTheta_teichmuller, untilt_εroot, AI.ζ_eq, sub_self]
  · rw [map_sub, map_sub, h1, io_apply, GlobalTheory.ThetaTie.eD_ιA]

theorem epsT_pow_taylor : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied l P AI → ∀ s m M : ℕ, io AI (epsT AI s ^ m) - oB P (P.ζQ s ^ m) *
      ∑ j ∈ Finset.range M, qB P (((m : ℚ_[l]) / (l : ℚ_[l]) ^ s) ^ j / (j.factorial : ℚ_[l])) *
        tD P ^ j ∈ FilB P (M : ℤ) := by
  intro l _ P AI T s m M
  let π := Ideal.Quotient.mkₐ ℚ_[l] (filIdeal P M)
  have hπ : ∀ x y : ↥(filZero P), π x = π y ↔ (x : P.R.BdR) - y ∈ FilB P (M : ℤ) :=
    fun x y => Ideal.Quotient.eq
  have hnil : ∀ x : ↥(filZero P), (x : P.R.BdR) ∈ FilB P 1 → π x ^ M = 0 := by
    intro x hx
    rw [← map_pow, ← map_zero π, hπ]
    simpa using FilB_pow hx M
  let a : ↥(filZero P) := ⟨io AI (epsT AI s), io_mem AI _⟩
  let z : ↥(filZero P) := ⟨oB P (P.ζQ s), oB_mem_zero T _⟩
  let t : ↥(filZero P) := ⟨tD P, FilB_anti zero_le_one tD_mem⟩
  have hs : ∀ c : ℕ → ℚ_[l], ∑ j ∈ Finset.range M, algebraMap ℚ_[l] _ (c j) * π t ^ j =
      π (∑ j ∈ Finset.range M, algebraMap ℚ_[l] _ (c j) * t ^ j) := by
    intro c
    simp only [map_sum, map_mul, map_pow, AlgHom.commutes]
  have hc : ∀ c : ℕ → ℚ_[l],
      ((∑ j ∈ Finset.range M, algebraMap ℚ_[l] _ (c j) * t ^ j : ↥(filZero P)) : P.R.BdR) =
      ∑ j ∈ Finset.range M, qB P (c j) * tD P ^ j := by
    intro c
    rw [AddSubmonoidClass.coe_finset_sum]
    rfl
  have key := pow_eq_mul_exp (K := ℚ_[l]) (a := π a) (z := π z) (t := π t) (M := M) (N := l ^ s) m
    (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) (hnil t tD_mem)
    (by
      rw [← map_pow, ← map_one π]
      congr 1
      apply Subtype.ext
      change oB P (P.ζQ s) ^ l ^ s = 1
      rw [← map_pow, ζQ_pow, map_one])
    ⟨M, by rw [← map_sub]; exact hnil _ (epsT_sub_mem T s)⟩
    (by
      rw [hs (fun j => (j.factorial : ℚ_[l])⁻¹), ← map_pow, hπ, hc]
      change io AI (epsT AI s) ^ l ^ s - _ ∈ _
      rw [← map_pow, epsT_pow]
      exact GlobalTheory.T.teichmullerEpsilon_sub_exp_mem_hodgeFiltration l P AI T M)
  rw [hs (fun j => ((m : ℚ_[l]) / ((l ^ s : ℕ) : ℚ_[l])) ^ j / (j.factorial : ℚ_[l])), ← map_pow,
    ← map_pow, ← map_mul, hπ, Subalgebra.coe_mul, hc, Nat.cast_pow] at key
  rw [map_pow, map_pow]
  exact key

end GlobalTheory.ExpImage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerEpsilonRootsMemFrobeniusPerfectionModStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.teichmullerEpsilonRoots_mem_frobeniusPerfection_mod_l : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W), ∀ u ∈ Subring.closure (Set.range AI.εroot ∪ {xb | ∃ c : Om l, c ∈ K0 K ∧ ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ c ^ m = 1 ∧ IsTiltOf c m xb}), ∃ (n : ℕ) (e : W.EE) (r : RW LL), (φRW LL)^[n] ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] inclW l (WittVector.teichmuller l u)) = E.tie.ioE e + (l : RW LL) * r := by
  first | exact @GlobalTheory.DecomplPerf.teich_mem_perfection | exact GlobalTheory.DecomplPerf.teich_mem_perfection | (intros; apply GlobalTheory.DecomplPerf.teich_mem_perfection <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerRootsActFaithfullyLaurentStatement
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.teichmuller_roots_act_faithfully_laurent : ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] (R : RingPG k l) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι → ∃ σ : {z : ℤ_[l] // z ^ (l - 1) = 1} → (k⸨X⸩ →+* k⸨X⸩), (∀ z (b : k⟦X⟧), σ z (b : k⸨X⸩) = ((GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l z.1 b : k⟦X⟧) : k⸨X⸩)) ∧ Function.Injective σ ∧ ∀ c, (∀ z, σ z c = c) ↔ ∃ c₀, ι c₀ = c := by
  first | exact @GlobalTheory.DeltaInv.main | exact GlobalTheory.DeltaInv.main | (intros; apply GlobalTheory.DeltaInv.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltGaloisActionRootOfUnityCoprime
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

variable {l : ℕ} [Fact l.Prime]

theorem σC_root_of_unity {m n : ℕ} {g : GQ l} (hm : 0 < m) (hg : ∀ x : Om l, x ^ m = 1 → g x = x ^ n)
    {x : ℂ_[l]} (hx : x ^ m = 1) : Per.σC g x = x ^ n := by
  have : NeZero m := ⟨hm.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) m
  have hζ' := hζ.map_of_injective (algebraMap (Om l) ℂ_[l]).injective
  obtain ⟨i, -, rfl⟩ := hζ'.eq_pow_of_pow_eq_one hx
  have h1 : (ζ ^ i) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have h2 : Per.σC g (algebraMap (Om l) ℂ_[l] (ζ ^ i)) = algebraMap (Om l) ℂ_[l] (g (ζ ^ i)) :=
    GlobalTheory.RingBasics.σC_coe g (ζ ^ i)
  rw [← map_pow, h2, hg _ h1, map_pow]

theorem tilt_root_eq_one {c : Per.Fl l} {m : ℕ} (hlm : ¬ l ∣ m) (hc : c ^ m = 1)
    (h0 : PreTilt.coeff 0 c = 1) : c = 1 := by
  have : IsDomain (Per.Fl l) := inferInstance
  by_contra hne
  have h1 : (∑ i ∈ Finset.range m, c ^ i) * (c - 1) = 0 := by rw [geom_sum_mul, hc, sub_self]
  have h2 : (∑ i ∈ Finset.range m, c ^ i) = 0 :=
    (mul_eq_zero.1 h1).resolve_right (sub_ne_zero.2 hne)
  have h3 := congrArg (PreTilt.coeff (O := Per.OC l) (p := l) 0) h2
  simp only [map_sum, map_pow, h0, one_pow, Finset.sum_const, Finset.card_range, map_zero,
    nsmul_eq_mul, mul_one] at h3
  exact hlm ((CharP.cast_eq_zero_iff _ l m).1 h3)

theorem tilt_root_inj {a b : Per.Fl l} {m : ℕ} (hm : 0 < m) (hlm : ¬ l ∣ m) (ha : a ^ m = 1)
    (hb : b ^ m = 1) (h : a.untilt = b.untilt) : a = b := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hb' : b * b ^ k = 1 := by rw [← pow_succ', hb]
  have h0 : PreTilt.coeff 0 a = PreTilt.coeff 0 b := by
    rw [← PreTilt.mk_untilt_eq_coeff_zero, ← PreTilt.mk_untilt_eq_coeff_zero, h]
  have h1 : a * b ^ k = 1 := by
    refine tilt_root_eq_one hlm ?_ ?_
    · rw [mul_pow, ha, ← pow_mul, mul_comm k, pow_mul, hb, one_pow, one_mul]
    · rw [map_mul, h0, ← map_mul, hb', map_one]
  calc a = a * (b * b ^ k) := by rw [hb', mul_one]
    _ = (a * b ^ k) * b := by ring
    _ = b := by rw [h1, one_mul]

theorem σF_root_of_unity (l : ℕ) [Fact l.Prime] (e : Per.Fl l) (m n : ℕ) (g : GQ l) (hm : 0 < m)
    (hlm : ¬ l ∣ m) (he : e ^ m = 1) (hg : ∀ x : Om l, x ^ m = 1 → g x = x ^ n) :
    Per.σF g e = e ^ n := by
  refine tilt_root_inj hm hlm ?_ ?_ ?_
  · rw [← map_pow, he, map_one]
  · rw [← pow_mul, mul_comm, pow_mul, he, one_pow]
  · rw [GlobalTheory.RingBasics.untilt_σF, map_pow]
    have h1 : e.untilt ^ m = 1 := by rw [← map_pow, he, map_one]
    have h2 : ((e.untilt : Per.OC l) : ℂ_[l]) ^ m = 1 := by
      simpa using congrArg Subtype.val h1
    exact Subtype.ext ((GlobalTheory.RingIface.sigO_coe l g _).trans
      ((σC_root_of_unity hm hg h2).trans (by simp)))

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUnitTeichmullerPrincipalUnitSplitStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tilt_unit_teichmuller_principal_unit_split : ∀ (l : ℕ) [Fact l.Prime] (x : Per.Fl l), IsUnit x → ∃ (ω x₁ : Per.Fl l) (N : ℕ), x = ω * x₁ ∧ GlobalTheory.LogU.InJ (Per.tm (x₁ ^ (l ^ N)) - 1) ∧ ∀ (g : Per.Gq l) (e : Per.Fl l), e.untilt = 1 → Per.σF g x = x * e → Per.σF g ω = ω := by
  first | (exact @GlobalTheory.LogU.teich_split) | (exact GlobalTheory.LogU.teich_split) | (intros; apply GlobalTheory.LogU.teich_split  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionCoinvariantsTwistedCyclotomicGeneratorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_coinvariants_twistedCyclotomicGenerator : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m r : ℕ), Lev l m → ∀ (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l), Frame χ K m U g → ∀ J : Finset ℤ, HTBasis act χ (Gj K m) U (J : Set ℤ) → ∀ (i : ℤ) (w w' : Fin r → PadicComplex l) (k : ℕ), (∀ a, w a ∈ Ohat K) → (∀ a, w' a ∈ Ohat K) → twAct act χ i U g w' - w' = (l : PadicComplex l) ^ k • w → ∃ y : Fin r → PadicComplex l, (∀ a, y a ∈ Ohat K) ∧ twAct act χ i U g y - y = (l : PadicComplex l) ^ (max 1 (∑ u ∈ J.erase i, (m + padicValInt l (u - i)))) • w := by
  first | exact @GlobalTheory.CycCoinv.torsion_coinvariants | exact GlobalTheory.CycCoinv.torsion_coinvariants | (intros; apply GlobalTheory.CycCoinv.torsion_coinvariants <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceMirabolicDetAverageEqHarishChandraRestrictiStatement
section
open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_mirabolicDetAverage_eq_harishChandraRestriction : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ) (ψ : Gn g (n + 1) → ℂ) (θ : (ZMod g)ˣ →* ℂˣ),
    tr (mirEl θ (Pi.single (Fin.last n) 1) false) ψ =
        (g : ℂ) ^ n * ∑ x : Gn g 1, ((θ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res n 1 ψ 1 x ∧
      tr (mirEl θ (Pi.single 0 1) true) ψ =
        (g : ℂ) ^ n * ∑ x : Gn g 1, ((θ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res 1 n ψ x 1 := by
  first | exact @GlobalTheory.ResTr.trace_mir | exact GlobalTheory.ResTr.trace_mir | (intros; apply GlobalTheory.ResTr.trace_mir <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceMirabolicDetCharacterAverageVectorIndepStatement
section
open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_mirabolicDetCharacterAverage_vector_indep : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ) (ψ : Gn g (n + 1) → ℂ), IsClass ψ → ∀ (θ : (ZMod g)ˣ →* ℂˣ)
    (a : Fin (n + 1) → ZMod g), a ≠ 0 → ∀ b : Bool,
      tr (mirEl θ a b) ψ = tr (mirEl θ (if b then Pi.single 0 1 else Pi.single (Fin.last n) 1) b) ψ := by
  first | exact @GlobalTheory.MirAvg.tr_mirEl_indep | exact GlobalTheory.MirAvg.tr_mirEl_indep | (intros; apply GlobalTheory.MirAvg.tr_mirEl_indep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoCocycleFundamentalMultipleModPow
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt

namespace GlobalTheory.UnifSpan

open GlobalTheory.TateTop

private theorem quotRep_twist_apply {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {G : Type} [Group G] (ε : G →* Oˣ) (ϖ : O) (n : ℕ) (g : G) (q : O ⧸ powSub (M := O) ϖ n) :
    quotRep (twist ε O) ϖ n g q = ((ε g : Oˣ) : O) • q := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [quotRep_mk, twist_apply, Submodule.Quotient.mk_smul]

private theorem factor_quotRep_of_le {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {G : Type} [Group G] (ε : G →* Oˣ) (ϖ : O) {m n : ℕ} (hmn : m ≤ n) (g : G)
    (q : O ⧸ powSub (M := O) ϖ n) :
    Submodule.factor (powSub_anti (M := O) ϖ hmn) (quotRep (twist ε O) ϖ n g q) =
      quotRep (twist ε O) ϖ m g (Submodule.factor (powSub_anti (M := O) ϖ hmn) q) := by
  rw [quotRep_twist_apply, quotRep_twist_apply]
  exact map_smul _ _ _

theorem span_mod_pow {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O]
    {G : Type} [Group G] [TopologicalSpace G] (χ : G →* ℤ_[p]ˣ) (c : G × G → ℤ_[p])
    (hgen : ∀ r, GlobalTheory.TateTop.Gen χ r c) (φ : ℤ_[p] →+* O) (ε : G →* Oˣ)
    (hε : ∀ g, ((ε g : Oˣ) : O) = φ (χ g : ℤ_[p])) (ϖ : O) (hϖ : Irreducible ϖ)
    (hp : (p : O) ∈ IsLocalRing.maximalIdeal O)
    (hopen : ∀ n : ℕ, IsOpen ((powSub (M := O) ϖ n : Submodule O O) : Set O))
    (w : G × G → O) (hw : w ∈ Z2 (twist ε O)) :
    ∃ a : O, ∀ n : ℕ, ∃ b : G → O ⧸ powSub (M := O) ϖ n, Continuous b ∧
      ∀ g h : G, d1 (quotRep (twist ε O) ϖ n) b (g, h) =
        Submodule.Quotient.mk (w (g, h) - a * φ (c (g, h))) := by
  classical
  have hwZ := (mem_cocycles2 (twist ε O) w).mp hw

  have hp' := hp
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
    Ideal.mem_span_singleton] at hp'
  obtain ⟨t, ht⟩ := hp'

  have hdisc : ∀ n : ℕ, DiscreteTopology (O ⧸ powSub (M := O) ϖ n) := fun n =>
    QuotientAddGroup.discreteTopology (N := (powSub (M := O) ϖ n).toAddSubgroup) (hopen n)

  let S : ℕ → Set O := fun n => {a | ∃ b : G → O ⧸ powSub (M := O) ϖ n, Continuous b ∧
      ∀ g h : G, d1 (quotRep (twist ε O) ϖ n) b (g, h) =
        Submodule.Quotient.mk (w (g, h) - a * φ (c (g, h)))}

  have hne : ∀ n, (S n).Nonempty := by
    intro n
    have := hdisc n
    letI : Module ℤ_[p] (O ⧸ powSub (M := O) ϖ n) := Module.compHom _ φ
    have hsm : ∀ (s : ℤ_[p]) (q : O ⧸ powSub (M := O) ϖ n), s • q = φ s • q := fun _ _ => rfl
    have : CompactSpace (O ⧸ powSub (M := O) ϖ n) := by
      refine ⟨?_⟩
      rw [← (Submodule.mkQ_surjective (powSub (M := O) ϖ n)).range_eq]
      exact isCompact_range (Submodule.continuous_mkQ _)
    have : Finite (O ⧸ powSub (M := O) ϖ n) := finite_of_compact_of_discrete
    have hkill : ∀ m : O ⧸ powSub (M := O) ϖ n, ((p : ℤ_[p]) ^ n) • m = 0 := by
      intro m
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
      rw [hsm, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mem_powSub]
      refine ⟨t ^ n * x, ?_⟩
      rw [map_pow, map_natCast, ht, smul_eq_mul, smul_eq_mul]
      ring
    obtain ⟨-, hex, -⟩ := hgen n (O ⧸ powSub (M := O) ϖ n) hkill
    have hz : IsCoc χ (fun q : G × G => (Submodule.Quotient.mk (w q) : O ⧸ powSub (M := O) ϖ n)) := by
      refine ⟨(IsLocallyConstant.iff_continuous _).mpr ((Submodule.continuous_mkQ _).comp hwZ.1),
        fun g h k => ?_⟩
      have e := hwZ.2 g h k
      rw [twist_apply, hε g] at e
      rw [hsm, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_sub,
        ← Submodule.Quotient.mk_add, ← Submodule.Quotient.mk_sub, e, Submodule.Quotient.mk_zero]
    obtain ⟨x, b, hb, hzb⟩ := hex _ hz
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine ⟨a, b, hb.continuous, fun g h => ?_⟩
    have e := hzb (g, h)
    simp only [cob, hsm] at e
    rw [d1_apply, quotRep_twist_apply, hε g, Submodule.Quotient.mk_sub, e,
      show a * φ (c (g, h)) = φ (c (g, h)) • a from mul_comm _ _, Submodule.Quotient.mk_smul]
    abel

  have hanti : ∀ n, S (n + 1) ⊆ S n := by
    intro n a ha
    obtain ⟨b, hb, hd⟩ := ha
    refine ⟨fun g => Submodule.factor (powSub_anti (M := O) ϖ (Nat.le_succ n)) (b g),
      (continuous_factor ϖ (Nat.le_succ n)).comp hb, fun g h => ?_⟩
    have e := hd g h
    rw [d1_apply] at e
    rw [d1_apply, ← factor_quotRep_of_le ε ϖ (Nat.le_succ n), ← map_sub, ← map_add, e]
    exact Submodule.factor_mk _ _

  have hclosed : ∀ n, IsClosed (S n) := by
    intro n
    have := hdisc n
    have hpre : S n = (powSub (M := O) ϖ n).mkQ ⁻¹' ((powSub (M := O) ϖ n).mkQ '' S n) := by
      refine (Set.subset_preimage_image _ _).antisymm ?_
      rintro a' ⟨a, ⟨b, hb, hd⟩, hmk⟩
      refine ⟨b, hb, fun g h => ?_⟩
      rw [hd g h, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_sub]
      congr 1
      rw [Submodule.Quotient.eq]
      have hmk' : Submodule.Quotient.mk (p := powSub (M := O) ϖ n) a =
          Submodule.Quotient.mk a' := hmk
      have hd' := Submodule.smul_mem _ (φ (c (g, h))) ((Submodule.Quotient.eq _).mp hmk')
      rw [smul_eq_mul] at hd'
      convert hd' using 1
      ring
    rw [hpre]
    exact (isClosed_discrete _).preimage (Submodule.continuous_mkQ _)

  obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hanti hne
    (hclosed 0).isCompact hclosed
  exact ⟨a, fun n => Set.mem_iInter.mp ha n⟩

end GlobalTheory.UnifSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitVectorOfUnitFor
section
noncomputable section

namespace GlobalTheory.WachUnit

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

theorem unitVector_of_unitFor (E : EtTie W RA RW inclR φR gR πA)
    (hU : GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.UnitFor E) :
    ∃ (e : W.DD W.one) (e₀ : ↥W.one.L.T), Submodule.span O {e₀} = ⊤ ∧
      W.one.L.T = Submodule.span O {(e₀ : W.one.V)} ∧
      E.jD W.one e = (1 : RW) ⊗ₜ[O] e₀ ∧
      W.N W.one = Submodule.span (LetA O n) {e} ∧
      Submodule.span W.EE {e} = (⊤ : Submodule W.EE (W.DD W.one)) ∧
      W.φD W.one e = e ∧ (∀ g, W.γD W.one g e = e) ∧
      ∀ a : LetA O n, a • e = 0 → a = 0 := by
  obtain ⟨-, e₀, h₀, -, -⟩ := E.one_e
  obtain ⟨e, hj, hbij, hφ, hγ, hN⟩ := hU e₀ h₀
  refine ⟨e, e₀, h₀, ?_, hj, hN, ?_, hφ, hγ, fun a ha => ?_⟩
  · have h1 := congrArg (Submodule.map W.one.L.T.subtype) h₀
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, Set.image_singleton] at h1
    exact h1.symm
  · rw [eq_top_iff]
    rintro z -
    exact Submodule.mem_span_singleton.2 (hbij.2 z)
  · apply W.EE_inj
    apply hbij.1
    simp only
    rw [algebraMap_smul, algebraMap_smul, ha, zero_smul]

end Generic

open Formalism.MainNotions.N Formalism.MainNotions.LocalSituation

theorem unitVector : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∃ (e : W.DD W.one) (e₀ : ↥W.one.L.T), Submodule.span ↥(OL LL) {e₀} = ⊤ ∧ W.one.L.T = Submodule.span ↥(OL LL) {(e₀ : W.one.V)} ∧ E.jD W.one e = (1 : RW LL) ⊗ₜ[↥(OL LL)] e₀ ∧ W.N W.one = Submodule.span (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) {e} ∧ Submodule.span W.EE {e} = (⊤ : Submodule W.EE (W.DD W.one)) ∧ W.φD W.one e = e ∧ (∀ g, W.γD W.one g e = e) ∧ ∀ a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)), a • e = 0 → a = 0 := by
  intro D HW F l _ K s LL h
  exact unitVector_of_unitFor _ (unitPart l (D.loc l) (D.locA l) (HW l) (F l) K s LL h)

end GlobalTheory.WachUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIntegersTensorEqLetterwiseProductAinfStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedIntegers_tensor_eq_letterwise_product_Ainf : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ emb : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1), Function.Bijective emb → ∃ u : (ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL)) →ₐ[↥(OL LL)] RA LL, (∀ (c : ↥(K0 K)) (m : ℕ), 0 < m → ¬ l ∣ m → (c : Om l) ^ m = 1 → ∀ xb : OCb l, IsTiltOf (c : Om l) m xb → ∀ o : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL), (∀ i, ((o i : ↥(OL LL)) : ↥LL.1) = emb i c) → u o = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] WittVector.teichmuller l xb) ∧ ∀ (S : Type) [CommRing S] [Algebra ↥(OL LL) S] (f f' : (ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL)) →ₐ[↥(OL LL)] S), (∀ (c : ↥(K0 K)) (m : ℕ), 0 < m → ¬ l ∣ m → (c : Om l) ^ m = 1 → ∀ o : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL), (∀ i, ((o i : ↥(OL LL)) : ↥LL.1) = emb i c) → f o = f' o) → f = f' := by
  first | exact @GlobalTheory.UnramIdem.exists_prod_hom | exact GlobalTheory.UnramIdem.exists_prod_hom | (intros; apply GlobalTheory.UnramIdem.exists_prod_hom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XiGradedPieceIsoTwistedOCStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.xiGradedPiece_iso_twistedOC : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (i : ℤ), ∃ Φ : Qab (AinfSub l) (xiU AI) i (i + 1) →+ PadicComplex l, Function.Injective Φ ∧ Set.range Φ = {y | ‖y‖ ≤ 1} ∧ (∀ (z : ℤ_[l]) x, Φ (z • x) = zC z * Φ x) ∧ ∀ g : GQ l, g (P.ζQ 1) = P.ζQ 1 → ∀ x, Φ (actQab (xiOK AI) i (i + 1) g x) = chiC P.χQ i g * AI.actC g (Φ x) := by
  first | exact @GlobalTheory.Cyc.Graded.graded_iso | exact GlobalTheory.Cyc.Graded.graded_iso | (intros; apply GlobalTheory.Cyc.Graded.graded_iso <;> assumption)
end

