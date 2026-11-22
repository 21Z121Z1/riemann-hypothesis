import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0430
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0089
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0124
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0082
import Formalism.FormalDegreeBessel.StatementRP
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0139
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0121
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0112
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0132
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNeZeroCommonZeroOfConstantCoeffEqZero
section
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem exists_ne_zero_common_zero_of_constantCoeff_eq_zero :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (n r : ℕ) (f : Fin r → MvPolynomial (Fin n) k),
      (∀ i, MvPolynomial.constantCoeff (f i) = 0) → r < n →
        ∃ x : Fin n → k, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (f i) = 0 := by
  intro k _ _ n r f hf hrn
  classical
  set m : Ideal (MvPolynomial (Fin n) k) := RingHom.ker (MvPolynomial.eval (0 : Fin n → k)) with hm
  have hsurj : Function.Surjective (MvPolynomial.eval (0 : Fin n → k)) :=
    fun c => ⟨MvPolynomial.C c, by simp⟩
  haveI hmax : m.IsMaximal := RingHom.ker_isMaximal_of_surjective _ hsurj
  set I : Ideal (MvPolynomial (Fin n) k) := Ideal.span ((Finset.univ.image f : Finset _) : Set (MvPolynomial (Fin n) k)) with hI
  have hIm : I ≤ m := by
    rw [hI, Ideal.span_le]
    intro g hg
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ] at hg
    obtain ⟨i, rfl⟩ := hg
    simp [hm, RingHom.mem_ker, MvPolynomial.eval_zero, hf i]
  have hItop : I ≠ ⊤ := fun h => hmax.ne_top (top_le_iff.mp (h ▸ hIm))
  obtain ⟨P, hP⟩ := Ideal.nonempty_minimalPrimes hItop
  haveI hPp : P.IsPrime := hP.1.1
  have hht : P.height ≤ r := by
    have h1 := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hP
    refine h1.trans ?_
    exact_mod_cast Finset.card_image_le.trans (by simp)
  have hmh : m.height = n := (ReciprocityTheory.CA.height_maximal_mvPolynomial_field k n m).2
  have hPne : P ≠ m := by
    intro h
    rw [h, hmh] at hht
    exact absurd (by exact_mod_cast hht : n ≤ r) (not_le.mpr hrn)
  by_contra hcon
  push_neg at hcon
  apply hPne
  have hsub : MvPolynomial.zeroLocus k P ⊆ {0} := by
    intro x hx
    by_contra hx0
    obtain ⟨i, hi⟩ := hcon x hx0
    apply hi
    have := hx (f i) (hP.1.2 (Ideal.subset_span (by simp)))
    simpa [MvPolynomial.coe_aeval_eq_eval] using this
  have hle : m ≤ P := by
    intro p hp
    have h2 : p ∈ MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k P) := by
      intro x hx
      rw [Set.mem_singleton_iff.mp (hsub hx)]
      exact hp
    rwa [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, hPp.radical] at h2
  exact (hmax.eq_of_le hPp.ne_top hle).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNeZeroForallPointExtendSubalgebra
section
open Polynomial

namespace GlobalTheory

theorem exists_ne_zero_forall_point_extend_subalgebra :
    ∀ (k A R : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [CommRing R] [IsDomain R] [Algebra k R] (ξ : A →ₐ[k] R),
    Function.Injective ξ → ∀ T : Finset R,
    ∃ (a : A) (S : Subalgebra k R) (hξ : ∀ u, ξ u ∈ S), a ≠ 0 ∧ (∀ t ∈ T, t ∈ S) ∧
      ∀ φ : A →ₐ[k] k, φ a ≠ 0 → ∃ ψ : S →ₐ[k] k, ∀ u, ψ ⟨ξ u, hξ u⟩ = φ u := by
  intro k A R _ _ _ _ _ _ _ _ _ ξ hinj T
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra k A).FG)
  set S : Subalgebra k R := Algebra.adjoin k (ξ '' (s : Set A) ∪ (T : Set R)) with hSdef
  have hξ : ∀ u, ξ u ∈ S := by
    intro u
    have hu : u ∈ Algebra.adjoin k (s : Set A) := hs ▸ Algebra.mem_top
    have : ξ u ∈ (Algebra.adjoin k (s : Set A)).map ξ := ⟨u, hu, rfl⟩
    rw [AlgHom.map_adjoin] at this
    exact Algebra.adjoin_mono Set.subset_union_left this
  have hT : ∀ t ∈ T, t ∈ S := fun t ht => Algebra.subset_adjoin (Set.subset_union_right ht)
  have hSfg : S.FG := Subalgebra.fg_def.2
    ⟨_, (s.finite_toSet.image ξ).union T.finite_toSet, rfl⟩
  haveI : Algebra.FiniteType k S := (Subalgebra.fg_iff_finiteType S).1 hSfg
  let f : A →ₐ[k] S := ξ.codRestrict S hξ
  letI : Algebra A S := f.toRingHom.toAlgebra
  haveI : IsScalarTower k A S := IsScalarTower.of_algebraMap_eq fun c => (f.commutes c).symm
  haveI : Algebra.FiniteType A S := Algebra.FiniteType.of_restrictScalars_finiteType k A S
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have hfinj : Function.Injective (algebraMap A S) := by
    intro x y h
    apply hinj
    have := congrArg Subtype.val h
    exact this
  have hfp : Algebra.FinitePresentation A S := Algebra.FinitePresentation.of_finiteType.1 ‹_›
  have hc := PrimeSpectrum.isConstructible_range_comap
    (RingHom.finitePresentation_algebraMap.mpr hfp)
  obtain ⟨q, hq, H⟩ := exists_basicOpen_subset_of_isConstructible_of_bot_mem hc
    ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext (Ideal.comap_bot_of_injective _ hfinj)⟩
  refine ⟨q, S, hξ, hq, hT, fun φ hφ => ?_⟩
  obtain ⟨ψ, hψ⟩ := exists_ringHom_extend_of_ker_mem_range_comap (A := S) φ.toRingHom
    (H ⟨RingHom.ker φ.toRingHom, RingHom.ker_isPrime _⟩ (by simpa [RingHom.mem_ker] using hφ))
  have hψu : ∀ u, ψ ⟨ξ u, hξ u⟩ = φ u := fun u => by
    have := RingHom.congr_fun hψ u
    exact this
  refine ⟨{ ψ with commutes' := fun c => ?_ }, hψu⟩
  have h1 : (algebraMap k S c) = ⟨ξ (algebraMap k A c), hξ _⟩ := by
    ext; simp
  simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
    MonoidHom.coe_coe]
  rw [h1, hψu, φ.commutes]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPadicCocycleOfCompatiblePolyFamily
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3.CocLift

open MvPolynomial CongruenceSubgroup

theorem gamma_of_dvd {a b : ℕ} (h : a ∣ b) {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma b) : δ ∈ Gamma a := by
  rw [Gamma_mem] at hδ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hδ
  have key : ∀ x : ℤ, ZMod.castHom h (ZMod a) (x : ZMod b) = (x : ZMod a) := fun x => map_intCast _ x
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← key, h1, map_one]
  · rw [← key, h2, map_zero]
  · rw [← key, h3, map_zero]
  · rw [← key, h4, map_one]

theorem gamma_le_gam {N l K : ℕ} (hN : N ∣ K) (hl : l ∣ K) {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma K) :
    δ ∈ Gam N l := by
  have h1 := Gamma_mem.mp (gamma_of_dvd hN hδ)
  have h2 := Gamma_mem.mp (gamma_of_dvd hl hδ)
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Gamma1_mem]; exact ⟨h1.1, h1.2.2.2, h1.2.2.1⟩
  · rw [Gamma0_mem]; exact h2.2.2.1

theorem entries_of_gamma {K : ℕ} {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma K) :
    ∀ i j, (((δ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod K) = (((1 : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod K) := by
  obtain ⟨h1, h2, h3, h4⟩ := Gamma_mem.mp hδ
  intro i j
  fin_cases i <;> fin_cases j <;> simp [h1, h2, h3, h4]

theorem step (N l w : ℕ) [Fact l.Prime] (hN : 0 < N) (hl2 : l ≠ 2) (hlN : ¬ l ∣ N) (hw : Odd w)
    (Φ : (n : ℕ) → SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n))) (hΦ : IsFam l w (Gam N l) Φ)
    (n : ℕ) (y : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)))
    (hy : IsCoc w (Gam N l) y) (hyn : Near y (Φ n)) :
    ∃ y' : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ (n + 1))), IsCoc w (Gam N l) y' ∧ Near y' (Φ (n + 1)) ∧
      ∀ γ ∈ Gam N l, MvPolynomial.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n))) (y' γ) = y γ := by
  have hp : l.Prime := Fact.out
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero (l ^ (n + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨z', hz', hz'n⟩ := GlobalTheory.T.exists_homogeneousPolyCocycle_eqOn_congruence N l w hN hp hl2 hlN hw Φ hΦ (n + 1)
  set c := ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n)) with hc
  have L := GlobalTheory.KZ.polySlash_laws (ZMod (l ^ n))
  have L' := GlobalTheory.KZ.polySlash_laws (ZMod (l ^ (n + 1)))
  let r : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)) := fun δ => MvPolynomial.map c (z' δ)
  have hr : IsCoc w (Gam N l) r := by
    refine ⟨fun γ hγ => (hz'.1 γ hγ).map c, fun γ hγ δ hδ => ?_⟩
    simp only [r]
    rw [hz'.2 γ hγ δ hδ, map_add, L'.2.2.2.2.1 _ c]
  have hnear : Near r y := by
    obtain ⟨M1, hM1, h1⟩ := hz'n
    obtain ⟨M2, hM2, h2⟩ := hΦ.2.2.2 n
    obtain ⟨M3, hM3, h3⟩ := hyn
    refine ⟨M1 * M2 * M3, by positivity, fun δ hδ => ?_⟩
    have d1 := gamma_of_dvd (Dvd.intro _ rfl |>.trans (Dvd.intro _ rfl)) hδ
    have d2 := gamma_of_dvd ((Dvd.intro_left _ rfl).trans (Dvd.intro _ rfl)) hδ
    have d3 := gamma_of_dvd (Dvd.intro_left _ rfl) hδ
    simp only [r]
    rw [h1 δ d1]
    exact (h2 δ d2).trans (h3 δ d3).symm
  obtain ⟨p, hph, hpγ⟩ := GlobalTheory.T.homogeneousPolyCocycle_diff_coboundary_of_eqOn N l w n hN hp hl2 hlN hw r y hr hy hnear
  let pt : MvPolynomial (Fin 2) (ZMod (l ^ (n + 1))) :=
    ∑ m ∈ p.support, MvPolynomial.monomial m (((p.coeff m).val : ℕ) : ZMod (l ^ (n + 1)))
  have hpc : ∀ m, pt.coeff m = (((p.coeff m).val : ℕ) : ZMod (l ^ (n + 1))) := by
    intro m
    simp only [pt, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [MvPolynomial.notMem_support_iff] at h
      rw [h, ZMod.val_zero, Nat.cast_zero]
  have hmap : MvPolynomial.map c pt = p := by
    ext m
    rw [MvPolynomial.coeff_map, hpc, map_natCast, ZMod.natCast_zmod_val]
  have hpth : pt.IsHomogeneous w := by
    intro m hm
    apply hph
    intro h0
    apply hm
    rw [hpc, h0, ZMod.val_zero, Nat.cast_zero]
  refine ⟨fun δ => z' δ - (slP (δ : Matrix (Fin 2) (Fin 2) ℤ) pt - pt), ⟨fun γ hγ => ?_, fun γ hγ δ hδ => ?_⟩, ?_, ?_⟩
  · exact (hz'.1 γ hγ).sub ((L'.2.2.1 _ w pt hpth).sub hpth)
  · simp only
    rw [hz'.2 γ hγ δ hδ, Matrix.SpecialLinearGroup.coe_mul, L'.1, map_sub, map_sub]
    abel
  · obtain ⟨M1, hM1, h1⟩ := hz'n
    refine ⟨M1 * l ^ (n + 1), Nat.mul_pos hM1 (pow_pos hp.pos _), fun δ hδ => ?_⟩
    have d1 := gamma_of_dvd (Dvd.intro _ rfl) hδ
    have d2 := gamma_of_dvd (Dvd.intro_left _ rfl) hδ
    simp only
    rw [L'.2.2.2.2.2.1 _ 1 pt (entries_of_gamma d2), L'.2.1, sub_self, sub_zero, h1 δ d1]
  · intro γ hγ
    simp only
    rw [map_sub, map_sub, L'.2.2.2.2.1 _ c, hmap, ← hpγ γ hγ]
    simp only [r]
    abel

end GlobalTheory.KZ.H3.CocLift

namespace GlobalTheory.KZ.H3

open Classical in

theorem cocycle_lift_of_fam : ∀ (N l w : ℕ) [Fact l.Prime], 0 < N → l ≠ 2 → ¬ l ∣ N → Odd w → ∀ Φ, IsFam l w (Gam N l) Φ →
    ∃ z : SL(2, ℤ) → MvPolynomial (Fin 2) ℤ_[l], IsCoc w (Gam N l) z ∧
      ∀ n, Near (fun δ => MvPolynomial.map (PadicInt.toZModPow n) (z δ)) (Φ n) := by
  intro N l w _ hN hl2 hlN hw Φ hΦ
  have hp : l.Prime := Fact.out
  have lev := GlobalTheory.T.exists_homogeneousPolyCocycle_eqOn_congruence N l w hN hp hl2 hlN hw Φ hΦ
  choose F hF1 hF2 hF3 using CocLift.step N l w hN hl2 hlN hw Φ hΦ
  let seq : (n : ℕ) → {y : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)) // IsCoc w (Gam N l) y ∧ Near y (Φ n)} :=
    fun n => Nat.rec (motive := fun n => {y : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)) //
        IsCoc w (Gam N l) y ∧ Near y (Φ n)})
      ⟨(lev 0).choose, (lev 0).choose_spec⟩
      (fun n y => ⟨F n y.1 y.2.1 y.2.2, hF1 n y.1 y.2.1 y.2.2, hF2 n y.1 y.2.1 y.2.2⟩) n
  have hseq : ∀ n, ∀ γ ∈ Gam N l, MvPolynomial.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n)))
      ((seq (n + 1)).1 γ) = (seq n).1 γ :=
    fun n => hF3 n (seq n).1 (seq n).2.1 (seq n).2.2
  let fam : SL(2, ℤ) → (n : ℕ) → MvPolynomial (Fin 2) (ZMod (l ^ n)) :=
    fun δ n => if δ ∈ Gam N l then (seq n).1 δ else 0
  have hfam : ∀ δ ∈ Gam N l, ∀ n, fam δ n = (seq n).1 δ := fun δ hδ n => if_pos hδ
  have hhom : ∀ δ n, (fam δ n).IsHomogeneous w := by
    intro δ n
    by_cases hδ : δ ∈ Gam N l
    · rw [hfam δ hδ]; exact (seq n).2.1.1 δ hδ
    · simp only [fam, if_neg hδ]; exact MvPolynomial.isHomogeneous_zero _ _ _
  have hcomp : ∀ δ n, MvPolynomial.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n)))
      (fam δ (n + 1)) = fam δ n := by
    intro δ n
    by_cases hδ : δ ∈ Gam N l
    · rw [hfam δ hδ, hfam δ hδ]; exact hseq n δ hδ
    · simp only [fam, if_neg hδ, map_zero]
  choose q hq using fun δ => homogeneous_lift_compatible l w (fam δ) (hhom δ) (hcomp δ)
  have L := GlobalTheory.KZ.polySlash_laws ℤ_[l]
  refine ⟨q, ⟨fun γ _ => (hq γ).1, fun γ hγ δ hδ => ?_⟩, fun n => ?_⟩
  · refine ((hq (γ * δ)).2.2 _ fun n => ?_).symm
    have hγδ : γ * δ ∈ Gam N l := (Gam N l).mul_mem hγ hδ
    rw [map_add, L.2.2.2.2.1 _ _, (hq γ).2.1 n, (hq δ).2.1 n, hfam γ hγ, hfam δ hδ, hfam _ hγδ,
      (seq n).2.1.2 γ hγ δ hδ]
  · obtain ⟨M, hM, hMδ⟩ := (seq n).2.2
    refine ⟨M * (N * l), Nat.mul_pos hM (Nat.mul_pos hN hp.pos), fun δ hδ => ?_⟩
    have d1 := CocLift.gamma_of_dvd (Dvd.intro _ rfl) hδ
    have d2 := CocLift.gamma_le_gam (N := N) (l := l) ((Dvd.intro _ rfl).trans (Dvd.intro_left _ rfl))
      ((Dvd.intro_left _ rfl).trans (Dvd.intro_left _ rfl)) hδ
    simp only
    rw [(hq δ).2.1 n, hfam δ d2]
    exact hMδ δ d1

end GlobalTheory.KZ.H3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GramRight
section
open Matrix Formalism.QuantumDeterminants

noncomputable section

namespace GlobalTheory.LevelUnitary

def incl (k i r' : ℕ) : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * r' + k + 1)) ℂ :=
  fun p j => if p = levPos k i r' j then 1 else 0

def outer (k i r' : ℕ) : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ :=
  diagonal fun p => if i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i then 0 else 1

variable (k i r' : ℕ)

theorem mul_incl {m : Type} (M : Matrix m (Fin (2 * (i + r') + k + 1)) ℂ) (p : m) (j) :
    (M * incl k i r') p j = M p (levPos k i r' j) := by
  simp [Matrix.mul_apply, incl]

theorem inclH_mul {m : Type} (M : Matrix (Fin (2 * (i + r') + k + 1)) m ℂ) (p : m) (j) :
    ((incl k i r')ᴴ * M) j p = M (levPos k i r' j) p := by
  simp [Matrix.mul_apply, incl, conjTranspose_apply, apply_ite star]

theorem incl_mul {m : Type} (M : Matrix (Fin (2 * r' + k + 1)) m ℂ) (p) (q : m) :
    (incl k i r' * M) p q =
      if hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i then M ⟨p.val - i, by omega⟩ q else 0 := by
  rw [Matrix.mul_apply]
  split_ifs with hp
  · rw [Finset.sum_eq_single ⟨p.val - i, by omega⟩]
    · have : p = levPos k i r' ⟨p.val - i, by omega⟩ := by
        apply Fin.ext; simp only [levPos]; omega
      rw [incl, if_pos this, one_mul]
    · intro b _ hb
      have : ¬ p = levPos k i r' b := by
        intro h; apply hb; apply Fin.ext
        have := congrArg Fin.val h
        simp only [levPos] at this ⊢; omega
      rw [incl, if_neg this, zero_mul]
    · simp
  · apply Finset.sum_eq_zero
    intro b _
    have : ¬ p = levPos k i r' b := by
      intro h; apply hp
      have := congrArg Fin.val h
      have hb := b.isLt
      simp only [levPos] at this ⊢; omega
    rw [incl, if_neg this, zero_mul]

theorem gram_inner : (incl k i r')ᴴ * Hpk k (i + r') * incl k i r' = Hpk k r' := by
  ext a b
  rw [mul_incl, inclH_mul]
  have ha := a.isLt
  have hb := b.isLt
  have hva : (levPos k i r' a).val = a.val + i := rfl
  have hvb : (levPos k i r' b).val = b.val + i := rfl
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

end GlobalTheory.LevelUnitary
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesEqOfQExpansionSumAboveEventuallyEqStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hahnSeries_eq_of_qExpansionSumAbove_eventually_eq : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (C C' C'' : ℝ) (φ φ' : ℂ → ℂ) (h h' : HahnSeries ℚ Ω), Den h → Den h' → HS ε C φ h → HS ε C' φ' h' → (∀ z : ℂ, C'' < z.im → φ z = φ' z) → h = h' := by
  first | exact @GlobalTheory.FN.hs_uniq | exact GlobalTheory.FN.hs_uniq | (intros; apply GlobalTheory.FN.hs_uniq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSomeLevelOverCompGLTwoPosRatStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSomeLevelOver_compGLTwoPosRat : ∀ (E : Subring ℂ) (g : GQ) (f : ℍ → ℂ), (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) → InR E f → InR E (GlobalTheory.FN.cmp g f) := by
  first | exact @GlobalTheory.FN.inR_cmp | exact GlobalTheory.FN.inR_cmp | (intros; apply GlobalTheory.FN.inR_cmp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgZpMapOfAlgebraic
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.Glue

theorem isAlgZp_map_of_algebraic : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl] (j : Ω →+* Ωl) (x : Ω), IsAlgZp p (j x) := by
  intro Ω _ _ _ p _ Ωl _ _ j x
  have hx : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
  have hz : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 hx
  obtain ⟨P, hP, hPx⟩ := hz
  refine ⟨P.map (Int.castRingHom ℤ_[p]), ?_, ?_⟩
  · exact (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).2 hP
  · rw [Polynomial.map_map, Polynomial.aeval_def, Polynomial.eval₂_map]
    have e1 : (algebraMap (O0 p) Ωl).comp ((algebraMap ℤ_[p] (O0 p)).comp (Int.castRingHom ℤ_[p])) = j.comp (algebraMap ℤ Ω) := RingHom.ext_int _ _
    rw [e1, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, hPx, map_zero]

theorem zt_prim_and_pow : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (l n : ℕ), 0 < l → IsPrimitiveRoot (zt ε l n) (l ^ n) ∧ zt ε l (n + 1) ^ l = zt ε l n := by
  intro Ω _ _ _ ε l n hl
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hkey : ∀ m : ℕ, ε (zt ε l m) = Complex.exp (2 * Real.pi * Complex.I / ((l ^ m : ℕ) : ℂ)) := by
    intro m
    have hN : l ^ m ≠ 0 := pow_ne_zero _ hl.ne'
    have hw : Complex.exp (2 * Real.pi * Complex.I * (((1 / (l : ℚ) ^ m : ℚ)) : ℂ)) =
        Complex.exp (2 * Real.pi * Complex.I / ((l ^ m : ℕ) : ℂ)) := by
      congr 1; push_cast; ring
    haveI : NeZero ((l ^ m : ℕ) : Ω) := ⟨by exact_mod_cast hN⟩
    haveI : NeZero (l ^ m) := ⟨hN⟩
    obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ m)
    have hz' : IsPrimitiveRoot (ε z) (l ^ m) := hz.map_of_injective ε.injective
    have hp := Complex.isPrimitiveRoot_exp (l ^ m) hN
    obtain ⟨i, -, hi⟩ := hz'.eq_pow_of_pow_eq_one hp.pow_eq_one
    have hex : ∃ y, ε y = Complex.exp (2 * Real.pi * Complex.I * (((1 / (l : ℚ) ^ m : ℚ)) : ℂ)) :=
      ⟨z ^ i, by rw [map_pow, hi, hw]⟩
    show ε (Function.invFun ε _) = _
    rw [Function.invFun_eq hex, hw]
  refine ⟨?_, ?_⟩
  · rw [← IsPrimitiveRoot.map_iff_of_injective (f := ε) ε.injective, hkey]
    exact Complex.isPrimitiveRoot_exp _ (pow_ne_zero _ hl.ne')
  · apply ε.injective
    rw [map_pow, hkey, hkey, ← Complex.exp_nat_mul]
    congr 1
    have : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
    push_cast
    field_simp
    ring

theorem exists_cusp_embedding : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (A : ValuationSubring Ω), ((p : ℕ) : Ω) ∈ A.nonunits → ∃ (Ωl : Type) (_ : Field Ωl) (_ : Algebra (O0 p) Ωl), IsClo p Ωl ∧ ∃ (T : GlobalTheory.K5.Tower p Ωl) (j : Ω →+* Ωl), IsCusp ε A T j := by
  intro Ω _ _ _ ε X _ p _ _ A hA
  let Ωl := AlgebraicClosure (FractionRing (O0 p))
  have hcl : IsClo p Ωl := GlobalTheory.K5.Basic.isClo_algebraicClosure p
  haveI : CharZero Ωl := GlobalTheory.K5.Basic.charZero_of_isClo hcl
  haveI : IsAlgClosed Ωl := hcl.clo
  let j0 : Ω →+* Ωl := (IsAlgClosed.lift : Ω →ₐ[ℚ] Ωl).toRingHom
  obtain ⟨B, hBp, hB⟩ := GlobalTheory.T.exists_valuationSubring_pullback_integral_elements p Ωl hcl j0
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_algEquiv_map_valuationSubring_over_prime p A B hA hBp
  let j : Ω →+* Ωl := j0.comp σ.toRingEquiv.toRingHom
  have hint : ∀ x, x ∈ A ↔ IsInt p (j x) := fun x => (hσ x).symm.trans (hB _)
  have hl : 0 < p := (Fact.out : p.Prime).pos
  let T0 := (GlobalTheory.K5.Basic.nonempty_tower hcl).some
  let T : GlobalTheory.K5.Tower p Ωl :=
    { ζ := fun n => j (zt ε p n), qq := T0.qq,
      prim := fun n => (zt_prim_and_pow ε p n hl).1.map_of_injective j.injective,
      ζpow := fun n => by simp only [← map_pow, (zt_prim_and_pow ε p n hl).2],
      q0 := T0.q0, qpow := T0.qpow }
  refine ⟨Ωl, inferInstance, inferInstance, hcl, T, j, ?_⟩
  exact { int := hint, alg := isAlgZp_map_of_algebraic p Ωl j, root := fun n => rfl,
          dense := GlobalTheory.T.exists_algebraicNumber_congr_mod_prime_pow p A Ωl hcl j hint, down := GlobalTheory.T.exists_algClosure_automorphism_restricting_local p A Ωl hcl j hint,
          up := fun n s hs => GlobalTheory.T.exists_local_aut_fixing_tower_param_of_stabilizes p A Ωl hcl j hint T n s hs }

end GlobalTheory.Glue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralCoeffsOfGeometricFixedQExpansion
section
open GlobalTheory.K5

namespace GlobalTheory.K5.OrthDecomp

theorem orth : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (N : ℕ) (c : ℕ → Ω), (∀ j, ∀ g ∈ Ggeo p Ω, g (c j) = c j) →
      IsInt p (∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j) → ∀ j < p ^ N, IsInt p (c j) :=
  GlobalTheory.K5.Orth.orth

end GlobalTheory.K5.OrthDecomp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionFinsetProdZpowStatement
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLogDerivQExpansion_finset_prod_zpow : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n : ℕ) (s : ℚ) (ι : Type) (I : Finset ι) (f : ι → X.K) (φ : ι → HahnSeries ℚ Ω) (m : ι → ℤ), (∀ i ∈ I, IsDl X A l n s (f i) (φ i)) → IsDl X A l n s (∏ i ∈ I, f i ^ m i) (∑ i ∈ I, m i • φ i) := by
  first | exact @GlobalTheory.isDl_finset_prod_zpow | exact GlobalTheory.isDl_finset_prod_zpow | (intros; apply GlobalTheory.isDl_finset_prod_zpow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.JInvariantEqualSl2OrbitStatement
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.j_invariant_equal_sl2_orbit : ∀ τ σ : ℍ, E₄ τ ^ 3 * E₆ σ ^ 2 = E₆ τ ^ 2 * E₄ σ ^ 3 → ∃ γ : SL(2, ℤ), τ = γ • σ := by
  first | exact @GlobalTheory.JOrbit.exists_smul_of_E₄_E₆ | exact GlobalTheory.JOrbit.exists_smul_of_E₄_E₆ | (intros; apply GlobalTheory.JOrbit.exists_smul_of_E₄_E₆ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionFractionFieldOfQExpansionsStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_modularFunctionFractionField_of_qExpansions : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (a : ℂ → ℂ) (M : ℕ), 0 < M → DifferentiableOn ℂ a Hs → (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ z ∈ Hs, a (mob (ofSL γ) z) = a z) → (∀ γ : SL(2, ℤ), ∃ (c : ℤ → Ω) (n0 : ℤ), (∀ n < n0, c n = 0) ∧ ∀ z ∈ Hs, HasSum (fun n : ℤ => ε (c n) * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z / M)) (a (mob (ofSL γ) z))) → ∃ f : T.K, T.an f = (a : Mero) := by
  first | exact @GlobalTheory.FN.exists_of_qexp | exact GlobalTheory.FN.exists_of_qexp | (intros; apply GlobalTheory.FN.exists_of_qexp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemTowerUnionAdjoinOfGaloisFixedStatement
section
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_towerUnionAdjoin_of_galois_fixed : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (x : (integralClosure (O0 p) Ω)), (∀ g ∈ ⨅ n, Gn T n, g (x : Ω) = x) → x ∈ towerAlg T := by
  first | exact @GlobalTheory.K5.mem_towerAlg_of_fixed | exact GlobalTheory.K5.mem_towerAlg_of_fixed | (intros; apply GlobalTheory.K5.mem_towerAlg_of_fixed <;> assumption)
end

