import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Foundations.IsPrimitiveRootTopZeta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0054
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0055
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0198
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0208
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0210
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0218
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0217
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0126
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinsupp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0213
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0064

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRingOfIntegersOfHol
section
noncomputable section

open scoped MatrixGroups UpperHalfPlane
open Polynomial

namespace GlobalTheory.K4.TopUnits

open GlobalTheory.KZ GlobalTheory.Sieg

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def holSub (X : Tower Ω ε) : Subring X.K where
  carrier := {f | ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an f = (φ : Mero)}
  mul_mem' := by
    rintro f g ⟨φ, h1, h2⟩ ⟨ψ, h3, h4⟩
    exact ⟨φ * ψ, h1.mul h3, by rw [map_mul, h2, h4, Filter.Germ.coe_mul]⟩
  one_mem' := ⟨1, differentiableOn_const 1, by rw [map_one, Filter.Germ.coe_one]⟩
  add_mem' := by
    rintro f g ⟨φ, h1, h2⟩ ⟨ψ, h3, h4⟩
    exact ⟨φ + ψ, h1.add h3, by rw [map_add, h2, h4, Filter.Germ.coe_add]⟩
  zero_mem' := ⟨0, differentiableOn_const 0, by rw [map_zero, Filter.Germ.coe_zero]⟩
  neg_mem' := by
    rintro f ⟨φ, h1, h2⟩
    exact ⟨-φ, h1.neg, by rw [map_neg, h2, Filter.Germ.coe_neg]⟩

theorem finite_conj (X : Tower Ω ε) {M : ℕ} (hM : M ≠ 0) {f : X.K} (hf : f ∈ topL X M) :
    (Set.range fun γ : SL(2, ℤ) => X.sl (ofSL γ) f).Finite := by
  haveI : NeZero M := ⟨hM⟩
  haveI : (CongruenceSubgroup.Gamma M).FiniteIndex := by
    show (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))).ker.FiniteIndex
    exact Subgroup.finiteIndex_ker _
  refine (Set.finite_range fun q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma M => X.sl (ofSL q.out⁻¹) f).subset ?_
  rintro _ ⟨γ, rfl⟩
  obtain ⟨δ, hδ⟩ := QuotientGroup.mk_out_eq_mul (CongruenceSubgroup.Gamma M) γ⁻¹
  refine ⟨QuotientGroup.mk γ⁻¹, ?_⟩
  show X.sl (ofSL _) f = X.sl (ofSL γ) f
  rw [hδ, mul_inv_rev, inv_inv, map_mul, X.sl_mul, (mem_lev_iff X _ f).1 hf _ (inv_mem δ.2)]

theorem mem_ringOfIntegers_of_hol [IsAlgClosure ℚ Ω] (X : Tower Ω ε) {M : ℕ} (hM : M ≠ 0) {f : X.K} (hf : f ∈ topL X M)
    (hh : ∀ γ : SL(2, ℤ), X.sl (ofSL γ) f ∈ holSub X) :
    letI := algPoly X (CongruenceSubgroup.Gamma M)
    (⟨f, hf⟩ : topL X M) ∈ FunctionField.ringOfIntegers Ω (topL X M) := by
  letI := algPoly X (CongruenceSubgroup.Gamma M)
  classical
  set s : Finset X.K := (finite_conj X hM hf).toFinset with hs
  have hmem : ∀ g, g ∈ s ↔ ∃ γ : SL(2, ℤ), X.sl (ofSL γ) f = g := fun g => by simp [hs]
  set P : Polynomial X.K := ∏ g ∈ s, (Polynomial.X - C g) with hP
  have hmon : P.Monic := monic_prod_of_monic _ _ fun g _ => monic_X_sub_C g
  have hhol : ∀ n, P.coeff n ∈ holSub X := by
    have h1 : P ∈ Polynomial.liftsRing (holSub X).subtype := by
      refine Subring.prod_mem _ fun g hg => ?_
      obtain ⟨γ, rfl⟩ := (hmem g).1 hg
      exact ⟨Polynomial.X - C ⟨_, hh γ⟩, by simp⟩
    intro n
    obtain ⟨y, hy⟩ := (Polynomial.lifts_iff_coeff_lifts P).1 ((Polynomial.lifts_iff_liftsRing _ P).2 h1) n
    rw [← hy]
    exact y.2
  have hinv : ∀ (γ : SL(2, ℤ)) n, X.sl (ofSL γ) (P.coeff n) = P.coeff n := by
    intro γ n
    have e : P.map (X.sl (ofSL γ) : X.K →+* X.K) = P := by
      rw [hP, Polynomial.map_prod]
      simp only [Polynomial.map_sub, map_X, map_C]
      refine Finset.prod_nbij (fun g => X.sl (ofSL γ) g) (fun g hg => ?_) (fun a _ b _ h => (X.sl (ofSL γ)).injective h)
        (fun g hg => ?_) (fun g _ => rfl)
      · obtain ⟨δ, rfl⟩ := (hmem g).1 hg
        exact (hmem _).2 ⟨δ * γ, by rw [map_mul, X.sl_mul]⟩
      · obtain ⟨δ, rfl⟩ := (hmem g).1 hg
        refine ⟨X.sl (ofSL (δ * γ⁻¹)) f, (hmem _).2 ⟨_, rfl⟩, ?_⟩
        show X.sl (ofSL γ) _ = _
        rw [← X.sl_mul, ← map_mul, inv_mul_cancel_right]
    have := congrArg (fun Q => Polynomial.coeff Q n) e
    simpa only [Polynomial.coeff_map, RingHom.coe_coe] using this
  let A : (Polynomial Ω) →+* X.K := (Polynomial.aeval X.jK : (Polynomial Ω) →ₐ[Ω] X.K)
  have hl : P ∈ Polynomial.lifts A := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    have h := GlobalTheory.T.slTwo_invariant_holomorphic_mem_adjoin_jInvariant ε X ε.injective (X.j_hol.imp fun _ h => h.symm) _ (fun γ => hinv γ n) (hhol n)
    rw [Algebra.adjoin_singleton_eq_range_aeval] at h
    exact h
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hmon
  refine ⟨q, hqm, ?_⟩
  apply (topL X M).subtype.injective
  have eA : (topL X M).subtype.comp (algebraMap (Polynomial Ω) (topL X M)) = A := RingHom.ext fun p => coe_jPoly X _ p
  rw [Polynomial.hom_eval₂, eA, map_zero, ← Polynomial.eval_map, hq, hP, Polynomial.eval_prod]
  refine Finset.prod_eq_zero ((hmem f).2 ⟨1, by rw [map_one, X.sl_one]⟩) ?_
  simp

theorem siegel_hol [IsAlgClosure ℚ Ω] (X : Tower Ω ε) {c : ℕ} {y : Fin 2 → ℚ} (hy : admitted c y) :
    siegel X c y ∈ holSub X ∧ (siegel X c y)⁻¹ ∈ holSub X := by
  have hd : DifferentiableOn ℂ (sgC c y) Hs :=
    UpperHalfPlane.mdifferentiable_iff.1 (GlobalTheory.Sieg.mdifferentiable_sg c y hy)
  have hne : ∀ z, sgC c y z ≠ 0 := fun z => GlobalTheory.Sieg.sg_ne_zero c y _ hy
  have ha := SiegelMem.an_siegel_eq Ω ε X c y hy
  refine ⟨⟨_, hd, ha⟩, (sgC c y)⁻¹, hd.inv fun z _ => hne z, ?_⟩
  have h1 : X.an (siegel X c y)⁻¹ * X.an (siegel X c y) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (GlobalTheory.T.siegelUnitInTower_ne_zero Ω ε X c y hy), map_one]
  have h2 : X.an (siegel X c y) * (((sgC c y)⁻¹ : ℂ → ℂ) : Mero) = 1 := by
    rw [ha, ← Filter.Germ.coe_mul, ← Filter.Germ.coe_one]
    congr 1
    funext z
    exact mul_inv_cancel₀ (hne z)
  rw [← mul_one (X.an _), ← h2, ← mul_assoc, h1, one_mul]

def IsTopUnit (X : Tower Ω ε) (M : ℕ) (f : X.K) : Prop :=
  f ≠ 0 ∧ f ∈ topF X M ∧ ∃ hf : f ∈ topL X M,
    letI := algPoly X (CongruenceSubgroup.Gamma M)
    (⟨f, hf⟩ : topL X M) ∈ FunctionField.ringOfIntegers Ω (topL X M) ∧
      (⟨f, hf⟩ : topL X M)⁻¹ ∈ FunctionField.ringOfIntegers Ω (topL X M)

theorem isTopUnit_siegel [IsAlgClosure ℚ Ω] (X : Tower Ω ε) {c M a b : ℕ} (ha : a < M)
    (hy : admitted c ![(a : ℚ) / M, (b : ℚ) / M]) : IsTopUnit X M (siegel X c ![(a : ℚ) / M, (b : ℚ) / M]) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hM : 0 < M := lt_of_le_of_lt (Nat.zero_le a) ha
  have hL : siegel X c ![(a : ℚ) / M, (b : ℚ) / M] ∈ topL X M :=
    (mem_lev_iff X _ _).2 (GlobalTheory.T.siegel_invariant_principal_congruence Ω ε X c _ M hy hM ⟨a, b, by simp, by simp⟩)
  have hconj : ∀ γ : SL(2, ℤ), X.sl (ofSL γ) (siegel X c ![(a : ℚ) / M, (b : ℚ) / M]) = _ :=
    fun γ => SiegelSL.sl_siegel Ω ε X c _ γ hy
  refine ⟨GlobalTheory.T.siegelUnitInTower_ne_zero Ω ε X c _ hy, (mem_mdl_iff X _ _ _).2 ⟨hL, fun s hs => ?_⟩, hL, ?_, ?_⟩
  · have h := GlobalTheory.T.galois_action_siegelUnitInTower Ω ε X c M a b 1 s hM ha
      (by rw [Nat.cast_one]; exact (mem_fixMu_iff s).1 hs _ (isPrimitiveRoot_eOm ε hM.ne').pow_eq_one) hy
      (by rw [one_mul]; exact hy)
    rwa [one_mul] at h
  · exact mem_ringOfIntegers_of_hol X hM.ne' hL fun γ => by
      rw [hconj]; exact (siegel_hol X (SiegelMem.admissible_act_SL2 hy γ)).1
  · exact mem_ringOfIntegers_of_hol X hM.ne' (inv_mem hL) fun γ => by
      rw [map_inv₀, hconj]; exact (siegel_hol X (SiegelMem.admissible_act_SL2 hy γ)).2

theorem not_int {l c a M : ℕ} (hl : l.Prime) (hM : M ≠ 0) (hlM : l ∣ M) (hc : ¬ l ∣ c) (ha : ¬ l ∣ a) :
    (c : ℚ) * ((a : ℚ) / M) ∉ Set.range ((↑) : ℤ → ℚ) := by
  rintro ⟨m, hm⟩
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM
  have e : ((c * a : ℕ) : ℤ) = (M : ℤ) * m := by
    have : ((c * a : ℕ) : ℚ) = (M : ℚ) * m := by rw [hm]; push_cast; field_simp
    exact_mod_cast this
  have h : l ∣ c * a := hlM.trans (Int.natCast_dvd_natCast.1 ⟨m, e⟩)
  exact (hl.dvd_mul.1 h).elim hc ha

theorem isTopUnit_topU_topV [IsAlgClosure ℚ Ω] (X : Tower Ω ε) {l s N c d : ℕ} (x : ZMod N) (hl : l.Prime) (hN : 0 < N)
    (hs : 1 ≤ s) (hlN : Nat.Coprime l N) (hc1 : 1 < c) (hd1 : 1 < d) (hc : Nat.Coprime c (6 * l * N))
    (hd : Nat.Coprime d (6 * l * N)) :
    IsTopUnit X (l ^ s * N) (topU X l s N x c) ∧ IsTopUnit X (l ^ s * N) (topV X l s N d) := by
  have hM : l ^ s * N ≠ 0 := mul_ne_zero (pow_ne_zero s hl.ne_zero) hN.ne'
  have hls : l ∣ l ^ s := dvd_pow_self l (by omega)
  have hlM : l ∣ l ^ s * N := hls.mul_right N
  have hnd : ∀ {e : ℕ}, Nat.Coprime e (6 * l * N) → ¬ l ∣ e := fun {e} h =>
    (hl.coprime_iff_not_dvd).1 (h.coprime_dvd_right ((dvd_mul_left l 6).mul_right N)).symm
  have h6 : ∀ {e : ℕ}, Nat.Coprime e (6 * l * N) → Nat.Coprime e 6 := fun {e} h =>
    h.coprime_dvd_right ((dvd_mul_right 6 l).mul_right N)
  have hlN' : ¬ l ∣ N := (hl.coprime_iff_not_dvd).1 hlN
  have hlq : (l : ℚ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  constructor
  · have e : (![1 / (l : ℚ) ^ s, (x.val : ℚ) * (topT l s N : ℚ) / N] : Fin 2 → ℚ) =
        ![(N : ℚ) / (l ^ s * N : ℕ), ((x.val * topT l s N * l ^ s : ℕ) : ℚ) / (l ^ s * N : ℕ)] := by
      congr 1
      · push_cast; field_simp
      · congr 1; push_cast; field_simp
    unfold topU
    rw [e]
    refine isTopUnit_siegel X ?_ ⟨hc1, h6 hc, fun h => not_int hl hM hlM (hnd hc) hlN' h.1⟩
    have : 1 < l ^ s := Nat.one_lt_pow (by omega) hl.one_lt
    nlinarith
  · have e : (![0, 1 / (l : ℚ) ^ s + (topT l s N : ℚ) / N] : Fin 2 → ℚ) =
        ![((0 : ℕ) : ℚ) / (l ^ s * N : ℕ), ((N + topT l s N * l ^ s : ℕ) : ℚ) / (l ^ s * N : ℕ)] := by
      congr 1
      · simp
      · congr 1; push_cast; field_simp
    unfold topV
    rw [e]
    refine isTopUnit_siegel X (Nat.pos_of_ne_zero hM) ⟨hd1, h6 hd, fun h => not_int hl hM hlM (hnd hd) (fun h' => hlN' ?_) h.2⟩
    exact (Nat.dvd_add_left (hls.mul_left _)).1 h'

end GlobalTheory.K4.TopUnits

namespace GlobalTheory.K4

open GlobalTheory.KZ

end GlobalTheory.K4
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitAtScaledArgumentTwoVariableExpansion
section
noncomputable section

open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.Sieg GlobalTheory.QFam GlobalTheory.Sieg.DlogOne GlobalTheory.Sieg.Model

namespace GlobalTheory.SiegTwo

theorem map_smF {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K'] (ε : K →+* K') (c : ℤ) (j M : ℕ) (ζ : K)
    (a b : ℤ) (n : ℕ) : ε (smF c j M ζ a b n) = smF c j M (ε ζ) a b n := by
  simp [smF, eisF, const0, coefPos, apply_ite ε, map_ofNat]

theorem map_finsum_zpow {Ω : Type} [Field Ω] (ε : Ω →+* ℂ) (θ : ℤ →₀ ℤ) (w : ℤ → ℤ → ℤ) (hw : ∀ k, w k 0 = 0) (ζ : Ω)
    (g : ℤ) : ε (∑ᶠ k : ℤ, ((w k (θ k) : ℤ) : Ω) * ζ ^ (g * k)) = θ.sum fun k n => ((w k n : ℤ) : ℂ) * (ε ζ ^ g) ^ k := by
  rw [finsum_eq_sum_of_support_subset (s := θ.support), map_sum]
  · simp [Finsupp.sum, zpow_mul]
  · intro k hk
    by_contra h
    have : θ k = 0 := by simpa using h
    exact hk (by simp [this, hw])

theorem coeff_sgN {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : GlobalTheory.KZ.Tower Ω ε) (c : ℕ) {N : ℕ}
    (hN : 0 < N) (M : ℕ) (a : ℤ × ℤ) (r : ℚ) :
    (X.exp (sgN X c N M a)).coeff (r * N) = (X.exp (siegel X c ![(a.1 : ℚ) / M, (a.2 : ℚ) / M])).coeff r := by
  have hd : (0 : ℤ) < (!![(N : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by simpa [Matrix.det_fin_two] using hN
  have he : ∀ i k, ent (toGQ !![(N : ℤ), 0; 0, 1]) i k = ((!![(N : ℤ), 0; 0, 1] i k : ℤ) : ℚ) := fun i k => by
    simp only [ent, toGQ, dif_pos hd]; rfl
  have h := X.exp_upper (toGQ !![(N : ℤ), 0; 0, 1]) (by rw [he]; simp) (siegel X c ![(a.1 : ℚ) / M, (a.2 : ℚ) / M]) r
  rw [he, he, he] at h
  have h0 : eOm ε 0 = 1 := ε.injective (by rw [GalUnits.eps_eOm]; simp [ee])
  simpa [h0, sgN] using h

theorem sgN_two_variable : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (L N c : ℕ) (A₁ a₂ g : ℤ), 1 ≤ L → a₂ ≡ N * g [ZMOD (p : ℤ) ^ L] → (N : ℤ) ∣ a₂ → 0 < N → Nat.Coprime N p → 1 < c → Nat.Coprime c (6 * N * p) → ¬ (((N * p ^ L : ℕ) : ℤ) ∣ A₁) →
  ∃ θ : ℤ → ℤ → ℤ,
    (∀ r : ℤ, ∃ B : ℕ, ∀ k : ℤ, (B : ℤ) < |k| → θ k r = 0) ∧
    (∃ r0 : ℤ, ∀ k r : ℤ, r < r0 → θ k r = 0) ∧
    (∀ k r : ℤ, θ k r ≠ 0 → (p : ℤ) ^ L ∣ r - A₁ * k) ∧
    (∀ r : ℤ, (X.exp (sgN X c N (N * p ^ L) (A₁, a₂))).coeff ((r : ℚ) / (p : ℚ) ^ L) = ∑ᶠ k : ℤ, (θ k r : Ω) * zt ε p L ^ (g * k)) ∧
    (∀ r : ℤ, ∑ᶠ k : ℤ, ((k * θ k r : ℤ) : Ω) * zt ε p L ^ (g * k) =
      -∑ᶠ i : ℤ, (if 0 ≤ i then smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂ i.toNat else 0) *
        (X.exp (sgN X c N (N * p ^ L) (A₁, a₂))).coeff (((r - i : ℤ) : ℚ) / (p : ℚ) ^ L)) ∧
    (∀ n : ℕ, smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂ n ∈ Subring.closure {zt ε p L}) ∧
    (∃ r m : ℤ, (X.exp (sgN X c N (N * p ^ L) (A₁, a₂))).coeff ((r : ℚ) / (p : ℚ) ^ L) = zt ε p L ^ m ∨
      (X.exp (sgN X c N (N * p ^ L) (A₁, a₂))).coeff ((r : ℚ) / (p : ℚ) ^ L) = -(zt ε p L ^ m)) := by
  intro Ω _ _ _ ε X _ p hp _ L N c A₁ a₂ g _ hg hNa hN hNp hc hcop hA
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨g', rfl⟩ := hNa
  set M := N * p ^ L with hMd
  have hp0 : 0 < p := hp.out.pos
  have hM : 0 < M := by positivity
  have hMq : (M : ℚ) = N * p ^ L := by rw [hMd]; push_cast; rfl
  have hMc : (M : ℂ) = N * p ^ L := by rw [hMd]; push_cast; rfl
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hc6 : Nat.Coprime c 6 := (Nat.Coprime.coprime_mul_right_right hcop).coprime_mul_right_right
  have hcM : Nat.Coprime c M := Nat.Coprime.mul_right (Nat.Coprime.coprime_mul_right_right hcop).coprime_mul_left_right
    (hcop.coprime_mul_left_right.pow_right L)
  have hA2 : ¬ (M : ℤ) ∣ A₁ * c := fun h =>
    hA ((Nat.isCoprime_iff_coprime.2 hcM.symm).dvd_of_dvd_mul_right h)
  have hadm : admitted c ![(A₁ : ℚ) / M, ((N * g' : ℤ) : ℚ) / M] := by
    refine ⟨hc, hc6, fun ⟨⟨m, hm⟩, _⟩ => hA2 ⟨m, ?_⟩⟩
    have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
    have : (A₁ : ℚ) * c = M * m := by
      rw [hm]; simp only [Matrix.cons_val_zero]; field_simp
    exact_mod_cast this
  have ez : ε (zt ε p L) = ee (1 / (p : ℂ) ^ L) := by rw [zt, GalUnits.eps_eOm]; push_cast; rfl
  have eM : ε (eOm ε (1 / (M : ℚ))) = ee (1 / (M : ℂ)) := by rw [GalUnits.eps_eOm]; push_cast; rfl
  have hz1 : ee (1 / (p : ℂ) ^ L) ^ ((p : ℤ) ^ L) = 1 := by
    rw [← ee_int_mul]; push_cast; rw [mul_one_div_cancel (pow_ne_zero _ hpc)]; simp [ee]
  have hv : ee (((N * g' : ℤ) : ℂ) / M) = ε (zt ε p L) ^ g := by
    have hco : IsCoprime ((p : ℤ) ^ L) (N : ℤ) := (Nat.isCoprime_iff_coprime.2 hNp.symm).pow_left
    obtain ⟨u, hu⟩ := hco.dvd_of_dvd_mul_left (by simpa only [← mul_sub] using hg.dvd : (p : ℤ) ^ L ∣ N * (g - g'))
    rw [ez, show g = g' + (p : ℤ) ^ L * u by linarith, zpow_add₀ (ee_ne_zero _), zpow_mul, hz1, one_zpow, mul_one,
      ← ee_int_mul, hMc]
    congr 1
    push_cast
    field_simp
  obtain ⟨k, a, b, qa, qb, hj, i, hi⟩ := sg_jets hM hadm hA hA2
  rw [hv] at hj hi
  obtain ⟨r1, r2⟩ := exp_of_hasQ X _ _ hM k a (SiegelMem.an_siegel_eq Ω ε X c _ hadm) qa
  set y := X.exp (sgN X c N M (A₁, N * g')) with hy
  have hco : ∀ r : ℤ, y.coeff ((r : ℚ) / (p : ℚ) ^ L) =
      (X.exp (siegel X c ![(A₁ : ℚ) / M, ((N * g' : ℤ) : ℚ) / M])).coeff ((r : ℚ) / M) := fun r => by
    rw [← coeff_sgN X c hN M (A₁, N * g')]
    congr 1
    rw [hMq]; field_simp
  have c1 : ∀ n : ℕ, ε (y.coeff (((k + n : ℤ) : ℚ) / (p : ℚ) ^ L)) = a n := fun n => by
    rw [hco, ← r1]; push_cast; rfl
  have c0 : ∀ r : ℤ, r < k → y.coeff ((r : ℚ) / (p : ℚ) ^ L) = 0 := fun r hr => by
    rw [hco]
    refine r2 _ fun n h => ?_
    rw [div_left_inj' (by exact_mod_cast hM.ne')] at h
    have : r = k + n := by exact_mod_cast h
    omega
  have hb := HasQ.coeff_unique hM qb (by
    simpa only [neg_mul, one_mul] using ((GlobalTheory.T.hasQExpansion_smoothedEisensteinFx_weightOne c M A₁ (N * g') hM).mul_conv qa).const_mul (-1))
  choose θ t1 t2 t3 using fun n => exists_finsupp (hj n)
  have cases : ∀ r : ℤ, r < k ∨ ∃ n : ℕ, r = k + n := fun r => by
    rcases lt_or_ge r k with h | h
    · exact Or.inl h
    · exact Or.inr ⟨(r - k).toNat, by omega⟩
  set Θ : ℤ → ℤ → ℤ := fun l r => if r < k then 0 else θ (r - k).toNat l with hΘ
  have T0 : ∀ l r, r < k → Θ l r = 0 := fun l r h => if_pos h
  have T1 : ∀ l (n : ℕ), Θ l (k + n) = θ n l := fun l n => by
    simp only [hΘ]
    rw [if_neg (by omega), add_sub_cancel_left, Int.toNat_natCast]
  refine ⟨Θ, fun r => ?_, ⟨k, T0⟩, fun l r h => ?_, fun r => ?_, fun r => ?_, ?_, k, g * i, ?_⟩
  · rcases cases r with h | ⟨n, rfl⟩
    · exact ⟨0, fun l _ => T0 l r h⟩
    · refine ⟨(θ n).support.sup Int.natAbs, fun l hl => ?_⟩
      rw [T1]
      by_contra h
      have := Finset.le_sup (f := Int.natAbs) (Finsupp.mem_support_iff.2 h)
      rw [Int.abs_eq_natAbs] at hl
      omega
  · rcases cases r with h' | ⟨n, rfl⟩
    · exact absurd (T0 l r h') h
    · rw [T1] at h
      refine Dvd.dvd.trans ⟨N, ?_⟩ (t1 n l h)
      rw [hMd]; push_cast; ring
  · rcases cases r with h' | ⟨n, rfl⟩
    · simp [c0 r h', T0 _ r h']
    · simp only [T1]
      apply ε.injective
      rw [c1, map_finsum_zpow ε (θ n) (fun _ m => m) (fun _ => rfl)]
      exact t2 n
  · rcases cases r with h' | ⟨n, rfl⟩
    · simp only [T0 _ r h', mul_zero, Int.cast_zero, zero_mul, finsum_zero]
      rw [finsum_eq_zero_of_forall_eq_zero, neg_zero]
      intro l
      split_ifs with h
      · rw [c0 _ (by omega), mul_zero]
      · rw [zero_mul]
    · simp only [T1]
      apply ε.injective
      rw [map_finsum_zpow ε (θ n) (fun l m => l * m) (fun _ => mul_zero _), ← t3 n,
        finsum_eq_sum_of_support_subset (s := (Finset.range (n + 1)).image (Nat.cast : ℕ → ℤ)),
        Finset.sum_image (fun _ _ _ _ h => by exact_mod_cast h), hb, map_neg, map_sum]
      · simp only [conv, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, neg_inj]
        refine Finset.sum_congr rfl fun l hl => ?_
        have := Finset.mem_range.1 hl
        rw [map_mul, if_pos (by omega), Int.toNat_natCast, map_smF, eM, ← c1,
          show k + n - l = k + ((n - l : ℕ) : ℤ) by omega]
      · intro l hl
        by_contra h
        apply hl
        dsimp only
        split_ifs with h1
        · rw [c0, mul_zero]
          by_contra h2
          exact h (Finset.mem_coe.2 (Finset.mem_image.2 ⟨l.toNat, Finset.mem_range.2 (by omega), by omega⟩))
        · rw [zero_mul]
  · have hz : eOm ε (1 / (M : ℚ)) ^ (N * g') = zt ε p L ^ g := ε.injective (by
      rw [map_zpow₀, map_zpow₀, ← hv, eM, ← ee_int_mul, mul_one_div])
    have m0 : zt ε p L ∈ Subring.closure {zt ε p L} := Subring.subset_closure rfl
    have m1 : (zt ε p L)⁻¹ ∈ Subring.closure {zt ε p L} := by
      have h1 : zt ε p L ^ (p ^ L) = 1 := ε.injective (by
        rw [map_pow, ez, map_one, ← zpow_natCast]; push_cast; exact hz1)
      have : (zt ε p L)⁻¹ = zt ε p L ^ (p ^ L - 1) := by
        apply inv_eq_of_mul_eq_one_left
        rw [← pow_succ, Nat.sub_add_cancel (pow_pos hp0 L), h1]
      rw [this]
      exact pow_mem m0 _
    have m2 : ∀ m : ℤ, zt ε p L ^ m ∈ Subring.closure {zt ε p L} := fun m => by
      rcases Int.eq_nat_or_neg m with ⟨m, rfl | rfl⟩
      · rw [zpow_natCast]; exact pow_mem m0 _
      · rw [zpow_neg, zpow_natCast, ← inv_pow]; exact pow_mem m1 _
    refine GlobalTheory.T.smoothedEisensteinFxCoefficientSeq_one_mem_subring Ω _ c M _ A₁ _ hM hcM hA (by rw [hz]; exact m2 _) ?_
    rw [zpow_neg, hz, ← zpow_neg]
    exact m2 _
  · have := c1 0
    rw [Nat.cast_zero, add_zero] at this
    refine hi.imp (fun h => ε.injective ?_) (fun h => ε.injective ?_)
    · rw [this, h, map_zpow₀, zpow_mul]
    · rw [this, h, map_neg, map_zpow₀, zpow_mul]

end GlobalTheory.SiegTwo
end
end

