import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulSubEqZeroOfSum
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsLintegralConstantTermL2SqLe
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0291
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0289
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentLocalizationUniversal
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0285
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.Bundle0001
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLimHom
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.ContUniv

section Lim

variable {T : Type} [CommRing T] (ϖ : T)

def Tends (x : ℕ → T) (L : T) : Prop := ∀ k, ∃ M, ∀ m, M ≤ m → x m - L ∈ Ideal.span {ϖ ^ k}

variable {ϖ}

theorem smodEq_iff {a b : T} {k : ℕ} :
    a ≡ b [SMOD ((Ideal.span {ϖ}) ^ k • ⊤ : Submodule T T)] ↔ a - b ∈ Ideal.span {ϖ ^ k} := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]

theorem Tends.unique [IsHausdorff (Ideal.span {ϖ}) T] {x : ℕ → T} {L L' : T} (h : Tends ϖ x L)
    (h' : Tends ϖ x L') : L = L' := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {ϖ}) T) _ fun k => ?_
  have h0 : L - L' ∈ Ideal.span {ϖ ^ k} := by
    obtain ⟨M, hM⟩ := h k
    obtain ⟨M', hM'⟩ := h' k
    have := sub_mem (hM' (max M M') (le_max_right _ _)) (hM (max M M') (le_max_left _ _))
    simpa using this
  have : L - L' ≡ 0 [SMOD ((Ideal.span {ϖ}) ^ k • ⊤ : Submodule T T)] :=
    smodEq_iff.2 (by simpa using h0)
  exact this

theorem exists_tends [IsAdicComplete (Ideal.span {ϖ}) T] (x : ℕ → T)
    (h : ∀ k, ∃ M, ∀ m, M ≤ m → x m - x M ∈ Ideal.span {ϖ ^ k}) : ∃ L, Tends ϖ x L := by
  choose M hM using h
  let N : ℕ → ℕ := fun k => (Finset.range (k + 1)).sup M
  have hN : ∀ k, M k ≤ N k := fun k => Finset.le_sup (Finset.self_mem_range_succ k)
  have hmono : Monotone N := fun a b hab =>
    Finset.sup_mono (Finset.range_subset_range.2 (Nat.succ_le_succ hab))
  have hc : ∀ k m, N k ≤ m → x m - x (N k) ∈ Ideal.span {ϖ ^ k} := fun k m hm => by
    have := sub_mem (hM k m ((hN k).trans hm)) (hM k (N k) (hN k))
    simpa using this
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete (Ideal.span {ϖ}) T)
    (f := fun k => x (N k)) (fun {a b} hab => smodEq_iff.2 (by
      have := hc a (N b) (hmono hab)
      rw [← neg_sub]
      exact neg_mem this))
  refine ⟨L, fun k => ⟨N k, fun m hm => ?_⟩⟩
  have := add_mem (hc k m hm) (smodEq_iff.1 (hL k))
  simpa using this

theorem Tends.add {x y : ℕ → T} {a b : T} (hx : Tends ϖ x a) (hy : Tends ϖ y b) :
    Tends ϖ (fun m => x m + y m) (a + b) := fun k => by
  obtain ⟨M, hM⟩ := hx k
  obtain ⟨M', hM'⟩ := hy k
  refine ⟨max M M', fun m hm => ?_⟩
  have := add_mem (hM m ((le_max_left _ _).trans hm)) (hM' m ((le_max_right _ _).trans hm))
  convert this using 1; ring

theorem Tends.mul {x y : ℕ → T} {a b : T} (hx : Tends ϖ x a) (hy : Tends ϖ y b) :
    Tends ϖ (fun m => x m * y m) (a * b) := fun k => by
  obtain ⟨M, hM⟩ := hx k
  obtain ⟨M', hM'⟩ := hy k
  refine ⟨max M M', fun m hm => ?_⟩
  have := add_mem (Ideal.mul_mem_right (y m) _ (hM m ((le_max_left _ _).trans hm)))
    (Ideal.mul_mem_left _ a (hM' m ((le_max_right _ _).trans hm)))
  convert this using 1; ring

theorem tends_const (a : T) : Tends ϖ (fun _ => a) a := fun k => ⟨0, fun _ _ => by simp⟩

theorem exists_lim_hom {S : Type} [CommRing S] [IsAdicComplete (Ideal.span {ϖ}) T] (a : ℕ → S →+* T)
    (h : ∀ f k, ∃ M, ∀ m, M ≤ m → a m f - a M f ∈ Ideal.span {ϖ ^ k}) :
    ∃ ψ : S →+* T, ∀ f, Tends ϖ (fun m => a m f) (ψ f) := by
  choose L hL using fun f => exists_tends (ϖ := ϖ) (fun m => a m f) (h f)
  refine ⟨{ toFun := L, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hL⟩
  · exact (hL 1).unique (by simpa using tends_const (ϖ := ϖ) (1 : T))
  · intro f g
    exact (hL (f * g)).unique (by simpa using (hL f).mul (hL g))
  · exact (hL 0).unique (by simpa using tends_const (ϖ := ϖ) (0 : T))
  · intro f g
    exact (hL (f + g)).unique (by simpa using (hL f).add (hL g))

end Lim

variable {l : ℕ} [Fact l.Prime]

theorem exists_period (A : PAlg l) (f : (A.cont ℤ_[l]).A) (k : ℕ) :
    ∃ M : ℕ, ∀ z z' : ℤ_[l], PadicInt.toZModPow M z = PadicInt.toZModPow M z' →
      Hom.f (A.evCont z) f - Hom.f (A.evCont z') f ∈ Ideal.span {A.pi ^ k} := by
  obtain ⟨M, hM⟩ := GlobalTheory.CompanionTheory.PadicShift.exists_period l _ (f.2 k)
  refine ⟨M, fun z z' h => Ideal.Quotient.eq.1 (hM z z' ?_)⟩
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, h, sub_self]

end GlobalTheory.CompanionTheory.ContUniv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExponentMemFinset
section
open NumberField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.Latexp

open GroundTheory.Automorphic.Reduction in
theorem detModule_tor_one (K : Type) [Field K] [NumberField K] (n : ℕ) :
    (detModule K n (PositivityTheory.Rg.Rs.An.tor K fun _ : Fin n => (1 : ℝ)) : ℝ)
      = Real.exp ((n : ℝ) * (Module.finrank ℚ K : ℝ)) := by
  unfold PositivityTheory.Rg.Rs.An.tor
  rw [CuspidalSpectrum.detModule_diagUnits_posIdele]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, ← Real.exp_nat_mul]
  simp

open GroundTheory.Automorphic.Reduction in
theorem detModule_lhs (K : Type) [Field K] [NumberField K] (n : ℕ) (γ₀ : GL (Fin n) K) (m : ℤ) :
    (detModule K n (AdelicGLn.diagonal K n γ₀ * (PositivityTheory.Rg.Rs.An.tor K fun _ : Fin n => (1 : ℝ)) ^ m) : ℝ)
      = Real.exp ((m : ℝ) * ((n : ℝ) * (Module.finrank ℚ K : ℝ))) := by
  have h1 : detModule K n (AdelicGLn.diagonal K n γ₀) = 1 :=
    mem_normOneGL_iff_detModule.1 (rationalGL_le_normOneGL ⟨γ₀, rfl⟩)
  rw [map_mul, h1, one_mul, map_zpow]
  have hv : ∀ (s : {r : ℝ // 0 < r}) (k : ℤ), ((s ^ k : {r : ℝ // 0 < r}) : ℝ) = (s : ℝ) ^ k := by
    intro s k
    have hinv : ∀ u : {r : ℝ // 0 < r}, ((u⁻¹ : {r : ℝ // 0 < r}) : ℝ) = (u : ℝ)⁻¹ := by
      intro u
      have h := congrArg Subtype.val (mul_inv_cancel u)
      rw [Positive.val_mul, Positive.val_one] at h
      exact eq_inv_of_mul_eq_one_right h
    have hpow : ∀ (u : {r : ℝ // 0 < r}) (j : ℕ), ((u ^ j : {r : ℝ // 0 < r}) : ℝ) = (u : ℝ) ^ j := by
      intro u j
      induction j with
      | zero => simp
      | succ j ih => rw [pow_succ, pow_succ, Positive.val_mul, ih]
    cases k with
    | ofNat j => simp only [Int.ofNat_eq_natCast, zpow_natCast, hpow]
    | negSucc j => rw [zpow_negSucc, zpow_negSucc, hinv, hpow]
  rw [hv, detModule_tor_one, ← Real.rpow_intCast, ← Real.exp_mul, mul_comm]

open GroundTheory.Automorphic.Reduction in
theorem detModule_rhs (K : Type) [Field K] [NumberField K] (n r : ℕ) (X Y : UPos n r → 𝔸[K])
    (a q : AdelicGLn.AdelicGL K n) :
    detModule K n (unipGL X * a * q * a⁻¹ * (unipGL Y)⁻¹) = detModule K n q := by
  have h1 : detModule K n (unipGL X) = 1 :=
    mem_normOneGL_iff_detModule.1 (CuspidalSpectrum.unipGL_mem_normOneGL X)
  have h2 : detModule K n (unipGL Y) = 1 :=
    mem_normOneGL_iff_detModule.1 (CuspidalSpectrum.unipGL_mem_normOneGL Y)
  simp only [map_mul, map_inv, h1, h2, inv_one, one_mul, mul_one]
  rw [mul_comm (detModule K n a), mul_assoc, mul_inv_cancel, mul_one]

end GlobalTheory.CompanionTheory.Latexp

namespace GlobalTheory.CompanionTheory.Latexp
open GroundTheory.Automorphic.Reduction in

theorem exponent_mem_finset : ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ), 0 < n → ∀ (Q : Set (AdelicGLn.AdelicGL K n)), IsCompact Q → ∃ M : Finset ℤ, ∀ (t : ℝ) (X Y : UPos n r → 𝔸[K]), ∀ q ∈ Q, ∀ (γ₀ : GL (Fin n) K) (m : ℤ), AdelicGLn.diagonal K n γ₀ * (PositivityTheory.Rg.Rs.An.tor K fun _ : Fin n => (1 : ℝ)) ^ m = unipGL X * PositivityTheory.Rg.Rs.An.aR K n r t * q * (PositivityTheory.Rg.Rs.An.aR K n r t)⁻¹ * (unipGL Y)⁻¹ → m ∈ M := by
  intro K _ _ n r hn Q hQ
  have hdc : Continuous fun g : AdelicGLn.AdelicGL K n => (detModule K n g : ℝ) :=
    continuous_subtype_val.comp continuous_detModule
  obtain ⟨a, b, ha, -, hab⟩ := Reduction.exists_pos_bounds hQ hdc (fun g _ => (detModule K n g).2)
  have hN : 0 < (n : ℝ) * (Module.finrank ℚ K : ℝ) :=
    mul_pos (Nat.cast_pos.2 hn) (Nat.cast_pos.2 Module.finrank_pos)
  set N : ℝ := (n : ℝ) * (Module.finrank ℚ K : ℝ) with hNdef
  refine ⟨Finset.Icc ⌊Real.log a / N⌋ ⌈Real.log b / N⌉, ?_⟩
  intro t X Y q hq γ₀ m h
  have h1 := congrArg (fun g => (detModule K n g : ℝ)) h
  beta_reduce at h1
  rw [detModule_lhs, detModule_rhs] at h1
  obtain ⟨h2, h3⟩ := hab q hq
  rw [← h1] at h2 h3
  have h4 : Real.log a ≤ (m : ℝ) * N := (Real.log_le_iff_le_exp ha).2 h2
  have h5 : (m : ℝ) * N ≤ Real.log b := by
    have hb : 0 < b := lt_of_lt_of_le (Real.exp_pos _) h3
    exact (Real.le_log_iff_exp_le hb).2 h3
  rw [Finset.mem_Icc]
  constructor
  · have : Real.log a / N ≤ (m : ℝ) := (div_le_iff₀ hN).2 h4
    exact Int.cast_le.1 ((Int.floor_le _).trans this)
  · have : (m : ℝ) ≤ Real.log b / N := (le_div_iff₀ hN).2 h5
    exact Int.cast_le.1 (this.trans (Int.le_ceil _))
end GlobalTheory.CompanionTheory.Latexp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousLiftAdicFiltration
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)

namespace GlobalTheory.CompanionTheory.GE.Tower

variable {R : Type} [CommRing R] {N : ℕ}

theorem sub_tail_mem (I : Ideal R) (e : ℕ) (G : ℕ → MvPolynomial (Fin (N + 1)) R)
    (hd : ∀ i, G i - G (i + 1) ∈
      (I ^ (e + i + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) (m k : ℕ) :
    G m - G (m + k) ∈ (I ^ (e + m + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h2 : G (m + k) - G (m + k + 1) ∈ (I ^ (e + m + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) :=
      Ideal.map_mono (Ideal.pow_le_pow_right (by omega)) (hd (m + k))
    have h3 : G m - G (m + (k + 1)) = (G m - G (m + k)) + (G (m + k) - G (m + k + 1)) := by
      rw [show m + (k + 1) = m + k + 1 from rfl]
      ring
    rw [h3]
    exact add_mem ih h2

theorem exists_limit_form (I : Ideal R) [IsPrecomplete I R] (n e : ℕ)
    (G : ℕ → MvPolynomial (Fin (N + 1)) R) (hom : ∀ i, (G i).IsHomogeneous n)
    (hd : ∀ i, G i - G (i + 1) ∈
      (I ^ (e + i + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) :
    ∃ g : MvPolynomial (Fin (N + 1)) R, g.IsHomogeneous n ∧
      ∀ i, G i - g ∈ (I ^ (e + i + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
  classical
  have htop : ∀ k, (I ^ k • ⊤ : Submodule R R) = I ^ k := fun k => by
    rw [smul_eq_mul, Ideal.mul_top]
  have hcoef : ∀ d i k, coeff d (G i) - coeff d (G (i + k)) ∈ I ^ (e + i + 1) := by
    intro d i k
    have h := (mem_map_C_iff.1 (sub_tail_mem I e G hd i k)) d
    rwa [coeff_sub] at h
  have hL : ∀ d, ∃ Ld : R, ∀ i, coeff d (G i) - Ld ∈ I ^ (e + i + 1) := by
    intro d
    obtain ⟨Ld, hLd⟩ := IsPrecomplete.prec' (I := I) (fun i => coeff d (G i)) (by
      intro m n hmn
      rw [SModEq.sub_mem, htop]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      exact Ideal.pow_le_pow_right (by omega) (hcoef d m k))
    refine ⟨Ld, fun i => ?_⟩
    have h1 := hcoef d i (e + 1)
    have h2 := hLd (i + (e + 1))
    rw [SModEq.sub_mem, htop] at h2
    have h3 : coeff d (G i) - Ld =
        (coeff d (G i) - coeff d (G (i + (e + 1)))) + (coeff d (G (i + (e + 1))) - Ld) := by ring
    rw [h3]
    exact add_mem h1 (Ideal.pow_le_pow_right (by omega) h2)
  choose Lf hLf using hL
  refine ⟨∑ d ∈ (Finset.univ : Finset (Fin (N + 1))).finsuppAntidiag n, monomial d (Lf d), ?_, ?_⟩
  · refine IsHomogeneous.sum _ _ _ (fun d hd => isHomogeneous_monomial _ ?_)
    rw [Finset.mem_finsuppAntidiag] at hd
    rw [Finsupp.degree_eq_sum]
    exact hd.1
  · intro i
    rw [mem_map_C_iff]
    intro d
    rw [coeff_sub, coeff_sum]
    simp only [coeff_monomial]
    rw [Finset.sum_ite_eq']
    by_cases hdS : d ∈ (Finset.univ : Finset (Fin (N + 1))).finsuppAntidiag n
    · rw [if_pos hdS]
      exact hLf d i
    · rw [if_neg hdS, sub_zero]
      have h0 : coeff d (G i) = 0 := by
        by_contra hne
        apply hdS
        have hw := hom i hne
        rw [Finset.mem_finsuppAntidiag]
        refine ⟨?_, Finset.subset_univ _⟩
        rw [← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]
        exact hw
      rw [h0]
      exact zero_mem _

theorem exists_form_in_all (I : Ideal R) [IsPrecomplete I R]
    (L : ℕ → Ideal (MvPolynomial (Fin (N + 1)) R))
    (hbase : ∀ e, (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ≤ L e)
    (hanti : ∀ e, L (e + 1) ≤ L e) (n₀ : ℕ)
    (hlift : ∀ e n, n₀ ≤ n → ∀ f ∈ L e, f.IsHomogeneous n →
      ∃ f' ∈ L (e + 1), f'.IsHomogeneous n ∧
        f - f' ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R))
    (e n : ℕ) (hn : n₀ ≤ n) (g : MvPolynomial (Fin (N + 1)) R) (hg : g ∈ L e)
    (hgn : g.IsHomogeneous n) :
    ∃ g' : MvPolynomial (Fin (N + 1)) R, g'.IsHomogeneous n ∧ (∀ j, g' ∈ L j) ∧
      g - g' ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
  classical
  have hL : Antitone L := antitone_nat_of_succ_le hanti
  let lift' : ℕ → MvPolynomial (Fin (N + 1)) R → MvPolynomial (Fin (N + 1)) R := fun j f =>
    if h : ∃ f' ∈ L (j + 1), f'.IsHomogeneous n ∧
        f - f' ∈ (I ^ (j + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) then h.choose else f
  let s : ℕ → MvPolynomial (Fin (N + 1)) R := fun i =>
    Nat.rec (motive := fun _ => MvPolynomial (Fin (N + 1)) R) g (fun k f => lift' (e + k) f) i
  have hsS : ∀ i, s (i + 1) = lift' (e + i) (s i) := fun i => rfl
  have hstep : ∀ i, s i ∈ L (e + i) ∧ (s i).IsHomogeneous n →
      s (i + 1) ∈ L (e + i + 1) ∧ (s (i + 1)).IsHomogeneous n ∧
        s i - s (i + 1) ∈ (I ^ (e + i + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
    rintro i ⟨h1, h2⟩
    have hex := hlift (e + i) n hn (s i) h1 h2
    rw [hsS]
    simp only [lift']
    rw [dif_pos hex]
    exact hex.choose_spec
  have hinv : ∀ i, s i ∈ L (e + i) ∧ (s i).IsHomogeneous n := by
    intro i
    induction i with
    | zero => exact ⟨hg, hgn⟩
    | succ i ih => exact ⟨(hstep i ih).1, (hstep i ih).2.1⟩
  have hd : ∀ i, s i - s (i + 1) ∈ (I ^ (e + i + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) :=
    fun i => (hstep i (hinv i)).2.2
  obtain ⟨g', hg'n, hg'⟩ := exists_limit_form I n e s (fun i => (hinv i).2) hd
  refine ⟨g', hg'n, fun j => ?_, hg' 0⟩
  have h1 : s j ∈ L j := hL (by omega : j ≤ e + j) (hinv j).1
  have h2 : s j - g' ∈ L j := hL (by omega : j ≤ e + j) (hbase (e + j) (hg' j))
  have h3 : g' = s j - (s j - g') := by ring
  rw [h3]
  exact sub_mem h1 h2

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem exists_limit_ideal : ∀ (R : Type) [CommRing R] (I : Ideal R), IsAdicComplete I R → ∀ (N : ℕ)
    (L : ℕ → Ideal (MvPolynomial (Fin (N + 1)) R)),
    (∀ e, HomogIdeal (L e)) →
    (∀ e, (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ≤ L e) →
    (∀ e, L (e + 1) ≤ L e) →
    ∀ (n₀ : ℕ), (∀ e n, n₀ ≤ n → ∀ f ∈ L e, f.IsHomogeneous n →
      ∃ f' ∈ L (e + 1), f'.IsHomogeneous n ∧
        f - f' ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) →
    ∃ J : Ideal (MvPolynomial (Fin (N + 1)) R), HomogIdeal J ∧ ∀ e, J ≤ L e ∧
        ∀ f ∈ L e, ∀ k, ∃ m : ℕ, X k ^ m * f ∈
          J ⊔ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
  intro R _ I hI N L hhom hbase hanti n₀ hlift
  have : IsPrecomplete I R := hI.toIsPrecomplete
  classical
  let S : Set (MvPolynomial (Fin (N + 1)) R) := {g | ∃ n, n₀ ≤ n ∧ g.IsHomogeneous n ∧ ∀ j, g ∈ L j}
  refine ⟨Ideal.span S, ?_, fun e => ⟨?_, ?_⟩⟩
  · intro d f hf
    have hH : (Ideal.span S).IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) R) :=
      Ideal.homogeneous_span _ _ (fun x hx => by
        obtain ⟨n, _, hn, _⟩ := hx
        exact ⟨n, (mem_homogeneousSubmodule n x).2 hn⟩)
    have h := (Ideal.IsHomogeneous.mem_iff _ hH).1 hf d
    have e1 : (DirectSum.decompose (homogeneousSubmodule (Fin (N + 1)) R) f d :
        MvPolynomial (Fin (N + 1)) R) = homogeneousComponent d f := decomposition.decompose'_apply f d
    rwa [e1] at h
  · rw [Ideal.span_le]
    rintro g ⟨n, _, _, hall⟩
    exact hall e
  · intro f hf k
    refine ⟨n₀, ?_⟩
    rw [← sum_homogeneousComponent f, Finset.mul_sum]
    refine Submodule.sum_mem _ fun d _ => ?_
    have hmem : X k ^ n₀ * homogeneousComponent d f ∈ L e := Ideal.mul_mem_left _ _ (hhom e d f hf)
    have hh : (X k ^ n₀ * homogeneousComponent d f).IsHomogeneous (n₀ + d) :=
      (isHomogeneous_X_pow k n₀).mul (homogeneousComponent_isHomogeneous d f)
    obtain ⟨g', hg'n, hall, hdiff⟩ :=
      exists_form_in_all I L hbase hanti n₀ hlift e (n₀ + d) (Nat.le_add_right _ _) _ hmem hh
    have h3 : X k ^ n₀ * homogeneousComponent d f = g' + (X k ^ n₀ * homogeneousComponent d f - g') := by
      ring
    rw [h3]
    exact add_mem (Ideal.mem_sup_left (Ideal.subset_span ⟨n₀ + d, Nat.le_add_right _ _, hg'n, hall⟩))
      (Ideal.mem_sup_right hdiff)

end GlobalTheory.CompanionTheory.GE.Tower
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPowerAnnihilatesSections
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem cst_thick_eq_zero {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (V : X.Opens) {r : R}
    (hr : r ∈ I ^ (e + 1)) : AbLaw.cst (p ≫ thick R I e) V r = 0 := by
  have key : AbLaw.cst (p ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1))))) V =
      (AbLaw.cst p V).comp (Ideal.Quotient.mk (I ^ (e + 1))) := by
    ext a
    have := congrArg (fun q => q.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    simp only [AbLaw.cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
    rw [this]
  have h0 : AbLaw.cst (p ≫ thick R I e) V r =
      AbLaw.cst (p ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1))))) V r := rfl
  rw [h0, key, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]

theorem pow_smul_top_secOnR (R : Type) [CommRing R] (I : Ideal R)
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (e : ℕ) (M : LB (Y e).left)
    (V : (Y e).left.Opens) :
    I ^ (e + 1) • (⊤ : Submodule R (SecOnR (toR I Y e) M V)) = ⊥ := by
  rw [eq_bot_iff, Submodule.smul_le]
  intro r hr s _
  rw [Submodule.mem_bot, SecOnR.smul_def, cst_thick_eq_zero I e (Y e).hom V hr, zero_smul]

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentLocalizationUniversalStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_localization_universal : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (e : A.A), IsIdempotentElem e → ∃ (A' : PAlg l) (lam : A ⟶ A'), (A.IsTest → A'.IsTest) ∧ PAlg.Hom.f lam e = 1 ∧ (∀ (B : PAlg l) (ψ : A ⟶ B), PAlg.Hom.f ψ e = 1 → ∃! χ : A' ⟶ B, lam ≫ χ = ψ) ∧ ∀ n, Function.Surjective (mapAcr lam n) ∧ ∀ x, mapAcr lam n x = 0 → A.toAcr n (WittVector.teichmuller l e) * x = 0 := by
  first | exact @GlobalTheory.CompanionTheory.IdemObj.directFactor | exact GlobalTheory.CompanionTheory.IdemObj.directFactor | (intros; apply GlobalTheory.CompanionTheory.IdemObj.directFactor <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentRefinementOfUnimodularStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_refinement_of_unimodular : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), A.IsTest → ∀ {m : ℕ} (s : Fin m → A.U), Ideal.span (Set.range s) = ⊤ → ∃ e : Fin m → A.A, (∀ k, IsIdempotentElem (e k)) ∧ Ideal.span (Set.range e) = ⊤ ∧ ∀ k, A.sharp (e k) ∈ Ideal.span {s k} := by
  first | exact @GlobalTheory.CompanionTheory.TestCover.test_cover | exact GlobalTheory.CompanionTheory.TestCover.test_cover | (intros; apply GlobalTheory.CompanionTheory.TestCover.test_cover <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralNormSqLeToRealLintegralEnormSq
section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Dblock

theorem integral_norm_sq_le_toReal_lintegral_enorm_sq {α : Type} [MeasurableSpace α] (μ : Measure α) (f : α → ℂ) :
    ∫ x, ‖f x‖ ^ 2 ∂μ ≤ (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ).toReal := by
  by_cases h : Integrable (fun x => ‖f x‖ ^ 2) μ
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => by positivity) h.aestronglyMeasurable]
    apply le_of_eq
    congr 1
    apply lintegral_congr
    intro x
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  · rw [integral_undef h]
    exact ENNReal.toReal_nonneg

end GlobalTheory.CompanionTheory.Dblock
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsFirstChernThickeningMuBOfIsFirstChernDeRham
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.FirstChernRationalLift

variable {K B' : Type} [Field K] [CharZero K] [CommRing B'] [Algebra K B'] {I : Ideal B'} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of K)) (s : ℕ)

abbrev famK {C : Type 1} [Category.{0} C] (G : C ⥤ (TS γ q 1 s {⊤}).FullSubcategory) : C ⥤ Thick (smFun X q) :=
  G ⋙ (smO γ q 1 s {⊤}).G ⋙ (TO q 1 s {⊤}).ι

theorem pt_famK {C : Type 1} [Category.{0} C] (G : C ⥤ (TS γ q 1 s {⊤}).FullSubcategory) (c : C) :
    pt ((famK γ q s G).obj c) = pt (G.obj c).obj := Category.comp_id _

def liftK {C : Type 1} [Category.{0} C] {G : C ⥤ (TS γ q 1 s {⊤}).FullSubcategory} {D : E.LineData X}
    (Λ : B.CLift (q := q) (b := nlBase B' I γ 0) (ht := rfl) (κ := κA K I) (G ⋙ (TS γ q 1 s {⊤}).ι) D) :
    CLiftK (famK γ q s G) D where
  p c := Λ.p c
  hp c := (Λ.hp c).trans (Category.comp_id _).symm
  w φ := Λ.w φ
  hw φ h := Λ.hw φ h

theorem isFirstChernThickening_muB_of_isFirstChernDeRham (D : E.LineData X) (c : HdR q 2) (h : IsFirstChernDeRham q D c) :
    IsFirstChernThickening (TS γ q 1 s {⊤}) D s (muB γ q 1 s {⊤} 2 c) := by
  intro C _ G hG Λ
  have hpd : ∀ c', ((famK γ q s G).obj c').pdPow s = ⊥ := fun c' => ((smO γ q 1 s {⊤}).G.obj (G.obj c')).property.1.1
  have hV : ∀ c', ∃ (V : X.Opens) (σ : (V : Scheme.{0}) ⟶ D.Y), σ ≫ D.f = V.ι ∧ InU V ((famK γ q s G).obj c') := by
    intro c'
    obtain ⟨V, ⟨σ, hσ⟩, hU⟩ := hG c'
    refine ⟨V, σ, hσ, ?_⟩
    unfold InU
    rw [pt_famK]
    exact hU
  obtain ⟨z, hz, hzv, hcls⟩ := h s C (famK γ q s G) hpd hV (liftK γ q s Λ)
  let m' : CH.Mor (famK γ q s G ⋙ O (smFun X q)) (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) (algebraMap K B') :=
    ⟨𝟭 _, fun T => (smO γ q 1 s {⊤}).o.τ (G.obj T), fun φ x => (smO γ q 1 s {⊤}).o.nat (G.map φ) x⟩
  have e : (show CH.Cn (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2 from Λ.coc (RingHom.id _) s) = m'.pullC 2 z := by
    funext σ
    exact (hzv σ).symm
  have hb : CH.d (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2 (m'.pullC 2 z) = 0 := by
    rw [m'.d_pullC, hz, map_zero]
  have hz' : CH.d (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2 (Λ.coc (RingHom.id _) s) = 0 := (congrArg (CH.d (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2) e).trans hb
  refine ⟨hz', ?_⟩
  have e1 := CrystallineSemistableComparison.P.mapH_cls m'.hom 2 z hz hb
  have e2 : (CH.Mor.restrict (CH.modF (sP (TS γ q 1 s {⊤})).A) G).pull 2 (muB γ q 1 s {⊤} 2 c) =
      m'.pull 2 ((CH.Mor.restrict (O (smFun X q)) (famK γ q s G)).pull 2 c) := by
    have a1 := (CrystallineSemistableComparison.P.pull_comp (CH.Mor.restrict (O (smFun X q)) (TO q 1 s {⊤}).ι) (smO γ q 1 s {⊤}).o 2 c).1
    have a2 := (CrystallineSemistableComparison.P.pull_comp ((CH.Mor.restrict (O (smFun X q)) (TO q 1 s {⊤}).ι).comp (smO γ q 1 s {⊤}).o)
      (CH.Mor.restrict (CH.modF (sP (TS γ q 1 s {⊤})).A) G) 2 c).1
    have b := (CrystallineSemistableComparison.P.pull_comp (CH.Mor.restrict (O (smFun X q)) (famK γ q s G)) m' 2 c).1
    exact (congrArg ((CH.Mor.restrict (CH.modF (sP (TS γ q 1 s {⊤})).A) G).pull 2) a1.symm).trans (a2.symm.trans b)
  rw [e2, ← hcls]
  refine Eq.trans ?_ e1.symm
  have key : ∀ (a : CH.Cn (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2) (ha : CH.d (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2 a = 0),
      a = m'.pullC 2 z → (CH.cx (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A)).cls a ha =
        (CH.cx (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A)).cls (m'.pullC 2 z) hb := by
    rintro _ _ rfl
    rfl
  exact key _ hz' e

end GlobalTheory.CompanionTheory.FirstChernRationalLift
end
end

