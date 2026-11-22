import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0260
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0127
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0259
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverEta
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0243
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0264
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0048

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalTwoCocycleMultipleNotCoboundary
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt

namespace GlobalTheory.TateNat

theorem free_inj : ∀ {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] {G : Type} [Group G] [TopologicalSpace G] (χ : G →* ℤ_[p]ˣ) (c : G × G → ℤ_[p]), (∀ r, GlobalTheory.TateTop.Gen χ r c) → ∀ (φ : ℤ_[p] →+* O) (ε : G →* Oˣ), (∀ g, ((ε g : Oˣ) : O) = φ (χ g : ℤ_[p])) → ∀ (ϖ : O), Irreducible ϖ → (p : O) ∈ IsLocalRing.maximalIdeal O → (∀ n : ℕ, IsOpen ((powSub (M := O) ϖ n : Submodule O O) : Set O)) → ∀ (a : O) (f : G → O), Continuous f → (∀ g h : G, d1 (twist ε O) f (g, h) = a * φ (c (g, h))) → a = 0 := by
  intro p _ O _ _ _ _ _ _ G _ _ χ c hgen φ ε hεφ ϖ hϖ hp hopen a f hf hd
  have key : ∀ n : ℕ, a ∈ (powSub (M := O) ϖ n : Submodule O O) := by
    intro n
    set N : Submodule O O := powSub (M := O) ϖ n with hN
    letI : Module ℤ_[p] (O ⧸ N) := Module.compHom (O ⧸ N) φ
    have hs : ∀ (t : ℤ_[p]) (x : O), t • (Submodule.Quotient.mk x : O ⧸ N) =
        Submodule.Quotient.mk (φ t * x) := fun t x => by
      show (φ t) • (Submodule.Quotient.mk x : O ⧸ N) = _
      rw [← Submodule.Quotient.mk_smul, smul_eq_mul]
    haveI : Finite (O ⧸ N) := AddSubgroup.quotient_finite_of_isOpen N.toAddSubgroup (hopen n)
    have hM : ∀ m : O ⧸ N, (p : ℤ_[p]) ^ n • m = 0 := by
      intro m
      induction m using Submodule.Quotient.induction_on with
      | H x =>
        rw [hs, Submodule.Quotient.mk_eq_zero, map_pow, map_natCast]
        rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hp
        obtain ⟨u, hu⟩ := hp
        refine mem_powSub.2 ⟨u ^ n * x, ?_⟩
        rw [hu, smul_eq_mul, mul_pow]
        ring
    have hlc : IsLocallyConstant (fun g => (Submodule.Quotient.mk (f g) : O ⧸ N)) := by
      intro s
      have ho : IsOpen ((Submodule.Quotient.mk : O → O ⧸ N) ⁻¹' s) := by
        rw [isOpen_iff_forall_mem_open]
        intro x hx
        refine ⟨(fun y => y - x) ⁻¹' (N : Set O), fun y hy => ?_,
          (hopen n).preimage (continuous_id.sub continuous_const), ?_⟩
        · have e : (Submodule.Quotient.mk y : O ⧸ N) = Submodule.Quotient.mk x :=
            (Submodule.Quotient.eq N).2 hy
          show (Submodule.Quotient.mk y : O ⧸ N) ∈ s
          rw [e]
          exact hx
        · show x - x ∈ N
          rw [sub_self]
          exact N.zero_mem
      exact ho.preimage hf
    have h3 := ((hgen n) (O ⧸ N) hM).2.2 (Submodule.Quotient.mk a)
      (fun g => Submodule.Quotient.mk (f g)) hlc fun q => by
        obtain ⟨g, h⟩ := q
        have e := hd g h
        simp only [d1_apply] at e
        change (ε g : O) • f h - f (g * h) + f g = a * φ (c (g, h)) at e
        rw [smul_eq_mul, hεφ] at e
        simp only [GlobalTheory.TateTop.cob, hs]
        rw [← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add]
        congr 1
        linear_combination -e
    exact (Submodule.Quotient.mk_eq_zero N).1 h3
  have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal O)
    (IsLocalRing.maximalIdeal.isMaximal O).ne_top
  have hmem : a ∈ ⨅ i, (IsLocalRing.maximalIdeal O) ^ i := by
    refine Submodule.mem_iInf _ |>.2 fun i => ?_
    obtain ⟨y, hy⟩ := mem_powSub.1 (key i)
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← hy, smul_eq_mul]
    exact dvd_mul_right _ _
  rw [hbot] at hmem
  exact (Submodule.mem_bot O).1 hmem

end GlobalTheory.TateNat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisTwistedSelmerAuxprimesOfMatrixAndBounds
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys
open scoped TensorProduct

namespace GlobalTheory.TwSys

open Classical in

theorem aeval_gen_sub_one_surjective (O : Type) [CommRing O] (n : ℕ) [NeZero n] (ι : Type) [Fintype ι] :
    Function.Surjective (MvPolynomial.aeval (R := O) fun q : ι =>
      MonoidAlgebra.of O (Multiplicative (ι → ZMod n)) (Multiplicative.ofAdd (Pi.single q 1)) - 1) := by
  set φ := (MvPolynomial.aeval (R := O) fun q : ι =>
      MonoidAlgebra.of O (Multiplicative (ι → ZMod n)) (Multiplicative.ofAdd (Pi.single q 1)) - 1) with hφ
  have hg : ∀ g : Multiplicative (ι → ZMod n), MonoidAlgebra.of O _ g ∈ φ.range := by
    intro g
    refine ⟨∏ q, (MvPolynomial.X q + 1) ^ (Multiplicative.toAdd g q).val, ?_⟩
    have h1 : g = ∏ q, (Multiplicative.ofAdd (Pi.single q (1 : ZMod n) : ι → ZMod n)) ^ (Multiplicative.toAdd g q).val := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_prod]
      funext j
      simp only [toAdd_pow, toAdd_ofAdd, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, nsmul_one, ZMod.natCast_zmod_val]
    conv_rhs => rw [h1]
    simp only [hφ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_prod, map_pow, map_add, map_one,
      MvPolynomial.aeval_X, sub_add_cancel]
  intro x
  change x ∈ φ.range
  induction x using MonoidAlgebra.induction_on with
  | of g => exact hg g
  | add f g hf hg => exact add_mem hf hg
  | smul r f hf => exact Subalgebra.smul_mem _ hf r

theorem toLam_surjective {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)
    (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] : Function.Surjective (toLam X i M ι) := by
  have : NeZero (X.l i ^ M) := ⟨pow_ne_zero _ (X.lPrime i).out.ne_zero⟩
  exact aeval_gen_sub_one_surjective (X.O0 i) (X.l i ^ M) ι

theorem SlopeTestRemainingChoices.empty {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
    {i : X.Tw} {M : ℕ} {A : Finset (PlE D.host)} {ι : Type} {P : ι → PlE D.host} {d}
    (h : SlopeTestRemainingChoices X i M A P d) : SlopeTestRemainingChoices X i M ∅ P d := by
  refine ⟨fun q v hv => ?_, h.2⟩
  obtain ⟨h1, h2, h3, h4, -, h6⟩ := h.1 q v hv
  exact ⟨h1, h2, h3, h4, Finset.notMem_empty _, h6⟩

theorem galois_twisted_selmer_auxprimes_of_matrix_and_bounds : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂)
    (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X),
    ThmS bkP → SelmerLengthsByDeterminant bkP → ResidualBoundOddPrimes bkP → ThmC bkP → GaloisSideTwistedSelmerAuxiliaryPrimes bkP := by
  intro D N X bkP hS hS4 h103 hC i T hT
  have hO : OrdBound bkP i (IsDiscreteValuationRing.addVal (X.O0 i) ((X.l i : X.O0 i) ^ nu X i)) := by
    rcases Nat.eq_zero_or_pos (nu X i) with h | h
    · rw [h, pow_zero, IsDiscreteValuationRing.addVal_one]
      exact h103 i h
    · exact hC i h
  obtain ⟨R, Dd, M₀, hM₀⟩ := hO T hT
  refine ⟨R, Dd, max M₀ 1, le_max_right _ _, fun M hM H S d hF z hz H' ho hn A => ?_⟩
  have hM1 : 1 ≤ M := le_trans (le_max_right _ _) hM
  obtain ⟨P, hA, hSt, hP⟩ := hM₀ M (le_trans (le_max_left _ _) hM) H S d hF z hz H' ho hn A
  refine ⟨P, hA, hSt, fun s hs Q hQ => ?_⟩
  obtain ⟨a, Φ, hΦ, -⟩ := hS i s (hT s hs) M _ P _ Q hM1 hA.empty hQ
  obtain ⟨F, hFΦ⟩ := toLam_surjective X i M (Fin R ⊕ Fin R) Φ.det
  exact ⟨F, hS4 i s M _ P _ Q hM1 hA.empty hQ a Φ hΦ F hFΦ, hP s hs Q hQ a Φ hΦ F hFΦ⟩

end GlobalTheory.TwSys
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GeomSumOneAddPrime
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc

namespace GlobalTheory.Cyc

open PowerSeries in

theorem algHom_sub_dvd {O : Type} [CommRing O] (f : O⟦X⟧ →ₐ[O] O⟦X⟧) (hf : (X : O⟦X⟧) ∣ f X)
    (a : O⟦X⟧) : f X - X ∣ f a - a := by
  set y := f X with hy
  let g : ℕ → O⟦X⟧ := fun n => ∑ i ∈ Finset.range n, y ^ i * X ^ (n - 1 - i)
  have hg : ∀ n, g n * (y - X) = y ^ n - X ^ n := fun n => geom_sum₂_mul y X n
  have hgd : ∀ n, (X : O⟦X⟧) ^ (n - 1) ∣ g n := by
    intro n
    refine Finset.dvd_sum fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    have e : n - 1 = i + (n - 1 - i) := by omega
    conv_lhs => rw [e, pow_add]
    exact mul_dvd_mul (pow_dvd_pow_of_dvd hf i) dvd_rfl
  let P : ℕ → O⟦X⟧ := fun N => ∑ n ∈ Finset.range N, C (coeff n a) * g n
  have hP : ∀ m k, (X : O⟦X⟧) ^ m ∣ P (m + 1 + k) - P (m + 1) := by
    intro m k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : P (m + 1 + (k + 1)) - P (m + 1)
          = (P (m + 1 + k) - P (m + 1)) + C (coeff (m + 1 + k) a) * g (m + 1 + k) := by
        simp only [P, ← add_assoc, Finset.sum_range_succ _ (m + 1 + k)]; ring
      rw [e]
      exact dvd_add ih (Dvd.dvd.mul_left ((pow_dvd_pow _ (by omega)).trans (hgd _)) _)
  let b : O⟦X⟧ := PowerSeries.mk fun m => coeff m (P (m + 2))
  have hb : ∀ N, (X : O⟦X⟧) ^ N ∣ P (N + 1) - b := by
    intro N
    rw [X_pow_dvd_iff]
    intro m hm
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hm
    have := X_pow_dvd_iff.mp (hP (m + 1) k) m (by omega)
    rw [map_sub] at this ⊢
    rw [coeff_mk, show m + k + 1 + 1 = m + 1 + 1 + k by omega]
    exact this
  have hr : ∀ N, ∃ r : O⟦X⟧, a = ∑ n ∈ Finset.range N, C (coeff n a) * X ^ n + X ^ N * r := by
    intro N
    have : (X : O⟦X⟧) ^ N ∣ a - ∑ n ∈ Finset.range N, C (coeff n a) * X ^ n := by
      rw [X_pow_dvd_iff]
      intro m hm
      simp [coeff_X_pow, hm]
    obtain ⟨r, hr⟩ := this
    exact ⟨r, by rw [← hr]; ring⟩
  have hN : ∀ N, (X : O⟦X⟧) ^ N ∣ f a - a - (y - X) * P N := by
    intro N
    obtain ⟨r, hr⟩ := hr N
    have h1 : f a = ∑ n ∈ Finset.range N, C (coeff n a) * y ^ n + y ^ N * f r := by
      conv_lhs => rw [hr]
      simp only [map_add, map_sum, map_mul, map_pow, ← hy]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      congr 1
      exact f.commutes _
    have h2 : (y - X) * P N = ∑ n ∈ Finset.range N, C (coeff n a) * y ^ n
        - ∑ n ∈ Finset.range N, C (coeff n a) * X ^ n := by
      simp only [P, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [← mul_sub, ← hg]; ring
    have h3 : f a - a - (y - X) * P N = y ^ N * f r - X ^ N * r := by
      rw [h2, h1]; linear_combination -hr
    rw [h3]
    exact dvd_sub (Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hf N) _) (dvd_mul_right _ _)
  refine ⟨b, ?_⟩
  ext m
  have : (X : O⟦X⟧) ^ (m + 1) ∣ f a - a - (y - X) * b := by
    have e : f a - a - (y - X) * b
        = (f a - a - (y - X) * P (m + 1 + 1)) + (y - X) * (P (m + 1 + 1) - b) := by ring
    rw [e]
    exact dvd_add ((pow_dvd_pow _ (by omega)).trans (hN _)) (Dvd.dvd.mul_left (hb _) _)
  have := X_pow_dvd_iff.mp this m (by omega)
  rw [map_sub] at this
  exact sub_eq_zero.mp this

theorem geom_sum_one_add_prime {R : Type} [CommRing R] {p : ℕ} (hp : p.Prime) (x : R) :
    ∃ r, ∑ k ∈ Finset.range p, (1 + x) ^ k = x ^ (p - 1) + (p : R) * r := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (Polynomial.X : Polynomial ℤ) 1
  have h1 : (∑ k ∈ Finset.range p, (1 + Polynomial.X : Polynomial ℤ) ^ k)
      = Polynomial.X ^ (p - 1) + (p : Polynomial ℤ) * r := by
    apply mul_right_cancel₀ (Polynomial.X_ne_zero (R := ℤ))
    have h := geom_sum_mul (1 + Polynomial.X : Polynomial ℤ) p
    have e : (Polynomial.X : Polynomial ℤ) ^ p = Polynomial.X ^ (p - 1) * Polynomial.X := by
      rw [← pow_succ, Nat.sub_add_cancel hp.one_le]
    rw [add_comm Polynomial.X, one_pow, e] at hr
    rw [hr] at h
    linear_combination h
  refine ⟨Polynomial.aeval x r, ?_⟩
  have := congrArg (Polynomial.aeval x) h1
  simpa [map_sum] using this

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]

theorem act_X_eq (c : ℤ_[l]) : act l O c PowerSeries.X = cyc l O c := (GlobalTheory.Cyc.act_laws l O).1 c

theorem act_comm' (c c' : ℤ_[l]) (a) : act l O c (act l O c' a) = act l O c' (act l O c a) := by
  rw [(GlobalTheory.Cyc.act_laws l O).2.1, (GlobalTheory.Cyc.act_laws l O).2.1, mul_comm]

theorem act_nat_X (k : ℕ) : act l O (k : ℤ_[l]) PowerSeries.X = (1 + PowerSeries.X) ^ k - 1 := by
  rw [act_X_eq, (GlobalTheory.Cyc.act_laws l O).2.2.2.1]

theorem cyc_eq_X_mul (c : ℤ_[l]) :
    ∃ b, cyc l O c = PowerSeries.X * (PowerSeries.C (algebraMap ℤ_[l] O c) + PowerSeries.X * b) := by
  have : (PowerSeries.X : PowerSeries O) ^ 2 ∣
      cyc l O c - PowerSeries.C (algebraMap ℤ_[l] O c) * PowerSeries.X := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    interval_cases m
    · simp [cyc_const]
    · simp [(GlobalTheory.Cyc.act_laws l O).2.2.2.2.1]
  obtain ⟨b, hb⟩ := this
  exact ⟨b, by linear_combination hb⟩

theorem XX_mul_QQ (s : ℕ) : XX l O s * QQ l O s = (1 + XX l O s) ^ l - 1 := by
  have h := geom_sum_mul (1 + XX l O s) l
  unfold QQ
  linear_combination h

theorem XX_mul_QQ' (s : ℕ) (hs : 1 ≤ s) :
    XX l O s * QQ l O s = (1 + PowerSeries.X) ^ l ^ s - 1 := by
  rw [XX_mul_QQ, XX, add_sub_cancel, ← pow_mul, ← pow_succ, Nat.sub_add_cancel hs]

theorem phi_pow_X (n : ℕ) :
    (phi l O ^ n) PowerSeries.X = (1 + PowerSeries.X) ^ l ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', AlgHom.mul_apply, ih]
    simp only [map_sub, map_pow, map_add, map_one, phi, act_nat_X]
    rw [add_sub_cancel, ← pow_mul, ← pow_succ']

theorem act_C (c : ℤ_[l]) (x : O) : act l O c (PowerSeries.C x) = PowerSeries.C x :=
  (act l O c).commutes x

theorem act_QQ_one (c : ℤ_[l]ˣ) :
    ∃ b, act l O c (QQ l O 1) = QQ l O 1 * (1 + PowerSeries.X * b) := by
  obtain ⟨b, hb⟩ := cyc_eq_X_mul l O c
  have h1 : PowerSeries.X * QQ l O 1 = act l O (l : ℤ_[l]) PowerSeries.X := by
    have := XX_mul_QQ' l O 1 le_rfl
    rw [act_nat_X]
    simpa [XX] using this
  have h2 := act_comm' l O c l PowerSeries.X
  rw [← h1, map_mul, act_X_eq, hb] at h2
  simp only [map_mul, map_add, act_C, ← h1] at h2
  have hU : IsUnit (PowerSeries.C (algebraMap ℤ_[l] O c) + PowerSeries.X * b) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simpa using c.isUnit.map (algebraMap ℤ_[l] O)
  obtain ⟨v, hv⟩ := hU.exists_right_inv
  have h3 : (PowerSeries.C (algebraMap ℤ_[l] O c) + PowerSeries.X * b) * act l O c (QQ l O 1)
      = QQ l O 1 * (PowerSeries.C (algebraMap ℤ_[l] O c)
        + PowerSeries.X * QQ l O 1 * act l O (l : ℤ_[l]) b) := by
    apply PowerSeries.X_mul_cancel
    linear_combination h2
  refine ⟨v * (QQ l O 1 * act l O (l : ℤ_[l]) b - b), ?_⟩
  linear_combination v * h3 + (QQ l O 1 - act l O c (QQ l O 1)) * hv

theorem XX_QQ_properties : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O], ∀ s : ℕ, 1 ≤ s → phi l O (XX l O s) = XX l O s * QQ l O s ∧ (phi l O ^ (s - 1)) PowerSeries.X = XX l O s ∧ PowerSeries.constantCoeff (QQ l O s) = (l : O) ∧ (∃ b, QQ l O s = PowerSeries.X ^ (l ^ (s - 1) * (l - 1)) + (l : PowerSeries O) * b) ∧ (∃ b, QQ l O s = (l : PowerSeries O) + XX l O s * b) ∧ (∀ c : ℤ_[l]ˣ, (∃ b, act l O c (XX l O s) = XX l O s * (PowerSeries.C (algebraMap ℤ_[l] O c) + XX l O s * b)) ∧ ∃ b, act l O c (QQ l O s) = QQ l O s * (1 + XX l O s * b)) ∧ ∀ (u w : ℤ_[l]), u = 1 + (l : ℤ_[l]) ^ s * w → ∀ a, ∃ b, act l O u a - a = XX l O s * QQ l O s * b := by
  intro l _ O _ _ s hs
  have hp : l.Prime := Fact.out
  have hψ : act l O ((l ^ (s - 1) : ℕ) : ℤ_[l]) PowerSeries.X = XX l O s := act_nat_X l O _
  have hψQ : act l O ((l ^ (s - 1) : ℕ) : ℤ_[l]) (QQ l O 1) = QQ l O s := by
    have : XX l O 1 = PowerSeries.X := by simp [XX]
    simp only [QQ, this, map_sum, map_pow, map_add, map_one, hψ]
  have h0 : PowerSeries.constantCoeff (XX l O s) = 0 := by simp [XX]
  refine ⟨?_, phi_pow_X l O _, ?_, ?_, ?_, fun c => ⟨?_, ?_⟩, ?_⟩
  · rw [XX_mul_QQ' l O s hs, XX]
    simp only [map_sub, map_pow, map_add, map_one, phi, act_nat_X]
    rw [add_sub_cancel, ← pow_mul, ← pow_succ', Nat.sub_add_cancel hs]
  · simp [QQ, map_sum, h0]
  · obtain ⟨r, hr⟩ := geom_sum_one_add_prime hp (XX l O s)
    obtain ⟨t, ht⟩ := exists_add_pow_prime_pow_eq hp (PowerSeries.X : PowerSeries O) 1 (s - 1)
    have h1 : (l : PowerSeries O) ∣ XX l O s - PowerSeries.X ^ l ^ (s - 1) :=
      ⟨PowerSeries.X * t, by rw [XX, add_comm, ht]; ring⟩
    obtain ⟨q, hq⟩ := h1.trans (sub_dvd_pow_sub_pow _ _ (l - 1))
    refine ⟨q + r, ?_⟩
    rw [QQ, hr, pow_mul]
    linear_combination hq
  · have : XX l O s ∣ QQ l O s - l := by
      have e : QQ l O s - l = ∑ k ∈ Finset.range l, ((1 + XX l O s) ^ k - 1) := by
        simp [QQ, Finset.sum_sub_distrib]
      rw [e]
      refine Finset.dvd_sum fun k _ => ?_
      simpa using sub_one_dvd_pow_sub_one (1 + XX l O s) k
    obtain ⟨b, hb⟩ := this
    exact ⟨b, by linear_combination hb⟩
  · obtain ⟨b, hb⟩ := cyc_eq_X_mul l O c
    refine ⟨act l O ((l ^ (s - 1) : ℕ) : ℤ_[l]) b, ?_⟩
    conv_lhs => rw [← hψ, act_comm', act_X_eq, hb]
    simp only [map_mul, map_add, act_C, hψ]
  · obtain ⟨b, hb⟩ := act_QQ_one l O c
    refine ⟨act l O ((l ^ (s - 1) : ℕ) : ℤ_[l]) b, ?_⟩
    conv_lhs => rw [← hψQ, act_comm', hb]
    simp only [map_mul, map_add, map_one, hψ, hψQ]
  · intro u w hu a
    have hX : PowerSeries.X ∣ act l O u PowerSeries.X := by
      rw [act_X_eq, PowerSeries.X_dvd_iff]; exact cyc_const l O u
    refine Dvd.dvd.trans ?_ (algHom_sub_dvd (act l O u) hX a)
    obtain ⟨b, hb⟩ := cyc_eq_X_mul l O w
    have h1 : cyc l O (((l ^ s : ℕ) : ℤ_[l]) * w) = XX l O s * QQ l O s *
        act l O ((l ^ s : ℕ) : ℤ_[l]) (PowerSeries.C (algebraMap ℤ_[l] O w) + PowerSeries.X * b) := by
      rw [← act_X_eq, ← (GlobalTheory.Cyc.act_laws l O).2.1, act_X_eq l O w, hb, map_mul, act_nat_X,
        XX_mul_QQ' l O s hs]
    have h2 : cyc l O u + 1 = (cyc l O ((1 : ℕ) : ℤ_[l]) + 1) * (cyc l O (((l ^ s : ℕ) : ℤ_[l]) * w) + 1) := by
      simp only [cyc, sub_add_cancel]
      rw [← map_mul, ← PowerSeries.binomialSeries_add, hu]
      push_cast
      rfl
    rw [(GlobalTheory.Cyc.act_laws l O).2.2.2.1, h1] at h2
    rw [act_X_eq]
    exact ⟨(1 + PowerSeries.X) * act l O ((l ^ s : ℕ) : ℤ_[l])
      (PowerSeries.C (algebraMap ℤ_[l] O w) + PowerSeries.X * b), by linear_combination h2⟩

end GlobalTheory.Cyc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodCoefficientsExplicitSums
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory

theorem adicSpan_smul_top_mem_iff {O : Type} [CommRing O] (ϖ : O) (n : ℕ) (x : O) :
    x ∈ (Ideal.span {ϖ}) ^ n • (⊤ : Submodule O O) ↔ ∃ b : O, x = ϖ ^ n * b := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨a, mul_comm _ _⟩
  · rintro ⟨b, rfl⟩; exact ⟨b, mul_comm _ _⟩

theorem adicComplete_explicit_sums {O : Type} [CommRing O] (ϖ : O)
    [h : IsAdicComplete (Ideal.span {ϖ}) O] :
    (∀ x : ℕ → O, ∃ a : O, ∀ n : ℕ, ∃ b : O, a - ∑ j ∈ Finset.range n, ϖ ^ j * x j = ϖ ^ n * b) ∧
    (∀ a : O, (∀ n : ℕ, ∃ b : O, a = ϖ ^ n * b) → a = 0) := by
  refine ⟨fun x => ?_, fun a ha => ?_⟩
  · obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {ϖ}) (M := O)
      (fun n => ∑ j ∈ Finset.range n, ϖ ^ j * x j) (by
        intro m n hmn
        rw [SModEq.sub_mem, adicSpan_smul_top_mem_iff]
        refine ⟨-∑ j ∈ Finset.Ico m n, ϖ ^ (j - m) * x j, ?_⟩
        rw [← Finset.sum_range_add_sum_Ico _ hmn, mul_neg, Finset.mul_sum]
        have : ∑ j ∈ Finset.Ico m n, ϖ ^ m * (ϖ ^ (j - m) * x j)
            = ∑ j ∈ Finset.Ico m n, ϖ ^ j * x j := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' (Finset.mem_Ico.mp hj).1]
        rw [this]; ring)
    refine ⟨L, fun n => ?_⟩
    have h1 := (SModEq.sub_mem.mp (hL n))
    rw [adicSpan_smul_top_mem_iff] at h1
    obtain ⟨b, hb⟩ := h1
    exact ⟨-b, by rw [mul_neg, ← hb]; ring⟩
  · refine IsHausdorff.haus' (I := Ideal.span {ϖ}) a fun n => ?_
    rw [SModEq.zero, adicSpan_smul_top_mem_iff]
    exact ha n

theorem goodO_coeff_explicit_sums : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O →
    (∀ x : ℕ → O, ∃ a : O, ∀ n : ℕ, ∃ b : O,
      a - ∑ j ∈ Finset.range n, ((l : ℕ) : O) ^ j * x j = ((l : ℕ) : O) ^ n * b) ∧
    (∀ a : O, (∀ n : ℕ, ∃ b : O, a = ((l : ℕ) : O) ^ n * b) → a = 0) := by
  intro l _ LL _ _ _ O _ _ hG
  have hc := (GlobalTheory.T.coefficient_ring_integers_compact_adic_properties l LL O hG).2.2.2
  exact adicComplete_explicit_sums (h := hc) ((l : ℕ) : O)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodEigSumSupComplEigSumEqTop
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

namespace GlobalTheory.EtaJoin

theorem eigSum_good_sup_compl_eq_top : ∀ (D : D7) (i : D.nd.Loc), ZRat D (D.nd.mu i) (D.nd.j i) → SpecPr D i →
    D.nd.eigSum i ↑(D.nd.Zgood i) ⊔ D.nd.eigSum i (↑(D.nd.Zgood i))ᶜ = ⊤ := by
  intro D i hZ hS
  rw [eq_top_iff, ← D.nd.prMt_span i, Submodule.span_le]
  rintro _ ⟨y, rfl⟩
  have hy : y ∈ ratSub D (D.nd.mu i) (D.nd.j i) (Idx.Z0 D (D.nd.mu i) (D.nd.j i)) ⊔
      ratSub D (D.nd.mu i) (D.nd.j i) (Idx.Z0 D (D.nd.mu i) (D.nd.j i))ᗮ := by
    unfold ZRat at hZ
    rw [hZ]; exact Submodule.mem_top
  obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.1 hy
  rw [map_add]
  exact Submodule.add_mem_sup (hS.1 u hu) (hS.2 u' hu')

end GlobalTheory.EtaJoin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1LatticeRankGrowth
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

set_option autoImplicit false

namespace GlobalTheory.H1Rank

theorem growth_H1T_dim_H1V : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), Module.Finite O (LatticeCohomology LA) → Module.Finite LL (H1V A.ρ) ∧ ∃ C : ℕ, 0 < C ∧ ∀ r : ℕ, Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL (H1V A.ρ)) ≤ Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) ∧ Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) ≤ C * Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL (H1V A.ρ)) := by
  intro l _ K LL _ _ _ O _ _ hG A LA hfin
  have hG' := hG
  obtain ⟨⟨hD, hDVR, hFr⟩, -, -, -, -⟩ := hG'
  haveI := hD
  haveI := hDVR
  haveI := hFr
  have hl0 : ((l : ℕ) : O) ≠ 0 := by
    intro h
    have h1 : algebraMap O LL ((l : ℕ) : O) = 0 := by rw [h, map_zero]
    rw [map_natCast] at h1
    have h2 : ((l : ℕ) : LL) = algebraMap ℚ_[l] LL (l : ℚ_[l]) := by rw [map_natCast]
    rw [h2] at h1
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) ((map_eq_zero_iff _ (algebraMap ℚ_[l] LL).injective).1 h1)
  have hfq : ∀ r : ℕ, Finite (O ⧸ Ideal.span {((l : ℕ) : O) ^ r}) :=
    (GlobalTheory.GoodCoeff.good_coeff_integers l LL O hG).2.2.1
  have hfq1 : Finite (O ⧸ Ideal.span {((l : ℕ) : O)}) := by simpa using hfq 1
  have hsurj : ∀ y : H1V A.ρ, ∃ n : ℕ, ∃ x : LatticeCohomology LA, toH1V LA x = ((l : ℕ) : O) ^ n • y := by
    intro y
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨n, hn⟩ := pow_smul_mem_Z1T l K LL O hG A LA c.1 c.2
    refine ⟨n, Submodule.Quotient.mk ⟨_, hn⟩, ?_⟩
    rw [toH1V_mk]
    rfl
  have hker : ∀ x : LatticeCohomology LA, toH1V LA x = 0 → ∃ n : ℕ, ((l : ℕ) : O) ^ n • x = 0 := by
    intro x hx
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [toH1V_mk, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨n, hn⟩ := pow_smul_mem_B1T l K LL O hG A LA c.1 c.2 hx
    refine ⟨n, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hn
  obtain ⟨hF, hr⟩ := finite_finrank_of_localizes O LL (LatticeCohomology LA) (H1V A.ρ) (toH1V LA) _ hl0 hsurj hker
  refine ⟨hF, ?_⟩
  rw [hr]
  obtain ⟨C, hC, hb⟩ := GlobalTheory.T.card_quot_pow_smul_bounds_dvr_fg_module O (LatticeCohomology LA) _ hl0 (not_isUnit_l l LL O hG) hfq
  have e2 : ∀ r : ℕ, Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank O (LatticeCohomology LA)) = Nat.card (O ⧸ Ideal.span {((l : ℕ) : O) ^ r}) ^ finrank O (LatticeCohomology LA) := by
    intro r
    rw [GlobalTheory.T.card_quot_span_pow_eq_card_pow_domain O _ hl0 hfq1 r, pow_mul]
  refine ⟨C, hC, fun r => ⟨?_, ?_⟩⟩
  · exact (e2 r).trans_le (hb r).1
  · exact (hb r).2.trans_eq (congrArg (C * ·) (e2 r).symm)

end GlobalTheory.H1Rank
end

