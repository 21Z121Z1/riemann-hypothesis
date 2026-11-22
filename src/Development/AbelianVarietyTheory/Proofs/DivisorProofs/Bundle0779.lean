import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0347
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0769
import GroundTheory.ArithmeticGeometry.ToricVarieties.Dimension
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0114
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0102
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0111
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0747
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0768
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantIntegralKilledOfLowerDim
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

private theorem ringKrullDim_le_quotient_of_algebraMap_eq_zero (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] (s : R) (hs : algebraMap R S s = 0) :
    ringKrullDim S ≤ ringKrullDim (R ⧸ Ideal.span {s}) := by
  rw [ringKrullDim_quotient]
  have hmem : ∀ P : PrimeSpectrum S, (⟨P.asIdeal.comap (algebraMap R S), inferInstance⟩ : PrimeSpectrum R) ∈
      PrimeSpectrum.zeroLocus (R := R) (Ideal.span {s}) := fun P => by
    simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_le,
      Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, hs, Ideal.zero_mem]
  exact Order.krullDim_le_of_strictMono (fun P => ⟨_, hmem P⟩)
    (fun P Q h => Subtype.mk_lt_mk.mpr (Ideal.IsIntegral.comap_lt_comap (R := R) h))

private theorem hInv_adjoin_of_dim_quotient_lt (q : ℕ) [NeZero q] (d : ℕ)
    (hlow : ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R)
    (D : Type) [CommRing D] [Algebra.FiniteType ℤ D] (hqD : IsUnit (q : D)) (E : Type) [CommRing E]
    [Algebra D E] [Algebra.IsIntegral D E] (s : D) (hsE : algebraMap D E s = 0)
    (hlt : ringKrullDim (D ⧸ Ideal.span {s}) < d) (F : Finset E) :
    HInv q ((Algebra.adjoin D (F : Set E)).restrictScalars ℤ) := by
  set T := Algebra.adjoin D (F : Set E)
  have : Algebra.IsIntegral D T := ⟨fun x =>
    (isIntegral_algHom_iff T.val Subtype.val_injective).mp (Algebra.IsIntegral.isIntegral (x : E))⟩
  have : Algebra.FiniteType D T := (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset F)
  have : Algebra.FiniteType ℤ T := Algebra.FiniteType.trans (R := ℤ) (S := D) inferInstance inferInstance
  have hsT : algebraMap D T s = 0 := Subtype.ext (by simpa using hsE)
  have h1 : ringKrullDim T < d := (ringKrullDim_le_quotient_of_algebraMap_eq_zero D T s hsT).trans_lt hlt
  have h2 : IsUnit (q : T) := by simpa using hqD.map (algebraMap D T)
  exact hlow T h2 h1

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.hInv_of_integral_killed_of_lower : ∀ (q : ℕ) [NeZero q] (d : ℕ), (∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R) → ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D], IsUnit (q : D) → ringKrullDim D ≤ d → ∀ (E : Type) [CommRing E] [Algebra D E] [Algebra.IsIntegral D E] (s : D), s ≠ 0 → algebraMap D E s = 0 → HInv q E := by
  intro q _ d hlow D _ _ _ hqD hdD E _ _ _ s hs0 hsE
  have hquot := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hs0)
  have hlt : ringKrullDim (D ⧸ Ideal.span {s}) < d := by
    have h := hquot.trans hdD
    generalize ringKrullDim (D ⧸ Ideal.span {s}) = a at h ⊢
    cases a using WithBot.recBotCoe with
    | bot => exact WithBot.bot_lt_coe _
    | coe a =>
      have h' : a + 1 ≤ (d : ℕ∞) := by exact_mod_cast h
      have ha : a ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top d) (le_trans le_self_add h')
      exact_mod_cast (ENat.add_one_le_iff ha).mp h'
  exact GlobalTheory.T.hInv_of_directed_union_subalgebras q E (Finset E) (fun F => (Algebra.adjoin D (F : Set E)).restrictScalars ℤ)
    (fun F G h x hx => Algebra.adjoin_mono (Finset.coe_subset.mpr h) hx)
    (fun a => ⟨{a}, Algebra.subset_adjoin (by simp)⟩)
    (fun F => by
      have h := hqD.map (algebraMap D (Algebra.adjoin D (F : Set E)))
      rw [map_natCast] at h
      exact h)
    (fun F => hInv_adjoin_of_dim_quotient_lt q d hlow D hqD E s hsE hlt F)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EulerFactorEqOneOfExpAt
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
open scoped NNReal ENNReal

noncomputable section

attribute [local instance 2000] GlobalTheory.SplitWeil.matrixMeasurableSpace

namespace GlobalTheory.StdLocZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : ℕ}

def StdSupp (ϖ : kˣ) (c : ℕ) (x : Matrix (Fin n ⊕ Fin n') (Fin n) k) : Prop :=
  (∀ i j, x.toRows₁ i j ∈ 𝒪[k]) ∧ valuation k x.toRows₁.det = 1 ∧ ∀ i j, x.toRows₂ i j ∈ cball (ϖ ^ c)

theorem StdSupp.det_ne {ϖ : kˣ} {c : ℕ} {x : Matrix (Fin n ⊕ Fin n') (Fin n) k} (h : StdSupp ϖ c x) :
    x.toRows₁.det ≠ 0 := fun h0 => by
  have := h.2.1
  rw [h0, map_zero] at this
  exact zero_ne_one this

open Classical in

def stdDatum (μ : kˣ →* ℂˣ) (ϖ : kˣ) (c : ℕ) (x : Matrix (Fin n ⊕ Fin n') (Fin n) k) : ℂ :=
  if h : StdSupp ϖ c x then (((μ (Units.mk0 _ h.det_ne))⁻¹ : ℂˣ) : ℂ) else 0

theorem int_mul {m p r : Type} [Fintype p] {A : Matrix m p k} {B : Matrix p r k} (hA : ∀ i j, A i j ∈ 𝒪[k])
    (hB : ∀ i j, B i j ∈ 𝒪[k]) (i j) : (A * B) i j ∈ 𝒪[k] := by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun l _ => mul_mem (hA i l) (hB l j)

theorem cball_mul {m p r : Type} [Fintype p] {s : kˣ} {A : Matrix m p k} {B : Matrix p r k}
    (hA : ∀ i j, A i j ∈ cball s) (hB : ∀ i j, B i j ∈ 𝒪[k]) (i j) : (A * B) i j ∈ cball s := by
  rw [Matrix.mul_apply]
  refine Finset.sum_induction _ (· ∈ cball s) (fun _ _ => add_mem_cball) (by simp [cball]) fun l _ => ?_
  have h1 := hA i l
  have h2 := hB l j
  simp only [cball, Set.mem_setOf_eq, map_mul] at h1 ⊢
  rw [Valuation.mem_integer_iff] at h2
  calc valuation k (A i l) * valuation k (B l j) ≤ valuation k (s : k) * 1 := mul_le_mul' h1 h2
    _ = _ := mul_one _

theorem toRows₁_mul {m : Type} [Fintype m] (x : Matrix (Fin n ⊕ Fin n') m k) (g : Matrix m (Fin n) k) :
    (x * g).toRows₁ = x.toRows₁ * g := by ext i j; simp [Matrix.toRows₁, Matrix.mul_apply]

theorem toRows₂_mul {m : Type} [Fintype m] (x : Matrix (Fin n ⊕ Fin n') m k) (g : Matrix m (Fin n) k) :
    (x * g).toRows₂ = x.toRows₂ * g := by ext i j; simp [Matrix.toRows₂, Matrix.mul_apply]

theorem valuation_det_KO {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) : valuation k g.val.det = 1 := by
  obtain ⟨u, rfl⟩ := hg
  have h1 : (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u).val.det = algebraMap 𝒪[k] k u.val.det :=
    ((algebraMap 𝒪[k] k).map_det _).symm
  rw [h1]
  exact (Valuation.integer.integers (valuation k)).one_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).1 u.isUnit)

theorem StdSupp.mul {ϖ : kˣ} {c : ℕ} {x : Matrix (Fin n ⊕ Fin n') (Fin n) k} (h : StdSupp ϖ c x)
    {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) : StdSupp ϖ c (x * g.val) := by
  have hgi := ((SplitFlip.mem_KO_iff g).1 hg).1
  refine ⟨?_, ?_, ?_⟩
  · rw [toRows₁_mul]; exact int_mul h.1 hgi
  · rw [toRows₁_mul, Matrix.det_mul, map_mul, h.2.1, valuation_det_KO hg, one_mul]
  · rw [toRows₂_mul]; exact cball_mul h.2.2 hgi

end GlobalTheory.StdLocZeta

namespace GlobalTheory.StdLocZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : ℕ}

end GlobalTheory.StdLocZeta

namespace GlobalTheory.StdLocZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : ℕ}

end GlobalTheory.StdLocZeta

namespace GlobalTheory.StdLocZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : ℕ}

end GlobalTheory.StdLocZeta

namespace GlobalTheory.StdLocZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : ℕ}

end GlobalTheory.StdLocZeta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EulerLLocPolyNeZeroFarRight
section
open NumberField IsDedekindDomain MeasureTheory Matrix Polynomial GroundTheory.Automorphic UpperTheory.V
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin)
open UpperTheory.V.TR (Rinf Lie chart infGL pInf toL rmul invSet CuspSub)
open scoped ContDiff
open GlobalTheory.HenQ

namespace GlobalTheory.HenQ

lemma prod_inv_one_sub_eq_exp (x : ℂ) (m : Multiset ℂ) (h : ∀ b ∈ m, ‖b * x‖ ≤ 1 / 2) :
    (m.map fun b => (1 - b * x)⁻¹).prod =
      Complex.exp ((m.map fun b => -Complex.log (1 - b * x)).sum) := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons, Complex.exp_add,
      ih (fun b hb => h b (Multiset.mem_cons_of_mem hb))]
    congr 1
    have hne : (1 - a * x) ≠ 0 := by
      intro h0
      have ha := h a (Multiset.mem_cons_self a m)
      have h1 : a * x = 1 := by linear_combination -h0
      rw [h1, norm_one] at ha
      norm_num at ha
    rw [Complex.exp_neg, Complex.exp_log hne]

lemma norm_sum_neg_log_le (x : ℂ) (r : ℝ) (hr : r ≤ 1 / 2) (m : Multiset ℂ) (h : ∀ b ∈ m, ‖b * x‖ ≤ r) :
    ‖(m.map fun b => -Complex.log (1 - b * x)).sum‖ ≤ m.card * (3 / 2 * r) := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    have ha := h a (Multiset.mem_cons_self a m)
    have h1 : ‖-Complex.log (1 - a * x)‖ ≤ 3 / 2 * r := by
      rw [norm_neg, sub_eq_add_neg]
      refine (Complex.norm_log_one_add_half_le_self (by rw [norm_neg]; linarith)).trans ?_
      rw [norm_neg]; linarith
    have h2 := ih (fun b hb => h b (Multiset.mem_cons_of_mem hb))
    calc _ ≤ ‖-Complex.log (1 - a * x)‖ + ‖(m.map fun b => -Complex.log (1 - b * x)).sum‖ :=
          norm_add_le _ _
      _ ≤ 3 / 2 * r + m.card * (3 / 2 * r) := add_le_add h1 h2
      _ = _ := by push_cast; ring

lemma two_le_absNorm_prime {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    (2 : ℝ) ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  have : 2 ≤ Ideal.absNorm v.asIdeal := by omega
  exact_mod_cast this

theorem eulerL_locPoly_ne_zero_far_right : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ)
    (S : Set (HeightOneSpectrum (𝓞 K))) (B : HeightOneSpectrum (𝓞 K) → Multiset ℂˣ) (c : ℝ),
    (∀ w ∉ S, (B w).card = n) → (∀ w ∉ S, ∀ b ∈ B w, ‖(b : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ c) →
    ∀ s : ℂ, c + 2 < s.re → eulerL K (fun w => (B w).map fun b => (b : ℂ)) S s ≠ 0 ∧
      ∀ w ∉ S, (locPoly (B w)).eval ((Ideal.absNorm w.asIdeal : ℂ) ^ (-s)) ≠ 0 := by
  intro K _ _ n S B c hcard hB s hs
  set t := s.re - c with ht
  have ht2 : 2 < t := by rw [ht]; linarith

  have key : ∀ w ∉ S, ∀ b ∈ Multiset.map (fun b : ℂˣ => (b : ℂ)) (B w),
      ‖b * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (-t) := by
    intro w hw b hb
    obtain ⟨b', hb', rfl⟩ := Multiset.mem_map.mp hb
    have hN2 := two_le_absNorm_prime w
    have hNpos : (0 : ℝ) < Ideal.absNorm w.asIdeal := by linarith
    have hNpos' : 0 < Ideal.absNorm w.asIdeal := by exact_mod_cast hNpos
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hNpos', Complex.neg_re]
    calc ‖(b' : ℂ)‖ * (Ideal.absNorm w.asIdeal : ℝ) ^ (-s.re)
        ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ c * (Ideal.absNorm w.asIdeal : ℝ) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right (hB w hw b' hb') (by positivity)
      _ = _ := by rw [← Real.rpow_add hNpos, ht]; ring_nf
  have small : ∀ w : HeightOneSpectrum (𝓞 K), (Ideal.absNorm w.asIdeal : ℝ) ^ (-t) ≤ 1 / 2 := by
    intro w
    have hN2 := two_le_absNorm_prime w
    calc (Ideal.absNorm w.asIdeal : ℝ) ^ (-t) ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = (Ideal.absNorm w.asIdeal : ℝ)⁻¹ := Real.rpow_neg_one _
      _ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) hN2
  refine ⟨?_, ?_⟩
  · set g : {w // w ∉ S} → ℂ := fun w =>
      ((Multiset.map (fun b : ℂˣ => (b : ℂ)) (B w.1)).map fun b =>
        -Complex.log (1 - b * ((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ (-s))).sum with hg
    have hsumN : Summable fun w : {w // w ∉ S} => (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-t) :=
      (GlobalTheory.summable_absNorm_rpow_heightOneSpectrum K t (by linarith)).subtype _
    have hsum : Summable g := by
      refine Summable.of_norm_bounded (g := fun w : {w // w ∉ S} =>
        (n : ℝ) * (3 / 2 * (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-t))) ?_ ?_
      · exact (hsumN.mul_left (3 / 2)).mul_left (n : ℝ)
      · intro w
        have h := norm_sum_neg_log_le (((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ (-s))
          ((Ideal.absNorm w.1.asIdeal : ℝ) ^ (-t)) (small w.1) (Multiset.map (fun b : ℂˣ => (b : ℂ)) (B w.1))
          (key w.1 w.2)
        rw [Multiset.card_map, hcard w.1 w.2] at h
        exact h
    have hprod : HasProd (fun w : {w // w ∉ S} =>
        ((Multiset.map (fun b : ℂˣ => (b : ℂ)) (B w.1)).map fun b =>
          (1 - b * ((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹).prod) (Complex.exp (∑' w, g w)) := by
      have h := hsum.hasSum.cexp
      convert h using 1
      funext w
      simp only [Function.comp_apply, hg]
      exact prod_inv_one_sub_eq_exp _ _ (fun b hb => (key w.1 w.2 b hb).trans (small w.1))
    have hm : (fun w => ((B w).map fun b => (b : ℂ))) = fun w => Multiset.map (fun b : ℂˣ => (b : ℂ)) (B w) :=
      funext fun w => by simp only [Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_id']
    rw [hm]
    unfold eulerL
    rw [hprod.tprod_eq]
    exact Complex.exp_ne_zero _
  · intro w hw
    rw [locPoly, Polynomial.eval_multiset_prod, Multiset.map_map]
    refine Multiset.prod_ne_zero ?_
    intro h0
    obtain ⟨b, hb, hb0⟩ := Multiset.mem_map.mp h0
    simp only [Function.comp_apply, eval_sub, eval_one, eval_mul, eval_C, eval_X] at hb0
    have hb' : b ∈ Multiset.map (fun b : ℂˣ => (b : ℂ)) (B w) := by
      simpa only [Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton] using hb
    have hk := (key w hw b hb').trans (small w)
    have h1 : (b : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s) = 1 := by
      linear_combination -hb0
    rw [h1, norm_one] at hk
    norm_num at hk

end GlobalTheory.HenQ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyShiftMem
section
set_option autoImplicit false

noncomputable section

open Filter Topology TopologicalSpace CategoryTheory GlobalTheory.AnPer GlobalTheory.CatCoh GlobalTheory.Cris TensorProduct

namespace GlobalTheory.AnPer.CloseTaylor

variable {I : Type} [Fintype I] [DecidableEq I] {g : ℕ}

def splitL (I : Type) [Fintype I] (g : ℕ) : (I ⊕ Fin g → ℂ) →L[ℂ] Tot I g :=
  (ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.proj (Sum.inl i)).prod
    (ContinuousLinearMap.pi fun b ↦ ContinuousLinearMap.proj (Sum.inr b))

omit [DecidableEq I] in

theorem shift_eq (w : Fin g → ℂ) (x : I ⊕ Fin g → ℂ) :
    (((fun i ↦ x (Sum.inl i)), w + fun b ↦ x (Sum.inr b)) : Tot I g) = (0, w) + splitL I g x := by
  ext <;> simp [splitL]

theorem splitL_single (b : Fin g) :
    splitL I g (Pi.single (Sum.inr b) 1) = ((0, Pi.single b 1) : Tot I g) := by
  ext i <;> simp [splitL, Pi.single_apply]

omit [DecidableEq I] in

theorem eventually_shift_mem {W : Opens (Tot I g)} {w : Fin g → ℂ} (hw : ((0 : I → ℂ), w) ∈ W) :
    ∀ᶠ x : I ⊕ Fin g → ℂ in 𝓝 0, (0, w) + splitL I g x ∈ W := by
  have hc : Continuous (fun x : I ⊕ Fin g → ℂ ↦ ((0, w) : Tot I g) + splitL I g x) :=
    continuous_const.add (splitL I g).continuous
  refine hc.continuousAt.eventually (W.isOpen.mem_nhds ?_)
  simpa using hw

omit [DecidableEq I] in

theorem analyticAt_shifted {W : Opens (Tot I g)} (h : Hol W) {w : Fin g → ℂ} (hw : ((0 : I → ℂ), w) ∈ W) :
    AnalyticAt ℂ (fun x : I ⊕ Fin g → ℂ ↦ h.fn ((0, w) + splitL I g x)) 0 :=
  AnalyticAt.comp_of_eq (f := fun x : I ⊕ Fin g → ℂ ↦ ((0, w) : Tot I g) + splitL I g x)
    (h.analytic _ hw) (analyticAt_const.add ((splitL I g).analyticAt 0)) (by simp)

theorem fderiv_shifted {W : Opens (Tot I g)} (h : Hol W) {w : Fin g → ℂ} (hw : ((0 : I → ℂ), w) ∈ W)
    (b : Fin g) :
    (fun z ↦ fderiv ℂ (fun x : I ⊕ Fin g → ℂ ↦ h.fn ((0, w) + splitL I g x)) z (Pi.single (Sum.inr b) 1))
      =ᶠ[𝓝 0] fun x : I ⊕ Fin g → ℂ ↦ (dw b h).fn ((0, w) + splitL I g x) := by
  filter_upwards [eventually_shift_mem hw] with z hz
  have e : HasFDerivAt (fun x : I ⊕ Fin g → ℂ ↦ h.fn ((0, w) + splitL I g x))
      ((fderiv ℂ h.fn ((0, w) + splitL I g z)).comp (splitL I g)) z :=
    HasFDerivAt.comp (f := fun x : I ⊕ Fin g → ℂ ↦ ((0, w) : Tot I g) + splitL I g x) z
      (h.analytic _ hz).differentiableAt.hasFDerivAt ((splitL I g).hasFDerivAt.const_add _)
  rw [e.fderiv, ContinuousLinearMap.comp_apply, splitL_single]
  exact (Hol.fn_der _ h hz).symm

end GlobalTheory.AnPer.CloseTaylor

open GlobalTheory.AnPer.CloseTaylor in

theorem GlobalTheory.AnPer.close_of_sliceTaylor : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {D : Type} [CommRing D] [Algebra ℂ D] (J : Ideal D) (N : ℕ), (∀ s : Fin (N + 1) → D, (∀ a, s a ∈ J) → ∏ a, s a = 0) → ∀ (t : I → D), (∀ i, t i ∈ J) → ∀ (r : ℕ) (n : Fin r → Fin g → D), (∀ j a, n j a ∈ J) → (∀ j a b, n j a * n j b = 0) → ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (W : Opens (Tot I g)) (W₀ : Opens E) (a : E → Fin g → ℂ), AnalyticOnNhd ℂ a W₀ → (∀ p ∈ W₀, ((0 : I → ℂ), a p) ∈ W) → ∀ ρ₁ ρ₂ : Hol W →+* D ⊗[ℂ] Hol W₀, (∀ (h : Hol W) (p : E) (hp : p ∈ W₀), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) (ρ₁ h) = GlobalTheory.PeriodFamily.taylor N (Sum.elim t fun b ↦ ∑ j, n j b) (fun x : I ⊕ Fin g → ℂ ↦ h.fn (fun i ↦ x (Sum.inl i), a p + fun b ↦ x (Sum.inr b)))) → (∀ (h : Hol W) (p : E) (hp : p ∈ W₀), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) (ρ₂ h) = GlobalTheory.PeriodFamily.taylor N (Sum.elim t fun _ ↦ 0) (fun x : I ⊕ Fin g → ℂ ↦ h.fn (fun i ↦ x (Sum.inl i), a p + fun b ↦ x (Sum.inr b)))) → Close (J.map (Algebra.TensorProduct.includeLeft : D →ₐ[ℂ] D ⊗[ℂ] Hol W₀)) ρ₁ ρ₂ := by
  intro I _ _ g D _ _ J N hJ t ht r n hn hnn E _ _ _ W W₀ a ha hW ρ₁ ρ₂ h₁ h₂
  induction r generalizing ρ₁ with
  | zero =>
    have : ρ₁ = ρ₂ := RingHom.ext fun h ↦ GlobalTheory.tensor_hol_ext_of_values W₀ D _ _ fun p hp ↦ by
      rw [h₁, h₂]; simp
    rw [this]
    exact Relation.ReflTransGen.refl
  | succ r ih =>
    obtain ⟨ρ', hρ'⟩ := GlobalTheory.T.tensorLift_ev_rho_eq_taylor_slice N (Sum.elim t fun b ↦ ∑ j : Fin r, n j.succ b)
      (fun s ↦ hJ _ fun c ↦ by
        rcases s c with i | b
        · exact ht i
        · exact J.sum_mem fun j _ ↦ hn _ _) W W₀ a ha hW
    refine Relation.ReflTransGen.head (b := (ρ' : Hol W →+* D ⊗[ℂ] Hol W₀)) ?_
      (ih (fun j ↦ n j.succ) (fun j ↦ hn _) (fun j ↦ hnn _) _ hρ')
    refine ⟨fun b ↦ (-n 0 b) ⊗ₜ[ℂ] 1, fun b ↦ Ideal.mem_map_of_mem _ (J.neg_mem (hn 0 b)), fun b c ↦ ?_, fun h ↦ ?_⟩
    · rw [Algebra.TensorProduct.tmul_mul_tmul, neg_mul_neg, hnn, zero_tmul]
    refine GlobalTheory.tensor_hol_ext_of_values W₀ D _ _ fun p hp ↦ ?_
    have e : (Sum.elim t fun b ↦ ∑ j : Fin r, n j.succ b) = fun i : I ⊕ Fin g ↦
        (Sum.elim t fun b ↦ ∑ j, n j b) i + (Sum.elim (fun _ ↦ 0) fun b ↦ -n 0 b) i := by
      ext (i | b)
      · simp
      · simp [Fin.sum_univ_succ]
    have hs := GlobalTheory.T.taylor_add_square_zero_nilpotent N (Sum.elim t fun b ↦ ∑ j, n j b) (Sum.elim (fun _ : I ↦ 0) fun b ↦ -n 0 b)
      (fun s hs ↦ hJ s fun c ↦ (Ideal.span_le.2 (by
        rintro _ (⟨i | b, rfl⟩ | ⟨i | b, rfl⟩)
        · exact ht i
        · exact J.sum_mem fun j _ ↦ hn _ _
        · exact J.zero_mem
        · exact J.neg_mem (hn 0 b))) (hs c))
      (by rintro (i | b) (j | c) <;> simp [hnn]) _ (analyticAt_shifted h (hW p hp))
    obtain ⟨-, -, -, hcongr, -, -⟩ :=
      GlobalTheory.PeriodFamily.taylor_formal_properties N (Sum.elim t fun b ↦ ∑ j, n j b)
    rw [RingHom.coe_coe, hρ', map_add, map_sum, h₁, e]
    simp only [map_mul, h₁, shift_eq]
    rw [hs, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, mul_zero, Finset.sum_const_zero, zero_add]
    refine congrArg _ (Finset.sum_congr rfl fun b _ ↦ ?_)
    rw [hcongr _ _ (fderiv_shifted h (hW p hp) b)]
    simp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBirigidifiedBundleOfDescent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section
namespace GlobalTheory.UPel.HT.Hecke

theorem left_comp_of_comp {S : Scheme.{0}} {X Y Z : Over S} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (e : f ≫ g = h) :
    f.left ≫ g.left = h.left := by
  rw [← Over.comp_left, e]

theorem exists_birigidified_of_descent : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A'), IsMonHom ψ → ∀ (m : ℕ) (P₀ : LB (G2 A').left), P₀.IsLB → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P₀.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → ∃ P' : LB (G2 A').left, P'.IsLB ∧ (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) ∧ (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) ∧ LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) := by
  intro p _ D R _ b M S s o A' _ _ ψ hψ m P₀ hP₀ H
  let φ : Fin 4 → ((G2 A').left ⟶ (G2 A').left) := ![𝟙 _, (lift (fst A' A') (1 : G2 A' ⟶ A')).left,
    (lift (1 : G2 A' ⟶ A') (snd A' A')).left, (lift (1 : G2 A' ⟶ A') (1 : G2 A' ⟶ A')).left]
  let ε : Fin 4 → ℤ := ![1, -1, -1, 1]
  have hε : ε 0 = 1 ∧ ε 1 = -1 ∧ ε 2 = -1 ∧ ε 3 = 1 := ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨LB.LinComb P₀ φ ε, DVR.linComb_isLB P₀ hP₀ φ ε, ?_, ?_, ?_⟩
  · refine GlobalTheory.PrimNorm.hasGen_nested hP₀ φ ε (fun _ : PUnit => _) (fun _ => 1) ?_
    have e0 : (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ 0 = (lift (1 : A' ⟶ A') (𝟙 A')).left := Category.comp_id _
    have e1 : (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ 1 = (lift (1 : A' ⟶ A') (1 : A' ⟶ A')).left :=
      left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
    have e2 : (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ 2 = (lift (1 : A' ⟶ A') (𝟙 A')).left :=
      left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
    have e3 : (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ 3 = (lift (1 : A' ⟶ A') (1 : A' ⟶ A')).left :=
      left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
    rw [Fintype.prod_unique, zpow_one, Fin.prod_univ_four, e0, e1, e2, e3]
    rw [hε.1, hε.2.1, hε.2.2.1, hε.2.2.2, zpow_one, zpow_one, zpow_neg_one, zpow_neg_one,
      mul_right_comm _ _ (GlobalTheory.PrimNorm.cls P₀ _)⁻¹, mul_inv_cancel, _root_.one_mul, inv_mul_cancel]
  · refine GlobalTheory.PrimNorm.hasGen_nested hP₀ φ ε (fun _ : PUnit => _) (fun _ => 1) ?_
    have e0 : (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ 0 = (lift (𝟙 A') (1 : A' ⟶ A')).left := Category.comp_id _
    have e1 : (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ 1 = (lift (𝟙 A') (1 : A' ⟶ A')).left :=
      left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
    have e2 : (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ 2 = (lift (1 : A' ⟶ A') (1 : A' ⟶ A')).left :=
      left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
    have e3 : (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ 3 = (lift (1 : A' ⟶ A') (1 : A' ⟶ A')).left :=
      left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
    rw [Fintype.prod_unique, zpow_one, Fin.prod_univ_four, e0, e1, e2, e3]
    rw [hε.1, hε.2.1, hε.2.2.1, hε.2.2.2, zpow_one, zpow_one, zpow_neg_one, zpow_neg_one,
      mul_inv_cancel, _root_.one_mul, inv_mul_cancel]
  · haveI := hψ
    let ρ : Fin 4 → ((G2 o.A).left ⟶ (G2 o.A).left) := ![𝟙 _, (lift (fst o.A o.A) (1 : G2 o.A ⟶ o.A)).left,
      (lift (1 : G2 o.A ⟶ o.A) (snd o.A o.A)).left, (lift (1 : G2 o.A ⟶ o.A) (1 : G2 o.A ⟶ o.A)).left]
    have hsq : ∀ k, sq2 ψ ≫ φ k = ρ k ≫ sq2 ψ := by
      intro k
      fin_cases k
      · exact (Category.comp_id _).trans (Category.id_comp _).symm
      all_goals
        refine (left_comp_of_comp rfl).trans ((left_comp_of_comp ?_).symm)
        apply CartesianMonoidalCategory.hom_ext <;> simp
    have hP := o.isLB
    have cls1 : ∀ (r : (G2 o.A).left ⟶ (G2 o.A).left),
        GlobalTheory.MulPull.HasGen o.P (fun _ : PUnit => r) (fun _ => 1) → GlobalTheory.PrimNorm.cls o.P r = 1 := by
      intro r h
      have := (GlobalTheory.PrimNorm.hasGen_iff hP _ _).1 h
      rwa [Fintype.prod_unique, zpow_one] at this
    have h1 : GlobalTheory.PrimNorm.cls o.P (ρ 1) = 1 := by
      refine cls1 _ ?_
      have h := GlobalTheory.MulPull.HasGen.pull (φ := fun _ : PUnit => (lift (𝟙 o.A) (1 : o.A ⟶ o.A)).left)
        (ε := fun _ => 1) o.rig₂ (fst o.A o.A).left
      have e : (fst o.A o.A).left ≫ (lift (𝟙 o.A) (1 : o.A ⟶ o.A)).left = ρ 1 :=
        left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
      simpa only [e] using h
    have h2 : GlobalTheory.PrimNorm.cls o.P (ρ 2) = 1 := by
      refine cls1 _ ?_
      have h := GlobalTheory.MulPull.HasGen.pull (φ := fun _ : PUnit => (lift (1 : o.A ⟶ o.A) (𝟙 o.A)).left)
        (ε := fun _ => 1) o.rig₁ (snd o.A o.A).left
      have e : (snd o.A o.A).left ≫ (lift (1 : o.A ⟶ o.A) (𝟙 o.A)).left = ρ 2 :=
        left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
      simpa only [e] using h
    have h3 : GlobalTheory.PrimNorm.cls o.P (ρ 3) = 1 := by
      refine cls1 _ ?_
      have h := GlobalTheory.MulPull.HasGen.pull (φ := fun _ : PUnit => (lift (𝟙 o.A) (1 : o.A ⟶ o.A)).left)
        (ε := fun _ => 1) o.rig₂ (fst o.A o.A ≫ (1 : o.A ⟶ o.A)).left
      have e : (fst o.A o.A ≫ (1 : o.A ⟶ o.A)).left ≫ (lift (𝟙 o.A) (1 : o.A ⟶ o.A)).left = ρ 3 :=
        left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
      simpa only [e] using h
    have L1 : (lbPow o.P m).IsLB := DVR.linComb_isLB o.P hP _ _
    have L2 : (LB.LinComb (lbPow o.P m) ρ ε).IsLB := DVR.linComb_isLB _ L1 _ _
    have L3 : (LB.LinComb P₀ (fun k => ρ k ≫ sq2 ψ) ε).IsLB := DVR.linComb_isLB _ hP₀ _ _
    have L4 : ((LB.LinComb P₀ φ ε).pull (sq2 ψ)).IsLB := DVR.linComb_isLB _ (DVR.linComb_isLB _ hP₀ _ _) _ _
    have I1 : LBIso (lbPow o.P m) (LB.LinComb (lbPow o.P m) ρ ε) := by
      refine LBIso.symm (GlobalTheory.PrimNorm.lbIso_nested hP (fun _ : Fin m => 𝟙 _) (fun _ => 1) ρ ε
        (fun _ : Fin m => 𝟙 _) (fun _ => 1) ?_)
      simp only [Category.comp_id, zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Fin.prod_univ_four, h1, h2, h3, one_pow, one_zpow, _root_.mul_one, hε.1]
      rfl
    obtain ⟨w, hw⟩ := H
    have I2 : LBIso (LB.LinComb (lbPow o.P m) ρ ε) (LB.LinComb P₀ (fun k => ρ k ≫ sq2 ψ) ε) :=
      iso_linComb ((isGen_iff w).1 hw) ρ ε
    have I3 : LBIso (LB.LinComb P₀ (fun k => ρ k ≫ sq2 ψ) ε) ((LB.LinComb P₀ φ ε).pull (sq2 ψ)) := by
      refine LBIso.symm (GlobalTheory.PrimNorm.lbIso_nested hP₀ φ ε (fun _ : PUnit => sq2 ψ) (fun _ => 1)
        (fun k => ρ k ≫ sq2 ψ) ε ?_)
      rw [Fintype.prod_unique, zpow_one]
      exact Finset.prod_congr rfl fun k _ => by rw [hsq k]
    exact LBIso.trans L1 L2 L4 I1 (LBIso.trans L2 L3 L4 I2 I3)
end GlobalTheory.UPel.HT.Hecke
end
end

