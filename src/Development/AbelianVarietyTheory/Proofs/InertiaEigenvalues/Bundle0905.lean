import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0898
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0894
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0645
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0872
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.Bundle0002
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0011
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0010
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0866
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0899
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIntegralUpperMspan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0890
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0895
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0791
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterValuesInjectiveLength
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0400
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0129
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0900
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilLagrangianTermsAbsTsumLeHeightPoly
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerProductRankinSelbergGLnGLmDirichletSeriesStatement
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eulerProduct_rankinSelbergGLnGLm_dirichletSeries : ∀ {I : Type} (q : I → ℕ) {n m : ℕ}, m ≤ n → ∀ (α : I → Fin n → ℂˣ) (β : I → Fin m → ℂˣ) (x : ℝ), 1 < x →
    (∀ i, 2 ≤ q i) → GlobalTheory.RSPole.eulD q (fun i j => (α i j : ℂ)) x ≠ ⊤ → GlobalTheory.RSPole.eulD q (fun i j => (β i j : ℂ)) x ≠ ⊤ →
    ∃ P : ℂ, HasProd (fun i => GlobalTheory.JSW.locL (q i) (Finset.univ.val.map (α i))
        ((Finset.univ.val.map (β i)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) P ∧
      HasSum (fun l : I →₀ (Fin m → ℤ) => l.prod fun i v =>
        GlobalTheory.RSnmUnf.rsTermNM (q i) (fun j => (α i j : ℂ)) (fun j => (β i j : ℂ)) x v) P := by
  first | (exact @GlobalTheory.RSnmEul.euler_rsTermNM) | (exact GlobalTheory.RSnmEul.euler_rsTermNM) | (intros; apply GlobalTheory.RSnmEul.euler_rsTermNM  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExcludedPrimesFewAndSmallAlongFamily
section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink.ExcBound

open GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes

theorem card_Icc_ceil_floor_le (a b : ℝ) :
    ((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℝ) ≤ max (b - a + 1) 0 := by
  have h : ((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℤ) = max (⌊b⌋ + 1 - ⌈a⌉) 0 := by
    rw [Int.card_Icc, Int.toNat_eq_max]
  have h' : (((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℤ) : ℝ) = ((max (⌊b⌋ + 1 - ⌈a⌉) 0 : ℤ) : ℝ) := by rw [h]
  push_cast at h'
  rw [h']
  exact max_le_max (by linarith [Int.floor_le b, Int.le_ceil a]) le_rfl

variable {D : D7} (L : SizeData₂ D)

theorem excOK_at (P : ParameterChoice' D L) (hS : SizesAt L) :
    ∃ exc : Finset ℕ, (exc : Set ℕ) = Exc L ∧ ExcOK L exc := by
  obtain ⟨-, -, -, -, -, -, -, -, hLa, hRho, hBot, -, -, -, -, hLs, -⟩ := hS
  obtain ⟨hL1, hL2⟩ := hLs
  have hsz : szlStar L = LevelStarExponents.lStar L := rfl
  rw [hsz] at hL1 hL2
  set ls := LevelStarExponents.lStar L with hls_def
  have hls : 0 < ls := lStar_pos L
  have h2ls : 2 * ls < L.sc.b := GlobalTheory.Survey.CongruenceBoundParameters.two_lStar_lt_b L
  have hx : 1 < L.sc.x := L.sc.one_lt_alt
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hη := L.etaSz_pos
  have hSc := L.Sc_pos
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)
  have hn1 : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := D.R.ord_pos
    exact_mod_cast this
  have hX : 1 ≤ L.sc.X' := Real.one_le_exp (by positivity)
  have hb' : 0 < L.sc.b' := by unfold Scale.b' Scale.a; positivity
  have ht0 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hbl : 0 ≤ L.sc.b / ls := by positivity

  have h8 : 8 * L.sc.b < ls ^ 2 := by
    have : 8 * L.sc.b / ls < ls := by
      have : 8 * L.sc.b / ls = 8 * (L.sc.b / ls) := by ring
      linarith
    rw [div_lt_iff₀ hls] at this; nlinarith

  have hsg0 : (0 : ℝ) ≤ (sgPlus L : ℝ) := by
    exact_mod_cast Int.floor_nonneg.2 (by positivity)
  have hsg1 : (sgPlus L : ℝ) ≤ 2 * L.sc.b / ls := Int.floor_le _
  have hsg2 : 2 * L.sc.b / ls = 2 * (L.sc.b / ls) := by ring
  rw [hsg2] at hsg1
  have hL2' : 2 * L.etaSz + D.R.t + 8 * (L.sc.b / ls) + 7 < ls := by
    have : 8 * L.sc.b / ls = 8 * (L.sc.b / ls) := by ring
    linarith

  have hw2 : L.sc.w'' D.R.n ≤ L.sc.b := by
    have : L.sc.w'' D.R.n = L.sc.b / (L.sc.X' * D.R.n) := by
      unfold Scale.w'' Scale.b' Scale.a; field_simp
    rw [this]; exact div_le_self hb.le (by nlinarith)
  have hbT : ∀ t, (L.bT t : ℝ) ≤ L.sc.b' + L.sc.b' / 4 := by
    intro t
    have h1 := hBot t
    have hk : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
    have hxe : 0 < L.sc.x ^ L.sc.eps := Real.rpow_pos_of_pos (by linarith) _
    have hΛ : 0 ≤ L.LaG := le_trans hxe.le hLa.1
    have hsec : 0 ≤ L.sc.x ^ szTh L * Real.log L.sc.x * L.LaG / D.R.k := by
      have := Real.log_nonneg hx.le
      have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ L.sc.x) (szTh L)
      positivity
    have hone : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.le (by norm_num)
    have hA : szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / 4 := by
      have : 4 * szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k =
          4 * (szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
      have := hRho
      unfold SizeRho at this
      linarith
    have : szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
        (szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
    rw [this] at h1
    nlinarith
  have hfl : ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ) ≤ L.sc.b' := by
    refine (Int.floor_le _).trans (div_le_self hb'.le hx.le)
  have hW2 : ∀ W ∈ baseSizes L, W ≤ 2 * L.sc.b := by
    rintro W (rfl | rfl | ⟨t, rfl⟩)
    · linarith
    · linarith
    · have := hbT t; linarith

  have hhi : ∀ W ∈ baseSizes L,
      W + (L.Sc + L.etaSz + L.etaSz + 2 * (sgPlus L : ℝ) + 4) < 3 * L.sc.b := by
    intro W hW
    have := hW2 W hW
    linarith

  let BS : Finset ℝ := {L.sc.b, L.sc.w'' D.R.n} ∪
    Finset.univ.image (fun t : D.host.TT => (L.bT t : ℝ) + ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ))
  have hBS : ∀ W, W ∈ BS ↔ W ∈ baseSizes L := by
    intro W
    simp only [BS, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_univ, true_and, baseSizes, Set.mem_setOf_eq]
    constructor
    · rintro ((h | h) | ⟨t, h⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨t, h.symm⟩)
    · rintro (h | h | ⟨t, h⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨t, h.symm⟩
  have hBScard : (BS.card : ℝ) ≤ (D.host.TT.card : ℝ) + 2 := by
    have h1 : BS.card ≤ ({L.sc.b, L.sc.w'' D.R.n} : Finset ℝ).card +
        (Finset.univ.image (fun t : D.host.TT => (L.bT t : ℝ) + ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ))).card :=
      Finset.card_union_le _ _
    have h2 : ({L.sc.b, L.sc.w'' D.R.n} : Finset ℝ).card ≤ 2 := Finset.card_le_two
    have h3 : (Finset.univ.image (fun t : D.host.TT => (L.bT t : ℝ) + ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ))).card
        ≤ D.host.TT.card := by
      refine Finset.card_image_le.trans ?_
      simp
    have : BS.card ≤ D.host.TT.card + 2 := by omega
    exact_mod_cast this

  let lo : ℝ → ℝ := fun W => W + (-L.etaSz - 2 * (sgPlus L : ℝ) - 3)
  let hi : ℝ → ℝ := fun W => W + (L.Sc + L.etaSz + L.etaSz + 2 * (sgPlus L : ℝ) + 4)
  let win : ℝ → Finset ℤ := fun W => Finset.Icc ⌈lo W⌉ ⌊hi W⌋
  have hwin : ∀ W n, n ∈ win W ↔ n ∈ window L W := by
    intro W n
    simp only [win, lo, hi, Finset.mem_Icc, Int.ceil_le, Int.le_floor, window, Set.mem_setOf_eq]
  have hwincard : ∀ W, ((win W).card : ℝ) ≤ L.Sc + 3 * L.etaSz + 4 * (sgPlus L : ℝ) + 8 := by
    intro W
    refine (card_Icc_ceil_floor_le (lo W) (hi W)).trans (max_le (le_of_eq (by simp only [lo, hi]; ring)) ?_)
    linarith

  let exc : Finset ℕ := BS.biUnion fun W => (win W).biUnion fun n =>
    n.natAbs.primeFactors.filter fun l : ℕ => ls < (l : ℝ)
  have hmem : ∀ l, l ∈ exc ↔ ∃ W ∈ baseSizes L, ∃ n ∈ window L W,
      0 < n ∧ (n : ℝ) < 3 * L.sc.b ∧ l.Prime ∧ l ∣ n.natAbs ∧ ls < (l : ℝ) := by
    intro l
    simp only [exc, Finset.mem_biUnion, Finset.mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨W, hW, n, hn, ⟨hp, hd, -⟩, hl⟩
      rw [hBS] at hW; rw [hwin] at hn
      exact ⟨W, hW, n, hn, GlobalTheory.Survey.CongruenceBoundParameters.window_pos P W hW n hn,
        lt_of_le_of_lt hn.2 (hhi W hW), hp, hd, hl⟩
    · rintro ⟨W, hW, n, hn, hpos, -, hp, hd, hl⟩
      refine ⟨W, (hBS W).2 hW, n, (hwin W n).2 hn, ⟨hp, hd, by omega⟩, hl⟩
  refine ⟨exc, ?_, ?_, ?_⟩
  · ext l
    simp only [Finset.mem_coe, hmem, Exc, Set.mem_setOf_eq]
    constructor
    · rintro ⟨W, hW, n, hn, -, -, hp, hd, hl⟩
      exact ⟨hp, hl, W, hW, n, hn, Int.ofNat_dvd_left.2 hd⟩
    · rintro ⟨hp, hl, W, hW, n, hn, hd⟩
      have hpos := GlobalTheory.Survey.CongruenceBoundParameters.window_pos P W hW n hn
      exact ⟨W, hW, n, hn, hpos, lt_of_le_of_lt hn.2 (hhi W hW), hp, Int.ofNat_dvd_left.1 hd, hl⟩
  ·
    have hone : ∀ W ∈ BS, ∀ n ∈ win W,
        (n.natAbs.primeFactors.filter fun l : ℕ => ls < (l : ℝ)).card ≤ 1 := by
      intro W hW n hn
      rw [hBS] at hW; rw [hwin] at hn
      have hpos := GlobalTheory.Survey.CongruenceBoundParameters.window_pos P W hW n hn
      have hup : (n : ℝ) < 3 * L.sc.b := lt_of_le_of_lt hn.2 (hhi W hW)
      rw [Finset.card_le_one]
      intro p hp q hq
      simp only [Finset.mem_filter, Nat.mem_primeFactors] at hp hq
      by_contra hpq
      have hcop : Nat.Coprime p q := (Nat.coprime_primes hp.1.1 hq.1.1).2 hpq
      have hdvd : p * q ∣ n.natAbs := hcop.mul_dvd_of_dvd_of_dvd hp.1.2.1 hq.1.2.1
      have hle : p * q ≤ n.natAbs := Nat.le_of_dvd (by omega) hdvd
      have hle' : ((p * q : ℕ) : ℝ) ≤ (n : ℝ) := by
        have : ((n.natAbs : ℤ) : ℝ) = (n : ℝ) := by rw [Int.natAbs_of_nonneg hpos.le]
        rw [← this]; exact_mod_cast hle
      push_cast at hle'
      have : ls ^ 2 < (p : ℝ) * q := by nlinarith [hp.2, hq.2]
      linarith
    have hc1 : exc.card ≤ ∑ W ∈ BS, ∑ n ∈ win W,
        (n.natAbs.primeFactors.filter fun l : ℕ => ls < (l : ℝ)).card := by
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun W _ => Finset.card_biUnion_le)
    have hc2 : exc.card ≤ ∑ W ∈ BS, (win W).card := by
      refine hc1.trans (Finset.sum_le_sum fun W hW => ?_)
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum fun n hn => hone W hW n hn
    have hc3 : (exc.card : ℝ) ≤ ∑ W ∈ BS, (L.Sc + 3 * L.etaSz + 4 * (sgPlus L : ℝ) + 8) := by
      have : (exc.card : ℝ) ≤ ∑ W ∈ BS, ((win W).card : ℝ) := by exact_mod_cast hc2
      exact this.trans (Finset.sum_le_sum fun W _ => hwincard W)
    rw [Finset.sum_const, nsmul_eq_mul] at hc3
    have hK0 : 0 ≤ L.Sc + 3 * L.etaSz + 4 * (sgPlus L : ℝ) + 8 := by linarith
    have hK : L.Sc + 3 * L.etaSz + 4 * (sgPlus L : ℝ) + 8 ≤
        L.Sc + 3 * L.etaSz + D.R.t + 8 * L.sc.b / TwistedPlaces.lStar L + 9 := by
      have : 8 * L.sc.b / TwistedPlaces.lStar L = 4 * (2 * L.sc.b / ls) := by
        show 8 * L.sc.b / LevelStarExponents.lStar L = 4 * (2 * L.sc.b / ls); ring
      rw [this, hsg2]; linarith
    refine hc3.trans ?_
    exact mul_le_mul hBScard hK hK0 (by positivity)
  · intro l hl
    obtain ⟨W, hW, n, hn, hpos, hup, hp, hd, -⟩ := (hmem l).1 hl
    have hle : l ≤ n.natAbs := Nat.le_of_dvd (by omega) hd
    have : ((n.natAbs : ℤ) : ℝ) = (n : ℝ) := by rw [Int.natAbs_of_nonneg hpos.le]
    have hle' : (l : ℝ) ≤ (n : ℝ) := by rw [← this]; exact_mod_cast hle
    linarith

end GlobalTheory.NLink.ExcBound

namespace GlobalTheory.NLink

theorem excOK_family : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x,
    ∃ exc : Finset ℕ, (exc : Set ℕ) = GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.Exc (Fm.L x i) ∧ ExcOK (Fm.L x i) exc := by
  intro eps Fm
  exact ⟨Fm.x1, fun x _ hx i => ExcBound.excOK_at (Fm.L x i) (Fm.params x hx i) (Fm.sizes x hx i)⟩

end GlobalTheory.NLink

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAnalyticSubOneDivOneSubUnitMulExpStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_analytic_sub_one_div_one_sub_mul_exp : ∀ (L : ℝ), 0 < L → ∀ χ : ℂ, ‖χ‖ = 1 → ∃ h : ℂ → ℂ, (∀ x : ℝ, 0 < x → AnalyticAt ℂ h (x : ℂ)) ∧ (∀ x : ℝ, 1 < x → h (x : ℂ) = ((x : ℂ) - 1) / (1 - χ * Complex.exp (-((L : ℂ) * ((x : ℂ) - 1))))) ∧ (χ ≠ 1 → h 1 = 0) := by
  first | exact @GlobalTheory.exists_analytic_sub_one_div_one_sub_unit_mul_exp | exact GlobalTheory.exists_analytic_sub_one_div_one_sub_unit_mul_exp | (intros; apply GlobalTheory.exists_analytic_sub_one_div_one_sub_unit_mul_exp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInertiaCyclotomicGeneratesUnitsMod
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut
open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.ConsExists GlobalTheory.SpanRing
namespace GlobalTheory.CycGen

open Pointwise

theorem fix_of_unram {E Ω : Type} [Field E] [NumberField E] [IsGalois ℚ E] [Field Ω] [Algebra E Ω]
    [Algebra ℚ Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (hw : IsPlaceOver A w)
    (he : w.asIdeal.ramificationIdx ℤ = 1) (σ : G ℚ Ω) (hσ : σ ∈ Ine (F := ℚ) A) (x : E) :
    σ (algebraMap E Ω x) = algebraMap E Ω x := by
  have : IsScalarTower ℚ E Ω := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  set τ : E ≃ₐ[ℚ] E := AlgEquiv.restrictNormalHom E σ with hτdef
  have hcomm : ∀ y : E, algebraMap E Ω (τ y) = σ (algebraMap E Ω y) := fun y =>
    AlgEquiv.restrictNormal_commutes σ E y
  have hin : τ ∈ Ideal.inertia (E ≃ₐ[ℚ] E) w.asIdeal := by
    intro y
    show τ • y - y ∈ w.asIdeal
    rw [← hw]
    have hy : algebraMap E Ω (y : E) ∈ A :=
      ReciprocityTheory.Gal.mem_of_isIntegral_int A ((y.2).map (IsScalarTower.toAlgHom ℤ E Ω))
    have h := hσ.2 (algebraMap E Ω (y : E)) ((A.valuation_le_one_iff _).mpr hy)
    have e : ((τ • y - y : 𝓞 E) : E) = τ y - y := rfl
    rw [e, map_sub, hcomm]
    exact h
  have hcard : Nat.card (Ideal.inertia (E ≃ₐ[ℚ] E) w.asIdeal) = 1 := by
    have := w.isPrime
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[ℚ] E) (w.asIdeal.under ℤ) w.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx (w.asIdeal.under ℤ) w.asIdeal (E ≃ₐ[ℚ] E), he]
  have h1 : τ = 1 := by
    have := (Subgroup.card_eq_one.mp hcard)
    have h2 : τ ∈ (⊥ : Subgroup (E ≃ₐ[ℚ] E)) := this ▸ hin
    exact Subgroup.mem_bot.mp h2
  rw [← hcomm, h1]
  rfl

end GlobalTheory.CycGen

namespace GlobalTheory.CycGen

theorem exists_unit_gen (l : ℕ) [Fact l.Prime] :
    ∃ v : ℤ_[l]ˣ, orderOf (PadicInt.toZMod (v : ℤ_[l])) = l - 1 := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := (ZMod l)ˣ)
  set b : ℤ_[l] := ((a : ZMod l).val : ℤ_[l])
  have hb : PadicInt.toZMod b = (a : ZMod l) := by
    simp only [b, map_natCast, ZMod.natCast_zmod_val]
  have hu : IsUnit b := by
    by_contra hn
    have hm : b ∈ IsLocalRing.maximalIdeal ℤ_[l] := hn
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, hb] at hm
    exact a.ne_zero hm
  refine ⟨hu.unit, ?_⟩
  rw [IsUnit.unit_spec, hb, orderOf_units, orderOf_eq_card_of_forall_mem_zpowers ha,
    Nat.card_eq_fintype_card, ZMod.card_units]

theorem main : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc), (∀ v ∈ placesOver H.E (N.l i), v.asIdeal.ramificationIdx ℤ = 1) → ∃ w ∈ placesOver H.E (N.l i), ∃ g0 ∈ Ine (F := H.E) (N.plOm.1 w), orderOf (PadicInt.toZMod ((cycZ (F := H.E) (Ω := N.Om) (N.l i) g0 : ℤ_[N.l i]ˣ) : ℤ_[N.l i])) = N.l i - 1 := by
  intro R H what₂ N i hram
  obtain ⟨w, hw⟩ := GlobalTheory.TameFixedLift.exists_place H.E (N.l i)
  refine ⟨w, hw, ?_⟩
  have : CharZero N.Om := charZero_of_injective_algebraMap (algebraMap H.E N.Om).injective
  have : IsAlgClosed N.Om := IsAlgClosure.isAlgClosed H.E
  have : IsScalarTower ℚ H.E N.Om := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  have : IsAlgClosure ℚ N.Om := IsAlgClosure.ofAlgebraic ℚ H.E N.Om
  have hA : (N.plOm.1 w).valuation (N.l i : N.Om) < 1 := by
    have := (N.plOm.2 w (N.l i : 𝓞 H.E)).2 hw
    simpa using this
  have := H.hostE_isGalois
  obtain ⟨v, hv⟩ := exists_unit_gen (N.l i)
  obtain ⟨σ, hσ, hσv⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective N.Om (N.l i) (N.plOm.1 w) hA v
  obtain ⟨g, hg, hc⟩ := GlobalTheory.TameFixedLift.transfer (E := H.E) (N.plOm.1 w) (N.l i) σ hσ
    (fix_of_unram (N.plOm.1 w) w (N.plOm.2 w) (hram w hw) σ hσ)
  exact ⟨g, hg, by rw [hc, hσv, hv]⟩

end GlobalTheory.CycGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWhittakerBumpExtensionSchurComplementStatement
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_whittaker_bump_extension_schur_complement : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (β : GA E (m + 1) → ℂ),
    (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, β (u * g) = GlobalTheory.JSW.psiN u * β g) →
    (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, β h ≠ 0 →
      ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * h ∈ C) →
    (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
      ∀ u ∈ U, ∀ g, β (g * finGL E (m + 1) u) = β g) →
    (∀ g, ContDiffOn ℝ ∞ (chart β g) (invSet E (m + 1))) →
    ∃ b : GA E (m + r + 1 + 1) → ℂ,
      (∀ u ∈ GlobalTheory.JSW.NA E (m + r + 1 + 1), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧
      (∃ C : Set (GA E (m + r + 1 + 1)), IsCompact C ∧ ∀ p ∈ GlobalTheory.JSW.mirS E S (m + r + 1), b p ≠ 0 →
        ∃ u ∈ GlobalTheory.JSW.NA E (m + r + 1 + 1), u⁻¹ * p ∈ C) ∧
      (∃ U : Subgroup (GL (Fin (m + r + 1 + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + r + 1 + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, b (g * finGL E (m + r + 1 + 1) u) = b g) ∧
      (∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (m + r + 1 + 1))) ∧
      ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, b (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) = β h := by
  first | (exact @GlobalTheory.SchurExt.exists_ext) | (exact GlobalTheory.SchurExt.exists_ext) | (intros; apply GlobalTheory.SchurExt.exists_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HenselRootsOfLocalFamily
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut
open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.ConsExists GlobalTheory.SpanRing

namespace GlobalTheory

theorem localSubalgebra_eval_sub_mem_maximalIdeal {X O : Type} [CommRing O] [IsLocalRing O]
    (T : Subalgebra O (X → O)) [IsLocalRing T] {f : X → O} (hf : f ∈ T) (x y : X) :
    f x - f y ∈ IsLocalRing.maximalIdeal O := by
  classical
  haveI : (IsLocalRing.maximalIdeal O).IsMaximal := IsLocalRing.maximalIdeal.isMaximal O
  letI : Field (O ⧸ IsLocalRing.maximalIdeal O) := Ideal.Quotient.field _
  let ψ : X → (T →+* O ⧸ IsLocalRing.maximalIdeal O) := fun z =>
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)).comp
      ((Pi.evalRingHom (fun _ : X => O) z).comp (T.val : T →+* (X → O)))
  have hψ : ∀ z (g : T), ψ z g = Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) ((g : X → O) z) :=
    fun _ _ => rfl
  have hsurj : ∀ z, Function.Surjective (ψ z) := by
    intro z q
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨algebraMap O T a, by rw [hψ]; rfl⟩
  have hker : ∀ z, RingHom.ker (ψ z) = IsLocalRing.maximalIdeal T := fun z =>
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ (hsurj z))
  have hg : (⟨f, hf⟩ - algebraMap O T (f y) : T) ∈ RingHom.ker (ψ y) := by
    rw [RingHom.mem_ker, hψ, Ideal.Quotient.eq_zero_iff_mem]
    simp
  rw [hker y, ← hker x, RingHom.mem_ker, hψ, Ideal.Quotient.eq_zero_iff_mem] at hg
  simpa using hg

theorem hensel_roots_of_local_family : ∀ {X O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [HenselianRing O (IsLocalRing.maximalIdeal O)] {t : ℕ} (T : Subalgebra O (X → O)), IsLocalRing T → ∀ (P : X → Polynomial O), (∀ j, (fun x => (P x).coeff j) ∈ T) → (∀ x, (P x).Monic ∧ (P x).natDegree = t) → ∀ (π : X) (d : Fin t → O), (∀ a b, a ≠ b → IsUnit (d a - d b)) → P π = ∏ c, (Polynomial.X - Polynomial.C (d c)) → ∀ x, ∃ β : Fin t → O, Function.Injective β ∧ P x = ∏ c, (Polynomial.X - Polynomial.C (β c)) := by
  classical
  intro X O _ _ _ _ t T hT P hcoeff hdeg π d hd hπ x
  have hmap : (P x).map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)) =
      (P π).map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)) := by
    ext j
    simp only [Polynomial.coeff_map]
    rw [Ideal.Quotient.eq]
    exact localSubalgebra_eval_sub_mem_maximalIdeal T (hcoeff j) x π
  have hroot : ∀ c, ∃ b, (P x).IsRoot b ∧ b - d c ∈ IsLocalRing.maximalIdeal O := by
    intro c
    apply HenselianRing.is_henselian (P x) (hdeg x).1 (d c)
    · rw [← Ideal.Quotient.eq_zero_iff_mem, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map,
        hmap, hπ, Polynomial.eval_map, Polynomial.eval₂_at_apply, Polynomial.eval_prod,
        Finset.prod_eq_zero (Finset.mem_univ c) (by simp), map_zero]
    · rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, ← Polynomial.derivative_map, hmap,
        Polynomial.derivative_map, Polynomial.eval_map, Polynomial.eval₂_at_apply]
      apply IsUnit.map
      rw [hπ, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c)]
      simp only [Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_X,
        Polynomial.derivative_C, sub_zero, one_mul, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul, add_zero,
        Polynomial.eval_prod]
      have : ∀ a ∈ Finset.univ.erase c, IsUnit (d c - d a) := fun a ha =>
        hd c a (Finset.ne_of_mem_erase ha).symm
      exact IsUnit.prod_iff.2 this
  choose β hβ hβm using hroot
  have hinj : Function.Injective β := by
    intro a b hab
    by_contra hne
    have hmem : d b - d a ∈ IsLocalRing.maximalIdeal O := by
      have := Ideal.sub_mem _ (hβm a) (hβm b)
      rw [hab] at this
      convert this using 1; ring
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem (hd b a (Ne.symm hne))
  refine ⟨β, hinj, ?_⟩
  have hx0 : P x ≠ 0 := (hdeg x).1.ne_zero
  have hle : (Finset.univ.val.map β) ≤ (P x).roots := by
    rw [Multiset.le_iff_subset (Multiset.Nodup.map hinj Finset.univ.nodup)]
    intro r hr
    obtain ⟨c, -, rfl⟩ := Multiset.mem_map.mp hr
    exact (Polynomial.mem_roots hx0).mpr (hβ c)
  have hcard : (P x).roots.card ≤ (Finset.univ.val.map β).card := by
    rw [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin, ← (hdeg x).2]
    exact Polynomial.card_roots' _
  have heq : Finset.univ.val.map β = (P x).roots := Multiset.eq_of_le_of_card_le hle hcard
  have hrc : (P x).roots.card = (P x).natDegree := by
    rw [← heq, Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin, (hdeg x).2]
  rw [← Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hdeg x).1 hrc, ← heq,
    Multiset.map_map]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilLagrangianTermsAbsTsumLeHeightPolyStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelWeilLagrangianTerms_abs_tsum_le_heightPoly : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∃ (M : ℕ) (C : ℝ), ∀ g₁ g₂ : GA D W, ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ ≤ ENNReal.ofReal (C * ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ W g₁ : ℝ) * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ W g₂ : ℝ)) ^ M) := by
  first | exact @GlobalTheory.SWAbsGrowth.tsum_lagTerm_le | exact GlobalTheory.SWAbsGrowth.tsum_lagTerm_le | (intros; apply GlobalTheory.SWAbsGrowth.tsum_lagTerm_le <;> assumption)
end

