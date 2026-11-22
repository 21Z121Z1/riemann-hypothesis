import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0123
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPrimeAdditiveCharacterUnramified
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta GlobalTheory.Idele WithZero
open GlobalTheory.StdDual (codiff codiff_ne_zero one_le_codiff char_fin_add)
open scoped nonZeroDivisors

namespace GlobalTheory.SplitUnram

variable {F : Type} [Field F] [NumberField F]

theorem mem_adelicIdeal_codiff_iff {ψ : AddChar (AF F) ℂ} (hc : Continuous ψ)
    (h : ∀ x : F, ψ (pairA F 0 (algebraMap F (Af F) x)) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ))) (y : Af F) :
    y ∈ adelicIdeal (codiff F) ↔
      ∀ α : Af F, (∀ v, α v ∈ v.adicCompletionIntegers F) → ψ (pairA F 0 (α * y)) = 1 := by
  have h1 : ∀ x : F, ψ (pairA F 0 (algebraMap F (Af F) x)) = 1 ↔
      Algebra.trace ℚ F x ∈ (algebraMap ℤ ℚ).range := fun x => by
    rw [h, mul_comm, Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have := mul_right_cancel₀ Complex.two_pi_I_ne_zero hn
      rw [eq_intCast]
      exact_mod_cast this.symm
    · rintro ⟨n, hn⟩
      exact ⟨n, by rw [← hn, eq_intCast, Rat.cast_intCast]⟩
  have h2 : ∀ x : F, x ∈ codiff F ↔
      ∀ a : 𝓞 F, ψ (pairA F 0 (algebraMap F (Af F) ((a : F) * x))) = 1 := fun x => by
    rw [FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))]
    simp_rw [h1, Algebra.traceForm_apply]
    constructor
    · intro H a
      rw [mul_comm]
      exact H _ ((FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩)
    · intro H a ha
      obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
      rw [mul_comm]
      exact H a
  have key : ∀ x : F, x ∈ codiff F ↔ ∀ α : Af F, (∀ v, α v ∈ v.adicCompletionIntegers F) →
      ψ (pairA F 0 (α * algebraMap F (Af F) x)) = 1 := fun x => by
    rw [h2]
    refine ⟨fun H α hα => GlobalTheory.IntDense.addChar_eq_one_of_integral F ψ hc x H α hα,
      fun H a => ?_⟩
    rw [map_mul]
    refine H _ fun v => ?_
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, adele_algebraMap_apply, valued_algebraMap]
    exact v.valuation_le_one a
  have hint : ∀ α : Af F, (∀ v, α v ∈ v.adicCompletionIntegers F) → ψ (pairA F 0 α) = 1 :=
    fun α hα => by
      have := (key 1).1 (one_le_codiff (FractionalIdeal.one_mem_one _)) α hα
      rwa [map_one, mul_one] at this
  obtain ⟨x, hx⟩ := exists_sub_mem_adelicIdeal (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F)) y
  have hx1 := mem_adelicIdeal_one_iff.1 hx
  have hx2 : y - algebraMap F (Af F) x ∈ adelicIdeal (codiff F) := by
    refine (mem_adelicIdeal_iff codiff_ne_zero).2 fun v => (hx1 v).trans ?_
    have := FractionalIdeal.count_mono F v (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))
      (one_le_codiff (F := F))
    rw [FractionalIdeal.count_one] at this
    rw [← exp_zero, exp_le_exp]
    omega
  have e : y = algebraMap F (Af F) x + (y - algebraMap F (Af F) x) := by ring
  rw [e, (adelicIdeal (codiff F)).add_mem_iff_left hx2, algebraMap_mem_adelicIdeal codiff_ne_zero, key]
  refine forall_congr' fun α => forall_congr' fun hα => ?_
  rw [mul_add, char_fin_add, hint (α * (y - algebraMap F (Af F) x))
    fun v => mul_mem (hα v) (hx1 v), mul_one]

theorem not_dvd_different {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 F))
    (hv : (p : 𝓞 F) ∈ v.asIdeal) (h2 : (p : 𝓞 F) ∉ v.asIdeal ^ 2) :
    ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F) := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp'.irreducible
  have hmap : Ideal.map (algebraMap ℤ (𝓞 F)) (Ideal.span {(p : ℤ)}) = Ideal.span {((p : ℕ) : 𝓞 F)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 F)) (Ideal.span {(p : ℤ)}) ≤ v.asIdeal := by
    rw [hmap, Ideal.span_le]; simpa using hv
  have := v.isPrime
  have : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.comap_ne_top _ v.isPrime.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
  have hb : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
  rw [not_dvd_differentIdeal_iff]
  apply Ideal.ramificationIdx_eq_one_iff.1
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) v.asIdeal hb]
  by_contra hne
  rw [← ne_eq, Ideal.ramificationIdx'_ne_one_iff hle, hmap, Ideal.span_le] at hne
  exact h2 (by simpa using hne)

theorem count_codiff_eq_zero (v : HeightOneSpectrum (𝓞 F)) (h : ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F)) :
    FractionalIdeal.count F v (codiff F) = 0 := by
  have hD : ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = (codiff F)⁻¹ :=
    coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)
  have h0 : differentIdeal ℤ (𝓞 F) ≠ 0 := differentIdeal_ne_bot
  have h1 := FractionalIdeal.count_coe F v h0
  rw [hD, FractionalIdeal.count_inv,
    not_not.1 (mt (Associates.count_ne_zero_iff_dvd h0 v.irreducible).1 h)] at h1
  simpa using h1

theorem not_mem_sq_of_ext {E : Type} [Field E] [NumberField E] [Algebra F E] {p : ℕ}
    (h : ∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal → (p : 𝓞 E) ∉ w.asIdeal ^ 2)
    (v : HeightOneSpectrum (𝓞 F)) : (p : 𝓞 F) ∉ v.asIdeal ^ 2 := by
  intro hv
  have := v.isMaximal
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hb : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  have hle : v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) ≤ Q :=
    Ideal.map_le_iff_le_comap.2 hQv.over.le
  have h1 := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) hv
  rw [Ideal.map_pow, map_natCast] at h1
  have h2 : (p : 𝓞 E) ∈ Q ^ 2 := Ideal.pow_right_mono hle 2 h1
  exact h ⟨Q, hQ.isPrime, hb⟩ (Ideal.pow_le_self two_ne_zero h2) h2

theorem psiUnramAt_of_splitsCompletely : ∀ (D : D7) (p : ℕ) (ψ : AddChar (AF D.host.F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains.SplitsCompletely D p → IsStdChar D ψ (-1) →
    ∀ v : HeightOneSpectrum (𝓞 D.host.F), (p : 𝓞 D.host.F) ∈ v.asIdeal → GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains.PsiUnramAt ψ v := by
  intro D p ψ hp hψ v hv α hα
  have hc := count_codiff_eq_zero v
    (not_dvd_different hp.1 v hv (not_mem_sq_of_ext (fun w hw => (hp.2 w hw).2) v))
  have h := mem_adelicIdeal_codiff_iff hψ.1.1 (GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ) α
  have h' : (∀ β ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F, ψ (pairA D.host.F 0 (α * β)) = 1) ↔
      α ∈ adelicIdeal (codiff D.host.F) := by
    rw [h]
    exact forall_congr' fun β => by rw [mul_comm]; rfl
  rw [h', mem_adelicIdeal_iff codiff_ne_zero, HeightOneSpectrum.mem_adicCompletionIntegers]
  constructor
  · intro H
    have := H v
    rwa [hc, neg_zero, exp_zero] at this
  · intro H w
    by_cases hw : w = v
    · subst hw
      rw [hc, neg_zero, exp_zero]
      exact H
    · have h0 : α w = 0 := hα w hw
      rw [h0, map_zero]
      exact zero_le

end GlobalTheory.SplitUnram

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPrimePlacesSplit
section
open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Links
open GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains GlobalTheory.PRep GlobalTheory.LFun
open Formalism.UG (IsCommensurated Hecke)
open Formalism.MainNotions.SchurIrreducible (IsSplit)

namespace GlobalTheory.SplitPlace

theorem isSplit_of_norm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) {p : ℕ} (hp : p.Prime)
    (h : ∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal →
      Ideal.absNorm w.asIdeal = p ∧ (p : 𝓞 E) ∉ w.asIdeal ^ 2)
    (v : HeightOneSpectrum (𝓞 F)) (hv : (p : 𝓞 F) ∈ v.asIdeal) : IsSplit (E := E) v := by
  classical
  haveI hfin : Module.Finite (𝓞 F) (𝓞 E) := by
    first
    | infer_instance
    | exact Module.Finite.of_restrictScalars_finite ℤ (𝓞 F) (𝓞 E)
  haveI hint : Algebra.IsIntegral (𝓞 F) (𝓞 E) := by
    first
    | infer_instance
    | exact Algebra.IsIntegral.of_finite (𝓞 F) (𝓞 E)

  have hdeg : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
    rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E]
    exact h2

  have hsum := Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 E)
  rw [hdeg] at hsum

  have hover : ∀ Q : Ideal (𝓞 E), Q.LiesOver v.asIdeal → (p : 𝓞 E) ∈ Q := by
    intro Q hQo
    have hmem : (p : 𝓞 F) ∈ Q.under (𝓞 F) := by
      rw [← hQo.over]
      exact hv
    have hmem' : algebraMap (𝓞 F) (𝓞 E) (p : 𝓞 F) ∈ Q := hmem
    simpa using hmem'

  have hf : ∀ q : v.asIdeal.primesOver (𝓞 E), q.1.inertiaDeg (𝓞 F) = 1 := by
    rintro ⟨Q, hQp, hQo⟩
    haveI := hQp
    haveI := hQo
    have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
    have hN : Ideal.absNorm Q = p := (h ⟨Q, hQp, hQ0⟩ (hover Q hQo)).1
    have key : Ideal.absNorm v.asIdeal ^ Q.inertiaDeg (𝓞 F) = p := by
      rw [Ideal.absNorm_pow_inertiaDeg v.asIdeal Q]
      exact hN
    exact Nat.Prime.eq_one_of_pow (by rw [key]; exact hp)

  have he : ∀ q : v.asIdeal.primesOver (𝓞 E), q.1.ramificationIdx (𝓞 F) = 1 := by
    rintro ⟨Q, hQp, hQo⟩
    haveI := hQp
    haveI := hQo
    have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
    have hsq : (p : 𝓞 E) ∉ Q ^ 2 := (h ⟨Q, hQp, hQ0⟩ (hover Q hQo)).2
    have hle : Q.ramificationIdx (𝓞 F) ≤ 1 := by
      rw [← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal Q v.ne_bot]
      by_contra hlt
      push_neg at hlt
      have hmap : v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) ≤ Q ^ 2 :=
        Ideal.le_pow_of_le_ramificationIdx' hlt
      apply hsq
      have hin := hmap (Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) hv)
      simpa using hin
    have hpos : 0 < Q.ramificationIdx (𝓞 F) := Ideal.ramificationIdx_pos Q (𝓞 F)
    show Q.ramificationIdx (𝓞 F) = 1
    omega

  by_contra hns
  obtain ⟨Q0, hQ0p, hQ0o⟩ : ∃ Q0 : Ideal (𝓞 E), Q0.IsPrime ∧ Q0.LiesOver v.asIdeal := by
    first
    | obtain ⟨Q0, hQ0m, hQ0o⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
      exact ⟨Q0, hQ0m.isPrime, hQ0o⟩
    | obtain ⟨Q0, hQ0⟩ := Set.nonempty_of_ncard_ne_zero
        (IsDedekindDomain.primesOver_ncard_ne_zero v.asIdeal (𝓞 E))
      exact ⟨Q0, hQ0.1, hQ0.2⟩
  let q0 : v.asIdeal.primesOver (𝓞 E) := ⟨Q0, hQ0p, hQ0o⟩
  have honly : ∀ q : v.asIdeal.primesOver (𝓞 E), q = q0 := by
    rintro ⟨Q, hQp, hQo⟩
    by_contra hne
    apply hns
    haveI := hQo
    haveI := hQ0o
    refine ⟨⟨Q, hQp, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩,
      ⟨Q0, hQ0p, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q0⟩, ?_, hQo.over.symm, hQ0o.over.symm⟩
    intro hPQ
    exact hne (Subtype.ext (congrArg HeightOneSpectrum.asIdeal hPQ))
  rw [Finset.sum_eq_single q0 (fun b _ hb => absurd (honly b) hb)
    (fun h0 => absurd (Finset.mem_univ q0) h0), he q0, hf q0] at hsum
  omega

theorem isSplit_of_splitsCompletely : ∀ (D : D7) (p : ℕ), SplitsCompletely D p → ∀ v : HeightOneSpectrum (𝓞 D.host.F), (p : 𝓞 D.host.F) ∈ v.asIdeal → IsSplit (E := D.host.E) v := by
  intro D p hp v hv
  have h2 : Module.finrank D.host.F D.host.E = 2 := by
    first
    | haveI : IsCMField D.host.E := Formalism.HC.HostAx.isCMField_hostE D.host.toHostAx
      exact IsQuadraticExtension.finrank_eq_two _ _
    | have hE := Formalism.HC.HostAx.finrank_cmField D.host.toHostAx
      have hF := Formalism.HC.HostAx.finrank_hostF D.host.toHostAx
      have hm := Module.finrank_mul_finrank ℚ D.host.F D.host.E
      have hpos : 0 < Module.finrank ℚ D.host.F := Module.finrank_pos
      rw [hE, hF] at hm
      rw [hF] at hpos
      exact Nat.eq_of_mul_eq_mul_left hpos (by linarith)
  exact isSplit_of_norm h2 hp.1 hp.2 v hv

end GlobalTheory.SplitPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqValueEqOneAtInertPlaceOfRestrictsToQuadratic
section
noncomputable section

namespace GlobalTheory.LFun

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU
open Formalism.L2.Host (IsUnifAt atFin)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}

namespace InertValue

theorem single_ne' {K : Type} [Field K] [NumberField K] {P Q : HeightOneSpectrum (𝓞 K)} (h : Q ≠ P)
    (u : (P.adicCompletion K)ˣ) : (GlobalTheory.CMVal.single P u : FiniteAdeleRing (𝓞 K) K) Q = 1 := by
  classical
  exact Pi.mulSingle_eq_of_ne h _

theorem exists_isUnifAt (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v) :
    ∃ a : (Fv F v)ˣ, IsUnifAt w (Units.map (complMap h).toMonoidHom a) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hπ0 : π ≠ 0 := by
    rintro rfl
    simp at hπ
    exact WithZero.exp_ne_zero hπ.symm
  refine ⟨Units.mk0 (algebraMap F (Fv F v) π) ((map_ne_zero _).2 hπ0), ?_⟩
  have hw' : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = w.asIdeal := hw
  have : w.asIdeal.LiesOver v.asIdeal := ⟨by subst h; rfl⟩
  have he : v.asIdeal.ramificationIdx' w.asIdeal = 1 := by
    apply Ideal.ramificationIdx'_spec
    · rw [pow_one, hw']
    · exact InertChart.not_map_le_sq hw
  show Valued.v (complMap h (algebraMap F (Fv F v) π)) = WithZero.exp (-1)
  rw [complMap_algebraMap]
  have hvw : Valued.v (algebraMap E (w.adicCompletion E) (algebraMap F E π)) = w.valuation E (algebraMap F E π) := by
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := w) (algebraMap F E π)
  rw [hvw, ← HeightOneSpectrum.valuation_liesOver E v w, he, pow_one, hπ]

theorem locIdele_complMap (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v) (a : (Fv F v)ˣ) :
    locIdele F w (Units.map (complMap h).toMonoidHom a) =
      ideleMap F E (GlobalTheory.CMVal.finIdele F (GlobalTheory.CMVal.single v a)) := by
  subst h
  have key : (finAdEquiv F E).symm ((GlobalTheory.CMVal.single w (Units.map (complMap rfl).toMonoidHom a) :
      (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) =
      ((GlobalTheory.CMVal.single (w.under (𝓞 F)) a : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (1 : E) := by
    rw [RingEquiv.symm_apply_eq]
    refine FiniteAdeleRing.ext (h := fun u => ?_)
    rw [finAdEquiv_apply (rfl : u.under (𝓞 F) = _)]
    simp only [Algebra.TensorProduct.map_tmul, toCompl_tmul, map_one, mul_one]
    classical
    have same : ∀ (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) (z : (P.adicCompletion K)ˣ),
        ((GlobalTheory.CMVal.single P z : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) P = z :=
      fun K _ _ P z => Pi.mulSingle_eq_same (M := fun R : HeightOneSpectrum (𝓞 K) => R.adicCompletion K) P
        (z : P.adicCompletion K)
    by_cases hu : u = w
    · subst hu
      rw [same]
      exact congrArg (complMap (rfl : u.under (𝓞 F) = _)) (same F _ a).symm
    · have hne : u.under (𝓞 F) ≠ w.under (𝓞 F) := fun h' => hu ((InertChart.under_eq_iff hw u).1 h')
      rw [single_ne' hu]
      have e2 : ((GlobalTheory.CMVal.single (w.under (𝓞 F)) a : (FiniteAdeleRing (𝓞 F) F)ˣ) :
          FiniteAdeleRing (𝓞 F) F) (u.under (𝓞 F)) = 1 := single_ne' hne a
      exact ((congrArg (complMap (rfl : u.under (𝓞 F) = _)) e2).trans (map_one _)).symm
  apply Units.ext
  show 1 - extZero F E 1 + extZero F E ((finAdEquiv F E).symm ((GlobalTheory.CMVal.single w
      (Units.map (complMap rfl).toMonoidHom a) : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E)) =
    algebraMap (AF F) (AF F ⊗[F] E) ((MonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
      ((GlobalTheory.CMVal.single (w.under (𝓞 F)) a : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F))
  rw [key]
  generalize ((GlobalTheory.CMVal.single (w.under (𝓞 F)) a : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) = s
  have h2 : extZero F E 1 = (@id (AF F) (LinearMap.inr F (Ainf F) (Af F) 1)) ⊗ₜ[F] (1 : E) :=
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU_tmul _ _ 1 1
  have h3 : extZero F E (s ⊗ₜ[F] (1 : E)) = (@id (AF F) (LinearMap.inr F (Ainf F) (Af F) s)) ⊗ₜ[F] (1 : E) :=
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU_tmul _ _ s 1
  have h4 : algebraMap (AF F) (AF F ⊗[F] E) (MonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) s) =
      (@id (AF F) (MonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) s)) ⊗ₜ[F] (1 : E) := rfl
  have hX : (1 : AF F) - (@id (AF F) (LinearMap.inr F (Ainf F) (Af F) 1)) +
      (@id (AF F) (LinearMap.inr F (Ainf F) (Af F) s)) =
      (@id (AF F) (MonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) s)) := by
    refine Prod.ext ?_ ?_
    · show (1 : Ainf F) - 0 + 0 = 1
      simp
    · show (1 : Af F) - 1 + s = s
      simp
  rw [h2, h3, h4, ← hX, TensorProduct.add_tmul, TensorProduct.sub_tmul]
  rfl

theorem eta_sq (h2 : Module.finrank F E = 2) {η : (AF F)ˣ →* Circle} (hη : IsEta F E η) (a : (AF F)ˣ) :
    η a ^ 2 = 1 := by
  have hn := hη.2.2.1 (ideleMap F E a)
  have hnorm : Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (ideleMap F E a) = a ^ 2 := by
    apply Units.ext
    show Algebra.norm (AF F) (algebraMap (AF F) (AF F ⊗[F] E) (a : AF F)) = ((a ^ 2 : (AF F)ˣ) : AF F)
    rw [Units.val_pow_eq_pow_val,
      Algebra.norm_algebraMap_of_basis (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)), Fintype.card_fin, h2]
  rw [hnorm, map_pow] at hn
  exact hn

end InertValue

open InertValue in

theorem val_sq_eq_one_of_isInertAt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (μ : (TensorProduct F (AF F) E)ˣ →* Circle) (b : ℕ) (hμ : ResEta F E μ b)
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (hw : IsInertAt F E v w) (hu : UnrAt μ w) :
    val μ w ^ 2 = 1 := by
  obtain ⟨⟨η, hη⟩, hres⟩ := hμ
  have h2 : Module.finrank F E = 2 := hσ.2.2.1
  have hw' : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = w.asIdeal := hw
  have hv : w.under (𝓞 F) = v := by
    ext1
    symm
    refine v.isMaximal.eq_of_le (w.under (𝓞 F)).isPrime.ne_top ?_
    exact Ideal.map_le_iff_le_comap.1 hw'.le
  obtain ⟨a, ha⟩ := exists_isUnifAt hw hv
  rw [← UnrAt.locChar_eq_val hu ha]
  simp only [locChar, MonoidHom.comp_apply]
  rw [locIdele_complMap hw hv a, hres η hη, ← map_pow, ← pow_mul, mul_comm, pow_mul, eta_sq h2 hη, one_pow,
    map_one]

end GlobalTheory.LFun

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnrOffOne
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepLaw

variable {D : D7}

def ResAt (c : (AE D)ˣ →* Circle) (PP : Pl D.host.E) (a : (kP PP)ˣ →* ℂˣ) : Prop :=
  ∀ e : AE D, Formalism.L2.NTheta.IsIdemAt e PP → ∀ x : (AE D)ˣ, e * ((x : AE D) - 1) = (x : AE D) - 1 →
    ∀ (hx : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (u : (kP PP)ˣ),
      (u : kP PP) = resS D.host.F PP ⟨toEAf D (x : AE D), hx⟩ → ((c x : Circle) : ℂ) = ((a u : ℂˣ) : ℂ)

def UnrOff (c : (AE D)ˣ →* Circle) (P : Finset (Pl D.host.E)) : Prop :=
  ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
    (∀ PP ∈ P, PP.under (𝓞 D.host.F) ≠ v) → UnramAt ε c

theorem ResAt.mul {c c' : (AE D)ˣ →* Circle} {PP : Pl D.host.E} {a a' : (kP PP)ˣ →* ℂˣ} (h : ResAt c PP a)
    (h' : ResAt c' PP a') : ResAt (c * c') PP (a * a') := by
  intro e he x hex hx u hu
  have k := h e he x hex hx u hu
  have k' := h' e he x hex hx u hu
  simp only [MonoidHom.mul_apply, Circle.coe_mul, Units.val_mul, k, k']

theorem ResAt.inv {c : (AE D)ˣ →* Circle} {PP : Pl D.host.E} {a : (kP PP)ˣ →* ℂˣ} (h : ResAt c PP a) :
    ResAt c⁻¹ PP a⁻¹ := by
  intro e he x hex hx u hu
  have k := h e he x hex hx u hu
  simp only [MonoidHom.inv_apply, Circle.coe_inv, Units.val_inv_eq_inv_val, k]

theorem UnrOff.mul {c c' : (AE D)ˣ →* Circle} {P : Finset (Pl D.host.E)} (h : UnrOff c P) (h' : UnrOff c' P) :
    UnrOff (c * c') P := by
  intro v ε hε hv x h₁ h₂ h₃
  rw [MonoidHom.mul_apply, h v ε hε hv x h₁ h₂ h₃, h' v ε hε hv x h₁ h₂ h₃, one_mul]

theorem UnrOff.inv {c : (AE D)ˣ →* Circle} {P : Finset (Pl D.host.E)} (h : UnrOff c P) :
    UnrOff c⁻¹ P := by
  intro v ε hε hv x h₁ h₂ h₃
  rw [MonoidHom.inv_apply, h v ε hε hv x h₁ h₂ h₃, inv_one]

end GlobalTheory.StepLaw

end
end

