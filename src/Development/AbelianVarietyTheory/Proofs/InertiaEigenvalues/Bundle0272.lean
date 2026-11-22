import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0253
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0245
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0256
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ShiftedJumpUpperBoundLeTwistBound
section
namespace GlobalTheory

open GlobalTheory.PositionData

theorem hS_le_bound : ∀ (t : ℕ) (up : Bool) (Fl Fc : Finset ℤ) (η S B W0 : ℝ), 1 ≤ t → (t : ℝ) ≤ η → 0 ≤ B → 0 ≤ S →
    (∀ z ∈ Fl, |(z : ℝ) - ((t : ℝ) - 1) / 2| ≤ η ∧ 2 * B + (t : ℝ) / 2 + 3 ≤ |(z : ℝ) - ((t : ℝ) - 1) / 2|) →
    (∀ z ∈ Fc, W0 ≤ (if up then (z : ℝ) - ((t : ℝ) - 1) / 2 else ((t : ℝ) - 1) / 2 - z) ∧
      (if up then (z : ℝ) - ((t : ℝ) - 1) / 2 else ((t : ℝ) - 1) / 2 - z) ≤ W0 + S + η + 1) →
    2 * B + (t : ℝ) / 2 + 3 ≤ W0 →
    ((GlobalTheory.PositionData.hS up t Fl Fc : ℕ) : ℝ) ≤ W0 + S + 2 * η + 3 := by
  intro t up Fl Fc η S B W0 ht htη hB hS0 hFl hFc hW
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hFl' : ∀ z ∈ Fl, ((t : ℝ) - 1) / 2 - η ≤ (z : ℝ) ∧ (z : ℝ) ≤ ((t : ℝ) - 1) / 2 + η := by
    intro z hz
    have h := (hFl z hz).1
    rw [abs_le] at h
    constructor <;> linarith [h.1, h.2]
  have castToNat : ∀ x : ℤ, ((x.toNat : ℕ) : ℝ) = max (x : ℝ) 0 := by
    intro x
    have h : ((x.toNat : ℕ) : ℤ) = max x 0 := Int.toNat_eq_max x
    rw [← Int.cast_natCast, h]
    push_cast
    rfl
  have hmn : ∀ (s : Finset ℤ) (H : s.Nonempty) (a : ℝ), (∀ y ∈ s, a ≤ (y : ℝ)) →
      a ≤ ((s.min' H : ℤ) : ℝ) := fun s H a h => h _ (Finset.min'_mem s H)
  have hmx : ∀ (s : Finset ℤ) (H : s.Nonempty) (a : ℝ), (∀ y ∈ s, (y : ℝ) ≤ a) →
      ((s.max' H : ℤ) : ℝ) ≤ a := fun s H a h => h _ (Finset.max'_mem s H)

  have hmxLo : ((mxLo t Fl : ℤ) : ℝ) ≤ ((t : ℝ) - 1) / 2 + η := by
    apply hmx
    intro y hy
    rw [Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · push_cast; linarith
    · exact (hFl' y hy).2
  cases up
  ·
    have hFc' : ∀ z ∈ Fc, ((t : ℝ) - 1) / 2 - W0 - S - η - 1 ≤ (z : ℝ) := by
      intro z hz
      have h := (hFc z hz).2
      simp only [Bool.false_eq_true, if_false] at h
      linarith
    have h1 : ((t : ℝ) - 1) / 2 - W0 - S - η - 1 ≤ ((mnAll Fl Fc : ℤ) : ℝ) := by
      apply hmn
      intro y hy
      rw [Finset.mem_insert, Finset.mem_union] at hy
      rcases hy with rfl | hy | hy
      · push_cast; linarith
      · linarith [(hFl' y hy).1]
      · exact hFc' y hy
    have h0 : mnAll Fl Fc ≤ 0 := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
    have hw : ((wS false Fl Fc : ℕ) : ℤ) = 1 - mnAll Fl Fc := by
      simp only [wS, Bool.false_eq_true, if_false]
      exact Int.toNat_of_nonneg (by omega)
    simp only [PositionData.hS, Bool.false_eq_true, if_false]
    rw [castToNat, hw]
    apply max_le
    · push_cast; linarith
    · linarith
  ·
    have hFc' : ∀ z ∈ Fc, (z : ℝ) ≤ ((t : ℝ) - 1) / 2 + W0 + S + η + 1 := by
      intro z hz
      have h := (hFc z hz).2
      simp only [if_true] at h
      linarith
    have h1 : ((mxAll t Fl Fc : ℤ) : ℝ) ≤ ((t : ℝ) - 1) / 2 + W0 + S + η + 1 := by
      apply hmx
      intro y hy
      rw [Finset.mem_insert, Finset.mem_union] at hy
      rcases hy with rfl | hy | hy
      · push_cast; linarith
      · linarith [(hFl' y hy).2]
      · exact hFc' y hy
    have h2 : ((t : ℝ) - 1) / 2 - η ≤ ((mnLo Fl : ℤ) : ℝ) := by
      apply hmn
      intro y hy
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · push_cast; linarith
      · exact (hFl' y hy).1
    have h0 : mnLo Fl ≤ 0 := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
    have hw : ((wS true Fl Fc : ℕ) : ℤ) = 1 - mnLo Fl := by
      simp only [wS, if_true]
      exact Int.toNat_of_nonneg (by omega)
    simp only [PositionData.hS, if_true]
    rw [castToNat, hw]
    apply max_le
    · push_cast; linarith
    · linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableLeSpanInvariantsOfSemilinearFamily
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

namespace GlobalTheory

private lemma span_range_eval_embeddings_eq_whole (F D : Type) [Field F] [Fintype D] (σ : D → (F →+* F))
    (hσ : Function.Injective σ) :
    Submodule.span F (Set.range (fun c : F => fun d : D => σ d c)) = ⊤ := by

  classical
  by_contra hne
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  have hli : LinearIndependent F (fun d : D => ((σ d : F →* F) : F → F)) := by
    refine (linearIndependent_monoidHom F F).comp (fun d => (σ d : F →* F)) ?_
    intro a b h
    apply hσ
    ext x
    exact congrArg (fun g : F →* F => g x) h
  rw [Fintype.linearIndependent_iff] at hli
  have hzero : ∑ d, f (Pi.single d 1) • ((σ d : F →* F) : F → F) = 0 := by
    funext c
    have hc : (fun d : D => σ d c) ∈ LinearMap.ker f := hle (Submodule.subset_span ⟨c, rfl⟩)
    rw [LinearMap.mem_ker] at hc
    have hdecomp : (fun d : D => σ d c) = ∑ d, σ d c • Pi.single d (1 : F) := by
      ext e
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hdecomp, map_sum] at hc
    simp only [map_smul, smul_eq_mul] at hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← hc]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp [mul_comm]
  have hall := hli _ hzero
  apply hf0
  ext d
  simpa using hall d

theorem stable_le_span_invariants_of_semilinear_family :
    ∀ (F M D : Type) [Field F] [AddCommGroup M] [Module F M] [Fintype D] (σ : D → (F →+* F)) (t : D → (M →+ M)) (V : Submodule F M), Function.Injective σ → (∀ d (c : F), ∀ y ∈ V, t d (c • y) = σ d c • t d y) → (∀ d, ∀ y ∈ V, t d y ∈ V) → (∀ d, ∀ y ∈ V, t d (∑ d', t d' y) = ∑ d', t d' y) → (∃ d, ∀ y ∈ V, t d y = y) → V ≤ Submodule.span F {y | y ∈ V ∧ ∀ d, t d y = y} := by
  classical
  rintro F M D _ _ _ _ σ t V hσ hsemi hV hinv ⟨d₀, hd₀⟩ y hy
  let W := Submodule.span F {y | y ∈ V ∧ ∀ d, t d y = y}
  let Φ : (D → F) →ₗ[F] M :=
    { toFun := fun w => ∑ d, w d • t d y
      map_add' := by
        intro a b
        simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        simp [Finset.smul_sum, smul_smul] }
  have hmem : ∀ c : F, (∑ d, σ d c • t d y) ∈ W := by
    intro c
    apply Submodule.subset_span
    have hcy : c • y ∈ V := V.smul_mem c hy
    have heq : ∑ d, σ d c • t d y = ∑ d, t d (c • y) :=
      Finset.sum_congr rfl fun d _ => (hsemi d c y hy).symm
    rw [heq]
    exact ⟨V.sum_mem fun d _ => hV d _ hcy, fun d => hinv d _ hcy⟩
  have hle : Submodule.span F (Set.range (fun c : F => fun d : D => σ d c)) ≤ W.comap Φ := by
    rw [Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    exact hmem c
  rw [span_range_eval_embeddings_eq_whole F D σ hσ] at hle
  have h1 : Φ (Pi.single d₀ 1) ∈ W := hle Submodule.mem_top
  have h2 : Φ (Pi.single d₀ 1) = y := by
    show ∑ d, (Pi.single d₀ (1 : F) : D → F) d • t d y = y
    rw [Finset.sum_eq_single d₀]
    · simp [hd₀ y hy]
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [h2] at h1
  exact h1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateH2PeriodDatum
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.TwistLift GlobalTheory.TateTop

namespace GlobalTheory.TateTop

theorem tateH2_of_duality_loc (hT : Formalism.GaloisCohomology.LocalTateDualityK) :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), LocalTateTopDegree (P.PD K) := by
  intro l _ P K LL _ _ _ O _ _ hO L1 hL1
  obtain ⟨hΦ1, hΦ2⟩ := continuous_fixingSubgroupEquiv K.1
  set Φ := K.1.fixingSubgroupEquiv with hΦ
  have hcyc : IsCyc P.χQ := P.χQ_cyc
  let χZ : Formalism.GaloisCohomology.GK l K.1 →* ℤ_[l]ˣ := (cyclotomicCharacter (PadicAlgCl l) l).comp
      (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK l K.1) (PadicAlgCl l))
  have hχZ : ∀ g, ((χZ g : ℤ_[l]) : ℚ_[l]) = (P.χQ (Φ.symm g : GQ l) : ℚ_[l]) := fun g => by
    rw [isCyc_unique hcyc (isCyc_cycChar l)]; rfl
  have hχc : Continuous fun g => (χZ g : ℤ_[l]) := by
    rw [continuous_iff_coe]
    simp only [hχZ]
    exact hcyc.continuous.comp (continuous_subtype_val.comp hΦ1)
  obtain ⟨c, hc⟩ := exists_gen_all hχc fun r => by
    have : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    exact exists_gen hχc
      (hT l K.1 K.2 (r + 1) (ZMod (l ^ (r + 1))) (ReciprocityTheory.Gal.charRep (redChar χZ (r + 1)))
        (Nat.succ_pos _) (contAction_charRep _ ((continuous_toZModPow _).comp hχc))).1
      fun M _ _ _ _ _ rho hrho => (hT l K.1 K.2 (r + 1) M rho (Nat.succ_pos _) hrho).2.2.2.2
  have hcpt : CompactSpace (GK K) := Φ.symm.surjective.compactSpace hΦ1
  obtain ⟨ι, hι⟩ := exists_ringHom hO
  let : Module ℤ_[l] (LL ⧸ L1.T) := Module.compHom _ ι
  have : SMulCommClass ℤ_[l] O (LL ⧸ L1.T) := ⟨fun a o x => smul_comm (ι a) o x⟩
  have hs : ∀ (a : ℤ_[l]) (x : LL), a • (Submodule.Quotient.mk x : LL ⧸ L1.T) =
      Submodule.Quotient.mk (algebraMap ℚ_[l] LL a * x) := fun a x => by
    rw [← hι, ← Algebra.smul_def]
    rfl
  refine @h2_equiv_of_torsion_character l _ (GK K) _ _ _ _ _ _ hcpt _ (fun r => (hc r).transport Φ hΦ2 hΦ1)
    (fun x => ?_) O _ _ _ _ fun g x => ?_
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨n, hn⟩ := exists_pow_smul_mem hO x
    refine ⟨n, ?_⟩
    rw [hs, Submodule.Quotient.mk_eq_zero, hL1]
    simpa using hn 1
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [hs]
    have h1 := hχZ (Φ g)
    rw [show Φ.symm (Φ g) = g from Φ.symm_apply_apply g, ← P.PD_χ K g] at h1
    change Submodule.Quotient.mk (algebraMap ℚ_[l] LL ((P.PD K).χ g : ℚ_[l]) * x) = _
    rw [← h1]
    rfl

end GlobalTheory.TateTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerEpsilonRootsMemFrobeniusPerfectionMod
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.DecomplPerf

section Generic

variable {U E R : Type} [CommRing U] [CommRing E] [CommRing R] (p : ℕ) (τ : U →* R)
  (φ : R →+* R) (io : E →+* R) (ψ : E → E)

theorem persist (hψ : ∀ e, io (ψ e) = φ (io e)) {x : R} {n : ℕ}
    (h : ∃ e r, φ^[n] x = io e + (p : R) * r) (k : ℕ) :
    ∃ e r, φ^[n + k] x = io e + (p : R) * r := by
  induction k with
  | zero => exact h
  | succ k ih =>
    obtain ⟨e, r, h⟩ := ih
    refine ⟨ψ e, φ r, ?_⟩
    rw [← add_assoc, Function.iterate_succ_apply', h, map_add, map_mul, map_natCast, hψ]

theorem closure_perf (hψ : ∀ e, io (ψ e) = φ (io e)) (h0 : τ 0 = 0)
    (hadd : ∀ x y, ∃ r, τ (x + y) = τ x + τ y + (p : R) * r)
    (hneg : ∀ x, ∃ r, τ (-x) = -τ x + (p : R) * r) (S : Set U)
    (hS : ∀ u ∈ S, ∃ n e r, φ^[n] (τ u) = io e + (p : R) * r) :
    ∀ u ∈ Subring.closure S, ∃ n e r, φ^[n] (τ u) = io e + (p : R) * r := by
  intro u hu
  induction hu using Subring.closure_induction with
  | mem x hx => exact hS x hx
  | zero => exact ⟨0, 0, 0, by simp [h0]⟩
  | one => exact ⟨0, 1, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    obtain ⟨e, r, h⟩ := persist p φ io ψ hψ hn m
    obtain ⟨e', r', h'⟩ := persist p φ io ψ hψ hm n
    obtain ⟨c, hc⟩ := hadd x y
    rw [add_comm m n] at h'
    rw [← RingHom.coe_pow] at h h'
    refine ⟨n + m, e + e', r + r' + (φ ^ (n + m)) c, ?_⟩
    rw [← RingHom.coe_pow, hc, map_add, map_add, map_mul, map_natCast, h, h', map_add]
    ring
  | neg x _ hx =>
    obtain ⟨n, e, r, h⟩ := hx
    obtain ⟨c, hc⟩ := hneg x
    rw [← RingHom.coe_pow] at h
    refine ⟨n, -e, -r + (φ ^ n) c, ?_⟩
    rw [← RingHom.coe_pow, hc, map_add, map_neg, map_mul, map_natCast, h, map_neg]
    ring
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    obtain ⟨e, r, h⟩ := persist p φ io ψ hψ hn m
    obtain ⟨e', r', h'⟩ := persist p φ io ψ hψ hm n
    rw [add_comm m n] at h'
    rw [← RingHom.coe_pow] at h h'
    refine ⟨n + m, e * e', io e * r' + r * (io e' + p * r'), ?_⟩
    rw [← RingHom.coe_pow, map_mul, map_mul, h, h', map_mul]
    ring

theorem iterate_τ (hφ : ∀ u, φ (τ u) = τ (u ^ p)) (n : ℕ) (u : U) :
    φ^[n] (τ u) = τ (u ^ p ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, hφ, ← pow_mul, pow_succ]

end Generic

variable {l : ℕ} [Fact l.Prime]

def teichW (l : ℕ) [Fact l.Prime] : OCb l →* WCb l :=
  (inclW l : Ainf l →* WCb l).comp (WittVector.teichmuller l)

theorem teichW_apply (u : OCb l) : teichW l u = inclW l (WittVector.teichmuller l u) := rfl

theorem teichW_coeff (u : OCb l) : (teichW l u).coeff 0 = algebraMap (OCb l) (Cb l) u := by
  rw [teichW_apply, coeff_inclW, WittVector.teichmuller_coeff_zero]

theorem teichW_add (x y : OCb l) :
    ∃ r, teichW l (x + y) = teichW l x + teichW l y + (l : WCb l) * r := by
  obtain ⟨r, hr⟩ := (coeff_zero_eq_zero_iff (teichW l (x + y) - teichW l x - teichW l y)).1 (by
    rw [sub_coeff_zero, sub_coeff_zero, teichW_coeff, teichW_coeff, teichW_coeff, map_add]
    ring)
  exact ⟨r, by linear_combination hr⟩

theorem teichW_zero : teichW l 0 = 0 := by
  rw [teichW_apply, WittVector.teichmuller_zero, map_zero]

theorem teichW_neg (x : OCb l) : ∃ r, teichW l (-x) = -teichW l x + (l : WCb l) * r := by
  obtain ⟨r, hr⟩ := teichW_add x (-x)
  rw [add_neg_cancel, teichW_zero] at hr
  exact ⟨-r, by linear_combination -hr⟩

theorem frobW_teichW (u : OCb l) : frobW l (teichW l u) = teichW l (u ^ l) := by
  change WittVector.map (frobenius (Cb l) l) (teichW l u) = _
  rw [teichW_apply, teichW_apply, inclW, WittVector.map_teichmuller, WittVector.map_teichmuller,
    WittVector.map_teichmuller, frobenius_def, ← map_pow]

theorem εroot_pow {P : LocPrime l} (AI : LocAinf l P) (k : ℕ) : AI.εroot k ^ l ^ k = AI.ε := by
  induction k with
  | zero => simp [LocAinf.εroot]
  | succ k ih =>
    rw [LocAinf.εroot, Function.iterate_succ_apply', pow_succ', pow_mul, frobeniusEquiv_symm_pow_p]
    exact ih

def rightW (LL : FinExt l) : WCb l →+* RW LL :=
  (Algebra.TensorProduct.includeRight : WCb l →ₐ[ℤ_[l]] RW LL).toRingHom

def teichR (LL : FinExt l) : OCb l →* RW LL := (rightW LL : WCb l →* RW LL).comp (teichW l)

theorem teichR_apply (LL : FinExt l) (u : OCb l) : teichR LL u = rightW LL (teichW l u) := rfl

theorem φRW_teichR (LL : FinExt l) (u : OCb l) :
    (φRW LL : RW LL →+* RW LL) (teichR LL u) = teichR LL (u ^ l) :=
  congrArg (rightW LL) (frobW_teichW u)

theorem teichR_εroot {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (s : ℕ) :
    teichR LL (AI.εroot s) = piR AI LL s + 1 := by
  have h : teichW l (AI.εroot s) = inclW l (piW AI s) + 1 := by
    rw [piW, map_sub, map_one, sub_add_cancel, teichW_apply]
  rw [teichR_apply, h, map_add, map_one]
  rfl

theorem isIntegral_of_pow_eq_one {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {x : B}
    {m : ℕ} (hm : 0 < m) (hx : x ^ m = 1) : IsIntegral A x :=
  IsIntegral.of_pow hm (hx ▸ isIntegral_one)

theorem add_one_pow_eq_ringHom_image_add_prime_mul_zero {E R : Type} [CommRing E] [CommRing R] (io : E →+* R) (p : ℕ) (a : E) (t : R)
    (ha : io a = t) (k : ℕ) : (t + 1) ^ k = io ((a + 1) ^ k) + (p : R) * 0 := by
  rw [map_pow, map_add, map_one, ha, mul_zero, add_zero]

theorem gen_aux₀ {E R : Type} [CommRing E] [CommRing R] (φ : R →+* R) (io : E →+* R) (p : ℕ)
    (a : E) (t : R) (ha : io a = t) : ∃ n e r, φ^[n] t = io e + (p : R) * r :=
  ⟨0, a, 0, by simp [ha]⟩

set_option maxHeartbeats 800000 in

theorem teich_mem_perfection : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W), ∀ u ∈ Subring.closure (Set.range AI.εroot ∪ {xb | ∃ c : Om l, c ∈ K0 K ∧ ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ c ^ m = 1 ∧ IsTiltOf c m xb}), ∃ (n : ℕ) (e : W.EE) (r : RW LL), (φRW LL)^[n] ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] inclW l (WittVector.teichmuller l u)) = E.tie.ioE e + (l : RW LL) * r := by
  intro l _ P AI K s LL h W E
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.Decompl.ioE_compat l P AI K s LL h W E
  refine closure_perf l (teichR LL) (φRW LL : RW LL →+* RW LL) (E.tie.ioE : W.EE →+* RW LL)
    W.φE h1 ?_ ?_ ?_ _ ?_
  · rw [teichR_apply, teichW_zero]; exact (rightW LL).map_zero
  · intro x y
    obtain ⟨r, hr⟩ := teichW_add x y
    refine ⟨rightW LL r, ?_⟩
    rw [teichR_apply, teichR_apply, teichR_apply, hr, (rightW LL).map_add, (rightW LL).map_add,
      (rightW LL).map_mul, map_natCast (rightW LL)]
  · intro x
    obtain ⟨r, hr⟩ := teichW_neg x
    refine ⟨rightW LL r, ?_⟩
    rw [teichR_apply, teichR_apply, hr, (rightW LL).map_add, (rightW LL).map_neg,
      (rightW LL).map_mul, map_natCast (rightW LL)]
  · rintro u (⟨k, rfl⟩ | ⟨c, hc, m, hm, hlm, hcm, hxb⟩)
    · refine ⟨k, (algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) W.EE letπ + 1) ^ l ^ s,
        0, ?_⟩
      have e1 := iterate_τ l (teichR LL) (φRW LL : RW LL →+* RW LL) (φRW_teichR LL) k (AI.εroot k)
      have e2 : teichR LL (AI.εroot k ^ l ^ k) = teichR LL (AI.εroot s) ^ l ^ s := by
        rw [εroot_pow, ← εroot_pow AI s]
        exact (teichR LL).map_pow _ _
      rw [teichR_εroot] at e2
      exact (e1.trans e2).trans (add_one_pow_eq_ringHom_image_add_prime_mul_zero (E.tie.ioE : W.EE →+* RW LL) l _ _ h3 _)
    · have hc' : (⟨c, hc⟩ : ↥(K0 K)) ^ m = 1 := Subtype.ext hcm
      have hint : ∀ i, IsIntegral ℤ_[l] (W.emb i ⟨c, hc⟩) := fun i =>
        isIntegral_of_pow_eq_one hm (by rw [← map_pow, hc', map_one])
      have e1 := E.inertia_action_on_roots ⟨c, hc⟩ m hm hlm hcm u hxb (fun i => ⟨W.emb i ⟨c, hc⟩, hint i⟩)
        (fun i => rfl)
      have e2 := (E.tie.ioE_ext _).trans (congrArg (inclR LL) e1)
      exact gen_aux₀ (φRW LL : RW LL →+* RW LL) (E.tie.ioE : W.EE →+* RW LL) l _ _ e2

end GlobalTheory.DecomplPerf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerEpsilonSubExpMemHodgeFiltrationStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.teichmullerEpsilon_sub_exp_mem_hodgeFiltration : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ M : ℕ, io AI (WittVector.teichmuller l AI.ε) - ∑ j ∈ Finset.range M, qB P ((j.factorial : ℚ_[l])⁻¹) * tD P ^ j ∈ FilB P (M : ℤ) := by
  first | exact @GlobalTheory.ExpImage.TaylorEps.eps_sub_exp | exact GlobalTheory.ExpImage.TaylorEps.eps_sub_exp | (intros; apply GlobalTheory.ExpImage.TaylorEps.eps_sub_exp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltSeparatedCompleteEpsilonRootSubOneStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tilt_separated_complete_epsilonRoot_sub_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (s : ℕ), (∀ x : OCb l, (∀ m : ℕ, (AI.εroot s - 1) ^ m ∣ x) → x = 0) ∧ ∀ a : ℕ → OCb l, ∃ x : OCb l, ∀ m : ℕ, (AI.εroot s - 1) ^ m ∣ x - ∑ i ∈ Finset.range m, (AI.εroot s - 1) ^ i * a i := by
  first | exact @GlobalTheory.TiltComplete.tilt_separated_complete | exact GlobalTheory.TiltComplete.tilt_separated_complete | (intros; apply GlobalTheory.TiltComplete.tilt_separated_complete <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistInvOfCharLawsMultOne
section
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.TypeLeaf

open Polynomial NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.TypeLeaf.lpChar_eq_triv_of_mul_eq_one (D : _root_.Formalism.BasicNotions.D7) (w : _root_.Formalism.BasicNotions.PlE D.host)
    (χ χ' : D.naut.LP w) (c c' : ℂ)
    (hu : D.naut.unr χ) (hu' : D.naut.unr χ') (hd' : D.naut.lpDim χ' = 1)
    (hc : D.naut.frobEig χ = {c}) (hc' : D.naut.frobEig χ' = {c'}) (h : c * c' = 1) :
    D.naut.lpChar χ χ' = D.naut.lpUnr w {1} := by
  have hu2 := D.naut.unr_char χ χ' hd' hu hu'
  rw [D.naut.unr_eq_lpUnr _ hu2, D.naut.frobEig_char χ χ' c' hu hu' hd' hc', hc]
  simp [h]

open Polynomial NumberField IsDedekindDomain in
private lemma exists_frobEig_etaT_inv_etaTinv (D : _root_.Formalism.BasicNotions.D7) (w : _root_.Formalism.BasicNotions.PlE D.host) :
    ∃ c : ℂ, c ≠ 0 ∧ D.naut.frobEig (D.naut.locG D.naut.etaT w) = {c} ∧
      D.naut.frobEig (D.naut.locG D.naut.etaTinv w) = {c⁻¹} := by
  have hu := D.naut.etaT_unr w
  have hcard : (D.naut.frobEig (D.naut.locG D.naut.etaT w)).card = 1 := by
    rw [D.naut.frobEig_card _ hu, D.naut.locG_dim]
  obtain ⟨c, hc⟩ := Multiset.card_eq_one.1 hcard
  have hne := D.naut.frobEig_ne_zero _ hu
  refine ⟨c, fun h0 => hne (by rw [hc, h0]; exact Multiset.mem_singleton_self 0), hc, ?_⟩
  rw [(D.naut.etaTinv_def w).2, hc]
  simp

open Polynomial NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.TypeLeaf.twistInv_of_charLaws_multOne :
    ∀ D : _root_.Formalism.BasicNotions.D7, _root_.GlobalTheory.TypeLeaf.CharLaws D → _root_.GlobalTheory.TypeLeaf.MultOne D →
      _root_.GlobalTheory.TypeLeaf.TwistInv D := by
  intro D hlaw hmult
  have hdim : ∀ w : _root_.Formalism.BasicNotions.PlE D.host, D.naut.lpDim (D.naut.locG D.naut.etaT w) = 1 :=
    fun w => D.naut.locG_dim _ w
  have hdim' : ∀ w : _root_.Formalism.BasicNotions.PlE D.host, D.naut.lpDim (D.naut.locG D.naut.etaTinv w) = 1 :=
    fun w => D.naut.locG_dim _ w
  constructor
  · intro a π ha
    refine hmult a _ _ ha fun w => ?_
    obtain ⟨c, hc0, hc, hc'⟩ := exists_frobEig_etaT_inv_etaTinv D w
    rw [D.naut.locG_tw, D.naut.locG_tw, (hlaw w _ _ _ (hdim w) (hdim' w)).1,
      _root_.GlobalTheory.TypeLeaf.lpChar_eq_triv_of_mul_eq_one D w _ _ c c⁻¹ (D.naut.etaT_unr w)
        (D.naut.etaTinv_def w).1 (hdim' w) hc hc' (mul_inv_cancel₀ hc0),
      (hlaw w _ _ _ (hdim w) (hdim w)).2]
  · intro a π ha
    refine hmult a _ _ ha fun w => ?_
    obtain ⟨c, hc0, hc, hc'⟩ := exists_frobEig_etaT_inv_etaTinv D w
    rw [D.naut.locG_tw, D.naut.locG_tw, (hlaw w _ _ _ (hdim' w) (hdim w)).1,
      _root_.GlobalTheory.TypeLeaf.lpChar_eq_triv_of_mul_eq_one D w _ _ c⁻¹ c (D.naut.etaTinv_def w).1
        (D.naut.etaT_unr w) (hdim w) hc' hc (inv_mul_cancel₀ hc0),
      (hlaw w _ _ _ (hdim w) (hdim w)).2]

end GlobalTheory.TypeLeaf
end

