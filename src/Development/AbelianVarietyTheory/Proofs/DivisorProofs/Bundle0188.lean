import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0107
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0108
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MapSpanBaseChangeEquivSubmoduleOf

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SingleMemOfMem
section
open scoped NNReal

namespace GlobalTheory.Div.KerFil
open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

variable {C : Type} [Field C] {w : Valuation C ℝ≥0}

theorem smul_vec_apply {r : ℕ} (b : w.valuationSubring) (v : Fin r → C) (i : Fin r) :
    (b • v) i = (b : C) * v i := rfl

theorem smul_C (b : w.valuationSubring) (z : C) : b • z = (b : C) * z := rfl

theorem smul_pi_apply {S : Type} {r : ℕ} (b : w.valuationSubring) (x : S → Fin r → C) (s : S)
    (i : Fin r) : (b • x) s i = (b : C) * x s i := rfl

theorem exists_prod_apply {S : Type} [DecidableEq S] {r : ℕ} (a : S → w.valuationSubring)
    (Fil : Submodule w.valuationSubring (S → Fin r → C))
    (hst : ∀ x ∈ Fil, unif a x ∈ Fil) (x : S → Fin r → C) (hx : x ∈ Fil) (T : Finset S) :
    ∃ y ∈ Fil, ∀ s' i, y s' i = (∏ s ∈ T, ((a s' : C) - a s)) * x s' i := by
  induction T using Finset.induction_on with
  | empty => exact ⟨x, hx, fun _ _ => by simp⟩
  | insert s0 T hs0 ih =>
    obtain ⟨y, hy, hyv⟩ := ih
    refine ⟨unif a y - a s0 • y, sub_mem (hst y hy) (Fil.smul_mem _ hy), fun s' i => ?_⟩
    rw [Finset.prod_insert hs0]
    simp only [Pi.sub_apply, unif, Pi.smul_apply, smul_eq_mul]
    rw [smul_C, hyv]
    ring

theorem single_mem_of_mem {S : Type} [Fintype S] [DecidableEq S] {r : ℕ}
    (a : S → w.valuationSubring) (Fil : Submodule w.valuationSubring (S → Fin r → C))
    (hst : ∀ x ∈ Fil, unif a x ∈ Fil) (τ : S) (x : S → Fin r → C) (hx : x ∈ Fil) :
    (Pi.single τ (diffGen a τ • x τ) : S → Fin r → C) ∈ Fil := by
  obtain ⟨y, hy, hyv⟩ := exists_prod_apply a Fil hst x hx (Finset.univ.erase τ)
  convert hy using 1
  funext s' i
  rw [hyv]
  by_cases e : s' = τ
  · subst e
    simp only [Pi.single_eq_same, smul_vec_apply, diffGen]
    push_cast
    rfl
  · rw [Finset.prod_eq_zero (i := s') (Finset.mem_erase.2 ⟨e, Finset.mem_univ _⟩) (sub_self _)]
    simp [e]

theorem diffGen_ne_zero {S : Type} [Fintype S] [DecidableEq S] (a : S → w.valuationSubring)
    (ha : Function.Injective a) (τ : S) : diffGen a τ ≠ 0 := by
  rw [diffGen, Finset.prod_ne_zero_iff]
  intro s hs e
  exact (Finset.mem_erase.1 hs).1 (ha (sub_eq_zero.1 e)).symm

end GlobalTheory.Div.KerFil

namespace GlobalTheory.Div.KerFil
open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

variable {C : Type} [Field C] {w : Valuation C ℝ≥0}

def clearDen {S : Type} [DecidableEq S] {r : ℕ}
    (Fil : Submodule w.valuationSubring (S → Fin r → C)) (τ : S) : Submodule C (Fin r → C) where
  carrier := {v | ∃ b : w.valuationSubring, b ≠ 0 ∧ (Pi.single τ (b • v) : S → Fin r → C) ∈ Fil}
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  add_mem' := by
    rintro v v' ⟨b, hb, h⟩ ⟨b', hb', h'⟩
    refine ⟨b * b', mul_ne_zero hb hb', ?_⟩
    have : (Pi.single τ ((b * b') • (v + v')) : S → Fin r → C) =
        b' • (Pi.single τ (b • v) : S → Fin r → C) + b • (Pi.single τ (b' • v') : S → Fin r → C) := by
      funext s i
      by_cases e : s = τ
      · subst e; simp only [Pi.single_eq_same, Pi.add_apply, smul_pi_apply, smul_vec_apply]
        push_cast; ring
      · simp [e]
    rw [this]
    exact add_mem (Fil.smul_mem _ h) (Fil.smul_mem _ h')
  smul_mem' := by
    rintro c v ⟨b, hb, h⟩
    by_cases hc0 : c = 0
    · exact ⟨1, one_ne_zero, by simp [hc0]⟩
    rcases w.valuationSubring.mem_or_inv_mem c with hc | hc
    · refine ⟨b, hb, ?_⟩
      have : (Pi.single τ (b • c • v) : S → Fin r → C) =
          (⟨c, hc⟩ : w.valuationSubring) • (Pi.single τ (b • v) : S → Fin r → C) := by
        funext s i
        by_cases e : s = τ
        · subst e; simp only [Pi.single_eq_same, smul_pi_apply, smul_vec_apply, Pi.smul_apply,
            smul_eq_mul, smul_C]
          ring
        · simp [e]
      rw [this]
      exact Fil.smul_mem _ h
    · have hne : (⟨c⁻¹, hc⟩ : w.valuationSubring) ≠ 0 := by
        intro e
        exact hc0 (inv_eq_zero.1 (congrArg Subtype.val e))
      refine ⟨b * ⟨c⁻¹, hc⟩, mul_ne_zero hb hne, ?_⟩
      have : (b * ⟨c⁻¹, hc⟩ : w.valuationSubring) • c • v = b • v := by
        funext i
        simp only [smul_vec_apply, Pi.smul_apply, smul_eq_mul, smul_C]
        push_cast
        field_simp
      rw [this]
      exact h

theorem ker_eq (C : Type) [Field C] (w : Valuation C ℝ≥0) (S : Type) [Fintype S] [DecidableEq S]
    (a : S → w.valuationSubring) (r : ℕ) (Fil : Submodule w.valuationSubring (S → Fin r → C))
    (τ : S) (ha : Function.Injective a) (hF : IsFiltration a Fil) :
    eigenSub (W := fun _ => Fin r → C) (freeLattice a r) τ ⊓
        LinearMap.ker (quotMap (w := w) (filSpace Fil τ)) =
      eigenSub (W := fun _ => Fin r → C) Fil τ := by
  apply le_antisymm
  · rintro v ⟨hH, hK⟩
    have hH' : (Pi.single τ v : S → Fin r → C) ∈ freeLattice a r := by
      simpa [eigenSub] using hH
    have hK' : v ∈ filSpace Fil τ := by
      simpa [quotMap, Submodule.Quotient.mk_eq_zero] using hK
    have hle : filSpace Fil τ ≤ clearDen Fil τ := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨diffGen a τ, diffGen_ne_zero a ha τ, single_mem_of_mem a Fil hF.stable τ x hx⟩
    obtain ⟨b, hb, hbv⟩ := hle hK'
    show (Pi.single τ v : S → Fin r → C) ∈ Fil
    refine hF.saturated _ hH' b hb ?_
    convert hbv using 1
    funext s i
    by_cases e : s = τ
    · subst e; simp [smul_pi_apply, smul_vec_apply, smul_C]
    · simp [smul_pi_apply, e]
  · intro v hv
    have hv' : (Pi.single τ v : S → Fin r → C) ∈ Fil := by simpa [eigenSub] using hv
    refine ⟨?_, ?_⟩
    · show (Pi.single τ v : S → Fin r → C) ∈ freeLattice a r
      exact hF.le hv'
    · show quotMap (w := w) (filSpace Fil τ) v = 0
      simp only [quotMap, LinearMap.restrictScalars_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      refine Submodule.subset_span ⟨_, hv', ?_⟩
      simp

end GlobalTheory.Div.KerFil

theorem GlobalTheory.Div.kerFil : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (r : ℕ) (Fil : Submodule w.valuationSubring (S → Fin r → C)) (τ : S), Function.Injective a → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsFiltration a Fil → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (W := fun _ => Fin r → C) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a r) τ ⊓ LinearMap.ker (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.quotMap (w := w) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil τ)) = GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (W := fun _ => Fin r → C) Fil τ :=
  fun C _ w S _ _ a r Fil τ ha hF => GlobalTheory.Div.KerFil.ker_eq C w S a r Fil τ ha hF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewFamilyInnerReEqStrictLowerAddDiagImStatement
section
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skew_family_inner_re_eq_strictLower_add_diagIm : ∀ {ι : Type} [Fintype ι] {r : ℕ} (s : Fin r → ℝ), (∀ a, s a * s a = 1) → ∀ (Y Y' : ι × Fin r × Fin r → ℂ), (∀ τ a b, Y (τ, b, a) = -((s a * s b : ℝ) : ℂ) * conj (Y (τ, a, b))) → (∀ τ a b, Y' (τ, b, a) = -((s a * s b : ℝ) : ℂ) * conj (Y' (τ, a, b))) → ∑ p, (conj (Y p) * Y' p).re = 2 * ∑ q : ι × {p : Fin r × Fin r // p.2 < p.1}, (conj (Y (q.1, q.2.1.1, q.2.1.2)) * Y' (q.1, q.2.1.1, q.2.1.2)).re + ∑ τ, ∑ a, (Y (τ, a, a)).im * (Y' (τ, a, a)).im := by
  first | exact @GlobalTheory.skew_family_inner_re_split | exact GlobalTheory.skew_family_inner_re_split | (intros; apply GlobalTheory.skew_family_inner_re_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianPerturbIdempotentDetNeZeroStatement
section
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_skewHermitian_det_mul_add_ne_zero_of_idempotent : ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → ∀ ε : k, ε ≠ 0 → σ ε = -ε →
    ∀ (n : ℕ) (E D : Matrix (Fin n) (Fin n) k), E * E = E → (E.map σ)ᵀ = E → E * (D.map σ)ᵀ + D * E = 0 →
    (∀ a : Fin n → k, a ᵥ* E = 0 → a ᵥ* D = 0 → a = 0) →
      ∃ V : Matrix (Fin n) (Fin n) k, (V.map σ)ᵀ = -V ∧ (E * V + D).det ≠ 0 := by
  first | exact @GlobalTheory.skewHermitian_perturb_idempotent_det_ne_zero | exact GlobalTheory.skewHermitian_perturb_idempotent_det_ne_zero | (intros; apply GlobalTheory.skewHermitian_perturb_idempotent_det_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAlongCurveProductsStable
section
open MeasureTheory
open scoped ContDiff

namespace GlobalTheory
namespace CurveProductSmooth

variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G)

def JointlySmooth {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (Φ : E → K) : Prop :=
  ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (g : F → E), ContDiff ℝ ∞ g →
    ∀ l : List (P × (F → ℝ)), (∀ a ∈ l, a.1 ∈ A ∧ ContDiff ℝ ∞ a.2) →
      ContDiff ℝ ∞ fun x : F => ρ (l.map fun a => e a.1 (a.2 x)).prod (Φ (g x))

variable {ρ A e}

theorem JointlySmooth.translate {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → K}
    (h : JointlySmooth ρ A e Φ) (m : List (P × (E → ℝ)))
    (hm : ∀ a ∈ m, a.1 ∈ A ∧ ContDiff ℝ ∞ a.2) :
    JointlySmooth ρ A e fun t => ρ (m.map fun a => e a.1 (a.2 t)).prod (Φ t) := by
  intro F _ _ g hg l hl
  have h1 := h F g hg (l ++ m.map fun a => (a.1, a.2 ∘ g)) (by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hl a ha
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
      exact ⟨(hm b hb).1, (hm b hb).2.comp hg⟩)
  simp only [List.map_append, List.prod_append, map_mul, List.map_map] at h1
  exact h1

theorem JointlySmooth.extra {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → K}
    (h : JointlySmooth ρ A e Φ) {p : P} (hp : p ∈ A)
    (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (g : F → E) (hg : ContDiff ℝ ∞ g)
    (l : List (P × (F → ℝ))) (hl : ∀ a ∈ l, a.1 ∈ A ∧ ContDiff ℝ ∞ a.2) :
    ContDiff ℝ ∞ fun y : F × ℝ =>
      ρ (l.map fun a => e a.1 (a.2 y.1)).prod (ρ (e p y.2) (Φ (g y.1))) := by
  have h1 := h (F × ℝ) (g ∘ Prod.fst) (hg.comp contDiff_fst)
    ((l.map fun a => (a.1, a.2 ∘ Prod.fst)) ++ [(p, Prod.snd)]) (by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
      exact ⟨(hl b hb).1, (hl b hb).2.comp contDiff_fst⟩
    · obtain rfl := List.mem_singleton.1 ha
      exact ⟨hp, contDiff_snd⟩)
  simp only [List.map_append, List.prod_append, map_mul, List.map_map, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h1
  exact h1

theorem JointlySmooth.deriv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → K}
    (h : JointlySmooth ρ A e Φ) {p : P} (hp : p ∈ A) :
    JointlySmooth ρ A e fun t => deriv (fun r : ℝ => ρ (e p r) (Φ t)) 0 := by
  intro F _ _ g hg l hl
  have h1 := h.extra hp F g hg l hl
  have h0 := h.extra hp F g hg [] (by simp)
  simp only [List.map_nil, List.prod_nil, map_one, one_apply_eq_self] at h0
  have hd : ∀ x : F, DifferentiableAt ℝ (fun r : ℝ => ρ (e p r) (Φ (g x))) 0 := fun x =>
    ((h0.comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ ∞ fun r : ℝ => (x, r))).differentiable
      (by simp)) 0
  have h2 : ContDiff ℝ ∞ fun x : F => fderiv ℝ (fun r : ℝ =>
      ρ (l.map fun a => e a.1 (a.2 x)).prod (ρ (e p r) (Φ (g x)))) 0 :=
    ContDiff.fderiv (f := fun (x : F) (r : ℝ) =>
      ρ (l.map fun a => e a.1 (a.2 x)).prod (ρ (e p r) (Φ (g x)))) (g := fun _ => (0 : ℝ))
      (m := ∞) h1 contDiff_const (by simp)
  have h3 := h2.clm_apply (contDiff_const (c := (1 : ℝ)))
  convert h3 using 2 with x
  have h4 := ((ρ (l.map fun a => e a.1 (a.2 x)).prod).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) (hd x).hasDerivAt
  exact h4.deriv.symm

theorem JointlySmooth.foldr {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → K}
    (h : JointlySmooth ρ A e Φ) (l : List P) (hl : ∀ p ∈ l, p ∈ A) :
    JointlySmooth ρ A e fun t =>
      l.foldr (fun p w => _root_.deriv (fun r : ℝ => ρ (e p r) w) 0) (Φ t) := by
  induction l with
  | nil => exact h
  | cons p l ih =>
    exact (ih fun q hq => hl q (List.mem_cons_of_mem _ hq)).deriv (hl p List.mem_cons_self)

end CurveProductSmooth

open MeasureTheory in
open scoped ContDiff in
variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G) in
variable {ρ A e} in
private theorem contDiff_prod_ofFn_apply_of_jointlySmooth {k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : E → K} (h : _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e Φ) {g : (Fin k → ℝ) → E}
    (hg : ContDiff ℝ ∞ g) (ps : Fin k → P) (hps : ∀ i, ps i ∈ A) :
    ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod (Φ (g t)) := by
  have h1 := h (Fin k → ℝ) g hg (List.ofFn fun i => (ps i, fun t : Fin k → ℝ => t i)) (by
    intro a ha
    rw [List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    exact ⟨hps i, contDiff_apply ℝ ℝ i⟩)
  simpa [List.map_ofFn, Function.comp_def] using h1

open MeasureTheory in
open scoped ContDiff in
variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G) in
variable {ρ A e} in
private theorem deriv_continuousLinearMap_comp_eq (T : K →L[ℂ] K) (f : ℝ → K) (hf : DifferentiableAt ℝ f 0) :
    deriv (fun r => T (f r)) 0 = T (deriv f 0) :=
  ((T.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hf.hasDerivAt).deriv

open MeasureTheory in
open scoped ContDiff in
variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G) in
variable {ρ A e} in
private theorem jointlySmooth_deriv_action {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → K}
    (h : _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e Φ) {p : P} (hp : p ∈ A) :
    _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e fun t => deriv (fun r : ℝ => ρ (e p r) (Φ t)) 0 := by
  intro F _ _ g hg l hl
  have hf : ∀ y : E, ContDiff ℝ ∞ fun r : ℝ => ρ (e p r) (Φ y) := fun y => by
    simpa using h ℝ (fun _ => y) contDiff_const [(p, id)] (by simp [hp, contDiff_id])
  let H : F × ℝ → K := fun z =>
    ρ (((l.map fun a : P × (F → ℝ) => (a.1, a.2 ∘ Prod.fst)) ++ [(p, Prod.snd)]).map
      fun a : P × (F × ℝ → ℝ) => e a.1 (a.2 z)).prod
      (Φ (g z.1))
  have hH : ContDiff ℝ ∞ H := h (F × ℝ) (g ∘ Prod.fst) (hg.comp contDiff_fst) _ (by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
      exact ⟨(hl b hb).1, (hl b hb).2.comp contDiff_fst⟩
    · rw [List.mem_singleton] at ha
      subst ha
      exact ⟨hp, contDiff_snd⟩)
  have hHx : ∀ x r, H (x, r) = ρ (l.map fun a => e a.1 (a.2 x)).prod (ρ (e p r) (Φ (g x))) := by
    intro x r
    simp [H, List.map_append, List.map_map, Function.comp_def, map_mul]
  have hder : ∀ x, ρ (l.map fun a => e a.1 (a.2 x)).prod (deriv (fun r : ℝ => ρ (e p r) (Φ (g x))) 0)
      = fderiv ℝ H (x, 0) (0, 1) := by
    intro x
    rw [← deriv_continuousLinearMap_comp_eq _ _ ((hf (g x)).differentiable (by simp)).differentiableAt]
    have h2 : HasDerivAt (fun r : ℝ => H (x, r)) (fderiv ℝ H (x, 0) (0, 1)) 0 :=
      (hH.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
        ((hasDerivAt_const (0 : ℝ) x).prodMk (hasDerivAt_id (0 : ℝ)))
    rw [← h2.deriv]
    simp only [hHx]
  have hfin : ContDiff ℝ ∞ fun x : F => fderiv ℝ H (x, 0) (0, 1) :=
    ((contDiff_infty_iff_fderiv.1 hH).2.comp (contDiff_id.prodMk contDiff_const)).clm_apply
      contDiff_const
  convert hfin using 1
  funext x
  exact hder x

open MeasureTheory in
open scoped ContDiff in
variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G) in
variable {ρ A e} in
private theorem jointlySmooth_const' {v : K}
    (hv : ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) →
      ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod v)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e (fun _ : E => v) := by
  intro F _ _ g _ l hl
  have h1 := hv l.length (fun i => l[i].1) (fun i => (hl _ (List.getElem_mem _)).1)
  have h2 : ContDiff ℝ ∞ fun x : F => fun i : Fin l.length => l[i].2 x :=
    contDiff_pi.2 fun i => (hl _ (List.getElem_mem _)).2
  have h3 := h1.comp h2
  convert h3 using 1
  funext x
  simp only [Function.comp_apply]
  have hlist : (l.map fun a : P × (F → ℝ) => e a.1 (a.2 x)) =
      List.ofFn fun i : Fin l.length => e l[i].1 (l[i].2 x) :=
    List.ext_getElem (by simp) (by simp)
  rw [hlist]

open MeasureTheory in
open scoped ContDiff in
variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G) in
variable {ρ A e} in
private theorem jointlySmooth_prod_map_action {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : E → K} (h : _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e Φ) (m : List (P × (E → ℝ)))
    (hm : ∀ a ∈ m, a.1 ∈ A ∧ ContDiff ℝ ∞ a.2) :
    _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e fun y => ρ (m.map fun a => e a.1 (a.2 y)).prod (Φ y) := by
  intro F _ _ g hg l hl
  have h1 := h F g hg (l ++ m.map fun a => (a.1, a.2 ∘ g)) (by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hl a ha
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
      exact ⟨(hm b hb).1, (hm b hb).2.comp hg⟩)
  convert h1 using 1
  funext x
  simp [List.map_append, List.prod_append, map_mul, List.map_map, Function.comp_def]

open MeasureTheory in
open scoped ContDiff in
variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G) in
variable {ρ A e} in
private theorem jointlySmooth_foldr_deriv_action {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : E → K} (h : _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e Φ) (l : List P) (hl : ∀ p ∈ l, p ∈ A) :
    _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e fun t =>
      l.foldr (fun p w => deriv (fun r : ℝ => ρ (e p r) w) 0) (Φ t) := by
  induction l with
  | nil => exact h
  | cons q l ih =>
    exact jointlySmooth_deriv_action (ih fun p hp => hl p (List.mem_cons_of_mem _ hp)) (hl q (by simp))

open scoped ContDiff in

theorem _root_.GlobalTheory.smooth_along_curve_products_stable : ∀ (G : Type) [Group G] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (ρ : G →* (K →L[ℂ] K)) (P : Type) (A : Set P) (e : P → ℝ → G) (v : K), (∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod v) → (∀ p ∈ A, ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod (deriv (fun r : ℝ => ρ (e p r) v) 0)) ∧ (∀ (m : ℕ) (qs : Fin m → P) (r : Fin m → ℝ), (∀ i, qs i ∈ A) → ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod (ρ (List.ofFn fun i => e (qs i) (r i)).prod v)) ∧ ∀ l : List P, (∀ p ∈ l, p ∈ A) → ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => l.foldr (fun p w => deriv (fun r : ℝ => ρ (e p r) w) 0) (ρ (List.ofFn fun i => e (ps i) (t i)).prod v) := by
  intro G _ K _ _ _ ρ P A e v hv
  refine ⟨fun p hp k ps hps => ?_, fun m qs r hqs k ps hps => ?_, fun l hl k ps hps => ?_⟩
  · exact contDiff_prod_ofFn_apply_of_jointlySmooth
      (jointlySmooth_deriv_action (jointlySmooth_const' hv (E := ℝ)) hp) (g := fun _ => 0) contDiff_const ps hps
  · have h1 := jointlySmooth_prod_map_action (jointlySmooth_const' hv (E := ℝ))
      (List.ofFn fun i => (qs i, fun _ : ℝ => r i)) (by
        intro a ha
        rw [List.mem_ofFn] at ha
        obtain ⟨i, rfl⟩ := ha
        exact ⟨hqs i, contDiff_const⟩)
    simpa [List.map_ofFn, Function.comp_def] using
      contDiff_prod_ofFn_apply_of_jointlySmooth h1 (g := fun _ => 0) contDiff_const ps hps
  · have h1 := jointlySmooth_prod_map_action (jointlySmooth_const' hv (E := Fin k → ℝ))
      (List.ofFn fun i => (ps i, fun t : Fin k → ℝ => t i)) (by
        intro a ha
        rw [List.mem_ofFn] at ha
        obtain ⟨i, rfl⟩ := ha
        exact ⟨hps i, contDiff_apply ℝ ℝ i⟩)
    have h2 := jointlySmooth_foldr_deriv_action h1 l hl (Fin k → ℝ) id contDiff_id [] (by simp)
    simpa [List.map_ofFn, Function.comp_def] using h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothRangeOfIdempotentAlgHomStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_range_of_idempotent_algHom : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra.Smooth R A] (e : A →ₐ[R] A), (∀ x, e (e x) = e x) → Algebra.Smooth R e.range := by
  first | exact @GlobalTheory.smooth_range_of_idempotent | exact GlobalTheory.smooth_range_of_idempotent | (intros; apply GlobalTheory.smooth_range_of_idempotent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemOfMaximalIdealPowOfLocallySurjectiveStatement
section
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smul_mem_of_maximalIdeal_pow_of_locally_surjective : ∀ (R B : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [AddCommGroup B] [Module R B] [Module.Finite R B] (N : Submodule R B), (∀ (p : Ideal R), p.IsPrime → p ≠ maximalIdeal R → ∀ b : B, ∃ t ∉ p, t • b ∈ N) → ∃ k : ℕ, ∀ x ∈ maximalIdeal R ^ k, ∀ b : B, x • b ∈ N := by
  first | exact @GlobalTheory.smul_mem_of_maximalIdeal_pow_of_locally_eq | exact GlobalTheory.smul_mem_of_maximalIdeal_pow_of_locally_eq | (intros; apply GlobalTheory.smul_mem_of_maximalIdeal_pow_of_locally_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanCoeffProdLinearStatement
section
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_coeff_prod_linear_eq_prod_span : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (d m : ℕ)
    (c : Fin d → Fin m → V),
    Ideal.span (Set.range fun s => (∏ j, ∑ i, C (c j i) * X i : MvPolynomial (Fin m) V).coeff s) =
      ∏ j, Ideal.span (Set.range (c j)) := by
  first | exact @GlobalTheory.GaussContentLinearForms.span_coeff_prod_linear | exact GlobalTheory.GaussContentLinearForms.span_coeff_prod_linear | (intros; apply GlobalTheory.GaussContentLinearForms.span_coeff_prod_linear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanFiniteDimensionalOfBoundedFormsStatement
section
open Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_span_of_forall_linear_bounded : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (s : Set V),
    (∀ l : V →ₗ[ℂ] ℂ, ∃ C : ℝ, ∀ x ∈ s, ‖l x‖ ≤ C) → FiniteDimensional ℂ (Submodule.span ℂ s) := by
  first | exact @GlobalTheory.span_finiteDimensional_of_bounded_forms | exact GlobalTheory.span_finiteDimensional_of_bounded_forms | (intros; apply GlobalTheory.span_finiteDimensional_of_bounded_forms <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanImageInfOfLinearIndependent
section
open scoped TensorProduct

namespace GlobalTheory

theorem span_image_inf_of_linearIndependent {K V W ι : Type} [Field K] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module ℂ W] [Finite ι] (σ : K →+* ℂ) (j : V →ₛₗ[σ] W)
    (b : Module.Basis ι K V) (hb : LinearIndependent ℂ (fun k => j (b k)))
    (U U' : Submodule K V) :
    Submodule.span ℂ (j '' (U : Set V)) ⊓ Submodule.span ℂ (j '' (U' : Set V)) =
      Submodule.span ℂ (j '' ((U ⊓ U' : Submodule K V) : Set V)) := by
  classical
  letI : Algebra K ℂ := σ.toAlgebra
  haveI := Fintype.ofFinite ι
  let B := Algebra.TensorProduct.basis ℂ b
  let J : ℂ ⊗[K] V →ₗ[ℂ] W := B.constr ℂ (fun k => j (b k))
  have hJb : ∀ k, J (1 ⊗ₜ b k) = j (b k) := fun k => by
    have := B.constr_basis ℂ (fun k => j (b k)) k
    rwa [Algebra.TensorProduct.basis_apply] at this
  have hJ : ∀ v, J (1 ⊗ₜ v) = j v := fun v => by
    rw [← b.sum_repr v, TensorProduct.tmul_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [TensorProduct.tmul_smul, map_smulₛₗ j, ← hJb, ← map_smul,
      ← algebraMap_smul ℂ (b.repr v k)]
    rfl
  have hinj : Function.Injective J := by
    apply Module.Basis.injective_constr_of_linearIndependent
    exact hb
  have key : ∀ A : Submodule K V,
      Submodule.span ℂ (j '' (A : Set V)) = (A.baseChange ℂ).map J := fun A => by
    rw [Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe, Set.image_image]
    congr 1
    exact Set.image_congr fun v _ => (hJ v).symm
  rw [key, key, key, baseChange_inf, Submodule.map_inf _ hinj]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecLocalHomFactorsAffineOpenStatement
section
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_spec_factor_fromSpec_of_closedPoint_mem : ∀ (X : Scheme.{0}) (V : X.Opens) (hV : IsAffineOpen V) (A : Type) [CommRing A] [IsLocalRing A]
    (f : Spec (CommRingCat.of A) ⟶ X), f (IsLocalRing.closedPoint A) ∈ V →
    ∃ g : Γ(X, V) →+* A, f = Spec.map (CommRingCat.ofHom g) ≫ hV.fromSpec := by
  first | exact @GlobalTheory.spec_local_hom_factors_affineOpen | exact GlobalTheory.spec_local_hom_factors_affineOpen | (intros; apply GlobalTheory.spec_local_hom_factors_affineOpen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecWidePushoutIsoWidePullbackYonedaStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spec_widePushout_iso_widePullback_yoneda : ∀ (A B T : Type) [CommRing A] [CommRing B] [CommRing T] (a : A →+* B) (k : ℕ) (ι : Fin (k + 1) → (B →+* T)), (∀ j, (ι j).comp a = (ι 0).comp a) → (∀ (R : Type) [CommRing R] (g : Fin (k + 1) → (B →+* R)), (∀ j, (g j).comp a = (g 0).comp a) → ∃! φ : T →+* R, ∀ j, φ.comp (ι j) = g j) → ∃ e : yoneda.obj (Spec (CommRingCat.of T)) ≅ widePullback (yoneda.obj (Spec (CommRingCat.of A))) (fun _ : Fin (k + 1) => yoneda.obj (Spec (CommRingCat.of B))) (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom a))), ∀ j, e.hom ≫ WidePullback.π _ j = yoneda.map (Spec.map (CommRingCat.ofHom (ι j))) := by
  first | (exact @GlobalTheory.SpecWidePullback.yoneda_spec_isoWidePullback) | (exact GlobalTheory.SpecWidePullback.yoneda_spec_isoWidePullback) | (intros; apply GlobalTheory.SpecWidePullback.yoneda_spec_isoWidePullback  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializesLiftClosedFibreStalkBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_specializes_lift_pullback_snd_fromSpecStalk : ∀ {X Y : Scheme.{0}} (π : X ⟶ Y) (z : Y) (R : Type) [CommRing R] [IsLocalRing R] (i : Y.presheaf.stalk z →+* R) [IsLocalHom i], Function.Surjective (IsLocalRing.ResidueField.map i) → ∀ (v : ↥(pullback (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π)) (y : X), pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π v = IsLocalRing.closedPoint R → pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π v ⤳ y → π y = z → ∃ w : ↥(pullback (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π), v ⤳ w ∧ pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π w = y := by
  first | exact @GlobalTheory.specializes_lift_closedFibre_stalkBaseChange | exact GlobalTheory.specializes_lift_closedFibre_stalkBaseChange | (intros; apply GlobalTheory.specializes_lift_closedFibre_stalkBaseChange <;> assumption)
end

