import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LinMulti
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KFiniteSmoothVectors.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BesselDerivatives.ExpSup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ToGlob0
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0106
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SecondLabelsNonempty

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardLeOfSpan
section
open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S.Lat
open scoped Classical

namespace GlobalTheory.GenericOrder

theorem card_le_of_span {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] (g : R) {n : ℕ}
    [Finite (R ⧸ Ideal.span {g})] (q : Fin n → Q) (hq : ∀ b, g • q b = 0)
    (hs : Submodule.span R (Set.range q) = ⊤) :
    Nat.card Q ≤ Nat.card (R ⧸ Ideal.span {g}) ^ n := by
  have hk : ∀ b, Ideal.span {g} ≤ LinearMap.ker (LinearMap.toSpanSingleton R Q (q b)) := by
    intro b
    rw [Ideal.span_le, Set.singleton_subset_iff]
    simpa using hq b
  let φ : (Fin n → R ⧸ Ideal.span {g}) → Q := fun a =>
    ∑ b, Submodule.liftQ (Ideal.span {g}) (LinearMap.toSpanSingleton R Q (q b)) (hk b) (a b)
  have hφ : Function.Surjective φ := by
    intro x
    have hx : x ∈ Submodule.span R (Set.range q) := hs ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hx
    refine ⟨fun b => Submodule.Quotient.mk (c b), ?_⟩
    simp only [φ, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply]
    exact hc
  have := Nat.card_le_card_of_surjective φ hφ
  simpa [Nat.card_pi] using this

theorem mem_locP' {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime]
    (L : Submodule R W) (x : W) : x ∈ Formalism.HermitianLatticesTheory.localization₂ p L ↔ ∃ s, s ∉ p ∧ s • x ∈ L := Iff.rfl

theorem card_quot_le {R W : Type} [CommRing R] [IsDedekindDomain R] [AddCommGroup W] [Module R W]
    (hR : ¬ IsField R) (g : R) [Finite (R ⧸ Ideal.span {g})] {n : ℕ}
    (B U M : Submodule R W) (w : Fin n → W) (hw : ∀ b, g • w b ∈ U) (hwM : ∀ b, w b ∈ M)
    (hM : M ≤ U ⊔ Submodule.span R (Set.range w))
    (h : ∀ P : HeightOneSpectrum R,
      (g ∈ P.asIdeal → (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal B = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M)) ∧
      (g ∉ P.asIdeal → (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal B = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal U))) :
    Nat.card (B ⧸ U.comap B.subtype) ≤ Nat.card (R ⧸ Ideal.span {g}) ^ n := by
  have key : ∀ J : Ideal R, (∀ P : HeightOneSpectrum R, ∃ s ∈ J, s ∉ P.asIdeal) → (1 : R) ∈ J := by
    intro J hJ
    by_contra h1
    have hne : J ≠ ⊤ := fun e => h1 (e ▸ Submodule.mem_top)
    obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hne
    obtain ⟨s, hs, hs'⟩ := hJ ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm hR⟩
    exact hs' (hJm hs)
  let I : Ideal R := ⨅ b, B.comap (LinearMap.toSpanSingleton R W (w b))
  have hI : ∀ s, s ∈ I ↔ ∀ b, s • w b ∈ B := by
    intro s; simp [I]
  have h1 : (1 : R) ∈ I ⊔ Ideal.span {g} := by
    apply key
    intro P
    haveI := P.isPrime
    by_cases hg : g ∈ P.asIdeal
    · have hb : ∀ b, ∃ s, s ∉ P.asIdeal ∧ s • w b ∈ B := by
        intro b
        rw [← mem_locP', (h P).1 hg, mem_locP']
        exact ⟨1, (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top, by simpa using hwM b⟩
      choose s hs hsB using hb
      refine ⟨∏ b, s b, Submodule.mem_sup_left ((hI _).2 fun b => ?_), ?_⟩
      · rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ b), mul_smul]
        exact B.smul_mem _ (hsB b)
      · intro hm
        obtain ⟨b, -, hb⟩ := (Ideal.IsPrime.prod_mem_iff).1 hm
        exact hs b hb
    · exact ⟨g, Submodule.mem_sup_right (Ideal.mem_span_singleton_self g), hg⟩
  obtain ⟨c, hc, d, hd, hcd⟩ := Submodule.mem_sup.1 h1
  have hcB := (hI c).1 hc
  let q : Fin n → B ⧸ U.comap B.subtype := fun b => Submodule.Quotient.mk ⟨c • w b, hcB b⟩
  apply card_le_of_span g q
  · intro b
    simp only [q]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    show g • c • w b ∈ U
    rw [smul_comm]
    exact U.smul_mem _ (hw b)
  · let N : Submodule R W := U ⊔ Submodule.span R (Set.range fun b => c • w b)
    have hcM : ∀ y ∈ M, c • y ∈ N := by
      intro y hy
      obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 (hM hy)
      obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hv
      rw [smul_add, Finset.smul_sum]
      refine N.add_mem (Submodule.mem_sup_left (U.smul_mem _ hu))
        (N.sum_mem fun b _ => Submodule.mem_sup_right ?_)
      rw [smul_comm]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
    have hBN : ∀ x ∈ B, x ∈ N := by
      intro x hx
      have : (1 : R) ∈ N.comap (LinearMap.toSpanSingleton R W x) := by
        apply key
        intro P
        haveI := P.isPrime
        have hxl : x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal B :=
          (mem_locP' _ _ _).2 ⟨1, (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top, by simpa using hx⟩
        by_cases hg : g ∈ P.asIdeal
        · rw [(h P).1 hg, mem_locP'] at hxl
          obtain ⟨s, hs, hsx⟩ := hxl
          have hcP : c ∉ P.asIdeal := by
            intro hcP
            have hdP : d ∈ P.asIdeal := by
              refine (Ideal.span_le.2 ?_) hd
              simpa using hg
            exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top (hcd ▸ P.asIdeal.add_mem hcP hdP)
          refine ⟨c * s, ?_, fun hm => (P.isPrime.mem_or_mem hm).elim hcP hs⟩
          show (c * s) • x ∈ N
          rw [mul_smul]
          exact hcM _ hsx
        · rw [(h P).2 hg, mem_locP'] at hxl
          obtain ⟨s, hs, hsx⟩ := hxl
          exact ⟨s, (Submodule.mem_sup_left hsx : s • x ∈ N), hs⟩
      simpa using this
    rw [eq_top_iff]
    rintro y -
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (hBN x hx)
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hv
    refine (Submodule.mem_span_range_iff_exists_fun R).2 ⟨a, ?_⟩
    have e : ∑ b, a b • q b = Submodule.Quotient.mk (∑ b, a b • (⟨c • w b, hcB b⟩ : B)) := by
      simp only [q]
      rw [← Submodule.mkQ_apply, map_sum]
      simp only [map_smul, Submodule.mkQ_apply]
    rw [e, eq_comm, Submodule.Quotient.eq, Submodule.mem_comap]
    have : B.subtype (⟨x, hx⟩ - ∑ b, a b • (⟨c • w b, hcB b⟩ : B)) = u := by
      simp [← huv]
    rw [this]; exact hu

theorem frame_mem {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
    (Λ : Submodule (𝓞 E) S.V) {T : E} (F : LFlag S r T) (hL : IsLift Λ F) (hF : ∀ b, frame F b ∈ Λ)
    (b : Fin (r + 1)) : frame F b ∈ XLam Λ F ⊔ Submodule.span (𝓞 E) {F.zt} := by
  have hb := hF b
  induction b using Fin.lastCases with
  | last =>
    refine Submodule.mem_sup_right (Submodule.subset_span ?_)
    simp [frame, Formalism.MainNotions.S.FlagG.fvec, hL.2]
  | cast i =>
    refine Submodule.mem_sup_left ⟨hb, ?_⟩
    have : frame F i.castSucc = F.fl.e i := by simp [frame, Formalism.MainNotions.S.FlagG.fvec]
    rw [this]
    exact Submodule.subset_span (s := Set.range F.fl.e) ⟨i, rfl⟩

theorem card_BQ_le : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (T T' : E) (F : LFlag S r T) (F' : LFlag S r T'), g ≠ 0 → Submodule.IsLattice E Λ → IsLift Λ F → IsLift Λ F' → (∀ b, frame F b ∈ Λ) → (∀ b, frame F' b ∈ Λ) → IsGeneric Λ g F F' → (Nat.card (BQ Λ F F') : ℝ) ≤ NE (E := E) g ^ (r + 1) := by
  intro E _ _ _ S r Λ g T T' F F' hg _ hL hL' hF hF' hG
  obtain ⟨ξ, -, hξ⟩ := hG
  have hcard : Nat.card (𝓞 E ⧸ Ideal.span {(g : 𝓞 E)}) = g ^ finrank ℚ E := by
    rw [← RingOfIntegers.rank, ← Ideal.absNorm_span_natCast, Ideal.absNorm_apply,
      Submodule.cardQuot_apply]
  haveI : Finite (𝓞 E ⧸ Ideal.span {(g : 𝓞 E)}) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hU1 : XLam Λ F ⊔ Submodule.span (𝓞 E) {F.zt} ≤ UU Λ F F' :=
    le_sup_left.trans le_sup_left
  have hU2 : XLam Λ F' ⊔ Submodule.span (𝓞 E) {F'.zt} ≤ UU Λ F F' :=
    sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hsm : ∀ (o : 𝓞 E) (x : S.V), (o : E) • x = o • x := fun o x => algebraMap_smul E o x
  have main := card_quot_le (RingOfIntegers.not_isField E) (g : 𝓞 E) (BLat Λ F F') (UU Λ F F')
    (Mplus Λ g F F' ξ) (fun b => ((g : E)⁻¹) • (frame F' b - frameAct (frame F) ξ b))
    (by
      intro b
      have hg' : (g : E) ≠ 0 := Nat.cast_ne_zero.2 hg
      have e : ((g : 𝓞 E) : E) = (g : E) := by simp
      rw [← hsm, e, smul_smul, mul_inv_cancel₀ hg', one_smul]
      refine Submodule.sub_mem _ (hU2 (frame_mem Λ F' hL' hF' b)) (Submodule.sum_mem _ fun a _ => ?_)
      rw [hsm]
      exact Submodule.smul_mem _ _ (hU1 (frame_mem Λ F hL hF a)))
    (fun b => Submodule.subset_span (Or.inr ⟨b, rfl⟩))
    (by
      refine Submodule.span_le.2 ?_
      rintro x ((hx | hx) | hx)
      · exact Submodule.mem_sup_left (hU1 (Submodule.mem_sup_left hx))
      · exact Submodule.mem_sup_left (hU1 (Submodule.mem_sup_right (Submodule.subset_span hx)))
      · exact Submodule.mem_sup_right (Submodule.subset_span hx))
    hξ
  rw [hcard] at main
  unfold NE
  exact_mod_cast main

end GlobalTheory.GenericOrder
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DKerHasCompactSupport
section
noncomputable section

open MeasureTheory Matrix Filter Topology Set Metric
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.SmLinSub

section Smoothing

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PI.UpqRep PI.KFinSmoothW

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem expS_mul_neg (Z : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • Z) * NormedSpace.exp (t • -Z) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl Z).neg_right.smul_left t).smul_right t)]
  simp [smul_neg]

theorem expS_neg_mul (Z : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • -Z) * NormedSpace.exp (t • Z) = 1 := by
  have h := expS_mul_neg (-Z) t
  rwa [neg_neg] at h

def expU (Z : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) : (Matrix (Fin n) (Fin n) ℂ)ˣ :=
  ⟨NormedSpace.exp (t • Z), NormedSpace.exp (t • -Z), expS_mul_neg Z t, expS_neg_mul Z t⟩

def dKer (Z : Matrix (Fin n) (Fin n) ℂ) (Φ : Matrix (Fin n) (Fin n) ℂ → ℂ) : Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun m => fderiv ℝ Φ m (-Z * m)

end Smoothing

end GlobalTheory.SmLinSub

namespace GlobalTheory.SmLinSub

section Rep

open Formalism.MainNotions.S GlobalTheory.Ell

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {G : Matrix (Fin n) (Fin n) ℂ} {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem lie_smulR (c : ℝ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieOf G) : c • X ∈ lieOf G := by
  have h1 : Xᴴ * G + G * X = 0 := hX
  show (c • X)ᴴ * G + G * (c • X) = 0
  rw [conjTranspose_smul, star_trivial, smul_mul_assoc, mul_smul_comm, ← smul_add, h1, smul_zero]

theorem exp_mem {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieOf G) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH G :=
  CCRuleCW.exp_mem_UH G (t • X) (lie_smulR t hX)

theorem listProd_mem : ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ g ∈ l, g ∈ Formalism.QuantumDeterminants.UH G) →
    l.prod ∈ Formalism.QuantumDeterminants.UH G
  | [], _ => by
    show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * G * 1 = G
    simp
  | g :: l, h => by
    rw [List.prod_cons]
    exact CCRuleCW.UH_mul G _ _ (h g (by simp)) (listProd_mem l fun x hx => h x (by simp [hx]))

theorem expProd_mem {k : ℕ} {Xs : Fin k → Matrix (Fin n) (Fin n) ℂ} (hX : ∀ i, Xs i ∈ lieOf G)
    (t : Fin k → ℝ) : (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod ∈ Formalism.QuantumDeterminants.UH G :=
  listProd_mem _ fun g hg => by
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
    exact exp_mem (hX i) _

theorem isUnit_of_mem (hG : IsUnit G) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G) : IsUnit g := by
  have h : gᴴ * G * g = G := hg
  exact isUnit_of_mul_isUnit_right (h.symm ▸ hG : IsUnit (gᴴ * G * g))

theorem conj_mem_lie (hG : IsUnit G) {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G)
    (hX : X ∈ lieOf G) : g⁻¹ * X * g ∈ lieOf G := by
  have h : gᴴ * G * g = G := hg
  have hX' : Xᴴ * G + G * X = 0 := hX
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 (isUnit_of_mem hG hg)
  have h1 : G * g⁻¹ = gᴴ * G := by
    conv_lhs => rw [← h]
    rw [Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.mul_one]
  have h2 : (g⁻¹)ᴴ * G = G * g := by
    conv_lhs => rw [← h]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, mul_nonsing_inv _ hd]; simp
  show (g⁻¹ * X * g)ᴴ * G + G * (g⁻¹ * X * g) = 0
  calc (g⁻¹ * X * g)ᴴ * G + G * (g⁻¹ * X * g) = gᴴ * Xᴴ * ((g⁻¹)ᴴ * G) + (G * g⁻¹) * X * g := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = gᴴ * (Xᴴ * G + G * X) * g := by rw [h1, h2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX']; simp

theorem rep_mul (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) ρ) {g g' : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH G) (hg' : g' ∈ Formalism.QuantumDeterminants.UH G) (w : H) : ρ (g * g') w = ρ g (ρ g' w) := by
  rw [hπ.1.2 g hg g' hg']; rfl

theorem exp_conj_inv {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsUnit g) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (g⁻¹ * X * g)) = g⁻¹ * NormedSpace.exp (t • X) * g := by
  rw [← Matrix.exp_conj' _ _ hg, Matrix.mul_smul, Matrix.smul_mul]

theorem hasDerivAt_dR {w : H} (hw : SmV (lieOf G) ρ w) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieOf G) :
    HasDerivAt (fun t : ℝ => ρ (NormedSpace.exp (t • X)) w) (dR ρ X w) 0 := by
  have h1 := hw 1 (fun _ => X) (fun _ => hX)
  have h2 : ContDiff ℝ ∞ fun t : ℝ => fun _ : Fin 1 => t := contDiff_pi.2 fun _ => contDiff_id
  have h3 : ContDiff ℝ ∞ fun t : ℝ => ρ (NormedSpace.exp (t • X)) w := by
    simpa [Function.comp_def] using h1.comp h2
  exact (h3.differentiable (by simp) 0).hasDerivAt

theorem contDiff_deriv_snoc {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    {F : (Fin (k + 1) → ℝ) → E} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ fun t : Fin k → ℝ => deriv (fun s : ℝ => F (Fin.snoc t s)) 0 := by
  have hs : ContDiff ℝ ∞ fun p : (Fin k → ℝ) × ℝ => (Fin.snoc p.1 p.2 : Fin (k + 1) → ℝ) := by
    refine contDiff_pi.2 fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using contDiff_snd
    · simp only [Fin.snoc_castSucc]
      fun_prop
  have h1 : ContDiff ℝ ∞ (Function.uncurry fun (t : Fin k → ℝ) (s : ℝ) => F (Fin.snoc t s)) := hF.comp hs
  have h2 := ContDiff.fderiv (𝕜 := ℝ) (m := ∞) (n := ∞) (g := fun _ : Fin k → ℝ => (0 : ℝ)) h1 contDiff_const
    (le_of_eq rfl)
  exact h2.clm_apply (contDiff_const (c := (1 : ℝ)))

theorem dR_mem (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) ρ) {w : H} (hw : SmV (lieOf G) ρ w)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieOf G) : SmV (lieOf G) ρ (dR ρ X w) := by
  intro k Xs hXs
  have h1 := hw (k + 1) (Fin.snoc Xs X) (fun i => by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hX
    · simpa using hXs j)
  convert contDiff_deriv_snoc h1 using 2 with t
  have h2 := (((ρ _).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_dR hw hX) :
    HasDerivAt (fun s : ℝ => ρ (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod
      (ρ (NormedSpace.exp (s • X)) w)) _ 0)
  refine h2.deriv.symm.trans ?_
  congr 1
  funext s
  show ρ _ (ρ _ w) = _
  rw [← rep_mul hπ (expProd_mem hXs t) (exp_mem hX s)]
  simp [List.ofFn_succ', -List.ofFn_succ]

theorem prod_conj {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsUnit g) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    g * (l.map fun x => g⁻¹ * x * g).prod = l.prod * g := by
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 hg
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, Matrix.mul_assoc x, ← ih]
    simp only [← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul]

theorem rep_mem (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) ρ) {w : H} (hw : SmV (lieOf G) ρ w)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G) : SmV (lieOf G) ρ (ρ g w) := by
  intro k Xs hXs
  have hu := isUnit_of_mem hG hg
  have hY : ∀ i, g⁻¹ * Xs i * g ∈ lieOf G := fun i => conj_mem_lie hG hg (hXs i)
  have h1 := ((ρ g).restrictScalars ℝ).contDiff.comp (hw k _ hY)
  convert h1 using 2 with t
  show _ = ρ g _
  rw [← rep_mul hπ (expProd_mem hXs t) hg, ← rep_mul hπ hg (expProd_mem hY t), ← prod_conj hu,
    List.map_ofFn]
  simp only [exp_conj_inv hu, Function.comp_def]

theorem dR_rep (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) ρ) {w : H} (hw : SmV (lieOf G) ρ w)
    {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G) (hX : X ∈ lieOf G) :
    dR ρ X (ρ g w) = ρ g (dR ρ (g⁻¹ * X * g) w) := by
  have hu := isUnit_of_mem hG hg
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 hu
  have hY := conj_mem_lie hG hg hX
  have h2 := (((ρ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_dR hw hY) :
    HasDerivAt (fun s : ℝ => ρ g (ρ (NormedSpace.exp (s • (g⁻¹ * X * g))) w)) _ 0)
  refine Eq.trans ?_ h2.deriv
  unfold dR
  congr 1
  funext s
  show _ = ρ g (ρ _ w)
  rw [← rep_mul hπ hg (exp_mem hY s), ← rep_mul hπ (exp_mem hX s) hg, exp_conj_inv hu]
  simp only [← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul]

end Rep

end GlobalTheory.SmLinSub
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DuWinThreeOfCount
section
open Formalism.BasicNotions GlobalTheory.Diag.PG

namespace GlobalTheory.Diag.PG.DuWinThree

theorem star_pow {a G : ℝ} (ha : 0 < a) (hG : 0 < G) {n : ℕ} (hn : 0 < n) :
    (a ^ ((1 : ℝ) / n) * G ^ (-(2 : ℝ) / n)) ^ n = a / G ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [mul_pow, ← Real.rpow_natCast (a ^ _), ← Real.rpow_natCast (G ^ _), ← Real.rpow_mul ha.le,
    ← Real.rpow_mul hG.le, div_mul_cancel₀ _ hn', div_mul_cancel₀ _ hn', Real.rpow_one,
    Real.rpow_neg hG.le, div_eq_mul_inv]
  norm_num

theorem window {S T : ℝ} {f k : ℕ} (hS : 0 < S) (hT : 2 ≤ T) (hf : 1 ≤ f) (hfk : f ≤ k)
    (h1 : S ≤ T) (h2 : T ≤ (1 + 1 / ((f * k : ℕ) : ℝ)) * S) :
    S ^ (f * k) / 2 ≤ (T ^ k - 1) ^ f ∧ (T ^ k - 1) ^ f ≤ 3 * S ^ (f * k) := by
  have hk2 : 2 * k ≤ 2 ^ k := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have : j < 2 ^ j := Nat.lt_two_pow_self
    rw [pow_succ]; omega
  have hTk : (2 * f : ℝ) ≤ T ^ k := by
    calc (2 * f : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast (by omega : 2 * f ≤ 2 ^ k)
      _ ≤ T ^ k := pow_le_pow_left₀ (by norm_num) hT k
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hP : 0 < T ^ k := by linarith
  have hpow : (T ^ k) ^ f = T ^ (f * k) := by rw [← pow_mul, mul_comm]
  constructor
  · have e : T ^ k - 1 = T ^ k * (1 + (-(1 / T ^ k))) := by field_simp; ring
    have hsm : 1 / T ^ k ≤ 1 := by rw [div_le_one hP]; linarith
    have hb := one_add_mul_le_pow (a := -(1 / T ^ k)) (by linarith) f
    have hc : (f : ℝ) * (1 / T ^ k) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ hP]; linarith
    have hd : S ^ (f * k) ≤ T ^ (f * k) := pow_le_pow_left₀ hS.le h1 _
    have hTn : 0 ≤ T ^ (f * k) := by positivity
    rw [e, mul_pow, hpow]
    calc S ^ (f * k) / 2 ≤ T ^ (f * k) * (1 / 2) := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hTn
  · have hn : 0 < f * k := Nat.mul_pos hf (by omega)
    have hn' : (0 : ℝ) < ((f * k : ℕ) : ℝ) := by exact_mod_cast hn
    have he : (1 + 1 / ((f * k : ℕ) : ℝ)) ^ (f * k) ≤ 3 := by
      have h3 : 1 + 1 / ((f * k : ℕ) : ℝ) ≤ Real.exp (1 / ((f * k : ℕ) : ℝ)) := by
        have := Real.add_one_le_exp (1 / ((f * k : ℕ) : ℝ)); linarith
      calc _ ≤ Real.exp (1 / ((f * k : ℕ) : ℝ)) ^ (f * k) := pow_le_pow_left₀ (by positivity) h3 _
        _ = Real.exp 1 := by rw [← Real.exp_nat_mul, mul_one_div_cancel hn'.ne']
        _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    calc (T ^ k - 1) ^ f ≤ (T ^ k) ^ f := pow_le_pow_left₀ (by linarith) (by linarith) _
      _ = T ^ (f * k) := hpow
      _ ≤ ((1 + 1 / ((f * k : ℕ) : ℝ)) * S) ^ (f * k) := pow_le_pow_left₀ (by linarith) h2 _
      _ ≤ 3 * S ^ (f * k) := by
        rw [mul_pow]; exact mul_le_mul_of_nonneg_right he (by positivity)

end GlobalTheory.Diag.PG.DuWinThree

namespace GlobalTheory.Diag.PG

open GlobalTheory.Diag.PG.DuWinThree

theorem duWin_three_of_count : ∀ D : D7, (∀ u, (D.duS u : ℝ) = ((D.mem u).A.duStar : ℝ) *
    (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f) → DuWin D 3 := by
  intro D h u
  have hG : 0 < (D.mem u).A.GamP := lt_trans one_pos (D.mem u).A.one_lt_gammaP
  have hD : 0 < (D.mem u).A.Dstar := (D.mem u).A.Dstar_pos
  have hd : (0 : ℝ) < (D.mem u).A.duStar := by exact_mod_cast (D.mem u).A.duStar_pos
  have hT : 2 ≤ (D.mem u).A.T := (D.mem u).A.T_prime.two_le
  have hfk : D.R.f ≤ D.R.k := D.R.f_le_k
  have hf : 1 ≤ D.R.f := le_trans (by have := D.R.two_le_m; omega) (D.R.m_le_f : D.R.m ≤ D.R.f)
  have hn : 0 < D.R.f * D.R.k := Nat.mul_pos hf (by omega)
  have hS : 0 < (D.mem u).A.Tstar := by
    unfold ColumnsAtT.Tstar ColumnsAtT.Xu
    positivity
  have hSn : (D.mem u).A.Tstar ^ (D.R.f * D.R.k) =
      (D.mem u).A.Dstar / (D.mem u).A.duStar / (D.mem u).A.GamP ^ 2 := by
    rw [← star_pow (div_pos hD hd) hG hn, ColumnsAtT.Tstar, ColumnsAtT.Xu, Nat.cast_mul]
  obtain ⟨w1, w2⟩ := D.T_win u
  obtain ⟨a, b⟩ := window hS (by exact_mod_cast hT) hf hfk w1 (by rw [Nat.cast_mul]; exact w2)
  rw [hSn] at a b
  rw [h u, ← D.Dstar_eq u]
  set X := (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f
  have hG2 : (D.mem u).A.GamP ^ (-2 : ℤ) = 1 / (D.mem u).A.GamP ^ 2 := by
    rw [zpow_neg, one_div]; norm_cast
  rw [hG2]
  set c := (D.mem u).A.Dstar / (D.mem u).A.duStar / (D.mem u).A.GamP ^ 2 with hcdef
  have hc0 : 0 < c := by positivity
  have e : 1 / (D.mem u).A.GamP ^ 2 * (D.mem u).A.Dstar = ((D.mem u).A.duStar : ℝ) * c := by
    rw [hcdef]; field_simp
  rw [e]
  constructor
  · have := mul_le_mul_of_nonneg_left a hd.le
    nlinarith
  · have := mul_le_mul_of_nonneg_left b hd.le
    nlinarith

end GlobalTheory.Diag.PG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FolnerSingleTranslateProportionTendstoOne
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem folner_single_translate : ∀ (k r : ℕ) (S : Set (Mat k r)) (μ : Measure (Mt k r))
    (Om : ℕ → Set (Mt k r)), IsFolner S μ Om → ∀ p ∈ S,
    Filter.Tendsto (fun j => μ {s | s ∈ Om j ∧ lmulM p s ∈ Om j} / μ (Om j)) Filter.atTop (nhds 1) := by
  intro k r S μ Om h p hp
  obtain ⟨_, hC⟩ := h
  obtain ⟨Oc, hOc, hlim⟩ := hC {p} isCompact_singleton (Set.singleton_subset_iff.2 hp)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds (fun j => ?_) (fun j => ?_)
  · refine ENNReal.div_le_div_right (measure_mono fun x hx => ?_) _
    exact ⟨(hOc j).2.1 hx, (hOc j).2.2 p rfl x hx⟩
  · exact (ENNReal.div_le_div_right (measure_mono fun x hx => hx.1) _).trans ENNReal.div_self_le_one

end GlobalTheory.SgInf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalRankNumberBoundsGapsExceedStatement
section
open GlobalTheory.Diag.PG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalRankNumberBounds_gaps_exceed : ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C : ℝ, 0 < C → ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ m f k lrd Del : ℝ, RankNums x eps CD m f k lrd Del → ∀ r : ℝ, k ≤ r → r ≤ 2 * k → C * k * m ^ 4 + r * m ^ 10 < 4 * Del ∧ C * k * m ^ 4 + r * m ^ 10 < Real.sqrt (bx x eps) ∧ C * k * m ^ 4 + r * m ^ 10 < x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps ∧ C * r ^ 19 * f ^ 5 * x ^ eps ≤ x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps := by
  first | exact @GlobalTheory.Diag.PG.gaps_exceed | exact GlobalTheory.Diag.PG.gaps_exceed | (intros; apply GlobalTheory.Diag.PG.gaps_exceed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalRankNumberBoundsRankClausesFirstHalfStatement
section
open GlobalTheory.Diag.PG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_rankNums_imp_parameter_lower_bounds : ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C : ℝ, ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ m f k lrd Del : ℝ, RankNums x eps CD m f k lrd Del → C * m ^ 5 * f * x ^ eps ≤ k ∧ Real.log f ≤ Real.sqrt (m / 2 - 1) ∧ C * x ^ eps ≤ f * Real.log k ∧ C * (m ^ 2 * x ^ eps) ≤ k ∧ C ≤ m ∧ C * x ^ eps ≤ m - 1 ∧ C ≤ k ∧ 1 < x ^ eps := by
  first | exact @GlobalTheory.Diag.PG.rankNums_first_half | exact GlobalTheory.Diag.PG.rankNums_first_half | (intros; apply GlobalTheory.Diag.PG.rankNums_first_half <;> assumption)
end

