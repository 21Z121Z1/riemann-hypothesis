import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.PsiApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0024
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0025
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
import Formalism.RealPlaceAnalysis.Bundle0001

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StagedEstimateHolds
section
namespace GlobalTheory.CompanionTheory.RgEis

open PositivityTheory.RgEis

variable {G : Type} [Group G] {P Δ Γ : Subgroup G}

def cls (y : Γ) : Cos P Γ := Quotient.mk _ y

theorem cls_eq {a b : Γ} : (cls a : Cos P Γ) = cls b ↔ (b : G) * (a : G)⁻¹ ∈ P := by
  unfold cls
  rw [Quotient.eq]
  show QuotientGroup.rightRel _ a b ↔ _
  rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf]
  simp

theorem rep_mem (q : Cos P Γ) : rep q ∈ Γ := (Quotient.out q).2

theorem cls_rep (q : Cos P Γ) : cls ⟨rep q, rep_mem q⟩ = q := Quotient.out_eq q

theorem rep_cls (y : Γ) : ∃ p ∈ P, p ∈ Γ ∧ rep (cls y : Cos P Γ) = p * y := by
  have h : (cls y : Cos P Γ) = cls ⟨rep (cls y : Cos P Γ), rep_mem _⟩ := (cls_rep _).symm
  refine ⟨rep (cls y : Cos P Γ) * (y : G)⁻¹, cls_eq.1 h, Γ.mul_mem (rep_mem _) (Γ.inv_mem y.2), by group⟩

noncomputable def glue (hΔ : Δ ≤ Γ) (s : (_ : Cos Δ Γ) × Cos P Δ) : Cos P Γ :=
  cls ⟨rep s.2 * rep s.1, Γ.mul_mem (hΔ (rep_mem _)) (rep_mem _)⟩

theorem glue_injective (hΔ : Δ ≤ Γ) (hP : ∀ γ ∈ Γ, γ ∈ P → γ ∈ Δ) :
    Function.Injective (glue (P := P) hΔ) := by
  rintro ⟨r, q⟩ ⟨r', q'⟩ h
  have h1 : rep q' * rep r' * (rep q * rep r)⁻¹ ∈ P := cls_eq.1 h
  have hΓ : rep q' * rep r' * (rep q * rep r)⁻¹ ∈ Γ :=
    Γ.mul_mem (Γ.mul_mem (hΔ (rep_mem _)) (rep_mem _))
      (Γ.inv_mem (Γ.mul_mem (hΔ (rep_mem _)) (rep_mem _)))
  have h2 := hP _ hΓ h1
  have h3 : rep r' * (rep r)⁻¹ ∈ Δ := by
    have : rep r' * (rep r)⁻¹ = (rep q')⁻¹ * (rep q' * rep r' * (rep q * rep r)⁻¹) * rep q := by
      group
    rw [this]
    exact Δ.mul_mem (Δ.mul_mem (Δ.inv_mem (rep_mem _)) h2) (rep_mem _)
  have hr : r = r' := by
    rw [← cls_rep r, ← cls_rep r']
    exact cls_eq.2 h3
  subst hr
  have h4 : rep q' * (rep q)⁻¹ ∈ P := by
    have : rep q' * (rep q)⁻¹ = rep q' * rep r * (rep q * rep r)⁻¹ := by group
    rw [this]
    exact h1
  have hq : q = q' := by
    rw [← cls_rep q, ← cls_rep q']
    exact cls_eq.2 h4
  subst hq
  rfl

theorem glue_surjective (hΔ : Δ ≤ Γ) (hP : ∀ γ ∈ Γ, γ ∈ P → γ ∈ Δ) :
    Function.Surjective (glue (P := P) hΔ) := by
  intro t
  obtain ⟨y, rfl⟩ : ∃ y : Γ, cls y = t := ⟨_, cls_rep t⟩
  obtain ⟨d, hdΔ, -, hd⟩ := rep_cls (P := Δ) y
  obtain ⟨p, hpP, hpΔ, hp⟩ := rep_cls (P := P) (⟨d⁻¹, Δ.inv_mem hdΔ⟩ : Δ)
  refine ⟨⟨cls y, cls ⟨d⁻¹, Δ.inv_mem hdΔ⟩⟩, ?_⟩
  apply cls_eq.2
  show (y : G) * (rep (cls ⟨d⁻¹, Δ.inv_mem hdΔ⟩ : Cos P Δ) * rep (cls y : Cos Δ Γ))⁻¹ ∈ P
  rw [hp, hd]
  have : (y : G) * (p * d⁻¹ * (d * y))⁻¹ = p⁻¹ := by group
  rw [this]
  exact P.inv_mem hpP

theorem f_rep {X : Type} {f : G → X} (hf : ∀ γ ∈ Γ, γ ∈ P → ∀ x, f (γ * x) = f x) (y : Γ) (g : G) :
    f (rep (cls y : Cos P Γ) * g) = f (y * g) := by
  obtain ⟨p, hpP, hpΓ, hp⟩ := rep_cls (P := P) y
  rw [hp, mul_assoc, hf p hpΓ hpP]

theorem stage : PiLocalization₂ := by
  intro G _ X _ _ P Δ Γ f hΔ hP hf g hs
  have hmem : ∀ (q : Cos P Δ) (x : G), x ∈ Γ → rep q * x ∈ Γ := fun q x hx =>
    Γ.mul_mem (hΔ (rep_mem q)) hx

  have h1 : ∀ x ∈ Γ, Summable fun q : Cos P Δ => ‖f (rep q * (x * g))‖ := by
    intro x hx
    have hinj : Function.Injective fun q : Cos P Δ => (cls ⟨rep q * x, hmem q x hx⟩ : Cos P Γ) := by
      intro q q' h
      have h1 : rep q' * x * (rep q * x)⁻¹ ∈ P := cls_eq.1 h
      have h2 : rep q' * (rep q)⁻¹ ∈ P := by
        have : rep q' * (rep q)⁻¹ = rep q' * x * (rep q * x)⁻¹ := by group
        rw [this]
        exact h1
      rw [← cls_rep q, ← cls_rep q']
      exact cls_eq.2 h2
    refine (hs.comp_injective hinj).congr fun q => ?_
    simp only [Function.comp_apply]
    rw [f_rep hf, mul_assoc]

  let e : ((_ : Cos Δ Γ) × Cos P Δ) ≃ Cos P Γ :=
    Equiv.ofBijective (glue hΔ) ⟨glue_injective hΔ hP, glue_surjective hΔ hP⟩
  let φ : ((_ : Cos Δ Γ) × Cos P Δ) → X := fun s => f (rep s.2 * (rep s.1 * g))
  have hφ : ∀ s, f (rep (e s) * g) = φ s := by
    intro s
    show f (rep (glue hΔ s) * g) = _
    unfold glue
    rw [f_rep hf, mul_assoc]
  have hn : Summable fun s => ‖φ s‖ := by
    refine ((e.summable_iff (f := fun q : Cos P Γ => ‖f (rep q * g)‖)).2 hs).congr fun s => ?_
    simp only [Function.comp_apply]
    rw [hφ]
  have hsig := (summable_sigma_of_nonneg (fun s => norm_nonneg (φ s))).1 hn
  have hφs : Summable φ := hn.of_norm
  refine ⟨h1, hsig.2, ?_⟩
  have hfib : ∀ r, Summable fun q : Cos P Δ => φ ⟨r, q⟩ := fun r => (hsig.1 r).of_norm
  calc ∑' q : Cos P Γ, f (rep q * g) = ∑' s, f (rep (e s) * g) := (e.tsum_eq _).symm
    _ = ∑' s, φ s := tsum_congr hφ
    _ = ∑' r : Cos Δ Γ, ∑' q : Cos P Δ, φ ⟨r, q⟩ := hφs.tsum_sigma' hfib

end GlobalTheory.CompanionTheory.RgEis
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorEvalFixedOfFixed
section
open TensorProduct CrystallineSemistableComparison.Pb.Psi

namespace GlobalTheory.CompanionTheory.FrobFix

theorem extension_fixed : ∀ {W C₀ : Type} [CommRing W] [CommRing C₀] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (k : K₀ →+* C₀) {B : Type} [Field B] [IsFractionRing W K₀] (ι : C₀ →+* B) (σB : B →+* B) (h : L →+ B) (E : K₀ ⊗[W] L →+ B), (∀ x y, E (x ⊗ₜ y) = ι (k x) * h y) → (∀ w, σB (ι (k (algebraMap W K₀ w))) = ι (k (algebraMap W K₀ w))) → (∀ y, σB (h y) = h y) → ∀ v : K₀ ⊗[W] L, σB (E v) = E v := by
  intro W C₀ _ _ K₀ _ _ L _ _ k B _ _ ι σB h E hE hW hy v
  have hinj : Function.Injective (ι.comp k) := (ι.comp k).injective
  have hg : ∀ x : K₀, σB (ι (k x)) = ι (k x) := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := W) x
    have hb0 : algebraMap W K₀ b ≠ 0 :=
      (IsLocalization.map_units K₀ (⟨b, hb⟩ : nonZeroDivisors W)).ne_zero
    have hgb : ι (k (algebraMap W K₀ b)) ≠ 0 := by
      intro h0
      apply hb0
      apply hinj
      simpa using h0
    have hmul : ι (k (algebraMap W K₀ a / algebraMap W K₀ b)) * ι (k (algebraMap W K₀ b))
        = ι (k (algebraMap W K₀ a)) := by
      rw [← map_mul, ← map_mul, div_mul_cancel₀ _ hb0]
    apply mul_right_cancel₀ hgb
    calc σB (ι (k (algebraMap W K₀ a / algebraMap W K₀ b))) * ι (k (algebraMap W K₀ b))
        = σB (ι (k (algebraMap W K₀ a / algebraMap W K₀ b))) * σB (ι (k (algebraMap W K₀ b))) := by
          rw [hW b]
      _ = σB (ι (k (algebraMap W K₀ a))) := by rw [← map_mul, hmul]
      _ = ι (k (algebraMap W K₀ a)) := hW a
      _ = ι (k (algebraMap W K₀ a / algebraMap W K₀ b)) * ι (k (algebraMap W K₀ b)) := hmul.symm
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rw [hE, map_mul, hg, hy]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

end GlobalTheory.CompanionTheory.FrobFix
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorPrimeOverIdealCompletionStatement
section
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_prime_over_ideal_completion : ∀ {B R C M : Type} [CommRing B] [CommRing R] [CommRing C] [Algebra B R] [Algebra B C] [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower B R M] [Module.Finite R M] [IsNoetherianRing (R ⊗[B] C)] (I : Ideal B) (y : M), (∀ n : ℕ, y ⊗ₜ[B] (1 : C) ∈ LinearMap.range ((I ^ (n + 1) • ⊤ : Submodule B M).subtype.rTensor C)) → ∀ Q₁ : Ideal (R ⊗[B] C), Q₁.IsPrime → I.map (algebraMap B R) ≤ Q₁.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[B] C) → ∃ w : R ⊗[B] C, w ∉ Q₁ ∧ w • ((1 : R ⊗[B] C) ⊗ₜ[R] y) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.KrullBaseChange.krull_after_base_change | exact GlobalTheory.CompanionTheory.KrullBaseChange.krull_after_base_change | (intros; apply GlobalTheory.CompanionTheory.KrullBaseChange.krull_after_base_change <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorSumAnnihilatorStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_sum_annihilator : ∀ {ι : Type} (T : Finset ι) (l : ι → Multiset ℂ), ∃ l' : Multiset ℂ, Multiset.card l' = ∏ τ ∈ T, Multiset.card (l τ) ∧
  ∀ (R : Type) [CommRing R] [Algebra ℂ R] (h : ι → R), (∀ τ ∈ T, ((l τ).map fun c => h τ - algebraMap ℂ R c).prod = 0) →
    (l'.map fun c => ∑ τ ∈ T, h τ - algebraMap ℂ R c).prod = 0 := by
  first | exact @GlobalTheory.CompanionTheory.KillSum.sum_killed | exact GlobalTheory.CompanionTheory.KillSum.sum_killed | (intros; apply GlobalTheory.CompanionTheory.KillSum.sum_killed <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TmulEqZeroOfMemSpan
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.TensCompl

theorem tmul_eq_zero_of_mem_span {R N A : Type} [CommRing R] [AddCommGroup N] [Module R N]
    [CommRing A] [Algebra R A] (c : R) (M : ℕ) (hN : ∀ x : N, c ^ M • x = 0) (n : N) (a : A)
    (ha : a ∈ Ideal.span {algebraMap R A c ^ M}) : n ⊗ₜ[R] a = 0 := by
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  have : b * algebraMap R A c ^ M = c ^ M • b := by
    rw [Algebra.smul_def, map_pow, mul_comm]
  rw [this, ← smul_tmul, hN, zero_tmul]

theorem main : ∀ (R : Type) [CommRing R] (r : ℕ → R) (M : ℕ) (N : Type) [AddCommGroup N] [Module R N](B : Type) [CommRing B] [Algebra R B] (T : Type) [CommRing T] [Algebra R T] (g : B →ₐ[R] T), (∀ x : N, r 0 ^ M • x = 0) → (∀ y : T, ∃ x, y - g x ∈ Ideal.span {algebraMap R T (r 0) ^ M}) → (∀ x : B, g x ∈ Ideal.span {algebraMap R T (r 0) ^ M} → ∀ k, r k • x ∈ Ideal.span {algebraMap R B (r 0) ^ M}) → Function.Surjective (g.toLinearMap.lTensor N) ∧ ∀ w : N ⊗[R] B, g.toLinearMap.lTensor N w = 0 → ∀ k, r k • w = 0 := by
  intro R _ r M N _ _ B _ _ T _ _ g h1 h2 h3
  constructor
  · intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul n y =>
      obtain ⟨x, hx⟩ := h2 y
      refine ⟨n ⊗ₜ x, ?_⟩
      have h0 := tmul_eq_zero_of_mem_span (r 0) M h1 n _ hx
      rw [tmul_sub, sub_eq_zero] at h0
      rw [h0]
      simp
    | add a b ha hb =>
      obtain ⟨a', rfl⟩ := ha
      obtain ⟨b', rfl⟩ := hb
      exact ⟨a' + b', map_add _ _ _⟩
  · intro w hw k
    choose s hs using h2
    let I : Ideal T := Ideal.span {algebraMap R T (r 0) ^ M}
    let P : Submodule R B := (Ideal.span {algebraMap R B (r 0) ^ M}).restrictScalars R
    have key : ∀ x : B, g x ∈ I → r k • x ∈ P := fun x hx => h3 x hx k
    have hadd : ∀ y y' : T, r k • s (y + y') - (r k • s y + r k • s y') ∈ P := by
      intro y y'
      rw [← smul_add, ← smul_sub]
      apply key
      have e : g (s (y + y') - (s y + s y')) =
          (y - g (s y)) + (y' - g (s y')) - (y + y' - g (s (y + y'))) := by
        simp only [map_sub, map_add]; ring
      rw [e]
      exact I.sub_mem (I.add_mem (hs y) (hs y')) (hs _)
    have hsmul : ∀ (c : R) (y : T), r k • s (c • y) - c • (r k • s y) ∈ P := by
      intro c y
      rw [smul_comm c, ← smul_sub]
      apply key
      have e : g (s (c • y) - c • s y) =
          algebraMap R T c * (y - g (s y)) - (c • y - g (s (c • y))) := by
        rw [map_sub, map_smul, mul_sub, ← Algebra.smul_def, ← Algebra.smul_def]; abel
      rw [e]
      exact I.sub_mem (I.mul_mem_left _ (hs y)) (hs _)
    let L : T →ₗ[R] B ⧸ P :=
      { toFun := fun y => P.mkQ (r k • s y)
        map_add' := fun y y' => by
          rw [← map_add]
          exact (Submodule.Quotient.eq P).mpr (hadd y y')
        map_smul' := fun c y => by
          simp only [RingHom.id_apply]
          rw [← map_smul]
          exact (Submodule.Quotient.eq P).mpr (hsmul c y) }
    let F : (B ⧸ P) →ₗ[R] N →ₗ[R] N ⊗[R] B :=
      P.liftQ (TensorProduct.mk R N B).flip (by
        intro b hb
        rw [LinearMap.mem_ker]
        ext n
        exact tmul_eq_zero_of_mem_span (r 0) M h1 n b hb)
    let Φ : N ⊗[R] T →ₗ[R] N ⊗[R] B := TensorProduct.lift (F ∘ₗ L).flip
    have hΦ : ∀ (n : N) (y : T), Φ (n ⊗ₜ y) = n ⊗ₜ (r k • s y) := fun n y => by
      simp [Φ, F, L]
    have hcomp : ∀ v : N ⊗[R] B, Φ (g.toLinearMap.lTensor N v) = r k • v := by
      intro v
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul n b =>
        rw [LinearMap.lTensor_tmul, hΦ, ← tmul_smul, ← sub_eq_zero, ← tmul_sub, ← smul_sub]
        apply tmul_eq_zero_of_mem_span (r 0) M h1 n
        apply key
        have e : g (s (g b) - b) = -(g b - g (s (g b))) := by
          simp only [map_sub]; ring
        have e' : (g.toLinearMap) b = g b := rfl
        rw [e', e]
        exact I.neg_mem (hs _)
      | add a b ha hb => rw [map_add, map_add, ha, hb, smul_add]
    rw [← hcomp w, hw, map_zero]

end GlobalTheory.CompanionTheory.TensCompl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceDiagonalBlockConjugateFormula
section
open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHeFrame

theorem trace_diagonal_block_conjugate (n : ℕ) (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ)
    (g X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hg : IsUnit g.det)
    (hX : X * g = g * diagonal (fun i => ((d i : ℝ) : ℂ)))
    (hb : ∀ a b, X (e (Sum.inl a)) (e (Sum.inl b)) = if a = b then ((d' a : ℝ) : ℂ) else 0)
    (Y : Matrix (Fin n) (Fin n) ℂ) :
    trace (diagonal (fun i => ((d i : ℝ) : ℂ)) * (g⁻¹ * Matrix.reindex e e (Matrix.fromBlocks Y 0 0 0) * g))
      = trace (diagonal (fun a => ((d' a : ℝ) : ℂ)) * Y) := by
  set D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := diagonal (fun i => ((d i : ℝ) : ℂ)) with hD
  set B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    Matrix.reindex e e (Matrix.fromBlocks Y 0 0 0) with hB
  have h1 : g * D * g⁻¹ = X := by
    rw [← hX, Matrix.mul_assoc, Matrix.mul_nonsing_inv g hg, Matrix.mul_one]
  have h2 : trace (D * (g⁻¹ * B * g)) = trace (X * B) := by
    rw [← h1]
    have : D * (g⁻¹ * B * g) = (D * g⁻¹ * B) * g := by
      simp only [Matrix.mul_assoc]
    rw [this, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [h2]
  have h3 : trace (X * B) = ∑ u, ∑ w, X (e u) (e w) *
      (Matrix.fromBlocks Y 0 0 0 : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℂ) w u := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp [hB, Matrix.reindex_apply]
  rw [h3]
  simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero,
    Finset.sum_const_zero, add_zero, hb]
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply]

end GlobalTheory.CompanionTheory.RgHeFrame
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingBasisEval
section
open TensorProduct CrystallineSemistableComparison.Pb.Psi

namespace GlobalTheory.CompanionTheory.FrobFac

theorem T_fac : ∀ {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)), ∀ {B : Type} [Field B] (ι : C₀ →+* B) (i : A →+* B), (∀ a, ι (c a) = i a) → ∀ (h : L →+ B), (∀ (w : W) y, h (w • y) = i (algebraMap W A w) * h y) → ∀ {m : ℕ} (b : Module.Basis (Fin m) K₀ (K₀ ⊗[W] L)), ∃ E : K₀ ⊗[W] L →+ B, (∀ x y, E (x ⊗ₜ y) = ι (k x) * h y) ∧ ∀ G : A ⊗[W] L →+ B, (∀ a y, G (a ⊗ₜ y) = i a * h y) → ∀ z, G z = ∑ s, ι (T c k hk (b.coord s) z) * E (b s) := by
  intro W A C₀ _ _ _ _ K₀ _ _ L _ _ c k hk B _ ι i hi h hh m b
  let E : K₀ ⊗[W] L →+ B := TensorProduct.liftAddHom
    { toFun := fun x =>
        { toFun := fun y => ι (k x) * h y
          map_zero' := by simp
          map_add' := fun y y' => by simp [mul_add] }
      map_zero' := by
        ext y
        simp
      map_add' := fun x x' => by
        ext y
        simp [add_mul] }
    (fun r x y => by
      show ι (k (r • x)) * h y = ι (k x) * h (r • y)
      rw [hh, Algebra.smul_def, map_mul, hk, map_mul, hi]
      ring)
  have hE : ∀ x y, E (x ⊗ₜ y) = ι (k x) * h y := by
    intro x y
    first
    | rfl
    | simp [E, TensorProduct.liftAddHom_tmul]
  have hEs : ∀ (x : K₀) (t : K₀ ⊗[W] L), E (x • t) = ι (k x) * E t := by
    intro x t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x' y =>
      rw [TensorProduct.smul_tmul', hE, hE, smul_eq_mul, map_mul, map_mul, mul_assoc]
    | add t t' ht ht' =>
      rw [smul_add, map_add, map_add, ht, ht', mul_add]
  refine ⟨E, hE, fun G hG z => ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    have hsum : ∑ s, ι (T c k hk (b.coord s) (a ⊗ₜ y)) * E (b s) =
        ι (c a) * E ((1 : K₀) ⊗ₜ y) := by
      conv_rhs => rw [← b.sum_repr ((1 : K₀) ⊗ₜ y)]
      rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      have hT : T c k hk (b.coord s) (a ⊗ₜ y) = c a * k (b.repr ((1 : K₀) ⊗ₜ y) s) := by
        first
        | rfl
        | simp [T, TensorProduct.liftAddHom_tmul, Module.Basis.coord_apply]
      rw [hEs, hT, map_mul, mul_assoc]
    rw [hG, hsum, hE, map_one, map_one, one_mul, hi]
  | add x y hx hy =>
    simp only [map_add, hx, hy, add_mul, Finset.sum_add_distrib]

end GlobalTheory.CompanionTheory.FrobFac
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingFrobeniusCompat
section
open TensorProduct CrystallineSemistableComparison.Pb.Psi

namespace GlobalTheory.CompanionTheory.FrobPairing

theorem T_phi_expand {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A]
    {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L]
    (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w))
    {F : W →+* W} (φA : A →+* A) (φC : C₀ →+* C₀) (φL : L →ₛₗ[F] L) (fr : K₀ →+* K₀)
    (φD : K₀ ⊗[W] L →+ K₀ ⊗[W] L) (hD : ∀ x y, φD (x ⊗ₜ y) = fr x ⊗ₜ φL y)
    (pT : A ⊗[W] L →+ A ⊗[W] L) (hT : ∀ a y, pT (a ⊗ₜ y) = φA a ⊗ₜ φL y)
    (hφ : ∀ a, φC (c a) = c (φA a)) (hφk : ∀ x, φC (k x) = k (fr x))
    {m : ℕ} (b : Module.Basis (Fin m) K₀ (K₀ ⊗[W] L)) (f : Module.Dual K₀ (K₀ ⊗[W] L))
    (z : A ⊗[W] L) :
    T c k hk f (pT z) = ∑ s, φC (T c k hk (b.coord s) z) * k (f (φD (b s))) := by
  have hsmul : ∀ (x : K₀) (v : K₀ ⊗[W] L), φD (x • v) = fr x • φD v := by
    intro x v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x' y =>
      rw [TensorProduct.smul_tmul', hD, hD, smul_eq_mul, map_mul, TensorProduct.smul_tmul', smul_eq_mul]
    | add v₁ v₂ h₁ h₂ => rw [smul_add, map_add, map_add, h₁, h₂, smul_add]
  have hTt : ∀ (g : Module.Dual K₀ (K₀ ⊗[W] L)) (a : A) (y : L),
      T c k hk g (a ⊗ₜ y) = c a * k (g (1 ⊗ₜ y)) := fun g a y => rfl
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    rw [hT, hTt]
    simp_rw [hTt, map_mul, hφ, hφk]
    have h1 : (1 : K₀) ⊗ₜ[W] φL y = φD (1 ⊗ₜ y) := by rw [hD, map_one]
    have h2 : φD ((1 : K₀) ⊗ₜ[W] y) = ∑ s, fr (b.coord s (1 ⊗ₜ y)) • φD (b s) := by
      conv_lhs => rw [← b.sum_repr ((1 : K₀) ⊗ₜ[W] y)]
      rw [map_sum]
      simp_rw [hsmul]
      rfl
    rw [h1, h2, map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smul, smul_eq_mul, map_mul]
    ring
  | add z₁ z₂ h₁ h₂ =>
    rw [map_add, map_add, h₁, h₂, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_add, map_add, add_mul]

end GlobalTheory.CompanionTheory.FrobPairing
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingGaloisEquivariant
section
open TensorProduct CrystallineSemistableComparison.Pb.Psi

namespace GlobalTheory.CompanionTheory.FrobPairing

theorem T_gal {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A] {K₀ : Type} [Field K₀]
    [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (c : A →+* C₀) (k : K₀ →+* C₀)
    (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)) (σA : A →+* A) (σC : C₀ →+* C₀)
    (gT : A ⊗[W] L →+ A ⊗[W] L) (hg : ∀ a y, gT (a ⊗ₜ y) = σA a ⊗ₜ y)
    (hσ : ∀ a, σC (c a) = c (σA a)) (hσk : ∀ x, σC (k x) = k x)
    (f : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L) :
    T c k hk f (gT z) = σC (T c k hk f z) := by
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp only [map_zero]
  · intro a y
    rw [hg]
    simp only [T, TensorProduct.liftAddHom_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_mul, hσ, hσk]
  · intro x y hx hy
    simp only [map_add, hx, hy]

end GlobalTheory.CompanionTheory.FrobPairing
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingLTensorNaturality
section
open TensorProduct CrystallineSemistableComparison.Pb.Psi

namespace GlobalTheory.CompanionTheory.FrobPsi

theorem T_lTensor {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A]
    {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L]
    (c : A →+* C₀) (k : K₀ →+* C₀)
    (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w))
    {L' : Type 1} [AddCommGroup L'] [Module W L'] (g : L' →ₗ[W] L)
    (f : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L') :
    T c k hk f (LinearMap.lTensor A g z) = T c k hk (f ∘ₗ g.baseChange K₀) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a y =>
    rw [LinearMap.lTensor_tmul, T_tmul, T_tmul, LinearMap.comp_apply, LinearMap.baseChange_tmul]
  | add z z' hz hz' => simp only [map_add, hz, hz']

end GlobalTheory.CompanionTheory.FrobPsi
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingSmulDual
section
open TensorProduct CrystallineSemistableComparison.Pb.Psi

namespace GlobalTheory.CompanionTheory.FrobPsi

theorem T_ksmul : ∀ {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)), ∀ (x : K₀) (f : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L), T c k hk (x • f) z = k x * T c k hk f z := by
  intro W A C₀ _ _ _ _ K₀ _ _ L _ _ c k hk x f z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    rw [T_tmul, T_tmul, LinearMap.smul_apply, smul_eq_mul, map_mul]
    ring
  | add z z' hz hz' => rw [map_add, map_add, hz, hz', mul_add]

end GlobalTheory.CompanionTheory.FrobPsi
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingSmulLeft
section
open TensorProduct CrystallineSemistableComparison.Pb.Psi

namespace GlobalTheory.CompanionTheory.FrobPairing

theorem T_smul {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A]
    {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L]
    (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w))
    (f : Module.Dual K₀ (K₀ ⊗[W] L)) (a : A) (z : A ⊗[W] L) :
    T c k hk f (a • z) = c a * T c k hk f z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, mul_zero]
  | tmul b y =>
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    simp only [T, TensorProduct.liftAddHom_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_mul, mul_assoc]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, mul_add]

end GlobalTheory.CompanionTheory.FrobPairing
end

