import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0025
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0026
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0024
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TupCoordApply
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Bound

open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

variable {W : Type} [Fintype W] {n M : ℕ}

abbrev TupV (W : Type) [Fintype W] (n M : ℕ) : Type :=
  PiLp 2 (fun _ : W × Fin M => EuclideanSpace ℂ (Fin n))

def tupCoord : TupV W n M ≃L[ℝ] (W → Fin n → Fin M → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x w a p => x (w, p) a
      invFun := fun X => WithLp.toLp 2 fun k => WithLp.toLp 2 fun a => X k.1 a k.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

@[simp] theorem tupCoord_apply (x : TupV W n M) (w : W) (a : Fin n) (p : Fin M) :
    tupCoord x w a p = x (w, p) a := rfl

def diagOp (b : W → Matrix (Fin n) (Fin n) ℂ) : TupV W n M →ₗ[ℂ] TupV W n M where
  toFun y := WithLp.toLp 2 fun k => Matrix.toEuclideanLin (b k.1).transpose (y k)
  map_add' x y := by
    ext k : 2
    simp
  map_smul' c x := by
    ext k : 2
    simp

@[simp] theorem diagOp_apply (b : W → Matrix (Fin n) (Fin n) ℂ) (y : TupV W n M) (k : W × Fin M) :
    diagOp b y k = Matrix.toEuclideanLin (b k.1).transpose (y k) := rfl

def mixOp (J : W → Matrix (Fin M) (Fin M) ℂ) : TupV W n M →ₗ[ℂ] TupV W n M where
  toFun z := WithLp.toLp 2 fun k => (2 : ℂ) • ∑ j, J k.1 k.2 j • z (k.1, j)
  map_add' x y := by
    ext k : 2
    simp [smul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    ext k : 2
    simp [Finset.smul_sum, smul_smul, mul_comm, mul_left_comm]
    exact Finset.sum_congr rfl fun _ _ => by ring

@[simp] theorem mixOp_apply (J : W → Matrix (Fin M) (Fin M) ℂ) (z : TupV W n M) (k : W × Fin M) :
    mixOp J z k = (2 : ℂ) • ∑ j, J k.1 k.2 j • z (k.1, j) := rfl

def polarOp (J : W → Matrix (Fin M) (Fin M) ℂ) (b : W → Matrix (Fin n) (Fin n) ℂ) :
    TupV W n M →ₗ[ℝ] TupV W n M :=
  ((mixOp J).comp (diagOp b)).restrictScalars ℝ

theorem polarOp_apply (J : W → Matrix (Fin M) (Fin M) ℂ) (b : W → Matrix (Fin n) (Fin n) ℂ)
    (y : TupV W n M) : polarOp J b y = mixOp J (diagOp b y) := rfl

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Bound
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwKerEqMapOfSurjective
section
open GlobalTheory.PRep

namespace GlobalTheory.CompanionTheory.PRep

theorem twKer_eq_map_of_surjective {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (N : Subgroup G) (θ : N →* ℂˣ) (f : V →ₗ[ℂ] W) (hf : Function.Surjective f)
    (hint : ∀ g v, f (ρ g v) = σ g (f v)) : twKer σ N θ = (twKer ρ N θ).map f := by
  unfold GlobalTheory.PRep.twKer
  rw [Submodule.map_span]
  congr 1
  ext w
  constructor
  · rintro ⟨n, w', rfl⟩
    obtain ⟨v, rfl⟩ := hf w'
    exact ⟨ρ n v - (θ n : ℂ) • v, ⟨n, v, rfl⟩, by rw [map_sub, map_smul, hint]⟩
  · rintro ⟨_, ⟨n, v, rfl⟩, rfl⟩
    exact ⟨n, f v, by rw [map_sub, map_smul, hint]⟩

theorem twKer_map_closed : ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (N : Subgroup G)
    (θ : N →* ℂˣ) (f : V →ₗ[ℂ] W), Function.Surjective f → (∀ g v, f (ρ g v) = σ g (f v)) →
    twKer σ N θ = (twKer ρ N θ).map f :=
  fun ρ σ N θ f hf hint => GlobalTheory.CompanionTheory.PRep.twKer_eq_map_of_surjective ρ σ N θ f hf hint

end GlobalTheory.CompanionTheory.PRep
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformLowerBoundNearInjectiveStatement
section
open MeasureTheory
open scoped ENNReal NNReal Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_lower_bound_near_injective : ∀ (X P : Type) [AddCommGroup X] [TopologicalSpace X] [TopologicalSpace P] (N : ℕ) (e : X ≃+ (Fin N → ℝ)), Continuous e → Continuous e.symm → ∀ (c : P) (A : P → X →+ X), (∀ s, Continuous (A s)) → (∀ x, Filter.Tendsto (fun s => A s x) (nhds c) (nhds (A c x))) → Function.Injective (A c) → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ s in nhds c, ∀ x, δ * ‖e x‖ ≤ ‖e (A s x)‖ := by
  first | exact @GlobalTheory.CompanionTheory.RealCoordinates.eventually_lower_bound_of_tendsto_injective | exact GlobalTheory.CompanionTheory.RealCoordinates.eventually_lower_bound_of_tendsto_injective | (intros; apply GlobalTheory.CompanionTheory.RealCoordinates.eventually_lower_bound_of_tendsto_injective <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryExtensionOfBlockStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_extension_of_block : ∀ {n D m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (J' : Matrix (Fin m) (Fin m) ℂ) (C : Matrix (Fin n) (Fin D) ℂ) (R : Matrix (Fin n) (Fin m) ℂ), J * J = 1 → Jᴴ = J → Cᴴ * C = 1 → Cᴴ * J * C = 0 → Rᴴ * R = 1 → J * R = R * J' → Cᴴ * R = 0 → C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ = 1 → ∀ U₀ ∈ Matrix.unitaryGroup (Fin m) ℂ, ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ (s : Matrix (Fin n) (Fin n) ℂ) (b b' : Matrix (Fin D) (Fin D) ℂ) (t : Matrix (Fin m) (Fin m) ℂ), s * C = C * b → s * (R * U₀) = (R * U₀) * t → s * (J * C) = (J * C) * b' → b.BlockTriangular id → t.BlockTriangular id → (∀ x y, x < y → b' x y = 0) → (Uᴴ * s * U).BlockTriangular id := by
  first | exact @GlobalTheory.CompanionTheory.WittFrame.unitary_adapted_triangularises | exact GlobalTheory.CompanionTheory.WittFrame.unitary_adapted_triangularises | (intros; apply GlobalTheory.CompanionTheory.WittFrame.unitary_adapted_triangularises <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryFramesPreserveNormSqSumStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_frames_preserve_norm_sq_sum : ∀ (m : ℕ), 1 ≤ m → ∀ (J : Matrix (Fin m) (Fin m) ℂ) (fr fr' : GL (Fin m) ℂ) (ζ ζ' : ℂ) (s s' : ℤˣ), (ζ = 1 ∨ ζ = Complex.I) → (ζ' = 1 ∨ ζ' = Complex.I) → ζ • (fr.1ᵀ * J * fr.1.map star) = ((s : ℤ) : ℂ) • 1 → ζ' • (fr'.1ᵀ * J * fr'.1.map star) = ((s' : ℤ) : ℂ) • 1 → ∀ v : Fin m → ℂ, ∑ a, ‖((fr⁻¹).1 *ᵥ v) a‖ ^ 2 = ∑ a, ‖((fr'⁻¹).1 *ᵥ v) a‖ ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.UnitFrame.normSq_eq_of_unit_frames | exact GlobalTheory.CompanionTheory.UnitFrame.normSq_eq_of_unit_frames | (intros; apply GlobalTheory.CompanionTheory.UnitFrame.normSq_eq_of_unit_frames <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLiftCommutingInvolutionStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_lift_commuting_involution : ∀ {n D m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (J' : Matrix (Fin m) (Fin m) ℂ) (C : Matrix (Fin n) (Fin D) ℂ) (R : Matrix (Fin n) (Fin m) ℂ), J * J = 1 → Jᴴ = J → Cᴴ * C = 1 → Cᴴ * J * C = 0 → Rᴴ * R = 1 → J * R = R * J' → Cᴴ * R = 0 → C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ = 1 → ∀ k₀ ∈ Matrix.unitaryGroup (Fin D) ℂ, ∀ kR ∈ Matrix.unitaryGroup (Fin m) ℂ, kR * J' = J' * kR → ∃ k ∈ Matrix.unitaryGroup (Fin n) ℂ, k * J = J * k ∧ k * C = C * k₀ ∧ kᴴ * C = C * k₀ᴴ ∧ kᴴ * R = R * kRᴴ ∧ kᴴ * (J * C) = (J * C) * k₀ᴴ := by
  first | exact @GlobalTheory.CompanionTheory.UnitaryAssembly.exists_unitary_assemble | exact GlobalTheory.CompanionTheory.UnitaryAssembly.exists_unitary_assemble | (intros; apply GlobalTheory.CompanionTheory.UnitaryAssembly.exists_unitary_assemble <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticOrderPrincipalStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_quadratic_order_principal : ∀ (R O : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R] [CommRing O] (ι : R →+* O) (δ : O) (D : R), δ * δ = ι D → (∀ y : O, ∃ p q : R, y = ι p + ι q * δ) → (∀ p q : R, ι p + ι q * δ = 0 → p = 0 ∧ q = 0) → IsUnit D → IsUnit (2 : R) → (¬ ∃ e : R, D = e * e) → IsPrincipalIdealRing O := by
  first | exact @GlobalTheory.CompanionTheory.QuadraticUnit.isPrincipalIdealRing_of_nonsquare_unit | exact GlobalTheory.CompanionTheory.QuadraticUnit.isPrincipalIdealRing_of_nonsquare_unit | (intros; apply GlobalTheory.CompanionTheory.QuadraticUnit.isPrincipalIdealRing_of_nonsquare_unit <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValThree
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.ValThree

theorem val_three : ∀ (B : Type) [CommRing B] (π : B), VAL π → ∀ (f g : B) (M : ℕ), ∃ e₁ e₂ e : B, IsIdempotentElem e₁ ∧ IsIdempotentElem e₂ ∧ IsIdempotentElem e ∧ e₁ * f ∈ Ideal.span {π ^ M} ∧ (1 - e₁) * π ^ M ∈ Ideal.span {f} ∧ e₂ * g ∈ Ideal.span {π ^ M} ∧ (1 - e₂) * π ^ M ∈ Ideal.span {g} ∧ (1 - e₁) * (1 - e₂) * e * f ∈ Ideal.span {g} ∧ (1 - e₁) * (1 - e₂) * (1 - e) * g ∈ Ideal.span {f} := by
  intro B _ π hV f g M
  have hpair : ∀ x : B, π ^ M ∈ Ideal.span {x, π ^ M} := fun x => Ideal.subset_span (by simp)
  obtain ⟨e₁, he₁, h1a, h1b⟩ := hV f (π ^ M) ⟨M, hpair f⟩
  obtain ⟨e₂, he₂, h2a, h2b⟩ := hV g (π ^ M) ⟨M, hpair g⟩
  have i₁ : e₁ * e₁ = e₁ := he₁
  have i₂ : e₂ * e₂ = e₂ := he₂
  have he₃1 : (1 - e₁) * (1 - e₂) * (1 - e₁) = (1 - e₁) * (1 - e₂) := by
    linear_combination (1 - e₂) * i₁
  have he₃2 : (1 - e₁) * (1 - e₂) * (1 - e₂) = (1 - e₁) * (1 - e₂) := by
    linear_combination (1 - e₁) * i₂
  have he₃ : (1 - e₁) * (1 - e₂) * ((1 - e₁) * (1 - e₂)) = (1 - e₁) * (1 - e₂) := by
    linear_combination (1 - e₂) * he₃1 + he₃2
  generalize hE : (1 - e₁) * (1 - e₂) = E at he₃1 he₃2 he₃ ⊢
  obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.mp h1b
  have hM : π ^ M ∈ Ideal.span {E * f + (1 - E), E * g + (1 - E)} := by
    rw [Ideal.mem_span_pair]
    refine ⟨E * h + (1 - E) * π ^ M, 0, ?_⟩
    linear_combination (h * f - h - π ^ M * f + π ^ M) * he₃ + E * hh + π ^ M * he₃1
  obtain ⟨e, he, ha, hb⟩ := hV (E * f + (1 - E)) (E * g + (1 - E)) ⟨M, hM⟩
  obtain ⟨a, ha'⟩ := Ideal.mem_span_singleton'.mp ha
  obtain ⟨b, hb'⟩ := Ideal.mem_span_singleton'.mp hb
  refine ⟨e₁, e₂, e, he₁, he₂, he, h1a, h1b, h2a, h2b, ?_, ?_⟩
  · rw [hE]
    refine Ideal.mem_span_singleton'.mpr ⟨a * E, ?_⟩
    linear_combination E * ha' - (a * (g - 1) - e * (f - 1)) * he₃
  · rw [hE]
    refine Ideal.mem_span_singleton'.mpr ⟨b * E, ?_⟩
    linear_combination E * hb' - (b * (f - 1) - (1 - e) * (g - 1)) * he₃

end GlobalTheory.CompanionTheory.ValThree
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationPowerIff
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.PowComp

theorem smodEq_span_iff {S : Type} [CommRing S] (a x y : S) (n : ℕ) :
    x ≡ y [SMOD ((Ideal.span {a}) ^ n • ⊤ : Submodule S S)] ↔ a ^ n ∣ x - y := by
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem val_pow_iff {S : Type} [CommRing S] (ϖ : S) (k : ℕ) (hk : k ≠ 0) : Val (ϖ ^ k) ↔ Val ϖ := by
  have hiff : ∀ f g : S, (∃ N, (ϖ ^ k) ^ N ∈ Ideal.span {f, g}) ↔ (∃ N, ϖ ^ N ∈ Ideal.span {f, g}) := by
    intro f g
    constructor
    · rintro ⟨N, hN⟩
      exact ⟨k * N, by rwa [pow_mul]⟩
    · rintro ⟨N, hN⟩
      refine ⟨N, ?_⟩
      rw [← pow_mul]
      have hle : N ≤ k * N := Nat.le_mul_of_pos_left N (Nat.pos_of_ne_zero hk)
      rw [← Nat.add_sub_cancel' hle, pow_add]
      exact Ideal.mul_mem_right _ _ hN
  unfold Val
  constructor
  · intro h f g hfg
    exact h f g ((hiff f g).mpr hfg)
  · intro h f g hfg
    exact h f g ((hiff f g).mp hfg)

theorem isAdicComplete_of_pow {S : Type} [CommRing S] (ϖ : S) (k : ℕ) (hk : k ≠ 0)
    (h : IsAdicComplete (Ideal.span {ϖ ^ k}) S) : IsAdicComplete (Ideal.span {ϖ}) S := by
  have hH : IsHausdorff (Ideal.span {ϖ ^ k}) S := h.toIsHausdorff
  have hP : IsPrecomplete (Ideal.span {ϖ ^ k}) S := h.toIsPrecomplete
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  have H1 : IsHausdorff (Ideal.span {ϖ}) S := by
    refine ⟨fun x hx => hH.haus' x (fun n => ?_)⟩
    have := hx (k * n)
    rw [smodEq_span_iff] at this ⊢
    rwa [← pow_mul]
  have H2 : IsPrecomplete (Ideal.span {ϖ}) S := by
    refine ⟨fun f hf => ?_⟩
    obtain ⟨L, hL⟩ := hP.prec' (fun n => f (k * n)) (fun {m n} hmn => by
      have := hf (Nat.mul_le_mul_left k hmn)
      rw [smodEq_span_iff] at this ⊢
      rwa [← pow_mul])
    refine ⟨L, fun n => ?_⟩
    have h1 := hf (Nat.le_mul_of_pos_left n hkpos)
    have h2 := hL n
    rw [smodEq_span_iff] at h1 h2 ⊢
    rw [← pow_mul] at h2
    have h3 : ϖ ^ n ∣ f (k * n) - L := (pow_dvd_pow ϖ (Nat.le_mul_of_pos_left n hkpos)).trans h2
    have := dvd_add h1 h3
    rwa [sub_add_sub_cancel] at this
  exact { toIsHausdorff := H1, toIsPrecomplete := H2 }

theorem val_pow : ∀ {S : Type} [CommRing S] (ϖ : S) (k : ℕ), k ≠ 0 →
    (Val (ϖ ^ k) ↔ Val ϖ) ∧ (IsAdicComplete (Ideal.span {ϖ ^ k}) S → IsAdicComplete (Ideal.span {ϖ}) S) := by
  intro S _ ϖ k hk
  exact ⟨val_pow_iff ϖ k hk, isAdicComplete_of_pow ϖ k hk⟩

end GlobalTheory.CompanionTheory.PowComp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VandermondeSquares
section
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.CoefId

lemma prod_prs_eq_iter {n : ℕ} (f : Fin n × Fin n → ℂ) :
    ∏ p ∈ prs n, f p = ∏ i : Fin n, ∏ j ∈ Ioi i, f (i, j) := by
  apply Finset.prod_finset_product
  intro p
  simp [prs]

lemma det_rev_vandermonde {n : ℕ} (v : Fin n → ℂ) :
    (Matrix.of fun i j : Fin n => v i ^ (n - 1 - (j : ℕ))).det =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : ℂ) *
        ∏ p ∈ prs n, (v p.2 - v p.1) := by
  have h : (Matrix.of fun i j : Fin n => v i ^ (n - 1 - (j : ℕ))) =
      (Matrix.vandermonde v).submatrix id (Fin.revPerm : Equiv.Perm (Fin n)) := by
    ext i j
    have : n - 1 - (j : ℕ) = n - (j + 1) := by omega
    simp [Matrix.vandermonde_apply, Fin.val_rev, this]
  rw [h, Matrix.det_permute', Matrix.det_vandermonde, prod_prs_eq_iter]

theorem det_vandermonde_sq {n : ℕ} (z : Fin n → ℂ) :
    (Matrix.of fun i j : Fin n => (z i ^ 2) ^ (n - 1 - (j : ℕ))).det =
      (Matrix.of fun i j : Fin n => z i ^ (n - 1 - (j : ℕ))).det *
        ∏ p ∈ prs n, (z p.1 + z p.2) := by
  rw [det_rev_vandermonde (fun i => z i ^ 2), det_rev_vandermonde z, mul_assoc,
    ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro p _
  ring

end GlobalTheory.CompanionTheory.CoefId
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WallLawOfSectionLaw
section
noncomputable section

open Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEis

def cosMul {G : Type} [Group G] (P Γ : Subgroup G) (γ : Γ) : Cos P Γ ≃ Cos P Γ where
  toFun := Quotient.map (· * γ) (by
    intro x y h
    have h' : QuotientGroup.rightRel (P.subgroupOf Γ) x y := h
    show QuotientGroup.rightRel (P.subgroupOf Γ) (x * γ) (y * γ)
    rw [QuotientGroup.rightRel_apply] at h' ⊢
    simpa [mul_assoc] using h')
  invFun := Quotient.map (· * γ⁻¹) (by
    intro x y h
    have h' : QuotientGroup.rightRel (P.subgroupOf Γ) x y := h
    show QuotientGroup.rightRel (P.subgroupOf Γ) (x * γ⁻¹) (y * γ⁻¹)
    rw [QuotientGroup.rightRel_apply] at h' ⊢
    simpa [mul_assoc] using h')
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x => simp [Quotient.map_mk]
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x => simp [Quotient.map_mk]

theorem rep_mk {G : Type} [Group G] {P Γ : Subgroup G} (x : Γ) :
    ∃ δ : G, δ ∈ Γ ∧ δ ∈ P ∧ rep (Quotient.mk _ x : Cos P Γ) = δ * x := by
  have h : QuotientGroup.rightRel (P.subgroupOf Γ) (Quotient.out (Quotient.mk _ x : Cos P Γ)) x :=
    Quotient.mk_out (s := QuotientGroup.rightRel (P.subgroupOf Γ)) x
  rw [QuotientGroup.rightRel_apply] at h
  refine ⟨((x * (Quotient.out (Quotient.mk _ x : Cos P Γ))⁻¹)⁻¹ : Γ), Subtype.property _, ?_, ?_⟩
  · exact (Subgroup.mem_subgroupOf.mp (inv_mem h))
  · simp [rep]

theorem tsum_rep_mul {G : Type} [Group G] {X : Type} [AddCommMonoid X] [TopologicalSpace X]
    {P Γ : Subgroup G} (F : G → X) (hF : ∀ δ ∈ Γ, δ ∈ P → ∀ x, F (δ * x) = F x) {γ : G} (hγ : γ ∈ Γ) (g : G) :
    ∑' q : Cos P Γ, F (rep q * (γ * g)) = ∑' q : Cos P Γ, F (rep q * g) := by
  rw [← Equiv.tsum_eq (cosMul P Γ ⟨γ, hγ⟩) (fun q : Cos P Γ => F (rep q * g))]
  refine tsum_congr fun q => ?_
  have hq : cosMul P Γ ⟨γ, hγ⟩ q = Quotient.mk _ (Quotient.out q * ⟨γ, hγ⟩) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  obtain ⟨δ, h1, h2, h3⟩ := rep_mk (P := P) (Quotient.out q * (⟨γ, hγ⟩ : Γ))
  rw [hq, h3, mul_assoc δ, hF δ h1 h2]
  simp [rep, mul_assoc]

theorem norm_le_of_strip {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {f : ℂ → X}
    (hf : Differentiable ℂ f) {a b B C : ℝ} (hab : a < b)
    (hB : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ B) (ha : ∀ z : ℂ, z.re = a → ‖f z‖ ≤ C)
    (hb : ∀ z : ℂ, z.re = b → ‖f z‖ ≤ C) {z : ℂ} (h1 : a ≤ z.re) (h2 : z.re ≤ b) : ‖f z‖ ≤ C := by
  refine PhragmenLindelof.vertical_strip hf.diffContOnCl ?_ ha hb h1 h2
  refine ⟨0, div_pos Real.pi_pos (sub_pos.2 hab), 0, ?_⟩
  refine Asymptotics.IsBigO.of_bound B ?_
  filter_upwards [mem_inf_of_right (mem_principal_self _)] with w hw
  have := hB w hw.1.le hw.2.le
  simpa using this

theorem entire_eq {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] {f g : ℂ → X}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (R : ℝ) (h : ∀ z : ℂ, R < z.re → f z = g z) : f = g := by
  have hfa : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hga : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg.analyticAt z
  refine hfa.eq_of_eventuallyEq hga (z₀ := ((R + 1 : ℝ) : ℂ)) ?_
  have hopen : IsOpen {z : ℂ | R < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : ((R + 1 : ℝ) : ℂ) ∈ {z : ℂ | R < z.re} := by simp
  filter_upwards [hopen.mem_nhds hmem] with z hz using h z hz

theorem bound_left {A B p q n : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hp : 0 ≤ p) (hq : 0 ≤ q) (hn : 0 ≤ n) :
    A * p * n ≤ (A + B) * (p + q) * n := by
  refine mul_le_mul_of_nonneg_right ?_ hn
  nlinarith [mul_nonneg hA hq, mul_nonneg hB hp, mul_nonneg hB hq]

theorem bound_right {A B p q n : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hp : 0 ≤ p) (hq : 0 ≤ q) (hn : 0 ≤ n) :
    B * q * n ≤ (A + B) * (p + q) * n := by
  refine mul_le_mul_of_nonneg_right ?_ hn
  nlinarith [mul_nonneg hA hq, mul_nonneg hB hp, mul_nonneg hA hp]

section Sec

variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {Γ K P : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)} {η : G → ℝ} {w : W}

theorem sec_left (hP : IsPar Γ K P c)
    (h : ∀ w ∈ secSp K P c ρ, ∀ p ∈ P, ∀ k : K, sec K P c ρ (p * k) w = c p • ρ k⁻¹ w)
    (hw : w ∈ secSp K P c ρ) {δ : G} (h1 : δ ∈ Γ) (h2 : δ ∈ P) (x : G) :
    sec K P c ρ (δ * x) w = sec K P c ρ x w := by
  obtain ⟨p, hp, k, hk, rfl⟩ := hP.iwa x
  have e := h w hw (δ * p) (mul_mem h2 hp) ⟨k, hk⟩
  have e' := h w hw p hp ⟨k, hk⟩
  simp only at e e'
  rw [← mul_assoc, e, e', hP.ch.mul δ h2 p hp, hP.ch.rat δ h1 h2, one_mul]

theorem sec_right (hP : IsPar Γ K P c)
    (h : ∀ w ∈ secSp K P c ρ, ∀ p ∈ P, ∀ k : K, sec K P c ρ (p * k) w = c p • ρ k⁻¹ w)
    (hw : w ∈ secSp K P c ρ) (x : G) (k : K) :
    sec K P c ρ (x * k) w = ρ k⁻¹ (sec K P c ρ x w) := by
  obtain ⟨p, hp, k', hk', rfl⟩ := hP.iwa x
  have e := h w hw p hp (⟨k', hk'⟩ * k)
  have e' := h w hw p hp ⟨k', hk'⟩
  simp only at e'
  have e2 : p * k' * (k : G) = p * (((⟨k', hk'⟩ : K) * k : K) : G) := by simp [mul_assoc]
  rw [e2, e, e', map_smul, mul_inv_rev, map_mul]
  rfl

theorem eis_mul_left (hP : IsPar Γ K P c)
    (h : ∀ w ∈ secSp K P c ρ, ∀ p ∈ P, ∀ k : K, sec K P c ρ (p * k) w = c p • ρ k⁻¹ w)
    (hη : IsHt Γ K P η) (hw : w ∈ secSp K P c ρ) (z : ℂ) {γ : G} (hγ : γ ∈ Γ) (g : G) :
    eis Γ K P c ρ (fun x => z * η x) (γ * g) w = eis Γ K P c ρ (fun x => z * η x) g w := by
  unfold eis
  refine tsum_rep_mul (fun x => Complex.exp (z * η x) • sec K P c ρ x w) ?_ hγ g
  intro δ h1 h2 x
  simp only [sec_left hP h hw h1 h2 x, hη.left δ h2 x, hη.rat δ h1 h2, zero_add]

theorem norm_term_le {M : ℝ} (hb : ∀ g (w : W), ‖sec K P c ρ g w‖ ≤ M * ‖w‖) {l : G → ℝ} {Λ : G → ℂ}
    (hΛ : ∀ x, (Λ x).re = l x) (x : G) (w : W) :
    ‖Complex.exp (Λ x) • sec K P c ρ x w‖ ≤ M * ‖w‖ * Real.exp (l x) := by
  rw [norm_smul, Complex.norm_exp, hΛ, mul_comm]
  exact mul_le_mul_of_nonneg_right (hb x w) (Real.exp_pos _).le

theorem summable_term [CompleteSpace W] {M : ℝ} (hb : ∀ g (w : W), ‖sec K P c ρ g w‖ ≤ M * ‖w‖) {l : G → ℝ}
    (hl : Conv Γ P l) {Λ : G → ℂ} (hΛ : ∀ x, (Λ x).re = l x) (g : G) (w : W) :
    Summable fun q : Cos P Γ => Complex.exp (Λ (rep q * g)) • sec K P c ρ (rep q * g) w :=
  Summable.of_norm_bounded ((hl g).mul_left (M * ‖w‖)) fun q => norm_term_le hb hΛ _ w

theorem norm_eis_le {M : ℝ} (hb : ∀ g (w : W), ‖sec K P c ρ g w‖ ≤ M * ‖w‖) {l : G → ℝ}
    (hl : Conv Γ P l) {Λ : G → ℂ} (hΛ : ∀ x, (Λ x).re = l x) (g : G) (w : W) :
    ‖eis Γ K P c ρ Λ g w‖ ≤ M * ‖w‖ * pos Γ P l g :=
  tsum_of_norm_bounded ((hl g).hasSum.mul_left (M * ‖w‖)) fun q => norm_term_le hb hΛ _ w

theorem pos_nonneg (l : G → ℝ) (g : G) : 0 ≤ pos Γ P l g :=
  tsum_nonneg fun _ => (Real.exp_pos _).le

theorem eis_mul_right [CompleteSpace W] (hP : IsPar Γ K P c)
    (h : ∀ w ∈ secSp K P c ρ, ∀ p ∈ P, ∀ k : K, sec K P c ρ (p * k) w = c p • ρ k⁻¹ w)
    {M : ℝ} (hb : ∀ g (w : W), ‖sec K P c ρ g w‖ ≤ M * ‖w‖)
    (hη : IsHt Γ K P η) (hw : w ∈ secSp K P c ρ) (z : ℂ) (hc : Conv Γ P fun g => z.re * η g) (g : G) (k : K) :
    eis Γ K P c ρ (fun x => z * η x) (g * k) w = ρ k⁻¹ (eis Γ K P c ρ (fun x => z * η x) g w) := by
  have hs := summable_term (Γ := Γ) (l := fun g => z.re * η g) (Λ := fun x => z * η x) hb hc
    (by intro x; simp) g w
  unfold eis
  rw [(ρ k⁻¹).map_tsum hs]
  refine tsum_congr fun q => ?_
  rw [← mul_assoc]
  beta_reduce
  rw [hη.right _ k k.2, sec_right hP h hw, map_smul]

end Sec

theorem wallLaw_of_secLaw : SecLaw → WallLaw := by
  intro hS
  intro G _ _ _ _ _ W _ _ _ K ρ hK hρ Γ P P' c η η' β L R D Op H hP hP' hη hη' hβ hW
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  obtain ⟨h1, -, Ms, hb⟩ := hS G W K ρ hK hρ Γ P c hP
  obtain ⟨-, -, Ms', hb'⟩ := hS G W K ρ hK hρ Γ P' c hP'
  have hdiff : ∀ (g : G) (w : L), Differentiable ℂ fun z => H z g w := fun g w =>
    (hW.hol g).clm_apply (differentiable_const _)
  refine ⟨?_, ?_, ?_⟩
  · intro z γ hγ g
    refine ContinuousLinearMap.ext fun w => ?_
    have e : (fun z => H z (γ * g) w) = fun z => H z g w := by
      refine entire_eq (hdiff _ w) (hdiff _ w) R fun z hz => ?_
      rw [hW.eqR z hz, hW.eqR z hz, eis_mul_left hP h1 hη (hW.le w.2) z hγ g]
    exact congrFun e z
  · intro z g k w
    have e : (fun z => H z (g * k) w) = fun z => ρ k⁻¹ (H z g w) := by
      refine entire_eq (hdiff _ w) ((ρ k⁻¹).differentiable.comp (hdiff g w)) R fun z hz => ?_
      rw [hW.eqR z hz, hW.eqR z hz, eis_mul_right hP h1 hb hη (hW.le w.2) z (hW.convR _ hz) g k, map_smul]
    exact congrFun e z
  · intro a b ha hb₀
    obtain ⟨MD, hD⟩ := hW.dEnt.2 a a
    obtain ⟨MO, hO⟩ := hW.op.2 b b hb₀
    refine ⟨|MD| * |Ms| + |Ms'| * |MO|, ?_⟩
    intro z hz1 hz2 g
    have hab : b < a := by linarith [hW.pos]
    obtain ⟨U, hU, B, hB⟩ := hW.bdd b a g
    have hg : g ∈ U := mem_of_mem_nhds hU
    have hp := pos_nonneg (Γ := Γ) (P := P) (fun x => a * η x) g
    have hq := pos_nonneg (Γ := Γ) (P := P') (fun x => β x - b * η' x) g
    have hA : 0 ≤ |MD| * |Ms| := by positivity
    have hB' : 0 ≤ |Ms'| * |MO| := by positivity
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
    refine norm_le_of_strip (f := fun z => H z g w) (B := B * ‖w‖) (hdiff g w) hab ?_ ?_ ?_ hz1 hz2
    · intro u hu1 hu2
      exact ((H u g).le_opNorm w).trans (mul_le_mul_of_nonneg_right (hB u hu1 hu2 g hg) (norm_nonneg _))
    · intro u hu
      have hO' := hO u hu.ge hu.le
      have hu' : u.re < -R := by rw [hu]; exact hb₀
      have e2 := norm_eis_le (Γ := Γ) hb' (l := fun x => β x - b * η' x) (hW.convL b hb₀)
        (Λ := fun x => (β x : ℂ) - u * η' x) (by intro x; simp [hu]) g (Op u w : W)
      have e3 : ‖(Op u w : W)‖ ≤ |MO| * ‖w‖ := by
        have : ‖(Op u w : W)‖ = ‖Op u w‖ := rfl
        rw [this]
        exact ((Op u).le_opNorm w).trans
          (mul_le_mul_of_nonneg_right (hO'.trans (le_abs_self _)) (norm_nonneg _))
      show ‖H u g w‖ ≤ _
      rw [hW.eqL u hu' g w]
      calc _ ≤ Ms' * ‖(Op u w : W)‖ * _ := e2
        _ ≤ |Ms'| * (|MO| * ‖w‖) * _ := by
            refine mul_le_mul_of_nonneg_right ?_ hq
            exact mul_le_mul (le_abs_self _) e3 (norm_nonneg _) (abs_nonneg _)
        _ = |Ms'| * |MO| * _ * ‖w‖ := by ring
        _ ≤ _ := bound_right hA hB' hp hq (norm_nonneg _)
    · intro u hu
      have hD' := hD u hu.ge hu.le
      have hu' : R < u.re := by rw [hu]; exact ha
      have e2 := norm_eis_le (Γ := Γ) hb (l := fun x => a * η x) (hW.convR a ha)
        (Λ := fun x => u * η x) (by intro x; simp [hu]) g (w : W)
      show ‖H u g w‖ ≤ _
      rw [hW.eqR u hu' g w, norm_smul]
      calc _ ≤ |MD| * (|Ms| * ‖w‖ * _) := by
            refine mul_le_mul (hD'.trans (le_abs_self _)) (e2.trans ?_) (norm_nonneg _) (abs_nonneg _)
            refine mul_le_mul_of_nonneg_right ?_ hp
            exact mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
        _ = |MD| * |Ms| * _ * ‖w‖ := by
            have : ‖w‖ = ‖(w : W)‖ := rfl
            ring
        _ ≤ _ := bound_left hA hB' hp hq (norm_nonneg _)

end GlobalTheory.CompanionTheory.RgEis
end
end

