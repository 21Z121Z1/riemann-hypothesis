import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0052
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.PsiApply
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0046
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
import Formalism.RealPlaceAnalysis.Bundle0001
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CorrESymmCoe
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.Descend

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorEvalFixedOfFixedStatement
section
open TensorProduct CrystallineSemistableComparison.Pb.Psi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_eval_fixed_of_fixed : ∀ {W C₀ : Type} [CommRing W] [CommRing C₀] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (k : K₀ →+* C₀) {B : Type} [Field B] [IsFractionRing W K₀] (ι : C₀ →+* B) (σB : B →+* B) (h : L →+ B) (E : K₀ ⊗[W] L →+ B), (∀ x y, E (x ⊗ₜ y) = ι (k x) * h y) → (∀ w, σB (ι (k (algebraMap W K₀ w))) = ι (k (algebraMap W K₀ w))) → (∀ y, σB (h y) = h y) → ∀ v : K₀ ⊗[W] L, σB (E v) = E v := by
  first | exact @GlobalTheory.CompanionTheory.FrobFix.extension_fixed | exact GlobalTheory.CompanionTheory.FrobFix.extension_fixed | (intros; apply GlobalTheory.CompanionTheory.FrobFix.extension_fixed <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorIdealMapInjective
section
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Descent

theorem mem_of_includeRight_mem_map :
  ∀ (O O' R : Type) [CommRing O] [CommRing O'] [Nontrivial O'] [Algebra O O'] [Module.Free O O'] [CommRing R] [Algebra O R] (I : Ideal R) (x : R), (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) x ∈ Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) I → x ∈ I := by
  intro O O' R _ _ _ _ _ _ _ I x hx
  have hnt : Nontrivial O := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact not_subsingleton O' (Module.subsingleton O O')
  have : Module.FaithfullyFlat O O' := inferInstance
  have : Module.FaithfullyFlat R (R ⊗[O] O') := inferInstance
  let c : O' ⊗[O] R ≃ₐ[O] R ⊗[O] O' := Algebra.TensorProduct.comm O O' R
  have hc : ∀ y : R, c (Algebra.TensorProduct.includeRight y) = algebraMap R (R ⊗[O] O') y := by
    intro y
    simp [c, Algebra.TensorProduct.algebraMap_apply]
  have hle : Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) I ≤
      Ideal.comap c (Ideal.map (algebraMap R (R ⊗[O] O')) I) := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    simp only [Ideal.mem_comap]
    rw [hc]
    exact Ideal.mem_map_of_mem _ hy
  have h1 : algebraMap R (R ⊗[O] O') x ∈ Ideal.map (algebraMap R (R ⊗[O] O')) I := by
    have h2 := hle hx
    simp only [Ideal.mem_comap] at h2
    rwa [hc] at h2
  have h4 := Ideal.comap_map_eq_self_of_faithfullyFlat (B := R ⊗[O] O') I
  rw [← h4]
  exact h1

end GlobalTheory.CompanionTheory.Descent
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsQuot
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

theorem tors_quot : ∀ (p : ℕ) [Fact p.Prime] (B : Type) [CommRing B] (π : B), Pf p B →
    ∃ (B₁ : Type) (_ : CommRing B₁) (q : B →+* B₁), Function.Surjective q ∧ Pf p B₁ ∧
      q π ∈ nonZeroDivisors B₁ ∧ (∀ x, q x = 0 ↔ π * x = 0) ∧ (AIC B → AIC B₁) ∧
      (VAL π → VAL (q π)) := by
  intro p _ B _ π h
  have hp : p.Prime := Fact.out
  obtain ⟨⟨F, hF⟩, hred, -, -, -⟩ := pf_facts p B h

  have hpow : ∀ (N : ℕ) (x : B), π ^ N * x = 0 → π * x = 0 := by
    intro N x e
    apply hred _ (N + 1)
    calc (π * x) ^ (N + 1) = π * x ^ N * (π ^ N * x) := by ring
      _ = 0 := by rw [e, mul_zero]

  have hfrob : ∀ x : B, π * x ^ p = 0 → π * x = 0 := by
    intro x e
    apply hred _ p
    have h1 : p = (p - 1) + 1 := by have := hp.one_lt; omega
    rw [mul_pow]
    conv_lhs => rw [h1, pow_succ π]
    rw [← h1, mul_assoc, e, mul_zero]
  let I : Ideal B :=
    { carrier := {x | π * x = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [mul_add, ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        simp only [Set.mem_setOf_eq, smul_eq_mul] at hx ⊢
        rw [mul_left_comm, hx, mul_zero] }
  have hI : ∀ x, Ideal.Quotient.mk I x = 0 ↔ π * x = 0 := fun x => Ideal.Quotient.eq_zero_iff_mem
  have hsurj : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  refine ⟨B ⧸ I, inferInstance, Ideal.Quotient.mk I, hsurj, ⟨?_, ?_, ?_⟩, ?_, hI, ?_, ?_⟩
  · rw [← map_natCast (Ideal.Quotient.mk I), h.char, map_zero]
  · intro a b e
    obtain ⟨x, rfl⟩ := hsurj a
    obtain ⟨y, rfl⟩ := hsurj b
    simp only at e
    rw [← map_pow, ← map_pow, ← sub_eq_zero, ← map_sub, hI] at e
    rw [← sub_eq_zero, ← map_sub, hI]
    apply hfrob
    have : (x - y) ^ p = x ^ p - y ^ p := by
      rw [← hF, map_sub, hF, hF]
    rw [this, e]
  · intro a
    obtain ⟨x, rfl⟩ := hsurj a
    obtain ⟨y, rfl⟩ := h.bij.2 x
    exact ⟨Ideal.Quotient.mk I y, by simp only [map_pow]⟩
  · rw [mem_nonZeroDivisors_iff_right]
    intro a e
    obtain ⟨x, rfl⟩ := hsurj a
    rw [← map_mul, hI] at e
    rw [hI]
    apply hpow 2
    rw [← e]
    ring
  · intro hA P hP hdeg
    have hl : P ∈ Polynomial.lifts (Ideal.Quotient.mk I) :=
      (Polynomial.map_surjective _ hsurj P).imp (fun Q hQ => by simpa using hQ) |> fun ⟨Q, hQ⟩ =>
        (Polynomial.mem_lifts _).2 ⟨Q, hQ⟩
    obtain ⟨Q, rfl, hQd, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hP
    obtain ⟨x, hx⟩ := hA Q hQm (hQd ▸ hdeg)
    exact ⟨Ideal.Quotient.mk I x, hx.map⟩
  · intro hV f₁ g₁ ⟨N, hN⟩
    obtain ⟨f, rfl⟩ := hsurj f₁
    obtain ⟨g, rfl⟩ := hsurj g₁
    obtain ⟨a₁, b₁, hab⟩ := Ideal.mem_span_pair.1 hN
    obtain ⟨a, rfl⟩ := hsurj a₁
    obtain ⟨b, rfl⟩ := hsurj b₁
    have ht : π * (a * f + b * g - π ^ N) = 0 := by
      rw [← hI, map_sub, map_add, map_mul, map_mul, map_pow, hab, sub_self]
    have hmem : π ^ (N + 1) ∈ Ideal.span {f, g} := by
      refine Ideal.mem_span_pair.2 ⟨π * a, π * b, ?_⟩
      linear_combination ht
    obtain ⟨e, he, h1, h2⟩ := hV f g ⟨N + 1, hmem⟩
    refine ⟨Ideal.Quotient.mk I e, he.map _, ?_, ?_⟩
    · rw [Ideal.mem_span_singleton] at h1 ⊢
      rw [← map_mul]
      exact map_dvd _ h1
    · rw [Ideal.mem_span_singleton] at h2 ⊢
      have : (1 - Ideal.Quotient.mk I e) * Ideal.Quotient.mk I g
          = Ideal.Quotient.mk I ((1 - e) * g) := by
        rw [map_mul, map_sub, map_one]
      rw [this]
      exact map_dvd _ h2

end GlobalTheory.CompanionTheory.PerfectRing
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceDiagonalBlockConjugateFormulaStatement
section
open Finset Matrix PositivityTheory.RgHe.Frame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_diagonal_block_conjugate_formula : ∀ (n : ℕ) (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ) (g X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), IsUnit g.det → X * g = g * diagonal (fun i => ((d i : ℝ) : ℂ)) → (∀ a b, X (e (Sum.inl a)) (e (Sum.inl b)) = if a = b then ((d' a : ℝ) : ℂ) else 0) → ∀ Y : Matrix (Fin n) (Fin n) ℂ, trace (diagonal (fun i => ((d i : ℝ) : ℂ)) * (g⁻¹ * Matrix.reindex e e (Matrix.fromBlocks Y 0 0 0) * g)) = trace (diagonal (fun a => ((d' a : ℝ) : ℂ)) * Y) := by
  first | exact @GlobalTheory.CompanionTheory.RgHeFrame.trace_diagonal_block_conjugate | exact GlobalTheory.CompanionTheory.RgHeFrame.trace_diagonal_block_conjugate | (intros; apply GlobalTheory.CompanionTheory.RgHeFrame.trace_diagonal_block_conjugate <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingBasisEvalStatement
section
open TensorProduct CrystallineSemistableComparison.Pb.Psi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_pairing_basis_eval : ∀ {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)), ∀ {B : Type} [Field B] (ι : C₀ →+* B) (i : A →+* B), (∀ a, ι (c a) = i a) → ∀ (h : L →+ B), (∀ (w : W) y, h (w • y) = i (algebraMap W A w) * h y) → ∀ {m : ℕ} (b : Module.Basis (Fin m) K₀ (K₀ ⊗[W] L)), ∃ E : K₀ ⊗[W] L →+ B, (∀ x y, E (x ⊗ₜ y) = ι (k x) * h y) ∧ ∀ G : A ⊗[W] L →+ B, (∀ a y, G (a ⊗ₜ y) = i a * h y) → ∀ z, G z = ∑ s, ι (T c k hk (b.coord s) z) * E (b s) := by
  first | exact @GlobalTheory.CompanionTheory.FrobFac.T_fac | exact GlobalTheory.CompanionTheory.FrobFac.T_fac | (intros; apply GlobalTheory.CompanionTheory.FrobFac.T_fac <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingFrobeniusCompatStatement
section
open TensorProduct CrystallineSemistableComparison.Pb.Psi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_pairing_frobenius_compat : ∀ {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)), ∀ {F : W →+* W} (φA : A →+* A) (φC : C₀ →+* C₀) (φL : L →ₛₗ[F] L) (fr : K₀ →+* K₀) (φD : K₀ ⊗[W] L →+ K₀ ⊗[W] L), (∀ x y, φD (x ⊗ₜ y) = fr x ⊗ₜ φL y) → ∀ (pT : A ⊗[W] L →+ A ⊗[W] L), (∀ a y, pT (a ⊗ₜ y) = φA a ⊗ₜ φL y) → (∀ a, φC (c a) = c (φA a)) → (∀ x, φC (k x) = k (fr x)) → ∀ {m : ℕ} (b : Module.Basis (Fin m) K₀ (K₀ ⊗[W] L)) (f : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L), T c k hk f (pT z) = ∑ s, φC (T c k hk (b.coord s) z) * k (f (φD (b s))) := by
  first | exact @GlobalTheory.CompanionTheory.FrobPairing.T_phi_expand | exact GlobalTheory.CompanionTheory.FrobPairing.T_phi_expand | (intros; apply GlobalTheory.CompanionTheory.FrobPairing.T_phi_expand <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingGaloisEquivariantStatement
section
open TensorProduct CrystallineSemistableComparison.Pb.Psi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_pairing_galois_equivariant : ∀ {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)), ∀ (σA : A →+* A) (σC : C₀ →+* C₀) (gT : A ⊗[W] L →+ A ⊗[W] L), (∀ a y, gT (a ⊗ₜ y) = σA a ⊗ₜ y) → (∀ a, σC (c a) = c (σA a)) → (∀ x, σC (k x) = k x) → ∀ (f : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L), T c k hk f (gT z) = σC (T c k hk f z) := by
  first | exact @GlobalTheory.CompanionTheory.FrobPairing.T_gal | exact GlobalTheory.CompanionTheory.FrobPairing.T_gal | (intros; apply GlobalTheory.CompanionTheory.FrobPairing.T_gal <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingLTensorNaturalityStatement
section
open TensorProduct CrystallineSemistableComparison.Pb.Psi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_pairing_lTensor_naturality : ∀ {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)) {L' : Type 1} [AddCommGroup L'] [Module W L'] (g : L' →ₗ[W] L) (f : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L'), T c k hk f (LinearMap.lTensor A g z) = T c k hk (f ∘ₗ g.baseChange K₀) z := by
  first | exact @GlobalTheory.CompanionTheory.FrobPsi.T_lTensor | exact GlobalTheory.CompanionTheory.FrobPsi.T_lTensor | (intros; apply GlobalTheory.CompanionTheory.FrobPsi.T_lTensor <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingSmulDualStatement
section
open TensorProduct CrystallineSemistableComparison.Pb.Psi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_pairing_smul_dual : ∀ {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)), ∀ (x : K₀) (f : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L), T c k hk (x • f) z = k x * T c k hk f z := by
  first | exact @GlobalTheory.CompanionTheory.FrobPsi.T_ksmul | exact GlobalTheory.CompanionTheory.FrobPsi.T_ksmul | (intros; apply GlobalTheory.CompanionTheory.FrobPsi.T_ksmul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingSmulLeftStatement
section
open TensorProduct CrystallineSemistableComparison.Pb.Psi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_pairing_smul_left : ∀ {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)), ∀ (f : Module.Dual K₀ (K₀ ⊗[W] L)) (a : A) (z : A ⊗[W] L), T c k hk f (a • z) = c a * T c k hk f z := by
  first | exact @GlobalTheory.CompanionTheory.FrobPairing.T_smul | exact GlobalTheory.CompanionTheory.FrobPairing.T_smul | (intros; apply GlobalTheory.CompanionTheory.FrobPairing.T_smul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransferOfSectionAndWallLaws
section
noncomputable section

open Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgTransfer

theorem transfer : SecLaw → WallLaw → Transfer := by
  intro hSec hWall G _ _ _ _ _ W _ _ _ K ρ hK hρ G' _ _ _ _ _ Γ Q S P₁ P₂ Γ' K' S' P₁' P₂' π ι c₀ c c'
    η₁ η₂ β ξ η₁' η₂' β' ξ' N hK' hL hS hP₁ hP₂ hS' hR₁ hR₂ hη₁ hη₂ hβ hp₁ hp₂ hpβ hpξ
  have hcont := resRep_cont hL hρ
  have c1 : c' 1 = 1 := isCh_one hR₁.ch
  have corr : ∀ {P : Subgroup G} {P' : Subgroup G'}, IsPull Q P P' π c₀ c c' →
      Corr ρ (secSp K P c ρ) (secSp K' P' c' (resRep hL ρ)) :=
    fun h w => mem_secSp_iff hL h c1 ρ w
  have lawG : ∀ {P : Subgroup G} {P' : Subgroup G'}, IsPull Q P P' π c₀ c c' →
      IsPar Γ' K' P' c' → Law K P c ρ :=
    fun h hp => (hSec G W K ρ hK hρ (Γ ⊓ Q) _ c (isPar_pull hL h hp)).1
  have lawG' : ∀ {P' : Subgroup G'}, IsPar Γ' K' P' c' → Law K' P' c' (resRep hL ρ) :=
    fun hp => (hSec G' _ K' (resRep hL ρ) hK' hcont Γ' _ c' hp).1
  obtain ⟨M₁, bd₁⟩ := (hSec G' _ K' (resRep hL ρ) hK' hcont Γ' _ c' hR₁).2.2
  obtain ⟨M₂, bd₂⟩ := (hSec G' _ K' (resRep hL ρ) hK' hcont Γ' _ c' hR₂).2.2
  have equi : ∀ {L' : Submodule ℂ (fixSp K Q π c₀ ρ)} {R : ℝ} {D : ℂ → ℂ}
      {Op' : ℂ → (L' →L[ℂ] secSp K' P₂' c' (resRep hL ρ))}
      {H' : ℂ → G' → (L' →L[ℂ] fixSp K Q π c₀ ρ)},
      Wall Γ' K' P₁' P₂' c' η₁' η₂' β' (resRep hL ρ) L' R D Op' H' →
      ∀ z (g : G') (k : K') (w : L'), H' z (g * k) w = resRep hL ρ k⁻¹ (H' z g w) :=
    fun hw => (hWall G' _ K' (resRep hL ρ) hK' hcont Γ' P₁' P₂' c' η₁' η₂' β' _ _ _ _ _ hR₁ hR₂
      hη₁ hη₂ hβ hw).2.1
  have key : ∀ {L : Submodule ℂ W} {L' : Submodule ℂ (fixSp K Q π c₀ ρ)} (hLL : Corr ρ L L')
      {R : ℝ} {D : ℂ → ℂ} {Op' : ℂ → (L' →L[ℂ] secSp K' P₂' c' (resRep hL ρ))}
      {H' : ℂ → G' → (L' →L[ℂ] fixSp K Q π c₀ ρ)},
      Wall Γ' K' P₁' P₂' c' η₁' η₂' β' (resRep hL ρ) L' R D Op' H' →
      Wall (Γ ⊓ Q) K P₁ P₂ c η₁ η₂ β ρ L R D (fun z => cj (corrE hLL) (corrE (corr hP₂)) (Op' z))
        (hOf hL ρ (corrE hLL) H') :=
    fun hLL _ _ _ _ hw => wall_pull hK hL hρ hP₁ hP₂ hR₁ hR₂ hη₁ hη₂ hβ hp₁ hp₂ hpβ (lawG hP₁ hR₁)
      (lawG hP₂ hR₂) (lawG' hR₁) (lawG' hR₂) bd₁ bd₂ hLL (corr hP₁) (corr hP₂) hw (equi hw)
  have hCS := corr hS
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨R, D, Op', H', hw⟩ := h _ (resRep hL ρ) hcont
    exact ⟨R, D, _, _, key (corr hP₁) hw⟩
  · obtain ⟨R, D, Op', H', hw, ⟨a, ha, hH0⟩, O', hO, hOp⟩ := h _ (resRep hL ρ) hcont
    refine ⟨R, D, _, _, key hCS hw, ⟨a, ha, fun g w => ?_⟩,
      fun z => cj (corrE hCS) (corrE (corr hP₂)) (O' z),
      leftGood_comp (cj (corrE hCS) (corrE (corr hP₂))) hO, fun z hz => ?_⟩
    · obtain ⟨q, k, rfl⟩ := exists_qk hL g
      rw [hOf_eq hL ρ _ (equi hw), hH0, map_smul]
      have := sec_pull hL hS hS'.iwa (lawG hS hS') (lawG' hS') (corrE hCS w).2 w.2 q k
      exact congrArg (fun u => a • u) this.symm
    · show cj (corrE hCS) (corrE (corr hP₂)) (Op' z) = z • cj (corrE hCS) (corrE (corr hP₂)) (O' z)
      rw [hOp z hz, map_smul]
  · obtain ⟨R, D, Op', H', hw, hd, T', hT⟩ := h _ (resRep hL ρ) hcont
    refine ⟨R, D, _, _, key (corr hP₁) hw, hd, cj (corrE (corr hP₁)) (corrE hCS) T', fun g w => ?_⟩
    obtain ⟨q, k, rfl⟩ := exists_qk hL g
    rw [hOf_eq hL ρ _ (equi hw), hT, map_smul, hpξ q k k.2]
    have := sec_pull hL hS hS'.iwa (lawG hS hS') (lawG' hS') (T' (corrE (corr hP₁) w)).2
      (cj (corrE (corr hP₁)) (corrE hCS) T' w).2 q k
    exact congrArg (fun u => Complex.exp (ξ' (π q)) • u) this.symm

end GlobalTheory.CompanionTheory.RgTransfer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistOfSectionLaw
section
noncomputable section

namespace GlobalTheory.CompanionTheory.RgEisTwist

open PositivityTheory.RgEis

variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {Γ K : Subgroup G} {c₀ : G → ℂ}

lemma ch_mul (h : IsCh Γ ⊤ c₀) (a b : G) : c₀ (a * b) = c₀ a * c₀ b :=
  h.mul a (Subgroup.mem_top a) b (Subgroup.mem_top b)

lemma ch_one (h : IsCh Γ ⊤ c₀) : c₀ 1 = 1 :=
  h.rat 1 (one_mem _) (Subgroup.mem_top 1)

lemma ch_rat_mul (h : IsCh Γ ⊤ c₀) {γ : G} (hγ : γ ∈ Γ) (g : G) : c₀ (γ * g) = c₀ g := by
  rw [ch_mul h, h.rat γ hγ (Subgroup.mem_top γ), one_mul]

lemma ch_norm (h : IsCh Γ ⊤ c₀) (g : G) : ‖c₀ g‖ = 1 :=
  h.norm g (Subgroup.mem_top g)

lemma ch_cont (h : IsCh Γ ⊤ c₀) : Continuous c₀ := by
  have h' := h.cont
  rw [Subgroup.coe_top] at h'
  exact continuousOn_univ.mp h'

def twRep (h : IsCh Γ ⊤ c₀) (K : Subgroup G) (ρ : K →* (W →L[ℂ] W)) : K →* (W →L[ℂ] W) where
  toFun r := c₀ r • ρ r
  map_one' := by simp [ch_one h]
  map_mul' a b := by
    ext w
    simp [ch_mul h, smul_smul, mul_comm]

lemma twRep_apply (h : IsCh Γ ⊤ c₀) (ρ : K →* (W →L[ℂ] W)) (r : K) :
    twRep h K ρ r = c₀ r • ρ r := rfl

lemma twRep_cont (h : IsCh Γ ⊤ c₀) {ρ : K →* (W →L[ℂ] W)} (hρ : Continuous ρ) :
    Continuous (twRep h K ρ) :=
  ((ch_cont h).comp continuous_subtype_val).smul hρ

lemma secSp_twist (h : IsCh Γ ⊤ c₀) (ρ : K →* (W →L[ℂ] W)) (P : Subgroup G) (c : G → ℂ) :
    secSp K P (c * c₀) ρ = secSp K P c (twRep h K ρ) := by
  ext w
  have key : ∀ r : K, (c * c₀) (r : G) • ρ r w = c (r : G) • twRep h K ρ r w := fun r => by
    rw [twRep_apply, ContinuousLinearMap.smul_apply, smul_smul, Pi.mul_apply]
  change (∀ r : K, (r : G) ∈ P → (c * c₀) (r : G) • ρ r w = w) ↔
    ∀ r : K, (r : G) ∈ P → c (r : G) • twRep h K ρ r w = w
  simp only [key]

lemma sec_twist (h : IsCh Γ ⊤ c₀) (ρ : K →* (W →L[ℂ] W)) (P : Subgroup G) (c : G → ℂ) (g : G) :
    sec K P (c * c₀) ρ g = c₀ g • sec K P c (twRep h K ρ) g := by
  unfold sec
  by_cases hk : ∃ k : K, g * (k : G)⁻¹ ∈ P
  · rw [dif_pos hk, dif_pos hk, twRep_apply, Pi.mul_apply, Subgroup.coe_inv, ch_mul h g, smul_smul, smul_smul]
    congr 1
    ring
  · rw [dif_neg hk, dif_neg hk, smul_zero]

lemma eis_twist (h : IsCh Γ ⊤ c₀) (ρ : K →* (W →L[ℂ] W)) (P : Subgroup G) (c : G → ℂ) (Λ : G → ℂ)
    (g : G) (w : W) :
    eis Γ K P (c * c₀) ρ Λ g w = c₀ g • eis Γ K P c (twRep h K ρ) Λ g w := by
  unfold eis
  rw [← tsum_const_smul'']
  refine tsum_congr fun q => ?_
  have hq : rep q ∈ Γ := (Quotient.out q).2
  rw [sec_twist h, ContinuousLinearMap.smul_apply, ch_rat_mul h hq, smul_comm]

def castL {A B : Submodule ℂ W} (e : A = B) : A →L[ℂ] B :=
  (ContinuousLinearEquiv.ofEq A B e).toContinuousLinearMap

lemma leftGood_cast {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {A B : Submodule ℂ W} (e : A = B)
    {Op : ℂ → (X →L[ℂ] A)} {a : ℝ} (hO : LeftGood Op a) :
    LeftGood (fun z => (castL e).comp (Op z)) a := by
  subst e
  have hid : (fun z => (castL (rfl : A = A)).comp (Op z)) = Op := by
    funext z
    ext x
    rfl
  rwa [hid]

lemma wall_twist (h : IsCh Γ ⊤ c₀) {P P' : Subgroup G} {c : G → ℂ} {η η' β : G → ℝ}
    {ρ : K →* (W →L[ℂ] W)} {L : Submodule ℂ W} {R : ℝ} {D : ℂ → ℂ}
    {Op : ℂ → (L →L[ℂ] secSp K P' c (twRep h K ρ))} {H : ℂ → G → (L →L[ℂ] W)}
    (hw : Wall Γ K P P' c η η' β (twRep h K ρ) L R D Op H) :
    Wall Γ K P P' (c * c₀) η η' β ρ L R D
      (fun z => (castL (secSp_twist h ρ P' c).symm).comp (Op z)) (fun z g => c₀ g • H z g) where
  le := by
    rw [secSp_twist h ρ P c]
    exact hw.le
  pos := hw.pos
  convR := hw.convR
  convL := hw.convL
  dEnt := hw.dEnt
  dNe := hw.dNe
  op := leftGood_cast _ hw.op
  hol g := (hw.hol g).const_smul (c₀ g)
  cont := ((ch_cont h).comp continuous_snd).smul hw.cont
  bdd b a g := by
    obtain ⟨U, hU, M, hM⟩ := hw.bdd b a g
    refine ⟨U, hU, M, fun z h1 h2 g' hg' => ?_⟩
    rw [norm_smul, ch_norm h, one_mul]
    exact hM z h1 h2 g' hg'
  eqR z hz g w := by
    rw [ContinuousLinearMap.smul_apply, hw.eqR z hz g w, eis_twist h, smul_comm]
  eqL z hz g w := by
    rw [ContinuousLinearMap.smul_apply, hw.eqL z hz g w, eis_twist h]
    rfl

theorem twist : SecLaw → Twist := by
  intro _ G _ _ _ _ _ Γ K S P P' c c₀ η η' β ξ N _ h _ _ _
  refine ⟨fun hA W _ _ _ ρ hρ => ?_, fun hA W _ _ _ ρ hρ => ?_, fun hA W _ _ _ ρ hρ => ?_⟩
  · obtain ⟨R, D, Op, H, hw⟩ := hA W (twRep h K ρ) (twRep_cont h hρ)
    unfold HasWall
    rw [secSp_twist h ρ P c]
    exact ⟨R, D, _, _, wall_twist h hw⟩
  · obtain ⟨R, D, Op, H, hw, ⟨a, ha0, ha⟩, O, hO, hOp⟩ := hA W (twRep h K ρ) (twRep_cont h hρ)
    unfold HasFirst
    rw [secSp_twist h ρ S c]
    refine ⟨R, D, _, _, wall_twist h hw, ⟨a, ha0, fun g w => ?_⟩,
      fun z => (castL (secSp_twist h ρ P' c).symm).comp (O z), leftGood_cast _ hO, fun z hz => ?_⟩
    · rw [ContinuousLinearMap.smul_apply, ha g w, sec_twist h, ContinuousLinearMap.smul_apply, smul_comm]
    · change (castL (secSp_twist h ρ P' c).symm).comp (Op z) = _
      rw [hOp z hz, ContinuousLinearMap.comp_smul]
  · obtain ⟨R, D, Op, H, hw, hd, T, hT⟩ := hA W (twRep h K ρ) (twRep_cont h hρ)
    unfold HasLast
    rw [secSp_twist h ρ P c]
    refine ⟨R, D, _, _, wall_twist h hw, hd,
      (castL (secSp_twist h ρ S c).symm).comp T, fun g w => ?_⟩
    rw [ContinuousLinearMap.smul_apply, hT g w, sec_twist h, ContinuousLinearMap.smul_apply, smul_comm]
    rfl

end GlobalTheory.CompanionTheory.RgEisTwist
end
end

