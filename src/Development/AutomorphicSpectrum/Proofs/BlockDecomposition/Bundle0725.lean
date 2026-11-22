import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0561
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0388
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0410
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0454
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0044
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0490
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0403
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0398
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0420
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0418
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0712
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0469
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0715
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0701
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0716
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0717
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0641
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0699
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0718
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionProductRankZeroRight

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothIterPhi
section
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

namespace GlobalTheory.CompanionTheory.BZCuspPair

section Proofs
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem irrAdm : GlobalTheory.Published.IrreducibleAdmissibleGL := fun k _ _ _ _ n V _ _ π hs hi =>
  (GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k).1 (Fin n) V π hs hi

theorem twJ_congr {G G' V : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}
    {π' : Representation ℂ G' V} {N : Subgroup G} {N' : Subgroup G'} {θ : N →* ℂˣ} {θ' : N' →* ℂˣ}
    (h : twKer π N θ = twKer π' N' θ') :
    Nontrivial (TwJacquet π N θ) ↔ Nontrivial (TwJacquet π' N' θ') := by
  rw [Submodule.Quotient.nontrivial_iff, Submodule.Quotient.nontrivial_iff, h]

theorem exists_highest (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (N : ℕ) {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hn : Nontrivial V)
    (hg : ¬ IsGenericFor ψ π) :
    ∃ n, 0 < n ∧ n < N ∧ Nontrivial (TwJacquet π (derUnip k N n) (derChar k ψ N n)) ∧
      ∀ m < n, Subsingleton (TwJacquet π (derUnip k N m) (derChar k ψ N m)) := by
  have h0 : ¬ Nontrivial (TwJacquet π (derUnip k N 0) (derChar k ψ N 0)) := fun h =>
    hg ((twJ_congr (GlobalTheory.T.derivative_zero_whittaker_kernel k ψ N V π)).1 h)
  rcases N with _ | m
  · exfalso
    refine hg ?_
    show Nontrivial (V ⧸ twKer π (unipB k (Fin 0)) (whitChar ψ 0))
    have hb : twKer π (unipB k (Fin 0)) (whitChar ψ 0) = ⊥ := by
      unfold twKer
      rw [Submodule.span_eq_bot]
      rintro w ⟨u, v, rfl⟩
      have hu : (u : GL (Fin 0) k) = 1 := Subsingleton.elim _ _
      have hu' : u = 1 := Subtype.ext hu
      subst hu'
      simp
    rw [hb]
    exact (Submodule.quotEquivOfEqBot ⊥ rfl).toEquiv.nontrivial
  have hex : ∃ n, n ≤ m ∧ Nontrivial (TwJacquet π (derUnip k (m + 1) n) (derChar k ψ (m + 1) n)) := by
    obtain ⟨n, hnm, h⟩ := GlobalTheory.T.exists_nontrivial_derivative k ψ hc h1 m V (resM k π).ρ (isSmooth_comp hs _ continuous_subtype_val) hn
    exact ⟨n, hnm, (twJ_congr (GlobalTheory.T.restriction_mirabolic_twisted_kernel k ψ m n V π)).1 h⟩
  classical
  have hmin := fun (l : ℕ) (hl : l < Nat.find hex) => Nat.find_min hex hl
  obtain ⟨hle, hnt⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, Nat.pos_of_ne_zero fun e => h0 (e ▸ hnt), by omega, hnt, fun l hl => ?_⟩
  have := hmin l hl
  rw [not_and] at this
  exact not_nontrivial_iff_subsingleton.1 (this (by omega))

theorem isSmooth_iterPhi (ψ : AddChar k Circle) (n : ℕ) : ∀ (j : ℕ) (τ : MRep k (n + j)), IsSmooth τ.ρ →
    IsSmooth (iterPhi k ψ j τ).ρ
  | 0, _, h => h
  | j + 1, τ, h => isSmooth_iterPhi ψ n j (MRep.phiM k ψ τ) (GlobalTheory.T.smooth_phi_minus k ψ _ _ τ.ρ h)

theorem isSmooth_resM {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin (n + 1)) k) V}
    (h : IsSmooth π) : IsSmooth (resM k π).ρ := isSmooth_comp h _ continuous_subtype_val

theorem isSmooth_deriv (ψ : AddChar k Circle) {n : ℕ} (j : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin (n + j + 1)) k) V} (h : IsSmooth π) : IsSmooth (GlobalTheory.BZMir.deriv k ψ j π) :=
  GlobalTheory.T.smooth_psi_minus k _ _ _ (isSmooth_iterPhi ψ n j _ (isSmooth_resM h))

theorem iterPhi_derUnip (ψ : AddChar k Circle) (n₂ n' : ℕ) (hn : n₂ ≤ n') : ∀ (j : ℕ) (τ : MRep k (n' + j)),
    Nonempty (TwJacquet (iterPhi k ψ j τ).ρ (derUnipM k n' n₂) (derCharM k ψ n' n₂) ≃ₗ[ℂ]
      TwJacquet τ.ρ (derUnipM k (n' + j) n₂) (derCharM k ψ (n' + j) n₂))
  | 0, _ => ⟨LinearEquiv.refl _ _⟩
  | j + 1, τ => by
    obtain ⟨e₁⟩ := iterPhi_derUnip ψ n₂ n' hn j (MRep.phiM k ψ τ)
    obtain ⟨e₂⟩ := GlobalTheory.T.twisted_jacquet_phi_minus_equiv k ψ (n' + j) n₂ (by omega) _ τ.ρ
    exact ⟨e₁.trans e₂⟩

theorem phi_vanish (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (n j : ℕ) {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin (n + 1 + j + 1)) k) V) (hs : IsSmooth π)
    (hlow : ∀ m < n + 1, Subsingleton (TwJacquet π (derUnip k (n + 1 + j + 1) m) (derChar k ψ (n + 1 + j + 1) m))) :
    Subsingleton (TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k (n + 1)) (mirChar k ψ n)) := by
  by_contra hcon
  have hnt : Nontrivial (TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k (n + 1)) (mirChar k ψ n)) :=
    not_subsingleton_iff_nontrivial.1 hcon
  have hT := isSmooth_iterPhi ψ (n + 1) j (resM k π) (isSmooth_resM hs)
  obtain ⟨m, hm, h⟩ := GlobalTheory.T.exists_nontrivial_derivative k ψ hc h1 n _ (phiMinus k ψ (iterPhi k ψ j (resM k π)).ρ)
    (GlobalTheory.T.smooth_phi_minus k ψ _ _ _ hT) hnt
  obtain ⟨e₂⟩ := GlobalTheory.T.twisted_jacquet_phi_minus_equiv k ψ n m hm _ (iterPhi k ψ j (resM k π)).ρ
  obtain ⟨e₁⟩ := iterPhi_derUnip ψ m (n + 1) (by omega) j (resM k π)
  have h3 : Nontrivial (TwJacquet (resM k π).ρ (derUnipM k (n + 1 + j) m) (derCharM k ψ (n + 1 + j) m)) :=
    (e₂.trans e₁).symm.toEquiv.nontrivial
  have h4 := (twJ_congr (GlobalTheory.T.restriction_mirabolic_twisted_kernel k ψ (n + 1 + j) m V π)).1 h3
  exact not_subsingleton_iff_nontrivial.2 h4 (hlow m (by omega))

theorem deriv_nontrivial (ψ : AddChar k Circle) (n j : ℕ) {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin (n + 1 + j + 1)) k) V)
    (h : Nontrivial (TwJacquet π (derUnip k (n + 1 + j + 1) (n + 1)) (derChar k ψ (n + 1 + j + 1) (n + 1)))) :
    Nontrivial (TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k (n + 1)) 1) := by
  obtain ⟨e⟩ := GlobalTheory.T.twisted_jacquet_iterated_phi_equiv k ψ (n + 1) j (resM k π)
  have h2 := (twJ_congr (GlobalTheory.T.restriction_mirabolic_twisted_kernel k ψ (n + 1 + j) (n + 1) V π)).2 h
  exact e.toEquiv.nontrivial

theorem detChar_zero {n : ℕ} (g : GL (Fin n) k) : ((detChar (Fin n) (absPow k ((0 : ℕ) : ℂ)) g : ℂˣ) : ℂ) = 1 := by
  have : absPow k ((0 : ℕ) : ℂ) = 1 := by
    rw [Nat.cast_zero, absPow_zero]
  rw [this]
  simp [detChar]

set_option maxHeartbeats 2000000 in

theorem pair_iter (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (n : ℕ) : ∀ (j s : ℕ) (τ τ' : MRep k (n + 1 + j)),
    IsSmooth τ.ρ → IsSmooth τ'.ρ → ∀ B : τ.V →ₗ[ℂ] τ'.V →ₗ[ℂ] ℂ,
    (∀ (p : Mir k (n + 1 + j)) v v', B (τ.ρ p v) (τ'.ρ p v') =
      ((detChar (Fin (n + 1 + j + 1)) (absPow k (s : ℂ)) (p : GL (Fin (n + 1 + j + 1)) k) : ℂˣ) : ℂ) * B v v') →
    (∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) →
    Subsingleton (TwJacquet (iterPhi k ψ j τ).ρ (MirUin k (n + 1)) (mirChar k ψ n)) →
    ∃ B' : TwJacquet (iterPhi k ψ j τ).ρ (MirUin k (n + 1)) 1 →ₗ[ℂ]
        TwJacquet (iterPhi k ψ⁻¹ j τ').ρ (MirUin k (n + 1)) 1 →ₗ[ℂ] ℂ,
      (∀ (g : GL (Fin (n + 1)) k) w w', B' (derivM k ψ j τ g w) (derivM k ψ⁻¹ j τ' g w') =
        ((detChar (Fin (n + 1)) (absPow k ((s + j : ℕ) : ℂ)) g : ℂˣ) : ℂ) * B' w w') ∧
      (∀ w, w ≠ 0 → ∃ w', B' w w' ≠ 0)
  | 0, s, τ, τ', hs, hs', B, hB, hn, hv =>
    GlobalTheory.T.invariant_pairing_mirabolic_vanishing k ψ hc h1 n s τ.V τ'.V τ.ρ τ'.ρ hs hs' B hB hn hv
  | j + 1, s, τ, τ', hs, hs', B, hB, hn, hv => by
    obtain ⟨B₁, hB₁, hn₁⟩ := GlobalTheory.T.invariant_pairing_mirabolic_smooth k ψ hc h1 (n + 1 + j) s _ _ τ.ρ τ'.ρ hs hs' B hB hn
    obtain ⟨B₂, hB₂, hn₂⟩ := pair_iter ψ hc h1 n j (s + 1) (MRep.phiM k ψ τ) (MRep.phiM k ψ⁻¹ τ')
      (GlobalTheory.T.smooth_phi_minus k ψ _ _ _ hs) (GlobalTheory.T.smooth_phi_minus k ψ⁻¹ _ _ _ hs') B₁ hB₁ hn₁ hv
    refine ⟨B₂, fun g w w' => ?_, hn₂⟩
    have e : s + (j + 1) = s + 1 + j := by omega
    rw [e]
    exact hB₂ g w w'

set_option maxHeartbeats 2000000 in

theorem pair_deriv (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (n j : ℕ) {V V' : Type} [AddCommGroup V]
    [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (π : Representation ℂ (GL (Fin (n + 1 + j + 1)) k) V)
    (π' : Representation ℂ (GL (Fin (n + 1 + j + 1)) k) V') (hs : IsSmooth π) (hs' : IsSmooth π')
    (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (hB : ∀ g v v', B (π g v) (π' g v') = B v v') (hn : ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0)
    (hv : Subsingleton (TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k (n + 1)) (mirChar k ψ n))) :
    ∃ B' : TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k (n + 1)) 1 →ₗ[ℂ]
        TwJacquet (iterPhi k ψ⁻¹ j (resM k π')).ρ (MirUin k (n + 1)) 1 →ₗ[ℂ] ℂ,
      (∀ (g : GL (Fin (n + 1)) k) w w', B' (GlobalTheory.BZMir.deriv k ψ j π g w) (GlobalTheory.BZMir.deriv k ψ⁻¹ j π' g w') =
        ((detChar (Fin (n + 1)) (absPow k (j : ℂ)) g : ℂˣ) : ℂ) * B' w w') ∧
      (∀ w, w ≠ 0 → ∃ w', B' w w' ≠ 0) := by
  have hB0 : ∀ (p : Mir k (n + 1 + j)) v v', B ((resM k π).ρ p v) ((resM k π').ρ p v') =
      ((detChar (Fin (n + 1 + j + 1)) (absPow k ((0 : ℕ) : ℂ)) (p : GL (Fin (n + 1 + j + 1)) k) : ℂˣ) : ℂ) * B v v' := by
    intro p v v'
    rw [detChar_zero, one_mul]
    exact hB (p : GL (Fin (n + 1 + j + 1)) k) v v'
  obtain ⟨B', h2, h3⟩ := pair_iter ψ hc h1 n j 0 (resM k π) (resM k π') (isSmooth_resM hs) (isSmooth_resM hs') B
    hB0 hn hv
  refine ⟨B', fun g w w' => ?_, h3⟩
  have := h2 g w w'
  rwa [Nat.zero_add] at this

end Proofs
end GlobalTheory.CompanionTheory.BZCuspPair
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSectionClosedCellStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_section_closed_cell : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {i t : ℕ} (h : (i + 1) + t = i + t + 1), 0 < t → LocSec (parab k (two (stdSum h))) (Mir k (i + t)) 1 := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.locSec_parab_mir_one | exact GlobalTheory.CompanionTheory.BZRes.locSec_parab_mir_one | (intros; apply GlobalTheory.CompanionTheory.BZRes.locSec_parab_mir_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSectionOpenCellStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_section_open_cell : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {i t : ℕ} (h : (i + 1) + t = i + t + 1), LocSec (parab k (two (stdSum h))) (Mir k (i + t)) (wGL k h) := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.locSec_wGL | exact GlobalTheory.CompanionTheory.BZRes.locSec_wGL | (intros; apply GlobalTheory.CompanionTheory.BZRes.locSec_wGL <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemHPGIffConjugateParabolicStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_HPG_iff_conjugate_parabolic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {i t : ℕ} (h : (i + 1) + t = i + t + 1) (p : Mir k (i + t)), p ∈ HPG k i t ↔ wGL k h * (p : GL (Fin (i + t + 1)) k) * (wGL k h)⁻¹ ∈ parab k (two (stdSum h)) := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.mem_HPG_iff_conj_mem_parab | exact GlobalTheory.CompanionTheory.BZRes.mem_HPG_iff_conj_mem_parab | (intros; apply GlobalTheory.CompanionTheory.BZRes.mem_HPG_iff_conj_mem_parab <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicClosedStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_closed : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), IsClosed (Mir k n : Set (GL (Fin (n + 1)) k)) := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.MirClosed.isClosed_mirabolic | exact GlobalTheory.CompanionTheory.BZRes.MirClosed.isClosed_mirabolic | (intros; apply GlobalTheory.CompanionTheory.BZRes.MirClosed.isClosed_mirabolic <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneFormMapEqKaehlerDifferentialMap
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hodge.FormBC

theorem subsingleton_of_tensor {R : Type} [CommRing R] {Q : Type} [AddCommGroup Q] [Module R Q] [Module.Finite R Q]
    {J : Type} (B : J → Type) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (hcov : ∀ p : PrimeSpectrum R, ∃ (i : J) (q : PrimeSpectrum (B i)), PrimeSpectrum.comap (algebraMap R (B i)) q = p)
    (h : ∀ i, Subsingleton (B i ⊗[R] Q)) : Subsingleton Q := by
  by_contra hQ
  rw [not_subsingleton_iff_nontrivial] at hQ
  obtain ⟨p, hp⟩ := Module.nonempty_support_of_nontrivial (R := R) (M := Q)
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hp
  obtain ⟨i, q, hq⟩ := hcov p
  have := h i
  let κ := q.asIdeal.ResidueField
  have h1 : Subsingleton (κ ⊗[R] Q) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R (B i) κ κ Q).symm.subsingleton
  have hpq : p.asIdeal = q.asIdeal.comap (algebraMap R (B i)) := by rw [← hq]; rfl
  letI : Algebra p.asIdeal.ResidueField κ :=
    (Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R (B i)) hpq).toAlgebra
  haveI : IsScalarTower R p.asIdeal.ResidueField κ := .of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R (B i) κ]
    exact (Ideal.ResidueField.map_algebraMap p.asIdeal q.asIdeal (algebraMap R (B i)) hpq r).symm
  have h2 : Nontrivial (κ ⊗[p.asIdeal.ResidueField] (p.asIdeal.ResidueField ⊗[R] Q)) :=
    Module.FaithfullyFlat.lTensor_nontrivial _ _ _
  exact not_subsingleton _
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R p.asIdeal.ResidueField κ κ Q).subsingleton

theorem bijective_of_lTensor {R : Type} [CommRing R] {N M : Type} [AddCommGroup N] [Module R N] [AddCommGroup M]
    [Module R M] [Module.Finite R N] [Module.Finite R M] [Module.Projective R M] (T : N →ₗ[R] M)
    {J : Type} (B : J → Type) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (hcov : ∀ p : PrimeSpectrum R, ∃ (i : J) (q : PrimeSpectrum (B i)), PrimeSpectrum.comap (algebraMap R (B i)) q = p)
    (h : ∀ i, Function.Bijective (T.lTensor (B i))) : Function.Bijective T := by
  have hs : Function.Surjective T := by
    have hQ : Subsingleton (M ⧸ LinearMap.range T) := subsingleton_of_tensor B hcov fun i ↦ by
      refine ⟨fun a b ↦ ?_⟩
      have key : ∀ x : B i ⊗[R] (M ⧸ LinearMap.range T), x = 0 := fun x ↦ by
        obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective (B i) (Submodule.mkQ_surjective (LinearMap.range T)) x
        obtain ⟨z, rfl⟩ := (h i).2 y
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, show (LinearMap.range T).mkQ ∘ₗ T = 0 from
          LinearMap.range_mkQ_comp T, LinearMap.lTensor_zero, LinearMap.zero_apply]
      rw [key a, key b]
    exact fun m ↦ LinearMap.mem_range.1 ((Submodule.Quotient.mk_eq_zero (LinearMap.range T)).1 (Subsingleton.elim (Submodule.Quotient.mk m) 0))
  obtain ⟨u, hu⟩ := Module.projective_lifting_property T LinearMap.id hs
  let r : N →ₗ[R] LinearMap.ker T := LinearMap.codRestrict _ (LinearMap.id - u ∘ₗ T) fun x ↦ by
    have := LinearMap.congr_fun hu (T x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp [this]
  have hr : r ∘ₗ (LinearMap.ker T).subtype = LinearMap.id := by
    ext x
    simp [r]
  have hrs : Function.Surjective r := fun x ↦ ⟨x.1, LinearMap.congr_fun hr x⟩
  haveI : Module.Finite R (LinearMap.ker T) := Module.Finite.of_surjective r hrs
  have hK : Subsingleton (LinearMap.ker T) := subsingleton_of_tensor B hcov fun i ↦ by
    have key : ∀ x : B i ⊗[R] LinearMap.ker T, x = 0 := fun x ↦ by
      have e : (LinearMap.ker T).subtype.lTensor (B i) x = 0 := (h i).1 <| by
        rw [map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
          show T ∘ₗ (LinearMap.ker T).subtype = 0 from LinearMap.ext fun x ↦ x.2, LinearMap.lTensor_zero,
          LinearMap.zero_apply]
      have e2 := congrArg (r.lTensor (B i)) e
      rwa [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hr, LinearMap.lTensor_id, LinearMap.id_apply, map_zero] at e2
    exact ⟨fun a b ↦ by rw [key a, key b]⟩
  exact ⟨(injective_iff_map_eq_zero T).2 fun x hx ↦ congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : LinearMap.ker T) 0), hs⟩

theorem exists_grp {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (A : Over (Sp R)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) {X' : Scheme.{0}} (s' : X' ⟶ Sp R')
    (φ : X' ⟶ A.left) (h : IsPullback φ s' A.hom (spMap (algebraMap R R'))) :
    ∃ _ : GrpObj (Over.mk s'), IsAbelianScheme (Over.mk s') ∧ SmoothOfRelativeDimension g s' := by
  obtain ⟨C, _, ψ, hψ⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A (spMap (algebraMap R R'))
  let e : C ≅ Over.mk s' := Over.isoMk (hψ.1.isoIsPullback _ _ h) (by simp)
  let _ : GrpObj (Over.mk s') := GrpObj.ofIso e
  have : IsMonHom e.hom := inferInstance
  have hC := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hψ
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} g
  have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  exact ⟨inferInstance, GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hC (GlobalTheory.SymExtendDvr.isGrpPullback_of_iso e.symm),
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) h hg⟩

theorem lTensor_bijective_of_isBaseChange {S B N M P : Type} [CommRing S] [CommRing B] [Algebra S B]
    [AddCommGroup N] [Module S N] [AddCommGroup M] [Module S M] [AddCommGroup P] [Module S P] [Module B P]
    [IsScalarTower S B P] (T : N →ₗ[S] M) (ev : M →ₗ[S] P) (h₁ : IsBaseChange B ev)
    (h₂ : IsBaseChange B (ev ∘ₗ T)) : Function.Bijective (T.lTensor B) := by
  have e : ∀ x, h₁.equiv (T.lTensor B x) = h₂.equiv x := fun x ↦ by
    induction x with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b n => simp [IsBaseChange.equiv_tmul]
  refine (Function.Bijective.of_comp_iff' h₁.equiv.bijective _).1 ?_
  have e' : (h₁.equiv ∘ T.lTensor B) = h₂.equiv := funext e
  rw [e']
  exact h₂.equiv.bijective

theorem oneFormMap_eq_kaehlerDifferential_map {R R' B B' : Type} [CommRing R] [CommRing R'] [CommRing B] [CommRing B'] [Algebra R R'] [Algebra R B]
    [Algebra R' B'] [Algebra B B'] [Algebra R B'] [IsScalarTower R R' B'] [IsScalarTower R B B']
    (hα : SemiHom (algebraMap R R') (algebraMap B B')) (x : Ω[B⁄R]) :
    hα.m1 x = KaehlerDifferential.map R R' B B' x := by
  induction x using ind1 with
  | h b c =>
    rw [SemiHom.oneFormMap_smul_semilinear, SemiHom.m1_D, map_smul, KaehlerDifferential.map_D, algebraMap_smul]
  | h0 => simp
  | ha x y hx hy => rw [map_add, map_add, hx, hy]

theorem isBaseChange_of_isPushout {R R' B B' W : Type} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    [Algebra R R'] [Algebra R B] [Algebra R' B'] [Algebra B B'] [Algebra R B'] [IsScalarTower R R' B']
    [IsScalarTower R B B'] [Algebra.IsPushout R R' B B'] [AddCommGroup W] [Module R W] (ev : W →ₗ[R] Ω[B⁄R])
    (hev : IsBaseChange B ev) (hα : SemiHom (algebraMap R R') (algebraMap B B'))
    (u : R' ⊗[R] W →ₗ[R'] Ω[B'⁄R']) (hu : ∀ c, u (1 ⊗ₜ c) = hα.m1 (ev c)) : IsBaseChange B' u := by
  have h₁ : IsBaseChange B' (KaehlerDifferential.map R R' B B') :=
    IsBaseChange.of_equiv (KaehlerDifferential.tensorKaehlerEquiv R R' B B') fun x ↦ by
      have hx : x ∈ Submodule.span B (Set.range (KaehlerDifferential.D R B)) :=
        (KaehlerDifferential.span_range_derivation R B).ge Submodule.mem_top
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        simp
      | zero => simp
      | add x y _ _ hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]
      | smul a x _ hx =>
        rw [TensorProduct.tmul_smul, ← algebraMap_smul B', map_smul, hx, map_smul, algebraMap_smul]
  have h₂ := IsBaseChange.comp hev h₁
  refine IsBaseChange.of_comp (TensorProduct.isBaseChange R W R') ?_
  convert h₂ using 1
  refine LinearMap.ext fun c ↦ ?_
  exact (hu c).trans (oneFormMap_eq_kaehlerDifferential_map hα _)

section Main

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'}
  {φ : X' ⟶ X}

def pairOf (h : IsPullback φ s' s (spMap (algebraMap R R'))) (U : X.affineOpens) : Pair φ :=
  ⟨(⟨φ ⁻¹ᵁ U.1, GlobalTheory.AbLaw.isAffineOpen_preimage_of_isPullback h U.2⟩, U), le_rfl⟩

theorem isBaseChange_at (h : IsPullback φ s' s (spMap (algebraMap R R'))) (hP : Par (OAff s)) (U : X.affineOpens)
    (u : R' ⊗[R] GlobForm s →ₗ[R'] Ω[Sec s' (φ ⁻¹ᵁ U.1)⁄R'])
    (hu : ∀ c : GlobForm s, u (1 ⊗ₜ c) = (semiHom_secPull h.w (pairOf h U)).m1 (c.1 (op U))) :
    IsBaseChange (Sec s' (φ ⁻¹ᵁ U.1)) u := by
  letI : Algebra (Sec s U.1) (Sec s' (φ ⁻¹ᵁ U.1)) := (CechDR.secPull s s' (pairOf h U)).toAlgebra
  letI : Algebra R (Sec s' (φ ⁻¹ᵁ U.1)) :=
    ((algebraMap R' (Sec s' (φ ⁻¹ᵁ U.1))).comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' (Sec s' (φ ⁻¹ᵁ U.1)) := .of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower R (Sec s U.1) (Sec s' (φ ⁻¹ᵁ U.1)) :=
    .of_algebraMap_eq fun r ↦ ((semiHom_secPull h.w (pairOf h U)).map_algebraMap r).symm
  haveI : Algebra.IsPushout R R' (Sec s U.1) (Sec s' (φ ⁻¹ᵁ U.1)) :=
    CommRingCat.isPushout_iff_isPushout.mp (GlobalTheory.AbLaw.isPushout_cst h U.2 rfl)
  exact isBaseChange_of_isPushout (B := Sec s U.1) (B' := Sec s' (φ ⁻¹ᵁ U.1)) (evForm (OAff s) (op U)) (hP (op U))
    (semiHom_secPull h.w (pairOf h U)) u hu

theorem exists_prime (h : IsPullback φ s' s (spMap (algebraMap R R'))) (e : Sp R' ⟶ X') (he : e ≫ s' = 𝟙 _)
    (p : PrimeSpectrum R') : ∃ (U : X.affineOpens) (q : PrimeSpectrum (Sec s' (φ ⁻¹ᵁ U.1))),
      PrimeSpectrum.comap (algebraMap R' (Sec s' (φ ⁻¹ᵁ U.1))) q = p := by
  let y : Sp R' := p
  obtain ⟨V, hV, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := φ (e y)) trivial
  have hU' := GlobalTheory.AbLaw.isAffineOpen_preimage_of_isPullback h hV
  refine ⟨⟨V, hV⟩, hU'.primeIdealOf ⟨e y, hx⟩, ?_⟩
  have e₁ := hU'.fromSpec_primeIdealOf ⟨e y, hx⟩
  have e₂ := affPt_w s' ⟨φ ⁻¹ᵁ V, hU'⟩
  have e₃ := congrArg (fun f ↦ f (hU'.primeIdealOf ⟨e y, hx⟩)) e₂
  have e₄ : s' (e y) = y := by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  have e₅ : s' (hU'.fromSpec (hU'.primeIdealOf ⟨e y, hx⟩)) =
      spMap (algebraMap R' (Sec s' (φ ⁻¹ᵁ V))) (hU'.primeIdealOf ⟨e y, hx⟩) :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans e₃
  exact ((congrArg (fun z ↦ s' z) e₁).symm.trans e₅).symm.trans e₄

end Main

theorem formBC : SteinSt → ParSt → FormBCSt := by
  intro _ hPar R _ A _ g hA hg R' _ _ X' s' φ h
  obtain ⟨_, hA', hg'⟩ := exists_grp A g hA hg s' φ h
  obtain ⟨hP, hV⟩ := hPar R A g hA hg
  obtain ⟨hP', hV'⟩ := hPar R' (Over.mk s') g hA' hg'
  replace hP' : Par (OAff s') := hP'
  replace hV' : VB R' (GlobForm s') g := hV'
  obtain ⟨f₁, f₂, -⟩ := hV'
  obtain ⟨f₃, -, -⟩ := hV
  let _ : Module R (GlobForm s') := Module.compHom _ (algebraMap R R')
  have : IsScalarTower R R' (GlobForm s') := .of_algebraMap_smul fun _ _ ↦ rfl
  let T : R' ⊗[R] GlobForm A.hom →ₗ[R'] GlobForm s' := LinearMap.liftBaseChange R'
    { toFun := pullForm h.w
      map_add' := map_add _
      map_smul' := (pullForm h.w).map_smulₛₗ }
  have hT : ∀ c : GlobForm A.hom, T (1 ⊗ₜ c) = pullForm h.w c := fun c ↦ by simp [T]
  let e : Sp R' ⟶ X' := (η[Over.mk s'] : 𝟙_ (Over (Sp R')) ⟶ Over.mk s').left
  have he : e ≫ s' = 𝟙 _ := Over.w (η[Over.mk s'] : 𝟙_ (Over (Sp R')) ⟶ Over.mk s')
  have hb : Function.Bijective T :=
    bijective_of_lTensor T (fun U : A.left.affineOpens ↦ Sec s' (φ ⁻¹ᵁ U.1)) (exists_prime h e he) fun U ↦ ?_
  · exact ⟨LinearEquiv.ofBijective T hb, fun c ↦ by
      have : LinearEquiv.ofBijective T hb (1 ⊗ₜ c) = pullForm h.w c := hT c
      rw [this]
      exact isPullForm_pullForm h.w c⟩
  · refine lTensor_bijective_of_isBaseChange T (evForm (OAff s') (op ⟨φ ⁻¹ᵁ U.1, GlobalTheory.AbLaw.isAffineOpen_preimage_of_isPullback h U.2⟩)) (hP' _) ?_
    refine isBaseChange_at h hP U _ fun c ↦ ?_
    have k := isPullForm_iff.1 (isPullForm_pullForm h.w c) (pairOf h U)
    exact (congrArg (fun z : GlobForm s' ↦ z.1 (op (pairOf h U).1.1)) (hT c)).trans k.symm

end GlobalTheory.CompanionTheory.Hodge.FormBC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellInducingCharacterStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_cell_inducing_character : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {i j : ℕ} (h : (i + 1) + (j + 1) = i + (j + 1) + 1) (π₁ : Representation ℂ (GL (Fin (i + 1)) k) V) (π₂ : Representation ℂ (GL (Fin (j + 1)) k) W) (g : HPG k i (j + 1)) (hq : wGL k h * ((g : Mir k (i + (j + 1))) : GL (Fin (i + (j + 1) + 1)) k) * (wGL k h)⁻¹ ∈ parab k (two (stdSum h))) (v : ⨂[ℂ] x, TwoT V W x), ((extTensor (mtw (gres (⟨V, π₁⟩ : GRep k (i + 1))) (((j + 1 : ℕ) : ℝ) / 2)).ρ (GRep.tw (⟨W, π₂⟩ : GRep k (j + 1)) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (pgProj k i (j + 1))) g (tE V W v) = tE V W (sQ h π₁ π₂ ⟨_, hq⟩ v) := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.open_orbit_twist | exact GlobalTheory.CompanionTheory.BZRes.open_orbit_twist | (intros; apply GlobalTheory.CompanionTheory.BZRes.open_orbit_twist <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenDoubleCosetCriterionStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_double_coset_criterion : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {i t : ℕ} (h : (i + 1) + t = i + t + 1), 0 < t → ∀ g : GL (Fin (i + t + 1)) k, g ∈ dcos (parab k (two (stdSum h))) (Mir k (i + t)) (wGL k h) ↔ ∃ a : Fin (i + 1), ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)) (stdSum h (Sum.inl a)) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.mem_dcos_wGL_iff | exact GlobalTheory.CompanionTheory.BZRes.mem_dcos_wGL_iff | (intros; apply GlobalTheory.CompanionTheory.BZRes.mem_dcos_wGL_iff <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitFinitenessOfLatticeBoundStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_finiteness_of_lattice_bound : LatBound → OrbFin := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.orbFin_of_latBound | exact GlobalTheory.CompanionTheory.ColumnSplitting.orbFin_of_latBound | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.orbFin_of_latBound <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicIffFrameParabolicStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis GlobalTheory.CompanionTheory.SiegelFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_iff_frame_parabolic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n), ∀ (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E) (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (t₀ : GL (Fin n) E), b.1.toCols₁ = diagCols (Fin n) * t₀.1 → ∀ x : G2 σ Y, (∃ t, IsPar x t) ↔ frameEquiv χ ε b hb x ∈ (adCM σ χ).uQ ε (Set.univ : Set (Fin n)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelFrame.ParStab.exists_isPar_iff_mem_uQ | exact GlobalTheory.CompanionTheory.SiegelFrame.ParStab.exists_isPar_iff_mem_uQ | (intros; apply GlobalTheory.CompanionTheory.SiegelFrame.ParStab.exists_isPar_iff_mem_uQ <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionProductRankZeroLeftStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restriction_product_rank_zero_left : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (j n : ℕ) (π₁ : GRep k 0) (π₂ : GRep k (j + 1)) (h : 0 + (j + 1) = n + 1) (h' : 0 + j = n), IsSmooth π₁.ρ → IsSmooth π₂.ρ → MIso (gres ((π₁.prod π₂).cast h)) (mcast h' (prodGPn π₁ (gres π₂))) := by
  first | exact @GlobalTheory.CompanionTheory.LeibRes0Left.gres_prod_zero_left' | exact GlobalTheory.CompanionTheory.LeibRes0Left.gres_prod_zero_left' | (intros; apply GlobalTheory.CompanionTheory.LeibRes0Left.gres_prod_zero_left' <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionProductRankZeroRightStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restriction_product_rank_zero_right : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i n : ℕ) (π₁ : GRep k (i + 1)) (π₂ : GRep k 0) (h : (i + 1) + 0 = n + 1) (h' : i + 0 = n), IsSmooth π₁.ρ → IsSmooth π₂.ρ → MIso (gres ((π₁.prod π₂).cast h)) (mcast h' (prodPGn (gres π₁) π₂)) := by
  first | exact @GlobalTheory.CompanionTheory.LeibTrivBlock.miso_gres_prod_zero | exact GlobalTheory.CompanionTheory.LeibTrivBlock.miso_gres_prod_zero | (intros; apply GlobalTheory.CompanionTheory.LeibTrivBlock.miso_gres_prod_zero <;> assumption)
end

