import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0054
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0025
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0026
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0035
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0027
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducibleEquivariantProjection
section
namespace GlobalTheory.AdmissibleProjection

open GlobalTheory.UnitarySemisimple

variable {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W]

def stab (ρ : Representation ℂ H W) (v : W) : Subgroup H where
  carrier := {g | ρ g v = v}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha]
      _ = v := rho_inv_rho ρ a v

theorem orbit_finite [TopologicalSpace H] [IsTopologicalGroup H] (ρ : Representation ℂ H W)
    (hsm : ∀ w, IsOpen {k : H | ρ k w = w}) (K : Subgroup H) (hK : IsCompact (K : Set H))
    (w : W) : (Set.range fun k : K => ρ k w).Finite := by
  have hopen : ∀ i : K, IsOpen {h : H | ρ h w = ρ (i : H) w} := by
    intro i
    have e : {h : H | ρ h w = ρ (i : H) w} = (fun h => (i : H)⁻¹ * h) ⁻¹' {h | ρ h w = w} := by
      ext h
      simp only [Set.mem_setOf_eq, Set.mem_preimage, map_mul, Module.End.mul_apply]
      constructor
      · intro e; rw [e, rho_inv_rho]
      · intro e
        calc ρ h w = ρ (i : H) (ρ (i : H)⁻¹ (ρ h w)) := (rho_rho_inv ρ _ _).symm
          _ = ρ (i : H) w := by rw [e]
    rw [e]
    exact (hsm w).preimage (continuous_mul_left _)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun i : K => {h : H | ρ h w = ρ (i : H) w}) hopen
    (fun h hh => Set.mem_iUnion.2 ⟨⟨h, hh⟩, rfl⟩)
  refine (t.finite_toSet.image (fun i : K => ρ (i : H) w)).subset ?_
  rintro _ ⟨k, rfl⟩
  obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.1 (ht k.2)
  exact ⟨i, hi, hki.symm⟩

theorem hadm_of [TopologicalSpace H] [IsTopologicalGroup H] (ρ : Representation ℂ H W)
    (hK0 : ∃ K : Subgroup H, IsOpen (K : Set H) ∧ IsCompact (K : Set H))
    (hsm : ∀ w, IsOpen {k : H | ρ k w = w})
    (hfd : ∀ K : Subgroup H, IsOpen (K : Set H) → FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K)) :
    ∀ v, ∃ K : Subgroup H, (∀ k ∈ K, ρ k v = v) ∧ FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K) ∧
      ∀ w, (Set.range fun k : K => ρ k w).Finite := by
  obtain ⟨K₀, hop, hco⟩ := hK0
  intro v
  refine ⟨K₀ ⊓ stab ρ v, fun k hk => hk.2, hfd _ ?_, fun w => ?_⟩
  · rw [Subgroup.coe_inf]; exact hop.inter (hsm v)
  · refine (orbit_finite ρ hsm K₀ hco w).subset ?_
    rintro _ ⟨k, rfl⟩
    exact ⟨⟨k, k.2.1⟩, rfl⟩

theorem exists_proj (ρ : Representation ℂ H W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ)
    (hdef : ∀ v, B v v = 0 → v = 0) (hinv : ∀ g u v, B (ρ g u) (ρ g v) = B u v)
    (hadm : ∀ v, ∃ K : Subgroup H, (∀ k ∈ K, ρ k v = v) ∧ FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K) ∧
      ∀ w, (Set.range fun k : K => ρ k w).Finite)
    (Z : Subrepresentation ρ) :
    ∃ P : W →ₗ[ℂ] W, (∀ w, P w ∈ Z.toSubmodule) ∧ (∀ w, ∀ z ∈ Z.toSubmodule, B z (w - P w) = 0) ∧
      ∀ g w, P (ρ g w) = ρ g (P w) := by
  classical
  have hex := fun w => exists_compl_proj ρ B hdef hinv hadm Z w
  let f : W → W := fun w => Classical.choose (hex w)
  have hf1 : ∀ w, f w ∈ Z.toSubmodule := fun w => (Classical.choose_spec (hex w)).1
  have hf2 : ∀ w, ∀ z ∈ Z.toSubmodule, B z (w - f w) = 0 :=
    fun w => (Classical.choose_spec (hex w)).2
  have huniq : ∀ w t, t ∈ Z.toSubmodule → (∀ z ∈ Z.toSubmodule, B z (w - t) = 0) → f w = t := by
    intro w t ht htw
    have hd : f w - t ∈ Z.toSubmodule := sub_mem (hf1 w) ht
    have h0 : B (f w - t) (f w - t) = 0 := by
      calc B (f w - t) (f w - t) = B (f w - t) ((w - t) - (w - f w)) := by congr 1; abel
        _ = 0 := by rw [map_sub, htw _ hd, hf2 w _ hd, sub_zero]
    exact sub_eq_zero.1 (hdef _ h0)
  let P : W →ₗ[ℂ] W :=
    { toFun := f
      map_add' := fun a b => huniq _ _ (add_mem (hf1 a) (hf1 b)) (fun z hz => by
        rw [show a + b - (f a + f b) = (a - f a) + (b - f b) by abel, map_add, hf2 a z hz,
          hf2 b z hz, add_zero])
      map_smul' := fun c a => by
        simp only [RingHom.id_apply]
        exact huniq _ _ (Z.toSubmodule.smul_mem c (hf1 a)) (fun z hz => by
          rw [← smul_sub, map_smul, hf2 a z hz, smul_zero]) }
  refine ⟨P, hf1, hf2, fun g w => ?_⟩
  exact huniq _ _ (Z.apply_mem_toSubmodule g (hf1 w)) (fun z hz => by
    rw [← map_sub]; exact orth_stable ρ B hinv Z (w - f w) (hf2 w) g z hz)

theorem exists_irreducible_equivariant_projection : ∀ (H W : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), (∀ u v, star (B u v) = B v u) → (∀ v, 0 ≤ (B v v).re) → (∀ v, B v v = 0 → v = 0) → (∀ g u v, B (ρ g u) (ρ g v) = B u v) → (∃ K : Subgroup H, IsOpen (K : Set H) ∧ IsCompact (K : Set H)) → (∀ w, IsOpen {k : H | ρ k w = w}) → (∀ K : Subgroup H, IsOpen (K : Set H) → FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K)) → ∀ x : W, x ≠ 0 → ∃ (U : Submodule ℂ W) (P : W →ₗ[ℂ] W), U ≠ ⊥ ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧ (∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U) ∧ (∀ w, P w ∈ U) ∧ (∀ g w, P (ρ g w) = ρ g (P w)) ∧ P x ≠ 0 := by
  intro H W _ _ _ _ _ ρ B hherm hpos hdef hinv hK0 hsm hfd x hx
  classical
  have hadm := hadm_of ρ hK0 hsm hfd
  obtain ⟨K0, hxK, hfdK, -⟩ := hadm x
  set F := GlobalTheory.PRep.fixed ρ K0 with hF
  haveI := hfdK
  have ofF : ∀ u ∈ F, ∀ k ∈ K0, ρ k u = u := by
    intro u hu k hk
    have := hu ⟨k, hk⟩
    simpa using this
  have memF : ∀ u, (∀ k ∈ K0, ρ k u = u) → u ∈ F := by
    intro u hu k
    show ρ (k : H) u = ((1 : ℂˣ) : ℂ) • u
    simp [hu k k.2]
  set O := (orbSpan ρ x).toSubmodule with hO
  let Q : W → Prop := fun y => y ≠ 0 ∧ y ∈ F ∧ y ∈ O
  have hex : ∃ n : ℕ, ∃ y, Q y ∧
      Module.finrank ℂ ((orbSpan ρ y).toSubmodule ⊓ F : Submodule ℂ W) = n :=
    ⟨_, x, ⟨hx, memF x hxK, mem_orbSpan ρ x⟩, rfl⟩
  obtain ⟨y, ⟨hy0, hyF, hyO⟩, hn⟩ := Nat.find_spec hex
  have hmin : ∀ t, Q t → Module.finrank ℂ ((orbSpan ρ y).toSubmodule ⊓ F : Submodule ℂ W) ≤
      Module.finrank ℂ ((orbSpan ρ t).toSubmodule ⊓ F : Submodule ℂ W) := by
    intro t ht
    rw [hn]
    exact Nat.find_min' hex ⟨t, ht, rfl⟩
  set U := orbSpan ρ y with hU
  have hyU : y ∈ U.toSubmodule := mem_orbSpan ρ y
  have hUO : U.toSubmodule ≤ O := orbSpan_le ρ y (orbSpan ρ x) hyO
  obtain ⟨P, hP1, hP2, hP3⟩ := exists_proj ρ B hdef hinv hadm U
  refine ⟨U.toSubmodule, P, ?_, fun g u hu => U.apply_mem_toSubmodule g hu, ?_, hP1, hP3, ?_⟩
  · intro h
    apply hy0
    rw [h] at hyU
    exact (Submodule.mem_bot ℂ).1 hyU
  · intro N hNU hN
    let N' : Subrepresentation ρ := ⟨N, by intro g v hv; exact hN g v hv⟩
    obtain ⟨t, htN, ht⟩ := exists_compl_proj ρ B hdef hinv hadm N' y
    have hfix : ∀ g, ρ g y = y → ρ g t = t := by
      intro g hg
      have h1 : ρ g t - t ∈ N'.toSubmodule := sub_mem (N'.apply_mem_toSubmodule g htN) htN
      have h2 : ∀ z ∈ N'.toSubmodule, B z (ρ g t - t) = 0 := by
        intro z hz
        have e : ρ g t - t = (y - t) - ρ g (y - t) := by
          rw [map_sub, hg]
          abel
        rw [e, map_sub, ht z hz, orth_stable ρ B hinv N' _ ht g z hz, sub_zero]
      exact sub_eq_zero.1 (hdef _ (h2 _ h1))
    by_cases ht0 : t = 0
    · left
      have hyo : ∀ z ∈ N'.toSubmodule, B z y = 0 := by
        intro z hz
        simpa [ht0] using ht z hz
      have hUo : ∀ z ∈ N'.toSubmodule, ∀ u ∈ U.toSubmodule, B z u = 0 := by
        intro z hz u hu
        have hle : U.toSubmodule ≤ LinearMap.ker (B z) := by
          refine Submodule.span_le.2 ?_
          rintro _ ⟨g, rfl⟩
          exact orth_stable ρ B hinv N' y hyo g z hz
        exact hle hu
      rw [Submodule.eq_bot_iff]
      intro v hv
      exact hdef _ (hUo _ hv _ (hNU hv))
    · right
      have hQt : Q t := ⟨ht0, memF t (fun k hk => hfix k (ofF y hyF k hk)), hUO (hNU htN)⟩
      have h1 := hmin t hQt
      haveI : FiniteDimensional ℂ (U.toSubmodule ⊓ F : Submodule ℂ W) :=
        Submodule.finiteDimensional_of_le inf_le_right
      haveI : FiniteDimensional ℂ (N ⊓ F : Submodule ℂ W) :=
        Submodule.finiteDimensional_of_le inf_le_right
      have hle1 : ((orbSpan ρ t).toSubmodule ⊓ F : Submodule ℂ W) ≤ N ⊓ F :=
        inf_le_inf_right _ (orbSpan_le ρ t N' htN)
      have hle2 : (N ⊓ F : Submodule ℂ W) ≤ U.toSubmodule ⊓ F := inf_le_inf_right _ hNU
      have h2 := LinearMap.finrank_le_finrank_of_injective (f := Submodule.inclusion hle1)
        (Submodule.inclusion_injective hle1)
      have heq := Submodule.eq_of_le_of_finrank_le hle2 (h1.trans h2)
      have hyN : y ∈ N := by
        have : y ∈ (N ⊓ F : Submodule ℂ W) := heq ▸ ⟨hyU, hyF⟩
        exact this.1
      exact le_antisymm hNU (orbSpan_le ρ y N' hyN)
  · intro hPx
    have hxo : ∀ z ∈ U.toSubmodule, B z x = 0 := by
      intro z hz
      simpa [hPx] using hP2 x z hz
    have hle : O ≤ LinearMap.ker (B y) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, rfl⟩
      exact orth_stable ρ B hinv U x hxo g y hyU
    exact hy0 (hdef _ (hle (hUO hyU)))

end GlobalTheory.AdmissibleProjection
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOddFrameNotReducesToSmallerOddWeightStatement
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_oddFrame_not_reducesToSmallerOddWeight : ∀ (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ), Γ.FiniteIndex → (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) → (∃ τ, (evM s w F τ).det ≠ 0) → ∃ (w' : Fin r → ℤ) (F' : Fin r → ℍ → ℂ), (∀ j, Odd (w' j) ∧ IsMF Γ (w' j) (F' j)) ∧ (∃ τ, (evM s w' F' τ).det ≠ 0) ∧ ¬ Reduces Γ w' F' := by
  first | exact @GlobalTheory.OddFrame.descent | exact GlobalTheory.OddFrame.descent | (intros; apply GlobalTheory.OddFrame.descent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOddWeightFrameDetNeZeroStatement
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_odd_weight_frame_det_ne_zero : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (τ₀ : ℍ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ → (-1 : SL(2, ℤ)) ∉ Γ → IsReps Γ s → (∀ (ι : Type) [Fintype ι] (x : ι → SL(2, ℤ)) (c : ι → ℂ), (∀ i j, x i * (x j)⁻¹ ∈ CongruenceSubgroup.Gamma M → i = j) → (∀ (k : ℤ) (f : ℍ → ℂ), IsMF (CongruenceSubgroup.Gamma M) k f → ∑ i, c i * (f ∣[k] x i) τ₀ = 0) → c = 0) → ∃ (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ), (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) ∧ (evM s w F τ₀).det ≠ 0 := by
  first | exact @GlobalTheory.OddFrame.exists_odd_det_evM_ne_zero | exact GlobalTheory.OddFrame.exists_odd_det_evM_ne_zero | (intros; apply GlobalTheory.OddFrame.exists_odd_det_evM_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPlusMinusCosetRepresentativesTwoMulCardStatement
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_plusMinusCosetRepresentatives_two_mul_card : ∀ (Γ : Subgroup SL(2, ℤ)), Γ.FiniteIndex → (-1 : SL(2, ℤ)) ∉ Γ → ∃ (r : ℕ) (s : Fin r → SL(2, ℤ)), IsReps Γ s ∧ 2 * r = Γ.index := by
  first | exact @GlobalTheory.OddFrame.reps_index | exact GlobalTheory.OddFrame.reps_index | (intros; apply GlobalTheory.OddFrame.reps_index <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPointSlashEvaluationsIndependentGammaStatement
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_point_slashEvaluations_independent_gamma : ∀ M : ℕ, 0 < M → (∀ x : SL(2, ℤ), x ∉ CongruenceSubgroup.Gamma M → ∃ (k : ℤ) (f : ℍ → ℂ), IsMF (CongruenceSubgroup.Gamma M) k f ∧ f ∣[k] x ≠ f) → ∃ τ₀ : ℍ, ∀ (ι : Type) [Fintype ι] (x : ι → SL(2, ℤ)) (c : ι → ℂ), (∀ i j, x i * (x j)⁻¹ ∈ CongruenceSubgroup.Gamma M → i = j) → (∀ (k : ℤ) (f : ℍ → ℂ), IsMF (CongruenceSubgroup.Gamma M) k f → ∑ i, c i * (f ∣[k] x i) τ₀ = 0) → c = 0 := by
  first | exact @GlobalTheory.CosetEval.evals_independent | exact GlobalTheory.CosetEval.evals_independent | (intros; apply GlobalTheory.CosetEval.evals_independent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPthPowerScaleThinShellStatement
section
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pth_power_scale_thin_shell : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ F : Subfield L, ApproxRoot p v F → 0 < v (p : L) → v (p : L) < 1 → ∀ r : ℝ≥0, r < 1 → ∀ x : L, x ≠ 0 → ∃ d ∈ F, d ≠ 0 ∧ r < v (x * d ^ p) ∧ v (x * d ^ p) ≤ 1 := by
  first | exact @GlobalTheory.AlmostEt.klc_scale | exact GlobalTheory.AlmostEt.klc_scale | (intros; apply GlobalTheory.AlmostEt.klc_scale <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfCosetRepresentativeTraceStatement
section
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reps_of_cosetRepresentativeTrace : ∀ (L : Type) [Field L] (G : Type) [Group G] [MulSemiringAction G L] (U : Subgroup G) [Fintype (G ⧸ U)] (S : Finset L), (∀ s ∈ S, s ∈ Fix L U) → ∀ y₀ ∈ Fix L U, ∃ (y : L) (D E : Finset G), y = ∑ d ∈ D, d • y₀ ∧ (∀ h : G, ∃! g, g ∈ E ∧ h • y = g • y ∧ ∀ s ∈ S, h • s = g • s) ∧ ∑ g ∈ E, g • y = cosetTrace U y₀ := by
  first | exact @GlobalTheory.AlmostEt.exists_reps_of_cosetTrace | exact GlobalTheory.AlmostEt.exists_reps_of_cosetTrace | (intros; apply GlobalTheory.AlmostEt.exists_reps_of_cosetTrace <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSquarefreePolyDistinctZerosOnCurve
section
open Polynomial

namespace GlobalTheory.SquarefreeFibre

theorem algebraMap_norm_mem_span {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Free R S] [Module.Finite R S] (g : S) :
    algebraMap R S (Algebra.norm R g) ∈ Ideal.span {g} := by
  set p := LinearMap.charpoly (Algebra.lmul R S g) with hp
  have h1 : aeval g p = 0 := by
    have h2 := congrArg (fun φ : Module.End R S => φ 1) (LinearMap.aeval_self_charpoly (Algebra.lmul R S g))
    rw [← hp, Polynomial.aeval_algHom_apply (Algebra.lmul R S) g p] at h2
    simpa using h2
  have h3 : algebraMap R S (p.coeff 0) = -(g * aeval g p.divX) := by
    have h4 := X_mul_divX_add p
    rw [← h4] at h1
    simp only [map_add, map_mul, aeval_X, aeval_C] at h1
    linear_combination h1
  rw [Algebra.norm_apply, LinearMap.det_eq_sign_charpoly_coeff, map_mul, ← hp, h3]
  exact Ideal.mul_mem_left _ _ ((Ideal.span {g}).neg_mem
    (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self g)))

theorem main : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A] [Module.Free k[X] A] (g : A) (s : ℕ), g ≠ 0 → ∃ (q : k[X]) (r : ℕ) (Q : Fin r → Ideal A), q.Monic ∧ q.natDegree = s ∧ (∀ i, (Q i).IsMaximal) ∧ Function.Injective Q ∧ (∀ i, g ∉ Q i) ∧ Ideal.span {algebraMap k[X] A q} = ∏ i, Q i := by
  intro k A _ _ _ _ _ _ _ _ _ _ g s hg
  classical
  obtain ⟨δ, hδ0, hδ⟩ := GlobalTheory.T.exists_nonzero_sub_C_not_mem_sq_maximal k A
  set u := algebraMap k[X] A with hu
  set N := Algebra.norm k[X] g with hNdef
  have hN : N ≠ 0 := Algebra.norm_ne_zero_iff.mpr hg
  have hinj : Function.Injective u := FaithfulSMul.algebraMap_injective k[X] A
  have huC : ∀ c : k, u (C c) = algebraMap k A c := by
    intro c
    rw [IsScalarTower.algebraMap_apply k k[X] A c, Polynomial.algebraMap_eq]

  have hCnot : ∀ (P : Ideal A), P.IsPrime → ∀ c : k, c ≠ 0 → u (C c) ∉ P := by
    intro P hP c hc hmem
    rw [huC] at hmem
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem ((Ne.isUnit hc).map (algebraMap k A)))

  have hgnot : ∀ (P : Ideal A), P.IsPrime → ∀ α : k, N.eval α ≠ 0 → u (X - C α) ∈ P → g ∉ P := by
    intro P hP α hα hX hgP
    have hNP : u N ∈ P := (Ideal.span_singleton_le_iff_mem P).mpr hgP (algebraMap_norm_mem_span g)
    have hdec := modByMonic_add_div N (X - C α)
    rw [modByMonic_X_sub_C_eq_C_eval] at hdec
    have h5 : C (N.eval α) = N - (X - C α) * (N /ₘ (X - C α)) := eq_sub_of_add_eq hdec
    have : u (C (N.eval α)) = u N - u (X - C α) * u (N /ₘ (X - C α)) := by
      rw [h5, map_sub, map_mul]
    exact hCnot P hP _ hα (this ▸ P.sub_mem hNP (P.mul_mem_right _ hX))

  have hδN : δ * N ≠ 0 := mul_ne_zero hδ0 hN
  have hfin : {a : k | (δ * N).eval a = 0}.Finite :=
    ((δ * N).roots.toFinset.finite_toSet).subset (fun a ha => by
      simp only [Set.mem_setOf_eq] at ha
      simp [Polynomial.mem_roots hδN, ha])
  have hinf : {a : k | (δ * N).eval a ≠ 0}.Infinite := by
    have := hfin.infinite_compl
    simpa [Set.compl_setOf] using this
  obtain ⟨F, hFS, hFcard⟩ := hinf.exists_subset_card_eq s
  have hF : ∀ a ∈ F, δ.eval a ≠ 0 ∧ N.eval a ≠ 0 := by
    intro a ha
    have := hFS ha
    simp only [Set.mem_setOf_eq, eval_mul] at this
    exact ⟨left_ne_zero_of_mul this, right_ne_zero_of_mul this⟩
  set q : k[X] := ∏ a ∈ F, (X - C a) with hq
  have hqm : q.Monic := monic_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)
  have hqdeg : q.natDegree = s := by
    rw [hq, natDegree_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)]
    simp [hFcard]

  have hone : ∀ (P : Ideal A), P.IsPrime → u q ∈ P → ∃ a ∈ F, u (X - C a) ∈ P := by
    intro P hP hqP
    rw [hq, map_prod] at hqP
    exact Ideal.IsPrime.prod_mem_iff.mp hqP
  have huniq : ∀ (P : Ideal A), P.IsPrime → ∀ a b : k, u (X - C a) ∈ P → u (X - C b) ∈ P → a = b := by
    intro P hP a b ha hb
    by_contra hab
    have : u (C (b - a)) = u (X - C a) - u (X - C b) := by
      rw [← map_sub]; congr 1; simp [C_sub]
    exact hCnot P hP (b - a) (sub_ne_zero.mpr (Ne.symm hab)) (this ▸ P.sub_mem ha hb)
  have hnotsq : ∀ (P : Ideal A), P.IsMaximal → u q ∉ P ^ 2 := by
    intro P hPm hq2
    have hP : P.IsPrime := hPm.isPrime
    obtain ⟨a, haF, haP⟩ := hone P hP (Ideal.pow_le_self two_ne_zero hq2)
    have hsplit : q = (∏ b ∈ F.erase a, (X - C b)) * (X - C a) := by
      rw [hq, mul_comm, Finset.mul_prod_erase F (fun b => X - C b) haF]
    rw [hsplit, map_mul] at hq2
    rcases Ideal.IsPrime.mul_mem_pow P hq2 with hrest | hX2
    · rw [map_prod] at hrest
      obtain ⟨b, hbF, hbP⟩ := Ideal.IsPrime.prod_mem_iff.mp hrest
      exact (Finset.ne_of_mem_erase hbF) (huniq P hP b a hbP haP)
    · exact hδ a (hF a haF).1 P hPm hX2

  set I : Ideal A := Ideal.span {u q} with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.span_singleton_eq_bot]
    exact fun h => hqm.ne_zero (hinj (h.trans (map_zero u).symm))
  have hsq : Squarefree I := by
    intro J hJ
    by_contra hJu
    have hJtop : J ≠ ⊤ := fun h => hJu (Ideal.isUnit_iff.mpr h)
    obtain ⟨P, hPm, hJP⟩ := Ideal.exists_le_maximal J hJtop
    have hle : I ≤ P ^ 2 := (Ideal.le_of_dvd hJ).trans (by rw [pow_two]; exact Ideal.mul_mono hJP hJP)
    exact hnotsq P hPm (hle (Ideal.mem_span_singleton_self _))
  have hnodup := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hI0).mp hsq
  set M := UniqueFactorizationMonoid.normalizedFactors I with hM
  have hmem : ∀ P ∈ M, P.IsMaximal ∧ g ∉ P := by
    intro P hPM
    have hPp : P.IsPrime := Ideal.isPrime_of_prime (UniqueFactorizationMonoid.prime_of_normalized_factor P hPM)
    have hPne : P ≠ ⊥ := UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hPM
    refine ⟨hPp.isMaximal hPne, ?_⟩
    have hqP : u q ∈ P := Ideal.le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hPM)
      (Ideal.mem_span_singleton_self _)
    obtain ⟨a, haF, haP⟩ := hone P hPp hqP
    exact hgnot P hPp a (hF a haF).2 haP
  let e := M.toFinset.equivFin
  refine ⟨q, M.toFinset.card, fun i => (e.symm i : Ideal A), hqm, hqdeg, ?_, ?_, ?_, ?_⟩
  · intro i; exact (hmem _ (Multiset.mem_toFinset.mp (e.symm i).2)).1
  · intro i j h; exact e.symm.injective (Subtype.ext h)
  · intro i; exact (hmem _ (Multiset.mem_toFinset.mp (e.symm i).2)).2
  · rw [Fintype.prod_equiv e.symm (fun i => (e.symm i : Ideal A)) (fun x => (x : Ideal A)) (fun _ => rfl),
      Finset.prod_coe_sort M.toFinset (fun x => x), Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
      hnodup.dedup, Multiset.map_id', hM, ← hI]
    exact (Ideal.prod_normalizedFactors_eq_self hI0).symm

end GlobalTheory.SquarefreeFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSurjHomZmodOfIsPGroupStatement
section
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_surjective_hom_zmod_of_isPGroup : ∀ (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] [Nontrivial G], IsPGroup p G → ∃ χ : G →* Multiplicative (ZMod p), Function.Surjective χ := by
  first | exact @GlobalTheory.AlmostEt.exists_surj_hom_zmod_of_isPGroup | exact GlobalTheory.AlmostEt.exists_surj_hom_zmod_of_isPGroup | (intros; apply GlobalTheory.AlmostEt.exists_surj_hom_zmod_of_isPGroup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteAlgebrasOverHenselianAndComplete
section
noncomputable section

namespace GlobalTheory

open IsLocalRing TensorProduct

universe u

open IsLocalRing TensorProduct in
open WithConv in

theorem _root_.GlobalTheory.bialgHom_map_antipode {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [HopfAlgebra R A] [HopfAlgebra R B] (g : A →ₐc[R] B) (a : A) :
    g (HopfAlgebra.antipode R a) = HopfAlgebra.antipode R (g a) := by
  have h1 := LinearMap.algHom_comp_convMul_distrib (g : A →ₐ[R] B)
    (toConv (HopfAlgebra.antipode R)) (toConv LinearMap.id)
  have h2 := LinearMap.convMul_comp_coalgHom_distrib (toConv LinearMap.id)
    (toConv (HopfAlgebra.antipode R)) (g : A →ₗc[R] B)
  have e1 : (g : A →ₐ[R] B).toLinearMap ∘ₗ ofConv (1 : WithConv (A →ₗ[R] A)) =
      ofConv (1 : WithConv (A →ₗ[R] B)) := by
    ext x
    simp only [LinearMap.convOne_def]
    exact (g : A →ₐ[R] B).commutes _
  have e2 : ofConv (1 : WithConv (B →ₗ[R] B)) ∘ₗ (g : A →ₗc[R] B).toLinearMap =
      ofConv (1 : WithConv (A →ₗ[R] B)) := by
    ext x
    simp [LinearMap.convOne_def]
  rw [LinearMap.antipode_mul_id, e1] at h1
  rw [LinearMap.id_mul_antipode, e2] at h2
  have h := left_inv_eq_right_inv (ofConv_injective h1).symm (ofConv_injective h2).symm
  simpa using congrArg (fun f : WithConv (A →ₗ[R] B) ↦ (ofConv f) a) h

open IsLocalRing TensorProduct in

theorem _root_.GlobalTheory.henselianLocalRing_of_isAdicComplete (R : Type*) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] : HenselianLocalRing R :=
  _root_.GlobalTheory.henselianLocalRing_of_henselianRing R

open IsLocalRing TensorProduct in

theorem _root_.GlobalTheory.exists_etale_henselian_lift_of_isSeparable (R : Type u) (L : Type*) [CommRing R]
    [HenselianLocalRing R] [Field L] [Algebra (ResidueField R) L]
    [Module.Finite (ResidueField R) L] [Algebra.IsSeparable (ResidueField R) L] :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A), Module.Finite R A ∧ Algebra.Etale R A ∧
      HenselianLocalRing A ∧ Nonempty (ResidueField R ⊗[R] A ≃ₐ[ResidueField R] L) := by
  obtain ⟨A, _, _, hfin, het, hloc, he⟩ := _root_.GlobalTheory.exists_etale_lift_of_isSeparable R L
  exact ⟨A, inferInstance, inferInstance, hfin, het, _root_.GlobalTheory.henselianLocalRing_of_finite R A, he⟩

open IsLocalRing TensorProduct in
open CategoryTheory in

theorem _root_.GlobalTheory.finite_algebras_over_henselian (R : Type u) [CommRing R] [HenselianLocalRing R] :
    (∀ (S : Type u) [CommRing S] [Algebra R S] [Module.Finite R S],
      (∃ (ι : Type u) (_ : Finite ι) (T : ι → Type u) (_ : ∀ i, CommRing (T i))
        (_ : ∀ i, Algebra R (T i)) (_ : S ≃ₐ[R] Π i, T i),
        ∀ i, HenselianLocalRing (T i) ∧ Module.Finite R (T i)) ∧
      ∀ c : S ⧸ (maximalIdeal R).map (algebraMap R S), IsIdempotentElem c →
        ∃! e : S, IsIdempotentElem e ∧ Ideal.Quotient.mk _ e = c) ∧
    (CommAlgCat.FiniteEtale.baseChange.{u} R (ResidueField R)).IsEquivalence ∧
    ∀ (L : Type u) [Field L] [Algebra (ResidueField R) L] [Module.Finite (ResidueField R) L]
      [Algebra.IsSeparable (ResidueField R) L],
      ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A), Module.Finite R A ∧ Algebra.Etale R A ∧
        HenselianLocalRing A ∧ Nonempty (ResidueField R ⊗[R] A ≃ₐ[ResidueField R] L) := by
  refine ⟨fun S _ _ _ ↦ ⟨_root_.GlobalTheory.exists_algEquiv_pi_henselianLocalRing R S,
    fun c hc ↦ _root_.GlobalTheory.existsUnique_idempotent_lift_quotient R hc⟩, ?_,
    fun L _ _ _ _ ↦ _root_.GlobalTheory.exists_etale_henselian_lift_of_isSeparable R L⟩
  refine
    { faithful := ⟨fun {X Y} f g h ↦ ?_⟩
      full := ⟨fun {X Y} φ ↦ ?_⟩
      essSurj := ⟨fun Y ↦ ?_⟩ }
  · have : Algebra.Etale R X.obj := X.property.2
    have : Module.Finite R Y.obj := Y.property.1
    exact ObjectProperty.hom_ext _ (CommAlgCat.hom_ext
      ((_root_.GlobalTheory.bijective_baseChange_residueField_of_etale R X.obj Y.obj).1
        (congrArg (fun φ ↦ φ.hom.hom) h)))
  · have : Algebra.Etale R X.obj := X.property.2
    have : Module.Finite R Y.obj := Y.property.1
    obtain ⟨f, hf⟩ := (_root_.GlobalTheory.bijective_baseChange_residueField_of_etale R X.obj Y.obj).2 φ.hom.hom
    exact ⟨ObjectProperty.homMk (CommAlgCat.ofHom f),
      ObjectProperty.hom_ext _ (CommAlgCat.hom_ext hf)⟩
  · have : Algebra.Etale (ResidueField R) Y.obj := Y.property.2
    obtain ⟨A, _, _, hfin, het, ⟨e⟩⟩ := _root_.GlobalTheory.exists_etale_lift_of_etale.{u, u} R Y.obj
    exact ⟨⟨CommAlgCat.of R A, ⟨hfin, het⟩⟩, ⟨ObjectProperty.isoMk _ (CommAlgCat.isoMk e)⟩⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteGaloisApproximationStatement
section
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_galois_approximation : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ S : Gal p Ω → Finset Ω, ∃ F : Finset (Gal p Ω), ∀ h : Gal p Ω, ∃ g ∈ F, ∀ x ∈ S g, h x = g x := by
  first | exact @GlobalTheory.K5.gal_finite_subcover | exact GlobalTheory.K5.gal_finite_subcover | (intros; apply GlobalTheory.K5.gal_finite_subcover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankEichlerShimuraCoboundariesOfGammaLeStatement
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_b1_eq_of_gamma_le : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (w : ℕ), 0 < M → 1 ≤ w → CongruenceSubgroup.Gamma M ≤ Γ → Module.finrank ℂ (B1 Γ w) = w + 1 := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.finrank_eichlerShimuraCoboundaries_of_Gamma_le | exact GlobalTheory.HeckeFamilyMatrices.finrank_eichlerShimuraCoboundaries_of_Gamma_le | (intros; apply GlobalTheory.HeckeFamilyMatrices.finrank_eichlerShimuraCoboundaries_of_Gamma_le <;> assumption)
end

