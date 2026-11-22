import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmHostRootComplexEqPmSqrt
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ConclusionsAtIdentity
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0008
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsKroneckerCharIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0056
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0030
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraEigenDecompositionCMSignature
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DegreeLieLatticesCmTripleBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0031
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0041
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0278
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0242
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0080

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CmCurveTorsionDefinedOverOfWeberValues
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin.CurveField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_periodPair (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    ∃ L : PeriodPair, ∀ x, x ∈ L.lattice ↔ ∃ s, x = wC H s := by
  have hd : 7 ≤ H.d := by have := H.d_mod; omega
  have hs : √(H.d : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < H.d))).ne'
  refine ⟨⟨1, (1 + Complex.I * Real.sqrt H.d) / 2, LinearIndependent.pair_iff.2 fun a b h => ?_⟩, fun x => ?_⟩
  · have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp [hs] at h1 h2
    simp [h2] at h1
    exact ⟨h1, h2⟩
  · rw [GlobalTheory.CompRat.Weber.exists_wC_iff, PeriodPair.mem_lattice]
    simp only [_root_.mul_one]
    exact ⟨fun ⟨m, n, e⟩ => ⟨m, n, e.symm⟩, fun ⟨m, n, e⟩ => ⟨m, n, e.symm⟩⟩

theorem actsBy_of_dvd {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (C : Curve H) (τ : ℂ ≃+* ℂ) (ι : _) {n m : ℕ}
    (hn : 0 < n) (hm : m ∣ n) (s : ℤ × ℤ) (h : C.ActsBy τ ι n s) : C.ActsBy τ ι m s := by
  obtain ⟨k, rfl⟩ := hm
  have hk : (k : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mul_pos_left hn).ne'
  have e : ∀ a : ℤ × ℤ, wC H (k * a.1, k * a.2) = k * wC H a := fun a => by
    simp only [wC]; push_cast; ring
  refine ⟨h.1, fun a => ?_⟩
  have h2 := h.2 (k * a.1, k * a.2)
  rw [e, Nat.cast_mul, mul_left_comm, mul_comm (m : ℂ), mul_div_mul_left _ _ hk, mul_div_mul_left _ _ hk] at h2
  exact h2

theorem curveOver_of_weberIn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (F : IntermediateField ℚ ℂ) (n : ℕ), 0 < n → (H.rt0 ∈ F → WeberIn H F n → CurveOver H F n) ∧ ∀ m, m ∣ n → CurveOver H F n → CurveOver H F m := by
  intro E _ _ _ H F n hn
  refine ⟨fun h0 hW τ hτ => ?_, fun m hm h τ hτ => ?_⟩
  · obtain ⟨L, hL⟩ := exists_periodPair H
    exact GlobalTheory.CompRat.Weber.fixesCurve_of_weber E H L n hn hL τ (hτ _ h0) (hτ _ (hW L hL).1)
      fun s hs => hτ _ ((hW L hL).2 s hs)
  · obtain ⟨C, ι, h'⟩ := h τ hτ
    exact ⟨C, ι, actsBy_of_dvd C τ ι hn hm _ h'⟩

end GlobalTheory.FinalJoin.CurveField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.EqOfLeOfISupIndep
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM.NumCompare

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.DegreeIdentityCharacter

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]

variable {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ}

theorem pure_decomposition (X : CMObj H K ρ σ₁ p q) (b : Bool) (F : GenFib (X.A b).pol) :
    (∀ τ : 𝓞 E →+* 𝓞 K, latRank K (F.eigLat (X.A b).t.act τ) =
      open Classical in if τ H.rt = (if b then ρ else -ρ) then 1 else 0) ∧
    iSupIndep (fun τ : 𝓞 E →+* 𝓞 K => Submodule.span K (F.eigLat (X.A b).t.act τ : Set (Fin F.P₀.g → K))) ∧
    ⨆ τ : 𝓞 E →+* 𝓞 K, Submodule.span K (F.eigLat (X.A b).t.act τ : Set (Fin F.P₀.g → K)) = ⊤ ∧
    F.P₀.g = Module.finrank ℚ E / 2 := by
  cases b
  · obtain ⟨a, b, c, d, -⟩ := EigDec.eigen_decomposition E H K (-ρ) _ F 1 0 X.split
      (Test.hasType_neg X.ρ_sq X.typeM) (by rw [neg_sq, X.ρ_sq])
    exact ⟨a, b, c, by rw [F.fib.1]; simpa using d⟩
  · obtain ⟨a, b, c, d, -⟩ := EigDec.eigen_decomposition E H K ρ _ F 1 0 X.split X.typeP X.ρ_sq
    exact ⟨a, b, c, by rw [F.fib.1]; simpa using d⟩

def MultiplierNonneg : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K)
    (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q) (j : Fin p ⊕ Fin q) (s : K →+* ℂ) (τ : 𝓞 E →+* 𝓞 K),
    0 ≤ (s (τ (X.hh j) : K)).re

section Linear

variable {k V J : Type} [Field k] [AddCommGroup V] [Module k V]

theorem eq_of_le_of_iSupIndep {N W : J → Submodule k V} (hle : ∀ i, N i ≤ W i) (hW : iSupIndep W)
    (hN : ⨆ i, N i = ⊤) (i : J) : W i ≤ N i := by
  have h₁ : (⊤ : Submodule k V) = N i ⊔ ⨆ j, ⨆ _ : j ≠ i, N j := by rw [← hN, iSup_split_single N i]
  have h₂ : Disjoint (W i) (⨆ j, ⨆ _ : j ≠ i, N j) := (hW i).mono_right (iSup₂_mono fun j _ => hle j)
  have h₃ := sup_inf_assoc_of_le (⨆ j, ⨆ _ : j ≠ i, N j) (hle i)
  rw [← h₁, top_inf_eq, h₂.symm.eq_bot, sup_bot_eq] at h₃
  exact h₃.le

variable [FiniteDimensional k V] [Fintype J]

theorem indep_of_sum_le {N : J → Submodule k V} {n : J → ℕ} (h : ⨆ i, N i = ⊤) (hn : ∀ i, Module.finrank k (N i) ≤ n i)
    (hd : ∑ i, n i ≤ Module.finrank k V) : iSupIndep N ∧ ∀ i, Module.finrank k (N i) = n i := by
  classical
  have hs : Function.Surjective (DirectSum.coeLinearMap N) := by
    rw [← LinearMap.range_eq_top, DirectSum.range_coeLinearMap, h]
  have h₁ := LinearMap.finrank_le_finrank_of_surjective hs
  have h₂ : ∑ i, Module.finrank k (N i) ≤ ∑ i, n i := Finset.sum_le_sum fun i _ => hn i
  have he : Module.finrank k (DirectSum J fun i => N i) = Module.finrank k V := by
    rw [Module.finrank_directSum] at h₁ ⊢
    omega
  refine ⟨DirectSum.IsInternal.submodule_iSupIndep
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank he).2 hs, hs⟩, fun i => ?_⟩
  rw [Module.finrank_directSum] at he
  exact (Finset.sum_eq_sum_iff_of_le fun i _ => hn i).1 (by omega) i (Finset.mem_univ _)

theorem sum_finrank_eq {N : J → Submodule k V} (hi : iSupIndep N) (h : ⨆ i, N i = ⊤) :
    ∑ i, Module.finrank k (N i) = Module.finrank k V := by
  classical
  rw [← Module.finrank_directSum]
  exact (LinearEquiv.ofBijective (DirectSum.coeLinearMap N)
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hi h)).finrank_eq

end Linear

theorem ind_concl_iff (X : CMObj H K ρ σ₁ p q) (FA : ∀ b, GenFib (X.A b).pol) (FB : GenFib X.B.pol)
    (M : ∀ j : Fin p ⊕ Fin q, (Fin (FA j.isLeft).P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)) :
    (let N : (Fin p ⊕ Fin q) × (𝓞 E →+* 𝓞 K) → Submodule (𝓞 K) (Fin FB.P₀.g → K) := fun x =>
      ((FA x.1.isLeft).eigLat (X.A x.1.isLeft).t.act x.2).map ((M x.1).restrictScalars (𝓞 K))
    (∀ x, N x ≤ FB.eigLat X.B.t.act x.2) ∧
    (∀ x, latRank K (N x) = open Classical in if x.2 H.rt = (if x.1.isLeft then ρ else -ρ) then 1 else 0) ∧
    (∀ j, Function.Injective (M j)) ∧
    iSupIndep (fun x => Submodule.span K (N x : Set (Fin FB.P₀.g → K))) ∧
    ⨆ x, Submodule.span K (N x : Set (Fin FB.P₀.g → K)) = ⊤) ↔
    ∀ τ : 𝓞 E →+* 𝓞 K,
      (∀ j : Fin p ⊕ Fin q, ∀ c ∈ (FA j.isLeft).eigLat (X.A j.isLeft).t.act τ, M j c ∈ FB.eigLat X.B.t.act τ) ∧
      (FB.eigLat X.B.t.act τ : Set (Fin FB.P₀.g → K)) ⊆
        Submodule.span K {y | ∃ j : Fin p ⊕ Fin q, ∃ c ∈ (FA j.isLeft).eigLat (X.A j.isLeft).t.act τ, y = M j c} := by
  classical
  set N : (Fin p ⊕ Fin q) × (𝓞 E →+* 𝓞 K) → Submodule (𝓞 K) (Fin FB.P₀.g → K) := fun x =>
    ((FA x.1.isLeft).eigLat (X.A x.1.isLeft).t.act x.2).map ((M x.1).restrictScalars (𝓞 K)) with hN
  obtain ⟨-, hBi, hBt, hBg, -⟩ := EigDec.eigen_decomposition E H K ρ X.B FB p q X.split X.typeB X.ρ_sq
  have hset : ∀ τ : 𝓞 E →+* 𝓞 K,
      Submodule.span K {y | ∃ j : Fin p ⊕ Fin q, ∃ c ∈ (FA j.isLeft).eigLat (X.A j.isLeft).t.act τ, y = M j c} =
        ⨆ j, Submodule.span K (N (j, τ) : Set (Fin FB.P₀.g → K)) := fun τ => by
    rw [← Submodule.span_iUnion]
    congr 1
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    exact exists_congr fun j => ⟨fun ⟨c, h, e⟩ => ⟨c, h, e.symm⟩, fun ⟨c, h, e⟩ => ⟨c, h, e.symm⟩⟩
  simp only [hset]
  refine ⟨fun ⟨h₁, _, _, _, h₅⟩ τ => ⟨fun j c hc => h₁ (j, τ) ⟨c, hc, rfl⟩, ?_⟩, fun h => ?_⟩
  · refine Submodule.subset_span.trans (eq_of_le_of_iSupIndep
      (N := fun τ => ⨆ j, Submodule.span K (N (j, τ) : Set (Fin FB.P₀.g → K)))
      (fun τ => iSup_le fun j => Submodule.span_mono (h₁ (j, τ))) hBi ?_ τ)
    rw [iSup_comm, ← h₅, iSup_prod]
  haveI : Finite (𝓞 E →+* 𝓞 K) := (Nat.card_pos_iff.1 (X.split ▸ Module.finrank_pos)).2
  haveI := Fintype.ofFinite (𝓞 E →+* 𝓞 K)
  have hA := fun b => pure_decomposition X b (FA b)
  have htop : ⨆ x, Submodule.span K (N x : Set (Fin FB.P₀.g → K)) = ⊤ := by
    rw [iSup_prod, iSup_comm, eq_top_iff, ← hBt]
    exact iSup_mono fun τ => Submodule.span_le.2 (h τ).2
  have hspan : ∀ x, Submodule.span K (N x : Set (Fin FB.P₀.g → K)) =
      (Submodule.span K ((FA x.1.isLeft).eigLat (X.A x.1.isLeft).t.act x.2 : Set _)).map (M x.1) := fun x => by
    rw [Submodule.map_span]
    rfl
  have hdim : ∑ j : Fin p ⊕ Fin q, Module.finrank K (Fin (FA j.isLeft).P₀.g → K) =
      Module.finrank K (Fin FB.P₀.g → K) := by
    have : FB.P₀.g = Module.finrank ℚ E / 2 * (p + q) := FB.fib.1.trans hBg
    simp [(hA _).2.2.2, this, mul_comm]
  obtain ⟨hi, hr⟩ := indep_of_sum_le (n := fun x : (Fin p ⊕ Fin q) × (𝓞 E →+* 𝓞 K) =>
    latRank K ((FA x.1.isLeft).eigLat (X.A x.1.isLeft).t.act x.2)) htop
    (fun x => by rw [hspan]; exact Submodule.finrank_map_le _ _) (by
      rw [← hdim, Fintype.sum_prod_type]
      exact le_of_eq (Finset.sum_congr rfl fun j _ => sum_finrank_eq (hA j.isLeft).2.1 (hA j.isLeft).2.2.1))
  have hsur : ⨆ j, LinearMap.range (M j) = ⊤ := by
    rw [eq_top_iff, ← htop]
    exact iSup_le fun x => (hspan x).le.trans (LinearMap.map_le_range.trans (le_iSup (fun j => LinearMap.range (M j)) x.1))
  refine ⟨fun x => ?_, fun x => (hr x).trans ((hA _).1 _), fun j => ?_, hi, htop⟩
  · rintro _ ⟨c, hc, rfl⟩
    exact (h x.2).1 x.1 c hc
  · have h₁ := (indep_of_sum_le hsur (fun j => LinearMap.finrank_range_le (M j)) hdim.le).2 j
    have := LinearMap.finrank_range_add_finrank_ker (M j)
    rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
    omega

end GlobalTheory.CM.NumCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.InvariantIsAlgebraic
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FinalJoin GlobalTheory.CompRat Formalism.MainNotions.StandardLatticesGL3

namespace GlobalTheory.WeberField

theorem weber_isAlgebraic (L : PeriodPair) (hj : IsAlgebraic ℚ (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)))
    {n : ℕ} (hn : 0 < n) {t : ℂ} (ht : t ∉ L.lattice) (hnt : (n : ℂ) * t ∈ L.lattice) :
    IsAlgebraic ℚ (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) := by
  have hD := g₂_cube_sub_g₃_sq_ne_zero L
  obtain ⟨m, hm⟩ := IsAlgClosed.exists_pow_nat_eq (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) (n := 12) (by norm_num)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hD (by simpa using hm.symm)
  have H := isHomothetic_scalePeriods L m hm0
  set L' := scalePeriods L m hm0
  have e2 : L'.g₂ ^ 3 = L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
    rw [H.g₂_eq, ← hm]; field_simp
  have e3 : L'.g₃ ^ 2 = (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) - 1) / 27 := by
    rw [H.g₃_eq, mul_pow, inv_pow, ← pow_mul, hm]; field_simp; ring
  have hjm := mem_algebraicClosure_iff.mpr hj
  have h2 : L'.g₂ ∈ algebraicClosure ℚ ℂ :=
    mem_algebraicClosure_iff.mpr (IsAlgebraic.of_pow three_pos (e2 ▸ hj))
  have h3 : L'.g₃ ∈ algebraicClosure ℚ ℂ := by
    refine mem_algebraicClosure_iff.mpr (IsAlgebraic.of_pow two_pos ?_)
    rw [← mem_algebraicClosure_iff, e3]
    exact div_mem (sub_mem hjm (one_mem _)) (ofNat_mem _ 27)
  have hp := (GlobalTheory.CurveAlgebraic.weierstrassP_mem L' h2 h3 hn (t := m * t) (fun h => ht ((H t).1 h))
    (by rw [mul_left_comm]; exact (H _).2 hnt)).1
  have e : L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t =
      L'.g₂ * L'.g₃ * L'.weierstrassP (m * t) := by
    rw [H.g₂_eq, H.g₃_eq, H.weierstrassP_mul, ← hm]; field_simp
  rw [e]
  exact mem_algebraicClosure_iff.mp (mul_mem (mul_mem h2 h3) hp)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem invariant_isAlgebraic (H : Host E) (L : PeriodPair) (hL : ∀ x, x ∈ L.lattice ↔ ∃ s, x = wC H s) :
    IsAlgebraic ℚ (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) := by
  obtain ⟨a, τ, ha, h⟩ := exists_lattice_eq_mul_tau L
  have key : ∀ y : ℂ, y ∈ Submodule.span ℤ {(τ : ℂ), 1} ↔ a * y ∈ L.lattice := fun y ↦ by
    rw [h, Submodule.mem_span_pair]
    simp [mul_right_inj' ha]
  have hi : IsIntegral ℤ (modularJ τ) := by
    refine isIntegral_modularJ_of_mul_mem (α := wC H (0, 1)) (fun m hm => ?_) fun x hx => ?_
    · have e : H.rt0 = ((2 * m - 1 : ℤ) : ℂ) := by
        simp only [wC] at hm
        push_cast at hm ⊢
        linear_combination 2 * hm
      have e' := H.sqrt_neg_disc_sq
      rw [e] at e'
      have e'' : (2 * m - 1) ^ 2 = -(H.d : ℤ) := by exact_mod_cast e'
      have := H.d_prime.pos
      nlinarith [sq_nonneg (2 * m - 1)]
    · rw [key] at hx ⊢
      obtain ⟨s, hs⟩ := (hL _).1 hx
      obtain ⟨b, hb⟩ := Weber.wC_mul H (0, 1) s
      rw [mul_left_comm, hs, hb]
      exact (hL _).2 ⟨b, rfl⟩
  rw [← g₂_cube_div_eq_modularJ ha h] at hi
  have := div_mem (mem_algebraicClosure_iff.mpr (hi.tower_top (A := ℚ)).isAlgebraic)
    (ofNat_mem (algebraicClosure ℚ ℂ) 1728)
  rw [mul_div_assoc, mul_div_cancel_left₀ _ (by norm_num)] at this
  exact mem_algebraicClosure_iff.mp this

end GlobalTheory.WeberField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.KFourierCoefficientRapidDecay
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.KFourier
open MeasureTheory

theorem hs_nonneg' {n : ℕ} (y : Mx n) : 0 ≤ hs y := by
  show 0 ≤ ∑ i, ∑ j, ‖y i j‖ ^ 2
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem kFourier_coeff_decay : ∀ {n : ℕ} (ε : Fin n → Bool) (N : ℕ) (F : List (Mx n) → Mx n → ℂ), IsDerFam ε F → FamGrowth ε N F → ContinuousOn (F []) (UJset ε) → ∀ e : ℕ → KG ε → ℂ, (∀ i, GlobalTheory.KFourier.IsKer ε i (e i)) → ∀ u : List (Mx n), (∀ X ∈ u, inK ε X) → ∃ b : ℕ → ℝ, Summable b ∧ ∀ i, ∀ y ∈ UJset ε, ‖∫ k, e i k * F u (y * toMK k) ∂(muK ε)‖ ≤ b i * (1 + hs y) ^ N := by
  intro n ε N F hD hG hC e he u hu
  obtain ⟨r, X, hX, hsp⟩ := GlobalTheory.T.exists_finite_real_spanning_compactLieAlgebra ε
  obtain ⟨c, α, hc, hα, hgap⟩ := GlobalTheory.T.compactUnitary_polynomial_spectral_gap ε X hX hsp
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (n : ℝ) ^ 2 + 2 < α * M := by
    obtain ⟨M, hM⟩ := exists_nat_gt (((n : ℝ) ^ 2 + 2) / α)
    exact ⟨M, by rw [div_lt_iff₀ hα] at hM; linarith⟩
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.compactUnitaryCasimir_pow_pairing_moderateGrowth_bound ε N F hD hG hC X hX 0 u hu
  obtain ⟨C, hCM⟩ := GlobalTheory.T.compactUnitaryCasimir_pow_pairing_moderateGrowth_bound ε N F hD hG hC X hX M u hu
  have hlnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ ((c * x ^ α) ^ M)⁻¹ := fun x hx =>
    inv_nonneg.mpr (pow_nonneg (mul_nonneg hc.le (Real.rpow_nonneg hx _)) _)
  let B : ℕ → ℝ := fun i => |C| * ((c * (i : ℝ) ^ α) ^ M)⁻¹ * ((i : ℝ) + 1) ^ (n ^ 2)
  refine ⟨fun i => if i = 0 then |C0| * Real.sqrt (Module.finrank ℂ (polyV ε 0)) else B i, ?_, ?_⟩
  · refine (summable_nat_add_iff 1).mp ?_
    have hp : (n : ℝ) ^ 2 - α * M < -1 := by linarith
    have hsm : Summable (fun i : ℕ => ((i + 1 : ℕ) : ℝ) ^ ((n : ℝ) ^ 2 - α * M)) :=
      (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hp)
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (hsm.mul_left (|C| * (c ^ M)⁻¹ * 2 ^ (n ^ 2)))
    · simp only [Nat.add_one_ne_zero, if_false, B]
      exact mul_nonneg (mul_nonneg (abs_nonneg _) (hlnn _ (Nat.cast_nonneg _))) (by positivity)
    · simp only [Nat.add_one_ne_zero, if_false, B]
      set x : ℝ := ((i + 1 : ℕ) : ℝ) with hx
      have hx1 : 1 ≤ x := by simp [hx]
      have hx0 : 0 < x := by linarith
      have e1 : (c * x ^ α) ^ M = c ^ M * x ^ (α * M) := by
        rw [mul_pow, ← Real.rpow_mul_natCast hx0.le]
      have e2 : (x + 1) ^ (n ^ 2) ≤ 2 ^ (n ^ 2) * x ^ ((n : ℝ) ^ 2) := by
        rw [show ((n : ℝ) ^ 2) = ((n ^ 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, ← mul_pow]
        exact pow_le_pow_left₀ (by linarith) (by linarith) _
      have e3 : x ^ ((n : ℝ) ^ 2 - α * M) = x ^ ((n : ℝ) ^ 2) * (x ^ (α * M))⁻¹ := by
        rw [Real.rpow_sub hx0, div_eq_mul_inv]
      rw [e1, e3, mul_inv]
      have h0 : 0 ≤ |C| * (c ^ M)⁻¹ * (x ^ (α * M))⁻¹ :=
        mul_nonneg (mul_nonneg (abs_nonneg _) (inv_nonneg.mpr (pow_nonneg hc.le _)))
          (inv_nonneg.mpr (Real.rpow_nonneg hx0.le _))
      calc |C| * ((c ^ M)⁻¹ * (x ^ (α * M))⁻¹) * (x + 1) ^ (n ^ 2)
          = (|C| * (c ^ M)⁻¹ * (x ^ (α * M))⁻¹) * (x + 1) ^ (n ^ 2) := by ring
        _ ≤ (|C| * (c ^ M)⁻¹ * (x ^ (α * M))⁻¹) * (2 ^ (n ^ 2) * x ^ ((n : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left e2 h0
        _ = _ := by ring
  · intro i y hy
    have hy0 : 0 ≤ (1 + hs y) ^ N := pow_nonneg (by linarith [hs_nonneg' y]) _
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp only [if_true]
      have h := hC0 0 (e 0) (he 0).1 y hy
      simp only [Function.iterate_zero, id] at h
      have hk := GlobalTheory.T.integral_normSq_reproducingKernel_le_finrank ε 0 (e 0) (he 0)
      calc _ ≤ C0 * (1 + hs y) ^ N * Real.sqrt (∫ k, ‖e 0 k‖ ^ 2 ∂(muK ε)) := h
        _ ≤ |C0| * (1 + hs y) ^ N * Real.sqrt (Module.finrank ℂ (polyV ε 0)) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self _) hy0) (Real.sqrt_le_sqrt hk)
              (Real.sqrt_nonneg _) (mul_nonneg (abs_nonneg _) hy0)
        _ = _ := by ring
    · have hi0 : i ≠ 0 := hi.ne'
      simp only [hi0, if_false]
      have hl : 0 < c * (i : ℝ) ^ α := mul_pos hc (Real.rpow_pos_of_pos (by exact_mod_cast hi) _)
      obtain ⟨s, hsP, hse, hsn⟩ := GlobalTheory.T.compactUnitaryCasimir_inverse_topDegree_bound ε X hX i (c * (i : ℝ) ^ α) hl
        (fun p hp hq => hgap i hi p hp hq) M (e i) (he i).1
        (fun q hq => by rw [← (he i).2.1 q hq]; congr 1; funext k; ring)
      have h := hCM i s hsP y hy
      rw [hse] at h
      have hk := GlobalTheory.T.integral_normSq_reproducingKernel_le_finrank ε i (e i) (he i)
      have hd : (Module.finrank ℂ (polyV ε i) : ℝ) ≤ ((i : ℝ) + 1) ^ (2 * n ^ 2) := by
        exact_mod_cast GlobalTheory.T.finrank_compactUnitaryPolyFunDegLE_le ε i
      have hsq : Real.sqrt (∫ k, ‖s k‖ ^ 2 ∂(muK ε)) ≤
          ((c * (i : ℝ) ^ α) ^ M)⁻¹ * ((i : ℝ) + 1) ^ (n ^ 2) := by
        have h1 : ∫ k, ‖s k‖ ^ 2 ∂(muK ε) ≤ (((c * (i : ℝ) ^ α) ^ M)⁻¹ * ((i : ℝ) + 1) ^ (n ^ 2)) ^ 2 := by
          calc _ ≤ ((c * (i : ℝ) ^ α) ^ (2 * M))⁻¹ * ∫ k, ‖e i k‖ ^ 2 ∂(muK ε) := hsn
            _ ≤ ((c * (i : ℝ) ^ α) ^ (2 * M))⁻¹ * (((i : ℝ) + 1) ^ (2 * n ^ 2)) :=
                mul_le_mul_of_nonneg_left (hk.trans hd) (inv_nonneg.mpr (pow_nonneg hl.le _))
            _ = _ := by rw [mul_pow ((c * (i : ℝ) ^ α) ^ M)⁻¹, inv_pow, ← pow_mul, ← pow_mul, mul_comm M 2, mul_comm (n ^ 2) 2]
        calc _ ≤ Real.sqrt ((((c * (i : ℝ) ^ α) ^ M)⁻¹ * ((i : ℝ) + 1) ^ (n ^ 2)) ^ 2) :=
              Real.sqrt_le_sqrt h1
          _ = _ := Real.sqrt_sq (mul_nonneg (hlnn _ (Nat.cast_nonneg _)) (by positivity))
      calc _ ≤ C * (1 + hs y) ^ N * Real.sqrt (∫ k, ‖s k‖ ^ 2 ∂(muK ε)) := h
        _ ≤ |C| * (1 + hs y) ^ N * Real.sqrt (∫ k, ‖s k‖ ^ 2 ∂(muK ε)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hy0) (Real.sqrt_nonneg _)
        _ ≤ |C| * (1 + hs y) ^ N * (((c * (i : ℝ) ^ α) ^ M)⁻¹ * ((i : ℝ) + 1) ^ (n ^ 2)) :=
            mul_le_mul_of_nonneg_left hsq (mul_nonneg (abs_nonneg _) hy0)
        _ = _ := by simp only [B]; ring

end GlobalTheory.KFourier
end
end

