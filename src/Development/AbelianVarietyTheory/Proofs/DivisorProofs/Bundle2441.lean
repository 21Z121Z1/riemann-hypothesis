import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0027
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaGeneratorsLeastValueOverLevelPrime
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0168
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0084
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0044
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2234
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2214
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2264
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2206
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummandDualAnnihilatorReductionProjective
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualSummand

open Module Submodule

variable {R : Type} [CommRing R] {C : Type*} [AddCommGroup C] [Module R C]

theorem isCompl_dualAnnihilator {K N : Submodule R C} (h : IsCompl K N) :
    IsCompl K.dualAnnihilator N.dualAnnihilator := by
  constructor
  · rw [disjoint_iff, eq_bot_iff]
    intro f hf
    rw [mem_inf, mem_dualAnnihilator, mem_dualAnnihilator] at hf
    rw [mem_bot]
    ext c
    rw [← projection_add_projection_eq_self h c, map_add, hf.1 _ (projection_apply_mem h c),
      hf.2 _ (projection_apply_mem h.symm c)]
    simp
  · rw [codisjoint_iff, eq_top_iff]
    intro f _
    have e : f = f ∘ₗ N.projection K h.symm + f ∘ₗ K.projection N h := by
      ext c
      simp only [LinearMap.add_apply, LinearMap.comp_apply]
      rw [← map_add, add_comm, projection_add_projection_eq_self h c]
    rw [e]
    refine add_mem_sup ?_ ?_
    · rw [mem_dualAnnihilator]
      intro k hk
      simp [projection_apply_of_mem_right h.symm hk]
    · rw [mem_dualAnnihilator]
      intro n hn
      simp [projection_apply_of_mem_right h hn]

theorem dualAnnihilator_dualCoannihilator_eq [Projective R C] {K N : Submodule R C}
    (h : IsCompl K N) : K.dualAnnihilator.dualCoannihilator = K := by
  refine le_antisymm (fun c hc => ?_) (le_dualAnnihilator_dualCoannihilator _)
  rw [mem_dualCoannihilator] at hc
  have hn : N.projection K h.symm c = 0 := by
    rw [← forall_dual_apply_eq_zero_iff R]
    intro φ
    have := hc (φ ∘ₗ N.projection K h.symm) (by
      rw [mem_dualAnnihilator]
      intro k hk
      simp [projection_apply_of_mem_right h.symm hk])
    simpa using this
  rw [← projection_add_projection_eq_self h c, hn, add_zero]
  exact projection_apply_mem h c

theorem mem_smul_top_of_forall_dual [Projective R C] (I : Ideal R) (c : C)
    (h : ∀ x : Dual R C, x c ∈ I) : c ∈ I • (⊤ : Submodule R C) := by
  obtain ⟨s, hs⟩ := projective_def.mp (inferInstance : Projective R C)
  rw [← hs c, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun m _ => ?_
  exact smul_mem_smul (by simpa using h (Finsupp.lapply m ∘ₗ s)) mem_top

variable {R₀ : Type} [CommRing R₀] {π : R →+* R₀} {C₀ : Type*} [AddCommGroup C₀] [Module R₀ C₀]

theorem exists_dual_lift [Projective R C] (hπ : Function.Surjective π) (ρ : C →ₛₗ[π] C₀)
    (y : Dual R₀ C₀) : ∃ x : Dual R C, ∀ c, π (x c) = y (ρ c) := by
  obtain ⟨s, hs⟩ := projective_def.mp (inferInstance : Projective R C)
  refine ⟨Finsupp.linearCombination R (fun m => Function.surjInv hπ (y (ρ m))) ∘ₗ s, fun c => ?_⟩
  conv_rhs => rw [← hs c]
  simp only [LinearMap.comp_apply, Finsupp.linearCombination_apply, Finsupp.sum, map_sum,
    smul_eq_mul, map_mul, Function.surjInv_eq, LinearMap.map_smulₛₗ, id, RingHom.id_apply]

theorem exists_dual_descent {ρ : C →ₛₗ[π] C₀} (hπ : Function.Surjective π)
    (hρ : Function.Surjective ρ) (hker : ∀ c, ρ c = 0 ↔ c ∈ RingHom.ker π • (⊤ : Submodule R C))
    (x : Dual R C) : ∃ y : Dual R₀ C₀, ∀ c, y (ρ c) = π (x c) := by
  have hI : RingHom.ker π • (⊤ : Submodule R C) ≤ Submodule.comap x (RingHom.ker π) := by
    rw [Submodule.smul_le]
    intro r hr n _
    rw [Submodule.mem_comap, map_smul, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hr
  have hx : ∀ a b, ρ a = ρ b → π (x a) = π (x b) := by
    intro a b hab
    have h1 : a - b ∈ RingHom.ker π • (⊤ : Submodule R C) := (hker _).mp (by rw [map_sub, hab, sub_self])
    have h2 := hI h1
    rw [Submodule.mem_comap, map_sub] at h2
    rw [← sub_eq_zero, ← map_sub]
    exact (RingHom.mem_ker).mp h2
  let g := Function.surjInv hρ
  have hg : ∀ v, ρ (g v) = v := Function.surjInv_eq hρ
  refine ⟨{ toFun := fun v => π (x (g v)), map_add' := ?_, map_smul' := ?_ }, fun c => hx _ _ (hg _)⟩
  · intro a b
    rw [show π (x (g a)) + π (x (g b)) = π (x (g a + g b)) by simp]
    exact hx _ _ (by rw [map_add, hg, hg, hg])
  · intro r v
    obtain ⟨r', rfl⟩ := hπ r
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [← map_mul, ← smul_eq_mul, ← map_smul]
    exact hx _ _ (by rw [LinearMap.map_smulₛₗ, hg, hg])

end GlobalTheory.DualSummand

namespace GlobalTheory.DualSummand

open Module Submodule

variable {R : Type} [CommRing R] {C : Type*} [AddCommGroup C] [Module R C]
variable {R₀ : Type} [CommRing R₀] {π : R →+* R₀} {C₀ : Type*} [AddCommGroup C₀] [Module R₀ C₀]

theorem eq_zero_of_forall_dual_reduction [Projective R C] {ρ : C →ₛₗ[π] C₀}
    (hπ : Function.Surjective π) (hρ : Function.Surjective ρ)
    (hker : ∀ c, ρ c = 0 ↔ c ∈ RingHom.ker π • (⊤ : Submodule R C))
    (v : C₀) (hv : ∀ φ : Dual R₀ C₀, φ v = 0) : v = 0 := by
  obtain ⟨c, rfl⟩ := hρ v
  rw [hker]
  refine mem_smul_top_of_forall_dual _ c fun x => ?_
  obtain ⟨y, hy⟩ := exists_dual_descent hπ hρ hker x
  rw [RingHom.mem_ker, ← hy]
  exact hv y

theorem exists_eq_dualAnnihilator [Projective R C] [Module.Finite R C]
    {G H : Submodule R (Dual R C)} (hGH : IsCompl G H) :
    ∃ K : Submodule R C, (∃ N, IsCompl K N) ∧ G = K.dualAnnihilator := by
  have hsurj : ∀ ψ : Dual R (Dual R C), ∃ k : C, ∀ φ : Dual R C, φ k = ψ φ := by
    intro ψ
    obtain ⟨k, hk⟩ := (Module.bijective_dual_eval R C).2 ψ
    exact ⟨k, fun φ => by rw [← hk, Dual.eval_apply]⟩
  have hsplit : ∀ φ : Dual R C, G.projection H hGH φ + H.projection G hGH.symm φ = φ :=
    projection_add_projection_eq_self hGH
  have hKL : IsCompl G.dualCoannihilator H.dualCoannihilator := by
    constructor
    · rw [disjoint_iff, eq_bot_iff]
      intro c hc
      rw [mem_inf, mem_dualCoannihilator, mem_dualCoannihilator] at hc
      rw [mem_bot, ← forall_dual_apply_eq_zero_iff R]
      intro φ
      rw [← hsplit φ, LinearMap.add_apply, hc.1 _ (projection_apply_mem hGH φ),
        hc.2 _ (projection_apply_mem hGH.symm φ), add_zero]
    · rw [codisjoint_iff, eq_top_iff]
      intro c _
      obtain ⟨k, hk⟩ := hsurj (Dual.eval R C c ∘ₗ H.projection G hGH.symm)
      obtain ⟨l, hl⟩ := hsurj (Dual.eval R C c ∘ₗ G.projection H hGH)
      refine Submodule.mem_sup.mpr ⟨k, ?_, l, ?_, ?_⟩
      · rw [mem_dualCoannihilator]
        intro g hg
        rw [hk g]
        simp [projection_apply_of_mem_right hGH.symm hg]
      · rw [mem_dualCoannihilator]
        intro h hh
        rw [hl h]
        simp [projection_apply_of_mem_right hGH hh]
      · rw [← sub_eq_zero, ← forall_dual_apply_eq_zero_iff R]
        intro φ
        rw [map_sub, map_add, hk φ, hl φ]
        simp only [LinearMap.comp_apply, Dual.eval_apply]
        rw [← LinearMap.add_apply, add_comm, hsplit φ, sub_self]
  refine ⟨G.dualCoannihilator, ⟨_, hKL⟩, le_antisymm ?_ ?_⟩
  · intro g hg
    rw [mem_dualAnnihilator]
    intro k hk
    exact (mem_dualCoannihilator _).mp hk g hg
  · intro φ hφ
    rw [mem_dualAnnihilator] at hφ
    have h0 : H.projection G hGH.symm φ = 0 := by
      ext c
      obtain ⟨k, hk, l, hl, rfl⟩ := Submodule.mem_sup.mp (hKL.sup_eq_top ▸ mem_top : c ∈ _)
      have e : H.projection G hGH.symm φ = φ - G.projection H hGH φ := by
        rw [eq_sub_iff_add_eq, add_comm, hsplit φ]
      rw [map_add, (mem_dualCoannihilator _).mp hl _ (projection_apply_mem hGH.symm φ), e,
        LinearMap.sub_apply, hφ k hk, (mem_dualCoannihilator _).mp hk _ (projection_apply_mem hGH φ)]
      simp
    rw [← hsplit φ, h0, add_zero]
    exact projection_apply_mem hGH φ

end GlobalTheory.DualSummand

namespace GlobalTheory.LiftSys

open Module Submodule GlobalTheory.DualSummand

theorem summand_dual_reduction :
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → ∀ (C C₀ : Type 1) [AddCommGroup C] [Module R C] [AddCommGroup C₀] [Module R₀ C₀], Module.Finite R C → Module.Projective R C → ∀ ρ : C →ₛₗ[π] C₀, Function.Surjective ρ → (∀ c, ρ c = 0 ↔ c ∈ RingHom.ker π • (⊤ : Submodule R C)) → ∀ F₀ : Submodule R₀ C₀, (∃ N₀, IsCompl F₀ N₀) → (∀ K : Submodule R C, (∃ N, IsCompl K N) → (∃ N, IsCompl K.dualAnnihilator N) ∧ K.dualAnnihilator.dualCoannihilator = K ∧ ((∀ c, c ∈ K ⊔ RingHom.ker π • ⊤ ↔ ρ c ∈ F₀) ↔ ∀ y : Module.Dual R₀ C₀, y ∈ F₀.dualAnnihilator ↔ ∃ x ∈ K.dualAnnihilator, ∀ c, y (ρ c) = π (x c))) ∧ ∀ G : Submodule R (Module.Dual R C), (∃ N, IsCompl G N) → ∃ K : Submodule R C, (∃ N, IsCompl K N) ∧ G = K.dualAnnihilator := by
  intro R R₀ _ _ π hπ C C₀ _ _ _ _ _ _ ρ hρ hker F₀ ⟨N₀, hF⟩
  refine ⟨fun K ⟨N, hKN⟩ => ⟨⟨_, isCompl_dualAnnihilator hKN⟩,
    dualAnnihilator_dualCoannihilator_eq hKN, ?_⟩, fun G ⟨H, hGH⟩ => exists_eq_dualAnnihilator hGH⟩
  have hsplit : ∀ c, K.projection N hKN c + N.projection K hKN.symm c = c :=
    projection_add_projection_eq_self hKN
  have hNK : ∀ k ∈ K, N.projection K hKN.symm k = 0 := fun k hk =>
    projection_apply_of_mem_right hKN.symm hk
  constructor
  · intro hL y
    constructor
    · intro hy
      rw [mem_dualAnnihilator] at hy
      obtain ⟨x₀, hx₀⟩ := exists_dual_lift hπ ρ y
      refine ⟨x₀ ∘ₗ N.projection K hKN.symm, ?_, fun c => ?_⟩
      · rw [mem_dualAnnihilator]
        intro k hk
        simp [hNK k hk]
      · rw [LinearMap.comp_apply, hx₀]
        conv_lhs => rw [← hsplit c]
        rw [map_add, map_add,
          hy _ ((hL _).mp (mem_sup_left (projection_apply_mem hKN c))), zero_add]
    · rintro ⟨x, hx, hxy⟩
      rw [mem_dualAnnihilator] at hx ⊢
      intro f hf
      obtain ⟨c, rfl⟩ := hρ f
      obtain ⟨k, hk, m, hm, rfl⟩ := Submodule.mem_sup.mp ((hL c).mpr hf)
      rw [map_add, (hker m).mpr hm, add_zero, hxy, hx k hk, map_zero]
  · intro hR c
    constructor
    · intro hc
      obtain ⟨k, hk, m, hm, rfl⟩ := Submodule.mem_sup.mp hc
      rw [map_add, (hker m).mpr hm, add_zero]
      have hv : N₀.projection F₀ hF.symm (ρ k) = 0 := by
        refine eq_zero_of_forall_dual_reduction hπ hρ hker _ fun φ => ?_
        obtain ⟨x, hx, hxy⟩ := (hR (φ ∘ₗ N₀.projection F₀ hF.symm)).mp (by
          rw [mem_dualAnnihilator]
          intro f hf
          simp [projection_apply_of_mem_right hF.symm hf])
        have := hxy k
        rw [LinearMap.comp_apply] at this
        rw [this, (mem_dualAnnihilator _).mp hx k hk, map_zero]
      rw [← projection_add_projection_eq_self hF (ρ k), hv, add_zero]
      exact projection_apply_mem hF _
    · intro hc
      rw [← hsplit c]
      refine add_mem_sup (projection_apply_mem hKN c) ?_
      refine mem_smul_top_of_forall_dual _ _ fun x₀ => ?_
      obtain ⟨y, hy⟩ := exists_dual_descent hπ hρ hker (x₀ ∘ₗ N.projection K hKN.symm)
      have hyF : y ∈ F₀.dualAnnihilator := (hR y).mpr ⟨x₀ ∘ₗ N.projection K hKN.symm, by
        rw [mem_dualAnnihilator]
        intro k hk
        simp [hNK k hk], hy⟩
      rw [RingHom.mem_ker, ← LinearMap.comp_apply, ← hy]
      exact (mem_dualAnnihilator _).mp hyF _ hc

end GlobalTheory.LiftSys
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupLatticeReferenceExponentThetaWeightLevelLeOne
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.RefLevel

theorem lattice_terms_le {κ R s N d g' V r φ cst : ℝ} (hκ : 0 ≤ κ) (hR : 0 ≤ R) (hs : 0 ≤ s) (hsN : s ≤ N) (hV : 0 < V)
    (hr : 0 < r) (hφ : 0 ≤ φ) (hg' : 0 < g') (hc : κ * N ^ 3 * (R * N / 4 + 2 * d ^ 2) / g' ≤ cst) :
    (R * s * (κ * s ^ 3 * (r * φ)) / (4 * g') + 2 * d ^ 2 * (κ * s ^ 3 * (r * φ)) / g') / (r * V) ≤ cst * φ / V := by
  have hN : 0 ≤ N := hs.trans hsN
  calc (R * s * (κ * s ^ 3 * (r * φ)) / (4 * g') + 2 * d ^ 2 * (κ * s ^ 3 * (r * φ)) / g') / (r * V)
      = κ * s ^ 3 * (R * s / 4 + 2 * d ^ 2) / g' * φ / V := by field_simp
    _ ≤ κ * N ^ 3 * (R * N / 4 + 2 * d ^ 2) / g' * φ / V := by gcongr
    _ ≤ cst * φ / V := by gcongr

theorem not_isUnit_of_vV_ne_zero (S : CDVR) (N : ℕ) (h : vV S.V ((N : ℕ) : S.Fr) ≠ 0) : ¬ IsUnit ((N : ℕ) : S.V) := by
  intro hu
  apply h
  have h2 : valV S.V (algebraMap S.V S.Fr ((N : ℕ) : S.V)) = 1 := by
    unfold valV
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (mem_nonunits_iff.1 h) hu
  rw [map_natCast] at h2
  unfold vV
  rw [h2]
  simp

theorem vV_pos {K : Type} [Field K] [NumberField K] {p : ℕ} (hp : p ≠ 0) {la : HeightOneSpectrum (𝓞 K)}
    (hla : (p : 𝓞 K) ∈ la.asIdeal) {T : CDVR} {io : K →+* T.Fr} {k : ℕ} (ho : OverLa la T.V io k) :
    0 < vV T.V (p : T.Fr) := by
  have h := ho.2 (p : K)
  rw [map_natCast] at h
  rw [h]
  refine mul_pos (by exact_mod_cast ho.1) ?_
  have h1 : la.valuation K (p : K) < 1 := by
    have := (la.valuation_lt_one_iff_mem (K := K) (p : 𝓞 K)).2 hla
    have e : ((p : 𝓞 K) : K) = (p : K) := map_natCast (algebraMap (𝓞 K) K) p
    rw [← e]
    exact this
  have h0 : la.valuation K (p : K) ≠ 0 := (Valuation.ne_zero_iff _).2 (Nat.cast_ne_zero.2 hp)
  have := (WithZero.log_lt_log h0 one_ne_zero).2 h1
  rw [WithZero.log_one] at this
  unfold vLa
  omega

theorem coprime_level (D : D7) (k : Fin 2) : Nat.Coprime (D.host.g k) (D.host.QS * D.host.q * D.host.d) := by
  have hc : D.host.g k % (D.host.QS * D.host.q * D.host.d) = 1 := D.ntypes.g_cond k
  rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hc]
  simp

theorem refExp_le_of_halfSplit (D : D7) (T : Core D) (hM : LawsM T) (j : ℕ) (hj : InR D j)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (cst : ℝ) (hDom : Dom a n) (hLast : LastPos (T.Q.Dw j) a)
    (hrn : 2 * D.R.r ≤ n) (g g' : ℕ) (ρ ρ' : 𝓞 D.host.E) (hH : HalfSplit T.Q.l g g' ρ ρ')
    (hcop : Nat.Coprime (g * g') (D.host.QS * D.host.q * D.host.d)) (hg : 4 * DF (T.Q.Dw j) a + 4 ≤ g)
    (hg' : 4 * DF (T.Q.Dw j) a + 4 ≤ g') (hM0 : (DF (T.Q.Dw j) a : ℝ) * (2 * Real.sqrt (2 * D.R.f * D.R.m)) < g')
    (hc : rr0 D * (2 * D.R.f * D.R.m : ℝ) ^ 3 *
      ((D.R.r : ℝ) * (2 * D.R.f * D.R.m) / 4 + 2 * (DF (T.Q.Dw j) a : ℝ) ^ 2) / g' ≤ cst) :
    refExp_vp (T.U j) cst (wtZ a n) g ≤ ((1 : ℝ) : EReal) := by
  rw [refExp_vp_le_iff]
  intro la S io e ho y hy φ hφ
  obtain ⟨st, nab, hn⟩ :=
    GlobalTheory.CanonConn.exists_isNab_uncond D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c
  have hst := GlobalTheory.PowGerm.starSt _ T.Q.H st hn.1
  subst hst
  letI := T.Q.H.starRing
  obtain ⟨-, -, -, -, -, hE, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q hM.pins
  obtain ⟨hpq, hr1, -⟩ := hnum j hj
  have hq : (T.Q.Dw j).q = D.R.m - j := (hM.pins.2.2.2 j hj).2.1
  obtain ⟨hTot, hcusp⟩ := GlobalTheory.thetaRules_exist_and_cusp D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r (T.U j) hr1
    (hM.unf j hj) nab hn
  obtain ⟨S', io', y', r, C, P, hy', hr, hFT, hTI, hφ', hOv, hvv, hnv⟩ :=
    GlobalTheory.T.exists_finiteExtension_uniformisedChart_scale D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S io y hy φ hφ
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S'.V
  obtain ⟨⟨Q, hQ⟩, -⟩ :=
    GlobalTheory.PowData.exists_powData D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S' io' y' C P ϖ hϖ
  obtain ⟨s, hs, hΦ, b, hb1, hb2⟩ :=
    GlobalTheory.T.exists_short_periodLattice_basis_balanced_slope D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S' io' y' _ hφ' C P ϖ hϖ Q hQ
  obtain ⟨m, hmfin, hmle, hmeq⟩ :=
    GlobalTheory.ThetaLow.thetaRule_bounded_below D T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c nab hn g g' ρ ρ' hH hcop a n
  obtain ⟨hgp, hgp', hne, hMl, hρ, hρ', hMb, hsp, -⟩ := hH
  have hρs : ρ * star ρ = (g : 𝓞 D.host.E) := hρ
  have hρs' : ρ' * star ρ' = (g' : 𝓞 D.host.E) := hρ'
  have hV : 0 < vV S.V (g : S.Fr) := vV_pos hgp.ne_zero la.2 ho
  have hV' := hvv g hgp.ne_zero
  have hrZ : (0 : ℤ) < r := by exact_mod_cast hr
  have hsN : (s : ℝ) ≤ 2 * D.R.f * D.R.m := by
    rw [hE, hq] at hs
    exact_mod_cast hs.trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : ℕ, vV S.V (g : S.Fr) = e₀ := ⟨_, (Int.toNat_of_nonneg hV.le).symm⟩
  have he₀0 : 0 < e₀ := by omega
  have hA := GlobalTheory.LevelPrimePoint.least_value_le GlobalTheory.ChF.hodgeTate_inclusion_chart D.host.E T.Q.H (T.Q.Dw j) T.Q.l
    (T.Q.Xo j) T.Q.c nab hn hTot S' io' y' C hFT P hTI hy' ϖ hϖ Q hQ _ _ s b hΦ hb1 hb2 g g' hgp hgp' hne hMl ρ ρ'
    hρs hρs' hMb hsp.1 hsp.2 (not_isUnit_of_vV_ne_zero S' g (by rw [hV']; exact (mul_pos hrZ hV).ne')) a n (r * e₀)
    hDom.1 (by rw [hpq]; exact hrn) (by omega) (Nat.mul_pos hr he₀0) (by omega) hg'
    (lt_of_le_of_lt (by gcongr) hM0)
  have hν : (∏ τ : D.host.E →+* ℂ, (io' (embK T.Q.c τ (star ρ * star ρ'))) ^ (∑ i : Fin ((T.Q.Dw j).mult τ), a (τ, i))) =
      io' (nrm (T.Q.Dw j) T.Q.c a (star ρ * star ρ')) := by
    unfold nrm
    simp only [map_prod, map_pow]
  have hν0 : nrm (T.Q.Dw j) T.Q.c a (star ρ * star ρ') ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ fun h0 => ?_
    have h1 : (star ρ * star ρ') * (ρ * ρ') = ((g * g' : ℕ) : 𝓞 D.host.E) := by
      rw [Nat.cast_mul, ← hρs, ← hρs']; ring
    have h2 := congrArg (embK T.Q.c τ) h1
    rw [map_mul, h0, zero_mul, map_natCast] at h2
    exact (Nat.cast_ne_zero.2 (Nat.mul_ne_zero hgp.ne_zero hgp'.ne_zero)) h2.symm
  rw [hν, hpq, hV', he₀, nval_of_ne ((map_ne_zero io').2 hν0)] at hA
  generalize nrm (T.Q.Dw j) T.Q.c a (star ρ * star ρ') = ν at hA hν0 hmeq
  generalize hN : ((vV S'.V (io' ν) : ℝ) / ((r * e₀ : ℕ) : ℝ) : ℝ) = N at hA
  have hlt : (⨅ f ∈ thGen (T.Q.Xo j) T.Q.c nab a n, nval S'.V (r * e₀) (evI y' f)) <
      ((1 + cst * φ / e₀ - N : ℝ) : EReal) := by
    rw [← EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)), ← EReal.coe_sub] at hA
    refine hA.trans_lt (EReal.coe_lt_coe_iff.2 (sub_lt_sub_right ?_ _))
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr
    have heR : (0 : ℝ) < e₀ := by exact_mod_cast he₀0
    have hgR : (4 : ℝ) * DF (T.Q.Dw j) a + 4 ≤ g := by exact_mod_cast hg
    have hd0 : (0 : ℝ) ≤ DF (T.Q.Dw j) a := Nat.cast_nonneg _
    rw [add_assoc, add_div]
    push_cast
    refine add_lt_add_of_lt_of_le ?_ (lattice_terms_le (by positivity) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hsN heR hrR
      hφ.nonneg (by exact_mod_cast hgp'.pos) hc)
    rw [mul_div_assoc, mul_div_cancel_left₀ _ (mul_pos hrR heR).ne', div_lt_one (by linarith)]
    linarith
  simp only [iInf_lt_iff] at hlt
  obtain ⟨f, hf, hlt⟩ := hlt
  obtain ⟨t, ht0, htv, w, hw, hwe⟩ := GlobalTheory.T.cuspForm_clear_denominators_away_from_place D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r (T.U j)
    (wtZ a n) ⟨f, hcusp a n hDom hLast f hf⟩ m hmfin (hmle f hf) la.1 (-vLa la.1 ν) fun v hv => by
      have h := hmle f hf la.1 v hv
      rw [hmeq la.1 (Or.inl la.2)] at h
      rw [Int.cast_neg]
      exact h
  have ho' := hOv la.1 e ho
  refine (iInf₂_le w hw).trans ?_
  show nval S.V (vV S.V (g : S.Fr)).toNat (evI y (w : Rul (T.Q.Xo j) T.Q.c)) ≤ _
  rw [hwe, evI_smul, he₀, Int.toNat_natCast, ← hnv nab hn a n e₀ t f hf, nval_mul, nval_of_ne ((map_ne_zero io').2 ht0),
    ho'.2 t, htv, neg_neg, ← ho'.2 ν, hN]
  refine (add_le_add le_rfl hlt.le).trans (le_of_eq ?_)
  rw [← EReal.coe_add, ← EReal.coe_add]
  congr 1
  push_cast
  ring

theorem refExp_level_le_one : ∀ (D : D7) (T : Core D), LawsM T → ∀ (_ : ErrX D) (j : ℕ), InR D j → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (cst : ℝ), Dom a n → LastPos (T.Q.Dw j) a → ∑ f : Lt1 (T.Q.Dw j), 2 * rk f ≤ n → 2 * D.R.r ≤ n → JetNum D (DF (T.Q.Dw j) a) cst → ∀ k : Fin 2, refExp_vp (T.U j) cst (wtZ a n) (D.host.g k) ≤ ((1 : ℝ) : EReal) := by
  intro D T hM EX j hj a n cst hDom hLast _ hrn hJ k
  obtain ⟨π, π', hH⟩ := GlobalTheory.SplitLevel.level_halfSplit D T hM EX
  obtain ⟨k', ρ, ρ', hk⟩ : ∃ (k' : Fin 2) (ρ ρ' : 𝓞 D.host.E), HalfSplit T.Q.l (D.host.g k) (D.host.g k') ρ ρ' := by
    fin_cases k
    · exact ⟨1, π, π', hH⟩
    · exact ⟨0, π', π, hH.symm⟩
  exact refExp_le_of_halfSplit D T hM j hj a n cst hDom hLast hrn _ _ ρ ρ' hk
    (Nat.Coprime.mul_left (coprime_level D k) (coprime_level D k')) (hJ k).1 (hJ k').1 (hJ k').2.1 (hJ k').2.2

end GlobalTheory.RefLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricTwoCocycleFreeAbelianIsCoboundary
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CoboundaryRoots

@[ext] structure CocExt (X A : Type) where
  fst : X
  snd : A

variable {X : Type} [AddCommGroup X] {A : Type} [CommGroup A]

theorem coc_zero_left (f : X → X → A)
    (hc : ∀ a b c, f (a + b) c * f a b = f a (b + c) * f b c) (c : X) : f 0 c = f 0 0 := by
  have h := hc 0 0 c
  simp only [add_zero, zero_add] at h
  exact (mul_left_cancel h).symm

theorem mul_mul_mul_inv_inv' (x y z : A) : x * y * z * x⁻¹ * y⁻¹ = z := by
  calc x * y * z * x⁻¹ * y⁻¹ = z * (x * x⁻¹) * (y * y⁻¹) := by ac_rfl
    _ = z := by simp

def extGroup (f : X → X → A) (hs : ∀ a b, f a b = f b a)
    (hc : ∀ a b c, f (a + b) c * f a b = f a (b + c) * f b c) : AddCommGroup (CocExt X A) :=
  letI : Add (CocExt X A) := ⟨fun p q => ⟨p.fst + q.fst, p.snd * q.snd * f p.fst q.fst⟩⟩
  letI : Zero (CocExt X A) := ⟨⟨0, (f 0 0)⁻¹⟩⟩
  letI : Neg (CocExt X A) := ⟨fun p => ⟨-p.fst, (p.snd * f p.fst (-p.fst) * f 0 0)⁻¹⟩⟩
  { add_assoc := fun p q r => by
        refine CocExt.ext (add_assoc p.fst q.fst r.fst) ?_
        show p.snd * q.snd * f p.fst q.fst * r.snd * f (p.fst + q.fst) r.fst
          = p.snd * (q.snd * r.snd * f q.fst r.fst) * f p.fst (q.fst + r.fst)
        calc p.snd * q.snd * f p.fst q.fst * r.snd * f (p.fst + q.fst) r.fst
            = p.snd * q.snd * r.snd * (f (p.fst + q.fst) r.fst * f p.fst q.fst) := by ac_rfl
          _ = p.snd * q.snd * r.snd * (f p.fst (q.fst + r.fst) * f q.fst r.fst) := by rw [hc]
          _ = _ := by ac_rfl
    zero_add := fun p => by
        refine CocExt.ext (zero_add p.fst) ?_
        show (f 0 0)⁻¹ * p.snd * f 0 p.fst = p.snd
        rw [coc_zero_left f hc p.fst, mul_comm (f 0 0)⁻¹ p.snd, inv_mul_cancel_right]
    add_zero := fun p => by
        refine CocExt.ext (add_zero p.fst) ?_
        show p.snd * (f 0 0)⁻¹ * f p.fst 0 = p.snd
        rw [hs p.fst 0, coc_zero_left f hc p.fst, inv_mul_cancel_right]
    nsmul := nsmulRec
    zsmul := zsmulRec
    neg_add_cancel := fun p => by
        refine CocExt.ext (neg_add_cancel p.fst) ?_
        show (p.snd * f p.fst (-p.fst) * f 0 0)⁻¹ * p.snd * f (-p.fst) p.fst = (f 0 0)⁻¹
        rw [hs (-p.fst) p.fst]; group
    add_comm := fun p q => by
        refine CocExt.ext (add_comm p.fst q.fst) ?_
        show p.snd * q.snd * f p.fst q.fst = q.snd * p.snd * f q.fst p.fst
        rw [hs, mul_comm p.snd q.snd] }

end GlobalTheory.CoboundaryRoots

namespace GlobalTheory

theorem symm_cocycle_isCoboundary : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] (A : Type) [CommGroup A] (f : X → X → A), (∀ a b, f a b = f b a) → (∀ a b c, f (a + b) c * f a b = f a (b + c) * f b c) → ∃ g : X → A, ∀ a b, f a b = g (a + b) * (g a)⁻¹ * (g b)⁻¹ := by
  intro X _ _ A _ f hs hc
  letI : AddCommGroup (GlobalTheory.CoboundaryRoots.CocExt X A) := GlobalTheory.CoboundaryRoots.extGroup f hs hc
  let bs := Module.Free.chooseBasis ℤ X
  let s : X →ₗ[ℤ] GlobalTheory.CoboundaryRoots.CocExt X A := bs.constr ℤ (fun i => ⟨bs i, 1⟩)
  let π : GlobalTheory.CoboundaryRoots.CocExt X A →+ X :=
    { toFun := GlobalTheory.CoboundaryRoots.CocExt.fst, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hcomp : π.toIntLinearMap.comp s = LinearMap.id :=
    bs.ext (fun i => by
      show π (s (bs i)) = bs i
      rw [show s (bs i) = ⟨bs i, 1⟩ from bs.constr_basis ℤ _ i]
      rfl)
  have hπ : ∀ x, (s x).fst = x := fun x => LinearMap.congr_fun hcomp x
  refine ⟨fun x => (s x).snd, fun a b => ?_⟩
  have h : (s (a + b)).snd = (s a).snd * (s b).snd * f (s a).fst (s b).fst :=
    congrArg GlobalTheory.CoboundaryRoots.CocExt.snd (s.map_add a b)
  rw [hπ, hπ] at h
  show f a b = (s (a + b)).snd * ((s a).snd)⁻¹ * ((s b).snd)⁻¹
  rw [h, GlobalTheory.CoboundaryRoots.mul_mul_mul_inv_inv']

end GlobalTheory
end

