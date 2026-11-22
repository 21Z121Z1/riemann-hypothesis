import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleUnitaryVectorDensity
section
open scoped InnerProductSpace

namespace GlobalTheory

namespace IrreducibleUnitaryDensity

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {n : ℕ}

noncomputable def diag (n : ℕ) (T : H →L[ℂ] H) :
    PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j => T.comp (PiLp.proj 2 (fun _ : Fin n => H) j))

@[simp] lemma diag_apply (T : H →L[ℂ] H) (x : PiLp 2 (fun _ : Fin n => H)) (j : Fin n) :
    diag n T x j = T (x j) := rfl

noncomputable def incl (j : Fin n) : H →L[ℂ] PiLp 2 (fun _ : Fin n => H) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℂ (fun _ : Fin n => H) j)

lemma incl_apply (j : Fin n) (x : H) (i : Fin n) :
    (incl j x : PiLp 2 (fun _ : Fin n => H)) i = (Pi.single j x : Fin n → H) i := rfl

lemma diag_incl (T : H →L[ℂ] H) (j : Fin n) (x : H) :
    diag n T (incl j x) = incl j (T x) := by
  ext i
  simp only [diag_apply, incl_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

lemma sum_incl (x : PiLp 2 (fun _ : Fin n => H)) : ∑ j, incl j (x j) = x := by
  ext i
  simp [incl_apply, Finset.sum_apply]

lemma comm_diag (P : PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H))
    (c : Fin n → Fin n → ℂ) (hc : ∀ i j x, P (incl j x) i = c i j • x) (T : H →L[ℂ] H)
    (x : PiLp 2 (fun _ : Fin n => H)) : P (diag n T x) = diag n T (P x) := by
  rw [← sum_incl x]
  simp only [map_sum, diag_incl]
  refine Finset.sum_congr rfl fun j _ => ?_
  ext i
  simp [hc]

end IrreducibleUnitaryDensity

open IrreducibleUnitaryDensity in

theorem irreducibleUnitary_density (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (G : Type) [Group G] (π : G →* (H →L[ℂ] H)) (hu : ∀ g x, ‖π g x‖ = ‖x‖)
    (hs : ∀ B : H →L[ℂ] H, (∀ g, B.comp (π g) = (π g).comp B) →
      ∃ c : ℂ, B = c • ContinuousLinearMap.id ℂ H)
    (n : ℕ) (a : Fin n → H) (Λ : Fin n → (H →L[ℂ] ℂ)) (h : ∀ g, ∑ j, Λ j (π g (a j)) = 0)
    (φ u : H) : ∑ j, ⟪φ, a j⟫_ℂ * Λ j u = 0 := by
  let a' : PiLp 2 (fun _ : Fin n => H) := WithLp.toLp 2 a
  let S : Submodule ℂ (PiLp 2 (fun _ : Fin n => H)) :=
    Submodule.span ℂ (Set.range fun g => diag n (π g) a')
  let W := S.topologicalClosure
  have hmul : ∀ g g' x, diag n (π g) (diag n (π g') x) = diag n (π (g * g')) x := by
    intro g g' x; ext i; simp
  have hone : ∀ x, diag n (π 1) x = x := by
    intro x; ext i; simp
  have hclos : ∀ (K : Submodule ℂ (PiLp 2 (fun _ : Fin n => H))), IsClosed (K : Set (PiLp 2 (fun _ : Fin n => H))) →
      (∀ g, diag n (π g) a' ∈ K) → W ≤ K := by
    intro K hK hg
    refine Submodule.topologicalClosure_minimal S ?_ hK
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, rfl⟩
    exact hg g
  have hgen : ∀ g, diag n (π g) a' ∈ W := fun g =>
    S.le_topologicalClosure (Submodule.subset_span ⟨g, rfl⟩)
  have hinv : ∀ g, ∀ x ∈ W, diag n (π g) x ∈ W := by
    intro g x hx
    have := hclos (W.comap (diag n (π g)).toLinearMap)
      (S.isClosed_topologicalClosure.preimage (diag n (π g)).continuous)
      (fun g' => by
        change diag n (π g) (diag n (π g') a') ∈ W
        rw [hmul]; exact hgen _) hx
    exact this
  have hinner : ∀ g (x y : H), ⟪π g x, π g y⟫_ℂ = ⟪x, y⟫_ℂ := fun g x y =>
    (LinearIsometry.mk (π g).toLinearMap (hu g)).inner_map_map x y
  have hinner' : ∀ g x y, ⟪diag n (π g) x, diag n (π g) y⟫_ℂ = ⟪x, y⟫_ℂ := by
    intro g x y
    simp [PiLp.inner_apply, hinner]
  have hinv' : ∀ g, ∀ x ∈ Wᗮ, diag n (π g) x ∈ Wᗮ := by
    intro g x hx
    rw [Submodule.mem_orthogonal] at hx ⊢
    intro w hw
    have h1 : w = diag n (π g) (diag n (π g⁻¹) w) := by rw [hmul, mul_inv_cancel, hone]
    rw [h1, hinner']
    exact hx _ (hinv _ _ hw)
  haveI : CompleteSpace W := S.isClosed_topologicalClosure.completeSpace_coe
  let P := W.starProjection
  have hP : ∀ g x, P (diag n (π g) x) = diag n (π g) (P x) := by
    intro g x
    refine Submodule.eq_starProjection_of_mem_orthogonal (hinv g _ (W.starProjection_apply_mem x)) ?_
    rw [← map_sub]
    exact hinv' g _ (W.sub_starProjection_mem_orthogonal x)
  have hblock : ∀ i j : Fin n, ∃ c : ℂ, ∀ x, P (incl j x) i = c • x := by
    intro i j
    obtain ⟨c, hc⟩ := hs ((PiLp.proj 2 (fun _ : Fin n => H) i).comp (P.comp (incl j))) (by
      intro g
      ext x
      change P (incl j (π g x)) i = π g (P (incl j x) i)
      rw [← diag_incl, hP, diag_apply])
    exact ⟨c, fun x => by simpa using congrArg (fun B : H →L[ℂ] H => B x) hc⟩
  choose c hc using hblock
  let R : H →L[ℂ] H := (innerSL ℂ φ).smulRight u
  have ha : a' ∈ W := hone a' ▸ hgen 1
  have hRa : diag n R a' ∈ W := by
    have h1 : P a' = a' := Submodule.starProjection_eq_self_iff.2 ha
    rw [← h1, ← comm_diag P c hc]
    exact W.starProjection_apply_mem _
  let L : PiLp 2 (fun _ : Fin n => H) →L[ℂ] ℂ :=
    ∑ j, (Λ j).comp (PiLp.proj 2 (fun _ : Fin n => H) j)
  have hL : ∀ x, L x = ∑ j, Λ j (x j) := by
    intro x; simp [L]
  have hker : W ≤ LinearMap.ker L.toLinearMap := by
    refine hclos _ (ContinuousLinearMap.isClosed_ker L) fun g => ?_
    change L _ = 0
    rw [hL]
    exact h g
  have h0 : L (diag n R a') = 0 := hker hRa
  rw [hL] at h0
  simpa [R, a'] using h0

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotypicFactorOfIsIrreduciblePiFiniteGroups
section
namespace GlobalTheory.PiIsotypic

open Representation

theorem nontrivial_of_isIrreducible {K G V : Type} [Field K] [Group G] [AddCommGroup V]
    [Module K V] (ρ : Representation K G V) (h : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  haveI := h
  exact bot_ne_top (α := Subrepresentation ρ)
    (Subrepresentation.ext (Submodule.eq_bot_of_subsingleton (p := (⊤ : Submodule K V))).symm)

theorem exists_irreducible_subrep {K G V : Type} [Field K] [Group G] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Nontrivial V] (ρ : Representation K G V) :
    ∃ S : Subrepresentation ρ, S.toRepresentation.IsIrreducible := by
  classical
  have hex : ∃ m : ℕ, ∃ S : Subrepresentation ρ, S.toSubmodule ≠ ⊥ ∧
      Module.finrank K S.toSubmodule = m :=
    ⟨_, ⟨⊤, fun _ _ _ => Submodule.mem_top⟩, top_ne_bot, rfl⟩
  obtain ⟨S, hS, hm⟩ := Nat.find_spec hex
  have hmin : ∀ T : Subrepresentation ρ, T.toSubmodule ≠ ⊥ →
      Module.finrank K S.toSubmodule ≤ Module.finrank K T.toSubmodule := by
    intro T hT
    rw [hm]
    exact Nat.find_min' hex ⟨T, hT, rfl⟩
  have : Nontrivial S.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hS
  refine ⟨S, ?_⟩
  have : Nontrivial (Subrepresentation S.toRepresentation) :=
    ⟨⊥, ⊤, fun h => by
      have h' : (⊥ : Submodule K S.toSubmodule) = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact bot_ne_top h'⟩
  refine ⟨fun T => ?_⟩
  by_cases hT : T.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hT)
  · right
    let T' : Subrepresentation ρ := ⟨T.toSubmodule.map S.toSubmodule.subtype, by
      rintro g _ ⟨v, hv, rfl⟩
      exact ⟨S.toRepresentation g v, T.apply_mem_toSubmodule g hv, rfl⟩⟩
    have hT' : T'.toSubmodule ≠ ⊥ := by
      intro h
      apply hT
      have h2 : T.toSubmodule.map S.toSubmodule.subtype = ⊥ := h
      rwa [← Submodule.map_bot S.toSubmodule.subtype,
        (Submodule.map_injective_of_injective S.toSubmodule.injective_subtype).eq_iff] at h2
    have h1 := hmin T' hT'
    have h2 : Module.finrank K T'.toSubmodule = Module.finrank K T.toSubmodule :=
      Submodule.finrank_map_subtype_eq _ _
    have h3 : T.toSubmodule = ⊤ :=
      Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) (h2 ▸ h1))
    exact Subrepresentation.toSubmodule_injective h3

def subrepOrderIso {K G V V' : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] (σ : Representation K G V) (τ : Representation K G V')
    (e : V ≃ₗ[K] V') (he : ∀ g v, τ g (e v) = e (σ g v)) :
    Subrepresentation σ ≃o Subrepresentation τ where
  toFun T := ⟨T.toSubmodule.map (e : V →ₗ[K] V'), by
    rintro g _ ⟨v, hv, rfl⟩
    exact ⟨σ g v, T.apply_mem_toSubmodule g hv, (he g v).symm⟩⟩
  invFun U := ⟨U.toSubmodule.comap (e : V →ₗ[K] V'), by
    intro g v hv
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hv ⊢
    rw [← he]
    exact U.apply_mem_toSubmodule g hv⟩
  left_inv T := Subrepresentation.ext (Submodule.comap_map_eq_of_injective e.injective _)
  right_inv U := Subrepresentation.ext (Submodule.map_comap_eq_of_surjective e.surjective _)
  map_rel_iff' {a b} := by
    show a.toSubmodule.map (e : V →ₗ[K] V') ≤ b.toSubmodule.map (e : V →ₗ[K] V') ↔
      a.toSubmodule ≤ b.toSubmodule
    exact Submodule.map_le_map_iff_of_injective e.injective _ _

theorem isIrreducible_of_linearEquiv {K G V V' : Type} [Field K] [Group G] [AddCommGroup V]
    [Module K V] [AddCommGroup V'] [Module K V'] (σ : Representation K G V)
    (τ : Representation K G V') (e : V ≃ₗ[K] V') (he : ∀ g v, τ g (e v) = e (σ g v))
    (h : σ.IsIrreducible) : τ.IsIrreducible := by
  haveI := h
  exact (subrepOrderIso σ τ e he).symm.isSimpleOrder

end GlobalTheory.PiIsotypic

namespace GlobalTheory.PiIsotypic

open Representation

theorem isotypic_factor_of_isIrreducible_pi : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, Finite (G i)] (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (∀ i, G i) W), ρ.IsIrreducible → ∀ i, ∃ (n : ℕ) (τ : Representation ℂ (G i) (Fin n → ℂ)), τ.IsIrreducible ∧ (∃ φ : (Fin n → ℂ) →ₗ[ℂ] W, Function.Injective φ ∧ ∀ g z, φ (τ g z) = ρ (Pi.mulSingle i g) (φ z)) ∧ Submodule.span ℂ {y | ∃ φ : (Fin n → ℂ) →ₗ[ℂ] W, (∀ g z, φ (τ g z) = ρ (Pi.mulSingle i g) (φ z)) ∧ y ∈ LinearMap.range φ} = ⊤ := by
  intro ι _ _ G _ _ W _ _ _ ρ hρ i
  classical
  haveI : Nontrivial W := nontrivial_of_isIrreducible ρ hρ
  let ρi : Representation ℂ (G i) W := ρ.comp (MonoidHom.mulSingle G i)
  obtain ⟨S, hS⟩ := exists_irreducible_subrep ρi
  let n := Module.finrank ℂ S.toSubmodule
  let e : S.toSubmodule ≃ₗ[ℂ] (Fin n → ℂ) :=
    LinearEquiv.ofFinrankEq _ _ (by simp [n])
  let τ : Representation ℂ (G i) (Fin n → ℂ) :=
    { toFun := fun g => e.toLinearMap ∘ₗ S.toRepresentation g ∘ₗ e.symm.toLinearMap
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hτe : ∀ g v, τ g (e v) = e (S.toRepresentation g v) := by
    intro g v; simp [τ]
  have hτ : τ.IsIrreducible := isIrreducible_of_linearEquiv S.toRepresentation τ e hτe hS
  let φ0 : (Fin n → ℂ) →ₗ[ℂ] W := S.toSubmodule.subtype ∘ₗ e.symm.toLinearMap
  have hφ0 : ∀ g z, φ0 (τ g z) = ρ (Pi.mulSingle i g) (φ0 z) := by
    intro g z
    simp [φ0, τ]
    rfl
  have hinj : Function.Injective φ0 :=
    Subtype.val_injective.comp e.symm.injective
  refine ⟨n, τ, hτ, ⟨φ0, hinj, hφ0⟩, ?_⟩
  set T : Set W := {y | ∃ φ : (Fin n → ℂ) →ₗ[ℂ] W,
    (∀ g z, φ (τ g z) = ρ (Pi.mulSingle i g) (φ z)) ∧ y ∈ LinearMap.range φ} with hTdef
  have hstab : ∀ g y, y ∈ T → ρ g y ∈ T := by
    rintro g y ⟨φ, hφ, hy⟩
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.1 hy
    let g' : ∀ j, G j := g * Pi.mulSingle i (g i)⁻¹
    have hcomm : ∀ h : G i, g' * Pi.mulSingle i h = Pi.mulSingle i h * g' := by
      intro h
      funext j
      by_cases hj : j = i
      · subst hj
        simp [g']
      · simp [g', Pi.mulSingle_eq_of_ne hj]
    have hg : g = g' * Pi.mulSingle i (g i) := by
      simp only [g', mul_assoc, ← Pi.mulSingle_mul, inv_mul_cancel, Pi.mulSingle_one, mul_one]
    refine ⟨ρ g' ∘ₗ φ, ?_, LinearMap.mem_range.2 ⟨τ (g i) z, ?_⟩⟩
    · intro h z'
      simp only [LinearMap.comp_apply]
      rw [hφ, ← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply]
    · simp only [LinearMap.comp_apply]
      rw [hφ, ← Module.End.mul_apply, ← map_mul, ← hg]
  let U : Subrepresentation ρ := ⟨Submodule.span ℂ T, fun g v hv => by
    have hle : Submodule.span ℂ T ≤ (Submodule.span ℂ T).comap (ρ g) :=
      Submodule.span_le.2 (fun y hy => Submodule.subset_span (hstab g y hy))
    exact hle hv⟩
  haveI := hρ
  rcases eq_bot_or_eq_top U with h | h
  · exfalso
    have hspan : Submodule.span ℂ T = ⊥ := congrArg Subrepresentation.toSubmodule h
    haveI : Nontrivial (Fin n → ℂ) := nontrivial_of_isIrreducible τ hτ
    obtain ⟨z, hz⟩ := exists_ne (0 : Fin n → ℂ)
    have hmem : φ0 z ∈ Submodule.span ℂ T :=
      Submodule.subset_span ⟨φ0, hφ0, LinearMap.mem_range.2 ⟨z, rfl⟩⟩
    rw [hspan, Submodule.mem_bot] at hmem
    exact hz (hinj (by rw [hmem, map_zero]))
  · exact congrArg Subrepresentation.toSubmodule h

end GlobalTheory.PiIsotypic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralHaarEqCompactSubgroupTransversal
section
open MeasureTheory

namespace GlobalTheory.Twist

theorem lintegral_haar_eq_transversal (G E : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace E] (μ mK : Measure G) [μ.IsHaarMeasure] [μ.IsInvInvariant]
    [IsProbabilityMeasure mK] (lam : Measure E) [SFinite lam] (K : Set G) (e : E → G)
    (he : Measurable e) (hK : mK Kᶜ = 0)
    (hinv : ∀ k ∈ K, Measure.map (fun x => x * k) mK = mK) (hlam : lam ≠ 0)
    (hfin : ∀ C : Set G, IsCompact C → lam {B | ∃ k ∈ K, k * e B ∈ C} < ⊤)
    (hact : ∀ g : G, ∃ ψ : E → E, Measurable ψ ∧ Measure.map ψ lam = lam ∧
      ∀ B, ∃ κ ∈ K, e B * g = κ * e (ψ B)) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : G → ENNReal, Measurable f →
      ∫⁻ g, f g ∂μ = ENNReal.ofReal c * ∫⁻ B, ∫⁻ k, f (k * e B) ∂mK ∂lam := by
  have hm : Measurable (fun z : E × G => z.2 * e z.1) :=
    measurable_snd.mul (he.comp measurable_fst)
  set ν : Measure G := Measure.map (fun z : E × G => z.2 * e z.1) (lam.prod mK) with hν
  have hint : ∀ f : G → ENNReal, Measurable f →
      ∫⁻ g, f g ∂ν = ∫⁻ B, ∫⁻ k, f (k * e B) ∂mK ∂lam := by
    intro f hf
    rw [hν, lintegral_map hf hm]
    exact lintegral_prod (fun z : E × G => f (z.2 * e z.1)) (hf.comp hm).aemeasurable
  have hH : ∀ f : G → ENNReal, Measurable f →
      Measurable (fun B => ∫⁻ k, f (k * e B) ∂mK) := by
    intro f hf
    exact Measurable.lintegral_prod_right' (f := fun z : E × G => f (z.2 * e z.1)) (hf.comp hm)
  have hR : ν.IsMulRightInvariant := by
    refine ⟨fun g => ?_⟩
    obtain ⟨ψ, hψ, hψl, hψe⟩ := hact g
    refine Measure.ext_of_lintegral _ (fun f hf => ?_)
    have hg : Measurable (fun x : G => x * g) := measurable_mul_const g
    rw [lintegral_map hf hg, hint (fun x => f (x * g)) (hf.comp hg), hint f hf]
    have h1 : ∀ B, ∫⁻ k, f (k * e B * g) ∂mK = ∫⁻ k, f (k * e (ψ B)) ∂mK := by
      intro B
      obtain ⟨κ, hκ, hk⟩ := hψe B
      have h2 := lintegral_map (μ := mK) (f := fun x => f (x * e (ψ B))) (g := fun x => x * κ)
        (hf.comp (measurable_mul_const _)) (measurable_mul_const κ)
      rw [hinv κ hκ] at h2
      rw [h2]
      simp only [mul_assoc, hk]
    simp only [h1]
    have h3 := lintegral_map (μ := lam) (hH f hf) hψ
    rw [hψl] at h3
    exact h3.symm
  have hF : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun C hC => ?_⟩
    have hCm : MeasurableSet C := hC.measurableSet
    have h1 := hint (C.indicator 1) (measurable_one.indicator hCm)
    rw [lintegral_indicator_one hCm] at h1
    rw [h1]
    set S := {B | ∃ k ∈ K, k * e B ∈ C} with hS
    refine lt_of_le_of_lt ?_ (hfin C hC)
    rw [← measure_toMeasurable, ← lintegral_indicator_one (measurableSet_toMeasurable _ _)]
    refine lintegral_mono (fun B => ?_)
    by_cases hB : B ∈ toMeasurable lam S
    · rw [Set.indicator_of_mem hB]
      calc ∫⁻ k, C.indicator (1 : G → ENNReal) (k * e B) ∂mK ≤ ∫⁻ _k, 1 ∂mK :=
            lintegral_mono (fun k => Set.indicator_le_self' (fun _ _ => zero_le_one) _)
        _ = 1 := by simp
    · rw [Set.indicator_of_notMem hB]
      have hB' : B ∉ S := fun h => hB (subset_toMeasurable _ _ h)
      have hae : ∀ᵐ k ∂mK, k ∈ K := hK
      have : ∫⁻ k, C.indicator (1 : G → ENNReal) (k * e B) ∂mK = ∫⁻ _k, 0 ∂mK := by
        refine lintegral_congr_ae (hae.mono fun k hk => ?_)
        exact Set.indicator_of_notMem (fun h => hB' ⟨k, hk, h⟩) _
      simp [this]
  have hν0 : ν ≠ 0 := by
    intro h
    have h1 := hint (fun _ => 1) measurable_const
    rw [h] at h1
    simp at h1
    exact hlam (Measure.measure_univ_eq_zero.mp h1.symm)
  have hmul := Measure.isMulLeftInvariant_eq_smul ν.inv μ
  set c := Measure.haarScalarFactor ν.inv μ with hc
  have hνc : ν = c • μ := by
    have : ν.inv.inv = (c • μ).inv := by rw [← hmul]
    rw [Measure.inv_inv] at this
    rw [this]
    change Measure.map _ (c • μ) = _
    rw [Measure.map_smul, Measure.map_inv_eq_self]
  have hc0 : c ≠ 0 := by
    intro h
    apply hν0
    rw [hνc, h, zero_smul]
  refine ⟨((c⁻¹ : NNReal) : ℝ), by exact_mod_cast inv_pos.mpr (pos_iff_ne_zero.mpr hc0), fun f hf => ?_⟩
  rw [← hint f hf, hνc, lintegral_smul_measure, ENNReal.ofReal_coe_nnreal, ENNReal.smul_def, smul_eq_mul,
    ← mul_assoc, ← ENNReal.coe_mul, inv_mul_cancel₀ hc0]
  simp

end GlobalTheory.Twist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralUnfoldingLeOfTranslateCover
section
open MeasureTheory

namespace GlobalTheory

theorem unfolding_cover_bound (G H : Type) [Group G] [Group H] [MeasurableSpace H] [MeasurableMul H]
    (μ : Measure H) [μ.IsMulLeftInvariant] (ι : H →* G) (hι : Function.Injective ι)
    (Γ : Subgroup G) [Countable Γ] (Kc : Set H)
    (hK : ∀ h, ∃ δ ∈ Γ.comap ι, δ * h ∈ Kc) (F : G → ENNReal)
    (hF : ∀ γ : G, Measurable fun h => F (γ * ι h)) :
    ∑' q : Γ ⧸ ι.range.subgroupOf Γ, ∫⁻ h, F ((q.out : Γ) * ι h) ∂μ
      ≤ ∫⁻ h in Kc, ∑' γ : Γ, F (γ * ι h) ∂μ := by
  classical
  haveI hcH : Countable (Γ.comap ι) := by
    have : Function.Injective (fun δ : Γ.comap ι => (⟨ι δ, δ.2⟩ : Γ)) := by
      intro a b hab
      apply Subtype.ext
      apply hι
      simpa using congrArg Subtype.val hab
    exact this.countable
  have step : ∀ g : G, ∫⁻ h, F (g * ι h) ∂μ
      ≤ ∑' δ : Γ.comap ι, ∫⁻ k in Kc, F (g * ι ((δ:H)⁻¹) * ι k) ∂μ := by
    intro g
    have hcov : (Set.univ : Set H) = ⋃ δ : Γ.comap ι, (fun h => (δ:H) * h) ⁻¹' Kc := by
      ext h
      simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_preimage, true_iff]
      obtain ⟨δ, hδ, hδK⟩ := hK h
      exact ⟨⟨δ, hδ⟩, hδK⟩
    calc ∫⁻ h, F (g * ι h) ∂μ
        = ∫⁻ h in ⋃ δ : Γ.comap ι, (fun h => (δ:H) * h) ⁻¹' Kc, F (g * ι h) ∂μ := by
          rw [← hcov, Measure.restrict_univ]
      _ ≤ ∑' δ : Γ.comap ι, ∫⁻ h in (fun h => (δ:H) * h) ⁻¹' Kc, F (g * ι h) ∂μ :=
          lintegral_iUnion_le _ _
      _ = ∑' δ : Γ.comap ι, ∫⁻ k in Kc, F (g * ι ((δ:H)⁻¹) * ι k) ∂μ := by
          congr 1; funext δ
          set e := MeasurableEquiv.mulLeft ((δ:H)⁻¹) with he
          have hmap : μ.map e = μ := by
            rw [MeasurableEquiv.coe_mulLeft]; exact map_mul_left_eq_self μ _
          have hpre : e ⁻¹' ((fun h => (δ:H) * h) ⁻¹' Kc) = Kc := by
            ext k; simp [e]
          calc ∫⁻ h in (fun h => (δ:H) * h) ⁻¹' Kc, F (g * ι h) ∂μ
              = ∫⁻ h in (fun h => (δ:H) * h) ⁻¹' Kc, F (g * ι h) ∂(μ.map e) := by rw [hmap]
            _ = ∫⁻ h, F (g * ι h) ∂((μ.restrict (e ⁻¹' ((fun h => (δ:H) * h) ⁻¹' Kc))).map e) := by
                rw [e.restrict_map]
            _ = ∫⁻ k, F (g * ι (e k)) ∂(μ.restrict (e ⁻¹' ((fun h => (δ:H) * h) ⁻¹' Kc))) :=
                lintegral_map_equiv _ _
            _ = _ := by rw [hpre]; simp [e, mul_assoc]
  haveI : Countable (Γ ⧸ ι.range.subgroupOf Γ) := QuotientGroup.mk_surjective.countable
  let φ : (Γ ⧸ ι.range.subgroupOf Γ) × Γ.comap ι → Γ := fun p =>
    (p.1.out : Γ) * ⟨ι ((p.2 : H)⁻¹), by simpa using Γ.inv_mem p.2.2⟩
  have hφ : Function.Injective φ := by
    rintro ⟨q₁, δ₁⟩ ⟨q₂, δ₂⟩ h
    have hv := congrArg Subtype.val h
    simp only [φ, Subgroup.coe_mul] at hv
    have hq : q₁ = q₂ := by
      rw [← QuotientGroup.out_eq' q₁, ← QuotientGroup.out_eq' q₂, QuotientGroup.eq,
        Subgroup.mem_subgroupOf, MonoidHom.mem_range]
      refine ⟨(δ₁:H)⁻¹ * (δ₂:H), ?_⟩
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [show ((q₁.out : Γ) : G)⁻¹ * ((q₂.out : Γ) : G)
          = ((q₁.out : Γ) : G)⁻¹ * (((q₂.out : Γ) : G) * ι ((δ₂:H)⁻¹)) * ι (δ₂:H) by
            rw [map_inv]; group, ← hv]
      simp only [map_mul, map_inv]; group
    subst hq
    have h2 : ι ((δ₁:H)⁻¹) = ι ((δ₂:H)⁻¹) := mul_left_cancel hv
    have h3 : (δ₁:H)⁻¹ = (δ₂:H)⁻¹ := hι h2
    simp only [Prod.mk.injEq, true_and]
    exact Subtype.ext (inv_injective h3)
  calc ∑' q : Γ ⧸ ι.range.subgroupOf Γ, ∫⁻ h, F ((q.out : Γ) * ι h) ∂μ
      ≤ ∑' q : Γ ⧸ ι.range.subgroupOf Γ, ∑' δ : Γ.comap ι,
          ∫⁻ k in Kc, F (((φ (q, δ)) : G) * ι k) ∂μ := by
        refine ENNReal.tsum_le_tsum fun q => ?_
        exact step _
    _ = ∑' p, ∫⁻ k in Kc, F ((φ p : G) * ι k) ∂μ := ENNReal.tsum_prod.symm
    _ = ∫⁻ k in Kc, ∑' p, F ((φ p : G) * ι k) ∂μ :=
        (lintegral_tsum fun p => (hF _).aemeasurable).symm
    _ ≤ ∫⁻ h in Kc, ∑' γ : Γ, F (γ * ι h) ∂μ :=
        lintegral_mono fun k => ENNReal.tsum_comp_le_tsum_of_injective hφ (fun γ : Γ => F (γ * ι k))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanPeriodicIndepOfCovolumeOne
section
open MeasureTheory

namespace GlobalTheory

open MeasureTheory in

theorem _root_.GlobalTheory.mean_periodic_indep_of_covolume_one :
    ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (μ μ' : Measure G) (𝓕 𝓕' : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 = 1 → μ'.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕' μ' → μ' 𝓕' = 1 → ∀ Φ : G → ℂ, Continuous Φ → (∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) → IntegrableOn Φ 𝓕 μ ∧ ∫ x in 𝓕, Φ x ∂μ = ∫ x in 𝓕', Φ x ∂μ' := by
  intro G _ _ _ _ _ _ _ _ Γ _ K hK hcov μ μ' 𝓕 𝓕' hμ h𝓕 h𝓕1 hμ' h𝓕' h𝓕'1 Φ hΦ hper
  haveI : Countable Γ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  obtain ⟨M, hM⟩ : ∃ M, ∀ x, ‖Φ x‖ ≤ M := by
    obtain ⟨M, hM⟩ := (hK.image hΦ.norm).bddAbove
    refine ⟨M, fun x => ?_⟩
    obtain ⟨γ, hγ, hx⟩ := hcov x
    rw [← hper γ hγ x]
    exact hM ⟨_, hx, rfl⟩
  have hint : IntegrableOn Φ 𝓕 μ :=
    Measure.integrableOn_of_bounded (by rw [h𝓕1]; exact ENNReal.one_ne_top)
      hΦ.aestronglyMeasurable (M := M) (Filter.Eventually.of_forall hM)
  refine ⟨hint, ?_⟩
  have hsm := Measure.isAddLeftInvariant_eq_smul μ' μ
  have hc0 : μ'.addHaarScalarFactor μ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hsm
    rw [hsm] at h𝓕'1
    simp at h𝓕'1
  have hac : μ ≪ μ' := by
    intro s hs
    rw [hsm, Measure.smul_apply] at hs
    simpa [hc0] using hs
  have h𝓕'μ : IsAddFundamentalDomain Γ 𝓕' μ := h𝓕'.mono hac
  have hc1 : μ'.addHaarScalarFactor μ = 1 := by
    have e := h𝓕'1
    rw [hsm, Measure.smul_apply, h𝓕'μ.measure_eq h𝓕, h𝓕1] at e
    simpa using e
  have hμμ' : μ' = μ := by rw [hsm, hc1, one_smul]
  rw [hμμ']
  exact h𝓕.setIntegral_eq h𝓕'μ (fun g x => hper g g.2 x)

end GlobalTheory
end

