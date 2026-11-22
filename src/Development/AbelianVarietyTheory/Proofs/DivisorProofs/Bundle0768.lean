import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0036
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0440
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0754
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0755
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0055
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0587
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0241
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0300
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0762
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0752

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelOneThetaNeZeroOnIdealHalfLattice
section
open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict
open GlobalTheory.SW hiding Level
open scoped ComplexConjugate Classical

namespace GlobalTheory.Dict.ThetaHalf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem EF_inv_smul (X : Data E r) (M : ℕ) (u v : Fin r → E) :
    EF X ((M : E)⁻¹ • u) v = (M : ℚ)⁻¹ * EF X u v := by
  have h : (M : E)⁻¹ • u = (M : ℚ)⁻¹ • u := by
    funext j
    simp [Rat.smul_def]
  rw [h, TensLat.EF_eq_bilin, TensLat.EF_eq_bilin, map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem mem_smul_iff (X : Data E r) {L : Lt E r} (hL : SelfD X L) {𝔪 : Ideal (𝓞 E)} {M : ℕ}
    (hM : M ≠ 0) (h𝔪 : 𝔪 * conjI 𝔪 = Ideal.span {(M : 𝓞 E)}) (x : Fin r → E) :
    x ∈ 𝔪 • L ↔ ∀ y ∈ 𝔪 • L, ∃ k : ℤ, (M : ℚ)⁻¹ * EF X x y = k := by
  have hME : (M : E) ≠ 0 := Nat.cast_ne_zero.2 hM
  have hcc : ∀ a : E, cc (cc a) = a := fun a => IsCMField.complexConj_apply_apply E a
  constructor
  · intro hx y hy
    refine Submodule.smul_induction_on hx (fun a ha u hu => ?_) fun x₁ x₂ h₁ h₂ => ?_
    · refine Submodule.smul_induction_on hy (fun b hb v hv => ?_) fun y₁ y₂ h₁ h₂ => ?_
      · let b' : 𝓞 E := ⟨cc (b : E), Base.isIntegral_cc b.isIntegral_coe⟩
        have hb' : b' ∈ conjI 𝔪 := Ideal.subset_span ⟨b, hb, rfl⟩
        obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (h𝔪 ▸ Ideal.mul_mem_mul ha hb')
        have ht' : (t : E) * M = a * cc (b : E) := by
          have h5 := congrArg (algebraMap (𝓞 E) E) ht
          rw [map_mul, map_mul, map_natCast] at h5
          exact h5
        obtain ⟨k, hk⟩ := (hL.2 _).1 (L.smul_mem t hu) v hv
        refine ⟨k, ?_⟩
        rw [← hk, ← EF_inv_smul]
        change EF X ((M : E)⁻¹ • (a : E) • u) ((b : E) • v) = EF X ((t : E) • u) v
        rw [← hcc (b : E), ← TensLat.EF_smul, smul_smul, smul_smul]
        congr 2
        field_simp
        linear_combination -ht'
      · obtain ⟨k₁, h₁⟩ := h₁
        obtain ⟨k₂, h₂⟩ := h₂
        refine ⟨k₁ + k₂, ?_⟩
        rw [Int.cast_add, ← h₁, ← h₂]
        simp only [TensLat.EF_eq_bilin, map_add, mul_add]
    · obtain ⟨k₁, h₁⟩ := h₁
      obtain ⟨k₂, h₂⟩ := h₂
      refine ⟨k₁ + k₂, ?_⟩
      rw [Int.cast_add, ← h₁, ← h₂]
      simp only [TensLat.EF_eq_bilin, map_add, mul_add, LinearMap.add_apply]
  · intro h
    have h1 : ∀ b ∈ conjI 𝔪, b • (M : E)⁻¹ • x ∈ L := by
      intro b hb
      induction hb using Submodule.span_induction with
      | mem b hb =>
        obtain ⟨a, ha, hb⟩ := hb
        refine (hL.2 _).2 fun u hu => ?_
        obtain ⟨k, hk⟩ := h _ (Submodule.smul_mem_smul ha hu)
        refine ⟨k, ?_⟩
        change EF X ((b : E) • (M : E)⁻¹ • x) u = k
        rw [hb, TensLat.EF_smul, hcc, EF_inv_smul]
        exact hk
      | zero => simp
      | add a b _ _ ha hb => rw [add_smul]; exact L.add_mem ha hb
      | smul t a _ ha => rw [smul_eq_mul, mul_smul]; exact L.smul_mem t ha
    have h2 : ∀ c ∈ 𝔪 * conjI 𝔪, c • (M : E)⁻¹ • x ∈ 𝔪 • L := by
      intro c hc
      refine Submodule.mul_induction_on hc (fun a ha b hb => ?_) fun c₁ c₂ h₁ h₂ => ?_
      · rw [mul_smul]; exact Submodule.smul_mem_smul ha (h1 b hb)
      · rw [add_smul]; exact add_mem h₁ h₂
    have h3 := h2 M (h𝔪 ▸ Ideal.mem_span_singleton_self _)
    have h4 : (M : 𝓞 E) • (M : E)⁻¹ • x = x := by
      rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hME,
        one_smul]
    rwa [h4] at h3

theorem span_smul (X : Data E r) {L : Lt E r} (hL : SelfD X L) {𝔪 : Ideal (𝓞 E)} {M : ℕ}
    (hM : M ≠ 0) (h𝔪 : 𝔪 * conjI 𝔪 = Ideal.span {(M : 𝓞 E)}) :
    Submodule.span E ((𝔪 • L : Lt E r) : Set (Fin r → E)) = ⊤ := by
  have hME : (M : E) ≠ 0 := Nat.cast_ne_zero.2 hM
  have hMm : (M : 𝓞 E) ∈ 𝔪 := by
    refine Ideal.mul_le_left (J := conjI 𝔪) ?_
    rw [h𝔪]
    exact Ideal.mem_span_singleton_self _
  rw [eq_top_iff, ← TensLat.span_of_selfD X hL, Submodule.span_le]
  intro u hu
  have h1 : (M : E)⁻¹ • (M : 𝓞 E) • u = u := by
    rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E, smul_smul, inv_mul_cancel₀ hME,
      one_smul]
  have h2 : (M : 𝓞 E) • u ∈ 𝔪 • L := Submodule.smul_mem_smul hMm hu
  have h3 := Submodule.smul_mem _ (M : E)⁻¹ (Submodule.subset_span (R := E) h2)
  rw [h1] at h3
  exact h3

theorem exists_ne_zero_of_scaled {V : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    {g : ℕ} (B : LinearMap.BilinForm ℚ V) (p : V →ₗ[ℤ] (Fin g → ℂ)) (hp : Function.Injective p)
    (L : Submodule ℤ V) (hfg : L.FG) {M : ℕ} (hM : 2 ≤ M)
    (hL : ∀ x, x ∈ L ↔ ∀ y ∈ L, ∃ k : ℤ, (M : ℚ)⁻¹ * B x y = k)
    (hsp : Submodule.span ℝ (p '' (L : Set V)) = ⊤) {Hm : Matrix (Fin g) (Fin g) ℂ}
    (hH : Hm.IsHermitian) (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re)
    (hB : ∀ u v, (p u ⬝ᵥ Hm.mulVec (star (p v))).im = (B u v : ℝ)) (c : V → ℂ)
    (hc : ∀ v, ‖c v‖ = 1) {f : (Fin g → ℂ) → ℂ} (hd : Differentiable ℂ f) (h0 : f ≠ 0)
    (hf : ∀ v ∈ L, ∀ z, f (z + p v) = (c v * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (p v))) +
      Real.pi / 2 * (p v ⬝ᵥ Hm.mulVec (star (p v))))) * f z) :
    ∃ v ∈ L, f ((M : ℂ)⁻¹ • p v) ≠ 0 := by
  have hM0 : M ≠ 0 := by omega
  have hMC : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hM0
  have hMR : (0 : ℝ) < (M : ℝ)⁻¹ := by positivity
  have hsc : ∀ z u : Fin g → ℂ, z ⬝ᵥ ((M : ℝ)⁻¹ • Hm).mulVec u = (M : ℝ)⁻¹ • (z ⬝ᵥ Hm.mulVec u) :=
    fun z u => by rw [smul_mulVec, dotProduct_smul]
  refine GlobalTheory.T.thetaFunction_ne_zero_at_divisionPoint_selfDual V g ((M : ℚ)⁻¹ • B) p hp L hfg hL hsp ((M : ℝ)⁻¹ • Hm) ?_ (fun z hz => ?_)
    (fun u v => ?_) c hc M hM f hd h0 fun v hv z => ?_
  · ext i j
    rw [conjTranspose_apply, Matrix.smul_apply, Matrix.smul_apply, star_smul, hH.apply, star_trivial]
  · rw [hsc, smul_re, smul_eq_mul]
    exact mul_pos hMR (hpos z hz)
  · rw [hsc, smul_im, LinearMap.smul_apply, LinearMap.smul_apply, hB]
    simp
  · rw [hf v hv z, hsc, hsc]
    congr 3
    simp only [real_smul]
    push_cast
    field_simp

theorem exists_ne_zero_on_half : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → ∀ (w : E) (L : Lt E r), SelfD X L → ∀ x ∈ X.dom, ∀ (𝔪 : Ideal (𝓞 E)) (M : ℕ), 2 ≤ M → 𝔪 * conjI 𝔪 = Ideal.span {(M : 𝓞 E)} → ∀ ϑ : (Fin g → ℂ) → ℂ, IsTheta1 X bas idx w x L ϑ → ϑ ≠ 0 → ∃ u ∈ 𝔪 • L, ϑ (pv X idx x ((M : E)⁻¹ • u)) ≠ 0 := by
  intro E _ _ _ r X g bas idx hs w L hL x hx' 𝔪 M hM h𝔪 θ hθ h0
  have hM0 : M ≠ 0 := by omega
  obtain ⟨hconj, hpos, him, -, hsm, hinj, hspan, -⟩ :=
    GlobalTheory.Dict.hx_laws E r X g bas idx 0 hs Even.zero x hx'
  set Hm := (hMat X bas idx x)ᵀ * imInv X bas idx x * (hMat X bas idx x).map star with hHm
  have hform : ∀ z u, hx X bas idx x z u = z ⬝ᵥ Hm.mulVec (star u) := fun z u =>
    SiegelNormalForm.form_pull _ _ z u
  have hH : Hm.IsHermitian := by
    ext i j
    have := hconj (Pi.single j 1) (Pi.single i 1)
    rw [hform, hform, SiegelNormalForm.form_single, SiegelNormalForm.form_single] at this
    exact this.symm
  clear_value Hm
  let p : (Fin r → E) →ₗ[ℤ] (Fin g → ℂ) := (AddMonoidHom.mk' (pv X idx x) fun u v => by
    unfold pv; rw [per_add]; rfl).toIntLinearMap
  have hp : ∀ v, p v = pv X idx x v := fun _ => rfl
  have hne : ∀ v, eps1 X w v ≠ 0 := fun v => Complex.exp_ne_zero _
  have key : ∀ v ∈ L, ∀ z, θ (z + p v) =
      ((eps1 X w v)⁻¹ * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (p v))) +
      Real.pi / 2 * (p v ⬝ᵥ Hm.mulVec (star (p v))))) * θ z := by
    intro v hv z
    have h1 := congrFun (hθ.2 v hv) z
    simp only [Pi.smul_apply, smul_eq_mul, fock, hform, add_dotProduct, smul_dotProduct] at h1
    rw [← h1, ← hp, _root_.mul_mul_mul_comm, inv_mul_cancel₀ (hne v), _root_.one_mul,
      ← _root_.mul_assoc, ← Complex.exp_add]
    refine (_root_.one_mul _).symm.trans ?_
    congr 1
    refine Complex.exp_zero.symm.trans (congrArg _ ?_)
    push_cast
    ring
  obtain ⟨u, hu, hu0⟩ := exists_ne_zero_of_scaled (traceFormBilin (X.κ0 / 2) X.Gm) p hinj
    ((𝔪 • L).restrictScalars ℤ)
    (Submodule.FG.of_le hL.1 (Submodule.smul_le_right (I := 𝔪))).restrictScalars hM
    (fun u => by simp only [← TensLat.EF_eq_bilin]; exact mem_smul_iff X hL hM0 h𝔪 u)
    (hspan _ (span_smul X hL hM0 h𝔪)).1 hH (fun z hz => hform z z ▸ hpos z hz)
    (fun u v => by rw [← TensLat.EF_eq_bilin, ← him, hform, hp, hp])
    (fun v => (eps1 X w v)⁻¹)
    (fun v => by
      have : eps1 X w v = cexp ((Real.pi * (EF X v (w • v) : ℚ) : ℝ) * I) := by
        unfold eps1; congr 1; push_cast; ring
      rw [norm_inv, this, Complex.norm_exp_ofReal_mul_I, inv_one])
    hθ.1 h0 (fun v hv => key v (Submodule.smul_le_right (I := 𝔪) hv))
  refine ⟨u, hu, ?_⟩
  have e : pv X idx x ((M : E)⁻¹ • u) = (M : ℂ)⁻¹ • p u := by
    rw [hsm]
    funext j
    rw [map_inv₀, map_natCast, hp, Pi.smul_apply, smul_eq_mul]
  rwa [e]

end GlobalTheory.Dict.ThetaHalf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroCoindIntertwinerOfDoubleCosetStatement
section
open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_coindIntertwiner_of_doubleCoset : ∀ (G : Type) [Group G] [Finite G] (P P' : Subgroup G) (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (σ : Representation ℂ P V) (σ' : Representation ℂ P' V') (x : G) (T : V →ₗ[ℂ] V'), T ≠ 0 → (∀ (p : P) (p' : P'), (p' : G) * x = x * (p : G) → σ' p' ∘ₗ T = T ∘ₗ σ p) → ∃ Φ : Representation.IntertwiningMap (Representation.coind P.subtype σ) (Representation.coind P'.subtype σ'), Φ ≠ 0 := by
  first | exact @GlobalTheory.exists_ne_zero_intertwiningMap_coind_of_doubleCoset | exact GlobalTheory.exists_ne_zero_intertwiningMap_coind_of_doubleCoset | (intros; apply GlobalTheory.exists_ne_zero_intertwiningMap_coind_of_doubleCoset <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroIntertwiningOfCommutingIsotypicFactoStatement
section
open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_intertwining_of_commuting_isotypicFactors : ∀ (M : Type) [Group M] [Finite M] (ι : Type) [Finite ι] (H : ι → Type) [∀ c, Group (H c)] [∀ c, Finite (H c)] (f : ∀ c, H c →* M), (⨆ c, (f c).range) = ⊤ → (∀ c c', c ≠ c' → ∀ (x : H c) (y : H c'), Commute (f c x) (f c' y)) → ∀ (W : ι → Type) [∀ c, AddCommGroup (W c)] [∀ c, Module ℂ (W c)] (ρ : ∀ c, Representation ℂ (H c) (W c)), (∀ c, (ρ c).IsIrreducible) → ∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] [Nontrivial V'] (τ : Representation ℂ M V) (τ' : Representation ℂ M V'), (∀ c, IsIsotypicOf (show Representation ℂ (H c) V from τ.comp (f c)) (ρ c)) → (∀ c, IsIsotypicOf (show Representation ℂ (H c) V' from τ'.comp (f c)) (ρ c)) → ∃ T : Representation.IntertwiningMap τ τ', T ≠ 0 := by
  first | exact @GlobalTheory.IsotypicFactors.exists_intertwining_ne_zero | exact GlobalTheory.IsotypicFactors.exists_intertwining_ne_zero | (intros; apply GlobalTheory.IsotypicFactors.exists_intertwining_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianShFactorStatement
section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_noetherian_sh_factorization : ∀ (R A : Type) [CommRing R] [IsNoetherianRing R] [CommRing A], SH A → ∀ b : R →+* A, ∃ (C : Type) (_ : CommRing C), IsNoetherianRing C ∧ SH C ∧ ∃ (f : R →+* C) (g : C →+* A), g.comp f = b := by
  first | (exact @GlobalTheory.NoethSHFactor.exists_noetherian_sh_factor) | (exact GlobalTheory.NoethSHFactor.exists_noetherian_sh_factor) | (intros; apply GlobalTheory.NoethSHFactor.exists_noetherian_sh_factor  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupSchemeOfIsOpenStable
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory.OpenSubgroup

theorem exists_open_subgroup : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (Z : Set G.left), IsOpen Z → (∀ s : S, (η[G]).left s ∈ Z) → (∀ w : (G ⊗ G).left, (fst G G).left w ∈ Z → (snd G G).left w ∈ Z → (μ[G]).left w ∈ Z) → (∀ y ∈ Z, (ι[G]).left y ∈ Z) → ∃ (G₀ : Over S) (_ : GrpObj G₀) (j : G₀ ⟶ G), IsMonHom j ∧ IsOpenImmersion j.left ∧ Set.range j.left = Z := by
  intro S G _ Z hZ h1 hmul hinv
  let U : G.left.Opens := ⟨Z, hZ⟩
  let G₀ : Over S := Over.mk (U.ι ≫ G.hom)
  let j : G₀ ⟶ G := Over.homMk U.ι rfl
  have hjo : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion U.ι)
  have hr : Set.range j.left = Z := U.range_ι
  have : Mono j := Over.mono_of_mono_left j
  have lift : ∀ (X : Over S) (φ : X ⟶ G), Set.range φ.left ⊆ Z → ∃ ψ : X ⟶ G₀, ψ ≫ j = φ := by
    intro X φ hsub
    have hsub' : Set.range φ.left ⊆ Set.range j.left := hr ▸ hsub
    refine ⟨Over.homMk (IsOpenImmersion.lift j.left φ.left hsub') ?_, ?_⟩
    · rw [← j.w, IsOpenImmersion.lift_fac_assoc, φ.w]
    · exact Over.OverMorphism.ext (IsOpenImmersion.lift_fac j.left φ.left hsub')
  have inZ : ∀ x : G₀.left, j.left x ∈ Z := fun x => hr ▸ Set.mem_range_self x
  obtain ⟨e, he⟩ := lift (𝟙_ _) η[G] (by
    rintro _ ⟨s, rfl⟩
    exact h1 s)
  obtain ⟨m, hm⟩ := lift (G₀ ⊗ G₀) ((j ⊗ₘ j) ≫ μ[G]) (by
    rintro _ ⟨w, rfl⟩
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    apply hmul
    · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, tensorHom_fst, Over.comp_left,
        Scheme.Hom.comp_apply]
      exact inZ _
    · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, tensorHom_snd, Over.comp_left,
        Scheme.Hom.comp_apply]
      exact inZ _)
  obtain ⟨i, hi⟩ := lift G₀ (j ≫ ι[G]) (by
    rintro _ ⟨x, rfl⟩
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    exact hinv _ (inZ x))
  obtain ⟨Gs, hG⟩ := exists_grpObj_of_mono_of_fac j e m i he hm hi
  exact ⟨G₀, Gs, j, hG, hjo, hr⟩

end GlobalTheory.OpenSubgroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPDivGroupFormalChartOfConnectedStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pDivGroupFormalChart_of_connected : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ G : PDivGroup p O, IsConn G → ∃ d : ℕ, Nonempty (QLog.Chart G d) := by
  first | exact @GlobalTheory.ChartEx.chart_exists | exact GlobalTheory.ChartEx.chart_exists | (intros; apply GlobalTheory.ChartEx.chart_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPermMatrixRepParabolicDoubleCosetStatement
section
open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_permMatrix_rep_parabolic_doubleCoset : ∀ (F : Type) [Field F] (r : ℕ) (b b' : Fin r → ℕ), Monotone b → Monotone b' → ∀ g : GL (Fin r) F, ∃ (w : Equiv.Perm (Fin r)) (p' : blockTri (κ := F) b') (p : blockTri (κ := F) b), g = (p' : GL (Fin r) F) * permGL F w * (p : GL (Fin r) F) := by
  first | exact @GlobalTheory.FinGL.Bruhat.exists_perm_rep_blockTri | exact GlobalTheory.FinGL.Bruhat.exists_perm_rep_blockTri | (intros; apply GlobalTheory.FinGL.Bruhat.exists_perm_rep_blockTri <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPermOfBlockSizeBijectionStatement
section
open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_perm_of_blockSize_bijection : ∀ (r : ℕ) (b b' : Fin r → ℕ) (R : ℕ → ℕ → Prop), (∀ c ∈ Set.range b, ∃! c', c' ∈ Set.range b' ∧ R c c') → (∀ c' ∈ Set.range b', ∃! c, c ∈ Set.range b ∧ R c c') → (∀ c ∈ Set.range b, ∀ c' ∈ Set.range b', R c c' → (block b c).card = (block b' c').card) → ∃ w : Equiv.Perm (Fin r), (∀ i, R (b i) (b' (w i))) ∧ ∀ i j : Fin r, b i = b j ↔ b' (w i) = b' (w j) := by
  first | exact @GlobalTheory.exists_perm_of_block_bijection | exact GlobalTheory.exists_perm_of_block_bijection | (intros; apply GlobalTheory.exists_perm_of_block_bijection <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionStrictHenselisationClosedFibrePoint
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.LocAcyc

theorem exists_section_strictHenselisation_at_closed : GlobalTheory.LocAcyc.KeyClosedPts →
    ∀ (T E : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing E]
      [Algebra (Polynomial T) E] [Algebra T E] [IsScalarTower T (Polynomial T) E]
      [Algebra.Etale (Polynomial T) E], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (y : Ideal E) [y.IsPrime],
      (y.comap (algebraMap (Polynomial T) E)).comap (Polynomial.C : T →+* Polynomial T) =
        IsLocalRing.maximalIdeal T →
      y.comap (algebraMap (Polynomial T) E) ≠
        (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (DE : Type) [CommRing DE] [Algebra (GlobalTheory.LocAcyc.GenFib T E) DE]
      (actE : Multiplicative (ZMod q) →* (DE ≃ₐ[GlobalTheory.LocAcyc.GenFib T E] DE)),
      GlobalTheory.LocAcyc.IsZModTorsor (GlobalTheory.LocAcyc.GenFib T E) DE q actE →
    ∃ (S : Type) (_ : CommRing S) (_ : IsLocalRing S) (_ : Algebra E S) (_ : Algebra T S)
      (_ : IsScalarTower T E S),
      (IsLocalRing.maximalIdeal S).comap (algebraMap E S) = y ∧ Module.Flat E S ∧
      GlobalTheory.LocAcyc.LocPiecesEtale E S ∧
      ∃ s : DE →+* GlobalTheory.LocAcyc.GenFib T S,
        ∀ e : E, s (algebraMap (GlobalTheory.LocAcyc.GenFib T E) DE (algebraMap E _ e)) =
          algebraMap S (GlobalTheory.LocAcyc.GenFib T S) (algebraMap E S e) := by
  intro hKey T E _ _ _ _ _ _ _ _ hT y _ hyT hyne q hq hqu DE _ _ actE htor
  obtain ⟨S, _, _, _, _, _, _, _, _, hmax, hflat, hloc, φ, hφ, hsh⟩ := GlobalTheory.T.strictHenselisation_etale_over_polynomial_alt T E y
  have hKey' := hKey
  unfold GlobalTheory.LocAcyc.KeyClosedPts GlobalTheory.LocAcyc.KeyLocalWith at hKey'
  have htriv : GlobalTheory.LocAcyc.TorsorsTrivial (GlobalTheory.LocAcyc.GenFib T S) q :=
    hKey' T S hT (y.comap (algebraMap (Polynomial T) E)) φ hφ hsh hyT hyne q hq hqu
  have hMN : Algebra.algebraMapSubmonoid E (nonZeroDivisors T) ≤
      (Algebra.algebraMapSubmonoid S (nonZeroDivisors T)).comap (algebraMap E S) := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Submonoid.mem_map.mp hx
    exact Submonoid.mem_map.mpr ⟨t, ht, IsScalarTower.algebraMap_apply T E S t⟩
  let f : GlobalTheory.LocAcyc.GenFib T E →+* GlobalTheory.LocAcyc.GenFib T S :=
    IsLocalization.map (S := GlobalTheory.LocAcyc.GenFib T E) (GlobalTheory.LocAcyc.GenFib T S) (algebraMap E S) hMN
  letI : Algebra (GlobalTheory.LocAcyc.GenFib T E) (GlobalTheory.LocAcyc.GenFib T S) := f.toAlgebra
  obtain ⟨act', -, htor'⟩ :=
    GlobalTheory.T.isZModTorsorFiniteProjective_baseChange (GlobalTheory.LocAcyc.GenFib T E) (GlobalTheory.LocAcyc.GenFib T S) DE q hq actE htor
  obtain ⟨σ⟩ := (GlobalTheory.LocAcyc.torsorsTrivial_iff _ q).mp htriv _ act' htor'
  refine ⟨S, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hmax, hflat, hloc, σ.toRingHom.comp
      (Algebra.TensorProduct.includeRight :
        DE →ₐ[GlobalTheory.LocAcyc.GenFib T E] GlobalTheory.LocAcyc.GenFib T S ⊗[GlobalTheory.LocAcyc.GenFib T E] DE).toRingHom,
    fun e => ?_⟩
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
  have hσ := σ.commutes (algebraMap (GlobalTheory.LocAcyc.GenFib T E) (GlobalTheory.LocAcyc.GenFib T S)
    (algebraMap E (GlobalTheory.LocAcyc.GenFib T E) e))
  simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at hσ
  rw [hσ, RingHom.algebraMap_toAlgebra]
  exact IsLocalization.map_eq hMN e

end GlobalTheory.LocAcyc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSliceTaylorAlgHomStatement
section
open Filter Topology TopologicalSpace GlobalTheory.AnPer TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorLift_ev_rho_eq_taylor_slice : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I ⊕ Fin g → D), (∀ s : Fin (N + 1) → I ⊕ Fin g, ∏ a, t (s a) = 0) → ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (W : Opens ((I → ℂ) × (Fin g → ℂ))) (W₀ : Opens E) (a : E → Fin g → ℂ), AnalyticOnNhd ℂ a W₀ → (∀ p ∈ W₀, ((0 : I → ℂ), a p) ∈ W) → ∃ ρ : Hol W →ₐ[ℂ] D ⊗[ℂ] Hol W₀, ∀ (h : Hol W) (p : E) (hp : p ∈ W₀), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) (ρ h) = GlobalTheory.PeriodFamily.taylor N t (fun x : I ⊕ Fin g → ℂ ↦ h.fn (fun i ↦ x (Sum.inl i), a p + fun b ↦ x (Sum.inr b))) := by
  first | exact @GlobalTheory.AnPer.exists_sliceTaylor_algHom | exact GlobalTheory.AnPer.exists_sliceTaylor_algHom | (intros; apply GlobalTheory.AnPer.exists_sliceTaylor_algHom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictlyHenselianEtaleStalkOverPoint
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in

theorem _root_.GlobalTheory.EtC.exists_isStalk_over_point : ∀ (S : Scheme.{0}) (U : Over S), Etale U.hom →
    ∀ u : U.left, ∃ (O : Type) (_ : CommRing O) (s : Spec (CommRingCat.of O) ⟶ S)
      (g : Over.mk s ⟶ U), _root_.GlobalTheory.EtC.IsStalk O s ∧ ∃ v, g.left v = u := by
  intro S U hU u
  let 𝒰 := U.left.affineOpenCover
  obtain ⟨y, hy⟩ := 𝒰.covers u
  let R : CommRingCat := 𝒰.X (𝒰.idx u)
  let f : Spec R ⟶ U.left := 𝒰.f (𝒰.idx u)
  haveI : IsOpenImmersion f := 𝒰.map_prop _
  haveI := hU
  let j : Spec R ⟶ S := f ≫ U.hom
  let y' : Spec R := y
  haveI := y'.isPrime
  obtain ⟨O, hO, hAO, hloc, hsh, hind, hcomap⟩ :=
    _root_.GlobalTheory.StrictHensPrime.exists_sh_indEt R y'.asIdeal
  let φ : Spec (CommRingCat.of O) ⟶ Spec R := Spec.map (CommRingCat.ofHom (algebraMap R O))
  refine ⟨O, hO, φ ≫ j, Over.homMk (φ ≫ f) (by simp [j]),
    ⟨hsh, R, inferInstance, hAO, j, inferInstance, hind, rfl⟩, IsLocalRing.closedPoint O, ?_⟩
  have hφ : φ (IsLocalRing.closedPoint O) = y' := by
    apply PrimeSpectrum.ext
    rw [← hcomap]
    rfl
  show (φ ≫ f) (IsLocalRing.closedPoint O) = u
  change f (φ (IsLocalRing.closedPoint O)) = u
  rw [hφ]
  exact hy

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationClosedChartsSubordinateToCover
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AnPer

theorem exists_affine_le_of_cover {X : Scheme.{0}} {N : Type} (𝒰 : N → X.Opens) (h𝒰 : ⨆ i, 𝒰 i = ⊤) (e : Sp ℂ ⟶ X) :
    ∃ i U, IsAffineOpen U ∧ U ≤ 𝒰 i ∧ ⊤ ≤ e ⁻¹ᵁ U := by
  have pt : Sp ℂ := (⊥ : PrimeSpectrum ℂ)
  have h1 : e pt ∈ ⨆ i, 𝒰 i := by rw [h𝒰]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 h1
  obtain ⟨U, hU, hx, hle⟩ := (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) hi
  refine ⟨i, U, hU, hle, fun y _ ↦ ?_⟩
  obtain rfl : y = pt := Subsingleton.elim _ _
  exact hx

theorem exists_charts_subordinate : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (u : Unif F s σ), X.IsSeparated → ∀ {N : Type} (𝒰 : N → X.Opens), ⨆ i, 𝒰 i = ⊤ → ∃ (K : Charts F) (r : Real K s σ) (j : K.K → N), K.Rich ∧ (∀ l k', ∃ k, K.le l k' k ∧ K.le (-l) k k') ∧ r.IsFor u ∧ ∀ k, ⊤ ≤ r.x k ⁻¹ᵁ 𝒰 (j k) := by
  intro I _ g Λ _ F B _ X s σ u hX N 𝒰 h𝒰
  let Q : Opens (Tot I g) → Prop := fun W ↦ ∃ i U, IsAffineOpen U ∧ U ≤ 𝒰 i ∧ ∀ p ∈ W, ⊤ ≤ u.E p ⁻¹ᵁ U
  obtain ⟨r, hr, hx⟩ := GlobalTheory.T.exists_analyticChartsRealization_of_affine u hX (Charts.std F Q) fun k ↦ by
    obtain ⟨i, U, h1, -, h3⟩ := k.2.2
    exact ⟨U, h1, h3⟩
  refine ⟨Charts.std F Q, r, fun k ↦ k.2.2.choose, ⟨fun p hp ↦ ?_, fun l k₁ k₂ p h₁ h₂ ↦ ?_⟩, fun l k' ↦ ?_, hr,
    fun k ↦ ?_⟩
  · obtain ⟨i, U, hU, hle, hp'⟩ := exists_affine_le_of_cover 𝒰 h𝒰 (u.E p)
    exact ⟨⟨⟨_, (u.hol U 0).1⟩, fun q hq ↦ hq.1, i, U, hU, hle, fun q hq ↦ hq.2⟩, hp, hp'⟩
  · have hc : ContinuousOn (F.shift l) (k₁.1 : Set (Tot I g)) := (F.shift_analytic l k₁.2.1).continuousOn
    obtain ⟨i, U, hU, hle, hW⟩ := k₁.2.2
    refine ⟨⟨⟨(k₁.1 : Set (Tot I g)) ∩ F.shift l ⁻¹' k₂.1, hc.isOpen_inter_preimage k₁.1.isOpen k₂.1.isOpen⟩,
      fun q hq ↦ k₁.2.1 q hq.1, i, U, hU, hle, fun q hq ↦ hW q hq.1⟩, ⟨h₁, h₂⟩, fun q hq ↦ ?_, fun q hq ↦ hq.2⟩
    rw [F.shift_zero]; exact hq.1
  · have hc : ContinuousOn (F.shift (-l)) (F.tot : Set (Tot I g)) := (F.shift_analytic (-l) fun _ h ↦ h).continuousOn
    obtain ⟨i, U, hU, hle, hW⟩ := k'.2.2
    refine ⟨⟨⟨(F.tot : Set (Tot I g)) ∩ F.shift (-l) ⁻¹' k'.1, hc.isOpen_inter_preimage F.tot.isOpen k'.1.isOpen⟩,
      fun q hq ↦ hq.1, i, U, hU, hle, fun q hq ↦ ?_⟩, fun q hq ↦ ⟨k'.2.1 q hq, ?_⟩, fun q hq ↦ hq.2⟩
    · rw [← u.per (-l) q hq.1]
      exact hW _ hq.2
    · change F.shift (-l) (F.shift l q) ∈ k'.1
      rwa [← F.shift_add, neg_add_cancel, F.shift_zero]
  · obtain ⟨U, hU, hle, hW⟩ := k.2.2.choose_spec
    exact fun y hy ↦ hle (hx k U hU hW hy)

end GlobalTheory.AnPer
end

