import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0233
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivariantOfWave
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0090
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0079
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0176
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeTransport
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum.Transport

variable {n : ℕ}

theorem conj_lie {A B G G' Y : Mx n} (hAB : A * B = 1) (hG : Aᴴ * G * A = G') (hY : Y ∈ lieOf G) :
    B * Y * A ∈ lieOf G' := by
  have hY' : Yᴴ * G + G * Y = 0 := hY
  show (B * Y * A)ᴴ * G' + G' * (B * Y * A) = 0
  rw [← hG]
  calc (B * Y * A)ᴴ * (Aᴴ * G * A) + Aᴴ * G * A * (B * Y * A)
      = Aᴴ * Yᴴ * (A * B)ᴴ * G * A + Aᴴ * G * (A * B) * Y * A := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Aᴴ * (Yᴴ * G + G * Y) * A := by
        rw [hAB]; simp only [conjTranspose_one, Matrix.mul_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hY']; simp

theorem conj_UH {A B G G' g : Mx n} (hAB : A * B = 1) (hG : Aᴴ * G * A = G') (hg : g ∈ Formalism.QuantumDeterminants.UH G) :
    B * g * A ∈ Formalism.QuantumDeterminants.UH G' := by
  have hg' : gᴴ * G * g = G := hg
  show (B * g * A)ᴴ * G' * (B * g * A) = G'
  rw [← hG]
  calc (B * g * A)ᴴ * (Aᴴ * G * A) * (B * g * A)
      = Aᴴ * (gᴴ * (A * B)ᴴ * G * (A * B) * g) * A := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by
        rw [hAB]; simp only [conjTranspose_one, Matrix.mul_one, hg']

theorem prod_conj {Q : Mx n} (h1 : Q⁻¹ * Q = 1) (h2 : Q * Q⁻¹ = 1) (l : List (Mx n)) :
    (l.map fun x => Q * x * Q⁻¹).prod = Q * l.prod * Q⁻¹ := by
  induction l with
  | nil => simp [h2]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih]
    calc Q * a * Q⁻¹ * (Q * l.prod * Q⁻¹) = Q * a * (Q⁻¹ * Q) * l.prod * Q⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem exp_smul_conj {Q : Mx n} (hQ : IsUnit Q) (X : Mx n) (t : ℝ) :
    NormedSpace.exp (t • (Q * X * Q⁻¹)) = Q * NormedSpace.exp (t • X) * Q⁻¹ := by
  rw [← Matrix.exp_conj Q _ hQ, Matrix.mul_smul, Matrix.smul_mul]

theorem hasType_transport : ∀ (n : ℕ) (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ₁ : Mx n → (H →L[ℂ] H)) (σ₂ : Mx n → (H' →L[ℂ] H')) (G₁ G₂ Q : Mx n), IsUnit G₁ → IsUnit Q → Qᴴ * G₂ * Q = G₁ → ∀ U : H ≃ₗᵢ[ℂ] H', (∀ g ∈ Formalism.QuantumDeterminants.UH G₁, ∀ v, U (σ₁ g v) = σ₂ (Q * g * Q⁻¹) (U v)) → ∀ f : Mx n → ℂ, HasType (lieOf G₁) (Formalism.QuantumDeterminants.UH G₁) σ₁ f → HasType (lieOf G₂) (Formalism.QuantumDeterminants.UH G₂) σ₂ (fun y => f (Q⁻¹ * y * Q)) := by
  intro n H H' _ _ _ _ σ₁ σ₂ G₁ G₂ Q hG hQ hGG U hU f hf
  have h1 : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hQ)
  have h2 : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hQ)
  have hGG' : (Q⁻¹)ᴴ * G₁ * Q⁻¹ = G₂ := by
    rw [← hGG]
    calc (Q⁻¹)ᴴ * (Qᴴ * G₂ * Q) * Q⁻¹ = (Q * Q⁻¹)ᴴ * G₂ * (Q * Q⁻¹) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h2]; simp
  have cd : ∀ Y : Mx n, Q * (Q⁻¹ * Y * Q) * Q⁻¹ = Y := fun Y => by
    calc Q * (Q⁻¹ * Y * Q) * Q⁻¹ = (Q * Q⁻¹) * Y * (Q * Q⁻¹) := by simp only [Matrix.mul_assoc]
      _ = Y := by rw [h2]; simp
  let Ur : H ≃L[ℝ] H' :=
    { U.toLinearEquiv.restrictScalars ℝ with
      continuous_toFun := U.continuous
      continuous_invFun := U.symm.continuous }
  have hUr : ∀ x, Ur x = U x := fun _ => rfl
  have key : ∀ (k : ℕ) (Xs : Fin k → Mx n), (∀ i, Xs i ∈ lieOf G₁) → ∀ w : H,
      (fun t : Fin k → ℝ => σ₂ (List.ofFn fun i => NormedSpace.exp (t i • (Q * Xs i * Q⁻¹))).prod (U w)) =
        Ur ∘ fun t : Fin k → ℝ => σ₁ (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod w := by
    intro k Xs hX w
    funext t
    have hm : (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod ∈ Formalism.QuantumDeterminants.UH G₁ :=
      GlobalTheory.GardingVec.list_prod_mem _ (by
        intro g hg
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
        exact GlobalTheory.GardingVec.exp_mem hG (hX i) _)
    rw [Function.comp_apply, hUr, hU _ hm, ← prod_conj h1 h2, List.map_ofFn]
    simp only [exp_smul_conj hQ, Function.comp_def]
  have smF : ∀ w, SmoothVec (lieOf G₁) σ₁ w → SmoothVec (lieOf G₂) σ₂ (U w) := by
    intro w hw k Ys hY
    have hX : ∀ i, Q⁻¹ * Ys i * Q ∈ lieOf G₁ := fun i => conj_lie h2 hGG (hY i)
    have := key k _ hX w
    simp only [cd] at this
    rw [this]
    exact Ur.contDiff.comp (hw k _ hX)
  have smB : ∀ w, SmoothVec (lieOf G₂) σ₂ (U w) → SmoothVec (lieOf G₁) σ₁ w := by
    intro w hw k Xs hX
    have := hw k _ fun i => conj_lie h1 hGG' (hX i)
    rw [key k Xs hX w] at this
    exact Ur.comp_contDiff_iff.1 this
  have hd : ∀ X ∈ lieOf G₁, ∀ w, dRep σ₂ (Q * X * Q⁻¹) (U w) = U (dRep σ₁ X w) := by
    intro X hX w
    have e : (fun t : ℝ => σ₂ (NormedSpace.exp (t • (Q * X * Q⁻¹))) (U w)) =
        Ur ∘ fun t : ℝ => σ₁ (NormedSpace.exp (t • X)) w := by
      funext t
      rw [Function.comp_apply, hUr, hU _ (GlobalTheory.GardingVec.exp_mem hG hX t), exp_smul_conj hQ]
    unfold dRep
    rw [e, deriv, deriv, Ur.comp_fderiv]
    rfl
  have hw : ∀ l : List (Mx n), (∀ X ∈ l, X ∈ lieOf G₁) → ∀ w,
      (l.map fun X => Q * X * Q⁻¹).foldr (dRep σ₂) (U w) = U (l.foldr (dRep σ₁) w) := by
    intro l hl w
    induction l with
    | nil => rfl
    | cons X l ih =>
      rw [List.map_cons, List.foldr_cons, List.foldr_cons, ih fun Y hY => hl Y (List.mem_cons_of_mem _ hY),
        hd X (hl X List.mem_cons_self)]
  obtain ⟨S, hS, ⟨B, hB, hBc⟩, v, ℓ, C, e1, e2, e3, e4, e5⟩ := hf
  have hs : ∀ w, sobNorm σ₂ (S.map fun l => l.map fun X => Q * X * Q⁻¹) (U w) = sobNorm σ₁ S w := by
    intro w
    unfold sobNorm
    rw [List.map_map]
    congr 1
    refine List.map_congr_left fun l hl => ?_
    simp only [Function.comp_apply]
    rw [hw l (hS l hl), U.norm_map]
  have hσ : ∀ g ∈ Formalism.QuantumDeterminants.UH G₂, ∀ w, σ₂ g (U w) = U (σ₁ (Q⁻¹ * g * Q) w) := fun g hg w => by
    rw [hU _ (conj_UH h2 hGG hg), cd]
  refine ⟨S.map fun l => l.map fun X => Q * X * Q⁻¹, ?_, ⟨fun y => B (Q⁻¹ * y * Q), hB.comp (by fun_prop), ?_⟩,
    fun i => U (v i), fun i => ℓ i ∘ₗ (U.symm.toLinearEquiv : H' →ₗ[ℂ] H), C, fun i => smF _ (e1 i), e2, ?_, ?_, ?_⟩
  · intro l hl X hX
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
    exact conj_lie h1 hGG' (hS l' hl' Y hY)
  · intro g hg w hw'
    obtain ⟨w, rfl⟩ := U.surjective w
    rw [hσ g hg, hs, hs]
    exact hBc _ (conj_UH h2 hGG hg) w (smB w hw')
  · intro i w hw'
    obtain ⟨w, rfl⟩ := U.surjective w
    rw [hs]
    simpa using e3 i w (smB w hw')
  · simpa only [hs] using e4
  · intro g hg
    simpa [hσ g hg] using e5 _ (conj_UH h2 hGG hg)

end GlobalTheory.TypeSum.Transport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerKAvgNeZero
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum.KCoef

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem toMK_mem_UJ (k : KG ε) : toMK k ∈ UJset ε := K_le_UJ (toMK_mem_K k)

theorem continuous_orbit (hσ : IsURepOn (UJset ε) σ) (w : H) : Continuous fun k : KG ε => σ (toMK k) w :=
  (hσ.2.2 w).comp_continuous (continuous_toMK ε) toMK_mem_UJ

theorem integrable_avg (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) (w : H) :
    Integrable (fun k : KG ε => e k • σ (toMK k) w) (muK ε) :=
  (he.smul (continuous_orbit hσ w)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem sigma_K_mul (hσ : IsURepOn (UJset ε) σ) (a b : KG ε) (w : H) :
    σ (toMK (a * b)) w = σ (toMK a) (σ (toMK b) w) :=
  sigma_mul hσ (toMK_mem_UJ a) (toMK_mem_UJ b) w

theorem inner_K (hσ : IsURepOn (UJset ε) σ) (a : KG ε) (x w : H) :
    ⟪σ (toMK a) w, x⟫_ℂ = ⟪w, σ (toMK a⁻¹) x⟫_ℂ := by
  have h := LinearIsometry.inner_map_map ⟨(σ (toMK a) : H →ₗ[ℂ] H), hσ.2.1 _ (toMK_mem_UJ a)⟩ w (σ (toMK a⁻¹) x)
  have e : σ (toMK a) (σ (toMK a⁻¹) x) = x := by
    rw [← sigma_K_mul hσ, mul_inv_cancel]; exact sigma_one hσ x
  rw [← h]
  exact congrArg (fun z => ⟪σ (toMK a) w, z⟫_ℂ) e.symm

theorem kFinFun_coef (hσ : IsURepOn (UJset ε) σ) {y : H} (hy : IsKFin ε σ y) :
    KFinFun ε (fun k => star ⟪y, σ (toMK k) y⟫_ℂ) := by
  obtain ⟨S, hS, hyS, hK⟩ := hy
  let φ : H → H → KG ε → ℂ := fun s s' k => ⟪σ (toMK k) s', s⟫_ℂ
  obtain ⟨t, ht⟩ : S.FG := Module.Finite.iff_fg.1 hS
  have hfin : (Set.image2 φ (t : Set H) (t : Set H)).Finite := t.finite_toSet.image2 _ t.finite_toSet
  have key : ∀ s ∈ S, ∀ s' ∈ S, φ s s' ∈ Submodule.span ℂ (Set.image2 φ (t : Set H) (t : Set H)) := by
    intro s hs s' hs'
    rw [← ht] at hs hs'
    induction hs using Submodule.span_induction with
    | mem x hx =>
      induction hs' using Submodule.span_induction with
      | mem z hz => exact Submodule.subset_span (Set.mem_image2_of_mem hx hz)
      | zero =>
        have : φ x 0 = 0 := by ext k; simp [φ]
        rw [this]; exact Submodule.zero_mem _
      | add a b _ _ ha hb =>
        have : φ x (a + b) = φ x a + φ x b := by ext k; simp [φ, inner_add_left]
        rw [this]; exact Submodule.add_mem _ ha hb
      | smul c a _ ha =>
        have : φ x (c • a) = (starRingEnd ℂ c) • φ x a := by ext k; simp [φ, inner_smul_left, mul_comm]
        rw [this]; exact Submodule.smul_mem _ _ ha
    | zero =>
      have : φ 0 s' = 0 := by ext k; simp [φ]
      rw [this]; exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
      have : φ (a + b) s' = φ a s' + φ b s' := by ext k; simp [φ, inner_add_right]
      rw [this]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      have : φ (c • a) s' = c • φ a s' := by ext k; simp [φ, inner_smul_right]
      rw [this]; exact Submodule.smul_mem _ _ ha
  have htS : ∀ x ∈ (t : Set H), x ∈ S := fun x hx => ht ▸ Submodule.subset_span hx
  refine ⟨Submodule.span ℂ (Set.image2 φ (t : Set H) (t : Set H)), FiniteDimensional.span_of_finite ℂ hfin, ?_, ?_, ?_⟩
  · have : (fun k : KG ε => star ⟪y, σ (toMK k) y⟫_ℂ) = φ y y := by
      ext k; exact inner_conj_symm _ _
    rw [this]; exact key y hyS y hyS
  · intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, -, b, -, rfl⟩ := hx
      exact (continuous_orbit hσ b).inner continuous_const
    | zero => exact continuous_zero
    | add a b _ _ ha hb => exact ha.add hb
    | smul c a _ ha => exact ha.const_smul c
  · intro ψ hψ k₀
    induction hψ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      constructor
      · have : (fun k => φ a b (k₀ * k)) = φ (σ (toMK k₀⁻¹) a) b := by
          ext k; simp only [φ]; rw [sigma_K_mul hσ, inner_K hσ]
        rw [this]; exact key _ (hK _ (toMK_mem_K _) _ (htS a ha)) _ (htS b hb)
      · have : (fun k => φ a b (k * k₀)) = φ a (σ (toMK k₀) b) := by
          ext k; simp only [φ]; rw [sigma_K_mul hσ]
        rw [this]; exact key _ (htS a ha) _ (hK _ (toMK_mem_K _) _ (htS b hb))
    | zero => exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
    | add a b _ _ ha hb => exact ⟨Submodule.add_mem _ ha.1 hb.1, Submodule.add_mem _ ha.2 hb.2⟩
    | smul c a _ ha => exact ⟨Submodule.smul_mem _ c ha.1, Submodule.smul_mem _ c ha.2⟩

variable [CompleteSpace H]

theorem inner_kAvg (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) (x w : H) :
    ⟪x, kAvg ε σ e w⟫_ℂ = ∫ k, e k * ⟪x, σ (toMK k) w⟫_ℂ ∂(muK ε) := by
  rw [kAvg, ← integral_inner (integrable_avg hσ he w)]
  simp only [inner_smul_right]

theorem inner_kAvg_ne_zero (hσ : IsURepOn (UJset ε) σ) {y : H} (hy : y ≠ 0) :
    ⟪y, kAvg ε σ (fun k => star ⟪y, σ (toMK k) y⟫_ℂ) y⟫_ℂ ≠ 0 := by
  have hc : Continuous fun k : KG ε => ⟪y, σ (toMK k) y⟫_ℂ := continuous_const.inner (continuous_orbit hσ y)
  rw [inner_kAvg hσ hc.star]
  have e : ∀ z : ℂ, star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
  simp only [e]
  rw [integral_complex_ofReal]
  have hpos : 0 < ∫ k : KG ε, ‖⟪y, σ (toMK k) y⟫_ℂ‖ ^ 2 ∂(muK ε) := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) (hc.norm.pow 2)
      (HasCompactSupport.of_compactSpace _) (fun k => by positivity) ?_
    have : σ (toMK (1 : KG ε)) y = y := sigma_one hσ y
    rw [this]
    exact pow_ne_zero _ (norm_ne_zero_iff.2 (inner_self_ne_zero.2 hy))
  exact_mod_cast hpos.ne'

omit [CompleteSpace H] in

theorem exists_clm_kAvg (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) :
    ∃ Q : H →L[ℂ] H, ∀ w, Q w = kAvg ε σ e w := by
  let L : H →ₗ[ℂ] H :=
    { toFun := kAvg ε σ e
      map_add' := fun x y => by
        simp only [kAvg, map_add, smul_add]
        exact integral_add (integrable_avg hσ he x) (integrable_avg hσ he y)
      map_smul' := fun c x => by
        simp only [kAvg, map_smul, RingHom.id_apply, smul_comm _ c]
        exact integral_smul _ _ }
  refine ⟨L.mkContinuous (∫ k, ‖e k‖ ∂(muK ε)) fun w => ?_, fun w => rfl⟩
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp only [norm_smul, fun k : KG ε => hσ.2.1 _ (toMK_mem_UJ k) w]
  exact integral_mul_const _ _

theorem kAvg_mem (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) {S : Submodule ℂ H}
    [FiniteDimensional ℂ S] (hK : IsKStableOn ε σ S) {z : H} (hz : z ∈ S) : kAvg ε σ e z ∈ S := by
  rw [← S.orthogonal_orthogonal, Submodule.mem_orthogonal]
  intro u hu
  rw [inner_kAvg hσ he]
  have : ∀ k : KG ε, ⟪u, σ (toMK k) z⟫_ℂ = 0 := fun k =>
    Submodule.inner_left_of_mem_orthogonal (hK _ (toMK_mem_K k) z hz) hu
  simp [this]

end GlobalTheory.TypeSum.KCoef

namespace GlobalTheory.TypeSum

theorem kCoef_kAvg : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → (∀ y, IsKFin ε σ y → KFinFun ε (fun k => star ⟪y, σ (toMK k) y⟫_ℂ)) ∧ (∀ y : H, y ≠ 0 → ⟪y, kAvg ε σ (fun k => star ⟪y, σ (toMK k) y⟫_ℂ) y⟫_ℂ ≠ 0) ∧ (∀ e : KG ε → ℂ, Continuous e → ∃ Q : H →L[ℂ] H, ∀ w, Q w = kAvg ε σ e w) ∧ ∀ e : KG ε → ℂ, Continuous e → ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → IsKStableOn ε σ S → ∀ z ∈ S, kAvg ε σ e z ∈ S :=
  fun _ _ _ _ _ _ _ hσ => ⟨fun _ hy => KCoef.kFinFun_coef hσ hy, fun _ hy => KCoef.inner_kAvg_ne_zero hσ hy,
    fun _ he => KCoef.exists_clm_kAvg hσ he, fun _ he _ _ hK _ hz => KCoef.kAvg_mem hσ he hK hz⟩

end GlobalTheory.TypeSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAvgClosure
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem isAvg_sigma {g : Mx n} (hg : g ∈ UJset ε) : IsAvg ε σ (σ g) :=
  ⟨{g}, 1, isCompact_singleton, Set.singleton_subset_iff.2 hg, zero_le_one, fun ι _ x w M _ h => by
    rw [one_mul]; exact h g rfl⟩

theorem IsAvg.add {T T' : H → H} (h : IsAvg ε σ T) (h' : IsAvg ε σ T') : IsAvg ε σ (fun w => T w + T' w) := by
  obtain ⟨Z, C, h1, h2, h3, h4⟩ := h
  obtain ⟨Z', C', k1, k2, k3, k4⟩ := h'
  refine ⟨Z ∪ Z', C + C', h1.union k1, Set.union_subset h2 k2, add_nonneg h3 k3, fun ι _ x w M hM hb => ?_⟩
  simp only [inner_add_right, Finset.sum_add_distrib, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (h4 ι x w M hM fun y hy => hb y (Or.inl hy))
    (k4 ι x w M hM fun y hy => hb y (Or.inr hy)))

theorem IsAvg.comp (hσ : IsURepOn (UJset ε) σ) {T T' : H → H} (h : IsAvg ε σ T) (h' : IsAvg ε σ T') :
    IsAvg ε σ (fun w => T (T' w)) := by
  obtain ⟨Z, C, h1, h2, h3, h4⟩ := h
  obtain ⟨Z', C', k1, k2, k3, k4⟩ := h'
  refine ⟨(fun p : Mx n × Mx n => p.1 * p.2) '' (Z ×ˢ Z'), C * C',
    (h1.prod k1).image (continuous_fst.matrix_mul continuous_snd), ?_, mul_nonneg h3 k3, fun ι _ x w M hM hb => ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact mul_mem_UJ (h2 hp.1) (k2 hp.2)
  rw [mul_assoc]
  refine h4 ι x (fun j => T' (w j)) (C' * M) (mul_nonneg k3 hM) fun y hy => ?_
  simp only [inner_sigma hσ (h2 hy)]
  refine k4 ι (fun j => σ y⁻¹ (x j)) w M hM fun y' hy' => ?_
  have := hb (y * y') ⟨(y, y'), ⟨hy, hy'⟩, rfl⟩
  simpa only [sigma_mul hσ (h2 hy) (k2 hy'), inner_sigma hσ (h2 hy)] using this

theorem IsAvg.smul (c : ℂ) {T : H → H} (h : IsAvg ε σ T) : IsAvg ε σ (fun w => c • T w) := by
  obtain ⟨Z, C, h1, h2, h3, h4⟩ := h
  refine ⟨Z, ‖c‖ * C, h1, h2, mul_nonneg (norm_nonneg _) h3, fun ι _ x w M hM hb => ?_⟩
  simp only [inner_smul_right, ← Finset.mul_sum, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h4 ι x w M hM hb) (norm_nonneg _)

theorem isAvg_zero : IsAvg ε σ (fun _ => 0) :=
  ⟨∅, 0, isCompact_empty, Set.empty_subset _, le_rfl, fun ι _ x w M _ _ => by simp⟩

theorem isAvg_kAvg [CompleteSpace H] (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) :
    IsAvg ε σ (kAvg ε σ e) := by
  refine ⟨Kset ε, ∫ k, ‖e k‖ ∂(muK ε), (maximal_compact_facts n ε).2.1, fun k hk => K_le_UJ hk,
    integral_nonneg fun _ => norm_nonneg _, fun ι _ x w M hM hb => ?_⟩
  have hi : ∀ v : H, Integrable (fun k : KG ε => e k • σ (toMK k) v) (muK ε) := fun v =>
    (he.smul ((hσ.2.2 v).comp_continuous (continuous_toMK ε)
      fun k => K_le_UJ (toMK_mem_K k))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp only [kAvg]
  simp only [fun j => (integral_inner (𝕜 := ℂ) (hi (w j)) (x j)).symm]
  rw [← integral_finset_sum _ fun j _ => (hi (w j)).const_inner (x j), ← integral_mul_const]
  refine norm_integral_le_of_norm_le ((he.norm.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)).mul_const M) (Eventually.of_forall fun k => ?_)
  simp only [inner_smul_right, ← Finset.mul_sum, norm_mul]
  exact mul_le_mul_of_nonneg_left (hb _ (toMK_mem_K k)) (norm_nonneg _)

theorem isAvg_closure : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → (∀ g ∈ UJset ε, IsAvg ε σ (σ g)) ∧ (∀ T T' : H → H, IsAvg ε σ T → IsAvg ε σ T' → IsAvg ε σ (fun w => T w + T' w) ∧ IsAvg ε σ (fun w => T (T' w))) ∧ (∀ (c : ℂ) (T : H → H), IsAvg ε σ T → IsAvg ε σ (fun w => c • T w)) ∧ (∀ e : KG ε → ℂ, Continuous e → IsAvg ε σ (kAvg ε σ e)) ∧ IsAvg ε σ (fun _ => 0) :=
  fun _ _ _ _ _ _ _ hσ => ⟨fun _ hg => isAvg_sigma hg, fun _ _ h h' => ⟨h.add h', h.comp hσ h'⟩,
    fun c _ h => h.smul c, fun _ he => isAvg_kAvg hσ he, isAvg_zero⟩

end GlobalTheory.TypeSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedDerivativeFamiliesModerateGrowth
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum.FamClosed

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem hasDerivAt_flow {R : ℝ → (E →L[ℂ] E)} (hR : ∀ s t, R (s + t) = (R s).comp (R t)) {a b : E}
    (h : HasDerivAt (fun t : ℝ => R t a) b 0) (s : ℝ) : HasDerivAt (fun t : ℝ => R t a) (R s b) s := by
  have h1 := ((R s).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h
  have h2 := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact h1)
  refine HasDerivAt.congr_of_eventuallyEq h2 (Filter.Eventually.of_forall fun t => ?_)
  show _ = R s (R (t - s) a)
  rw [← ContinuousLinearMap.comp_apply, ← hR, add_sub_cancel]

theorem norm_sub_le {f f' : ℝ → E} (hf : ∀ s, HasDerivAt f (f' s) s) {t C : ℝ}
    (hC : ∀ s, |s| ≤ |t| → ‖f' s‖ ≤ C) : ‖f t - f 0‖ ≤ C * |t| := by
  have := (convex_closedBall (0 : ℝ) |t|).norm_image_sub_le_of_norm_hasDerivWithin_le (f := f) (f' := f') (C := C)
    (fun s _ => (hf s).hasDerivWithinAt) (fun s hs => hC s (by simpa using hs))
    (Metric.mem_closedBall_self (abs_nonneg t)) (y := t) (by simp)
  simpa using this

theorem taylor_bound {R : ℝ → (E →L[ℂ] E)} (h0 : R 0 = 1) (hR : ∀ s t, R (s + t) = (R s).comp (R t)) {M : ℝ}
    (hM : ∀ s, |s| ≤ 1 → ‖R s‖ ≤ M) {a b c : E} (ha : HasDerivAt (fun t : ℝ => R t a) b 0)
    (hb : HasDerivAt (fun t : ℝ => R t b) c 0) {t : ℝ} (ht : |t| ≤ 1) :
    ‖R t a - a - t • b‖ ≤ M * ‖c‖ * |t| * |t| := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simp))
  have h1 : ∀ s, |s| ≤ |t| → ‖R s b - b‖ ≤ M * ‖c‖ * |t| := fun s hs => by
    have := norm_sub_le (hasDerivAt_flow hR hb) (t := s) (C := M * ‖c‖) fun u hu =>
      ((R u).le_opNorm c).trans (mul_le_mul_of_nonneg_right (hM u (hu.trans (hs.trans ht))) (norm_nonneg _))
    simp only [h0, ContinuousLinearMap.one_apply] at this
    exact this.trans (mul_le_mul_of_nonneg_left hs (by positivity))
  have h2 := norm_sub_le (f := fun s : ℝ => R s a - s • b) (f' := fun s => R s b - b)
    (fun s => by
      have := (hasDerivAt_flow hR ha s).fun_sub ((hasDerivAt_id' s).smul_const b)
      rwa [one_smul] at this) h1
  simp only [h0, ContinuousLinearMap.one_apply, zero_smul, sub_zero] at h2
  rwa [sub_right_comm]

theorem hasDerivAt_of_bound {f : ℝ → E} {b : E} {K : ℝ}
    (h : ∀ t, |t| ≤ 1 → ‖f t - f 0 - t • b‖ ≤ K * |t| * |t|) : HasDerivAt f b 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add]
  have h1 : (fun t : ℝ => f t - f 0 - t • b) =O[𝓝 0] fun t : ℝ => t ^ 2 := by
    refine Asymptotics.IsBigO.of_bound K ?_
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with t ht
    have := h t (by simpa using ht)
    rwa [norm_pow, Real.norm_eq_abs, sq, ← mul_assoc]
  exact h1.trans_isLittleO (Asymptotics.isLittleO_pow_id one_lt_two)

end GlobalTheory.TypeSum.FamClosed

open GlobalTheory.TypeSum.FamClosed in

theorem GlobalTheory.TypeSum.isClosed_fam (n : ℕ) (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (ρ : Mx n → (E →L[ℂ] E)) (hρ : ModRep ε ρ) : IsClosed (Fam ε ρ : Set (List (lie (Jm ε)) → E)) := by
  obtain ⟨h1, hmul, C, N, hC⟩ := hρ
  refine isClosed_of_closure_subset fun v hv => ⟨fun l X => ?_, fun l₁ l₂ a X Y => ?_, fun l₁ l₂ X Y Z hZ => ?_⟩
  · have hX : (X : Mx n) ∈ lieSet ε := X.2
    have h0 : ρ (NormedSpace.exp ((0 : ℝ) • (X : Mx n))) = 1 := by rw [zero_smul, NormedSpace.exp_zero, h1]
    have hR : ∀ s t : ℝ, ρ (NormedSpace.exp ((s + t) • (X : Mx n))) =
        (ρ (NormedSpace.exp (s • (X : Mx n)))).comp (ρ (NormedSpace.exp (t • (X : Mx n)))) := fun s t => by
      rw [exp_add_smul, hmul _ (exp_mem_UJ hX s) _ (exp_mem_UJ hX t)]
    have hc : Continuous fun s : ℝ => C * (1 + hs (NormedSpace.exp (s • (X : Mx n)))) ^ N :=
      continuous_const.mul ((continuous_const.add (continuous_hs.comp (continuous_exp_smul _))).pow N)
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℝ) 1).bddAbove_image hc.continuousOn
    have hM' : ∀ s : ℝ, |s| ≤ 1 → ‖ρ (NormedSpace.exp (s • (X : Mx n)))‖ ≤ M := fun s hs =>
      (hC _ (exp_mem_UJ hX s)).trans (hM ⟨s, by simpa using hs, rfl⟩)
    refine hasDerivAt_of_bound (K := M * ‖v (X :: X :: l)‖) fun t ht => ?_
    simp only [h0, ContinuousLinearMap.one_apply]
    have hcl : IsClosed {w : List (lie (Jm ε)) → E |
        ‖ρ (NormedSpace.exp (t • (X : Mx n))) (w l) - w l - t • w (X :: l)‖ ≤ M * ‖w (X :: X :: l)‖ * |t| * |t|} :=
      isClosed_le (by fun_prop) (by fun_prop)
    exact closure_minimal (fun w hw => taylor_bound (R := fun s : ℝ => ρ (NormedSpace.exp (s • (X : Mx n))))
      h0 hR hM' (hw.1 l X) (hw.1 (X :: l) X) ht) hcl hv
  · have hcl : IsClosed {w : List (lie (Jm ε)) → E |
        w (l₁ ++ (a • X + Y) :: l₂) = (a : ℂ) • w (l₁ ++ X :: l₂) + w (l₁ ++ Y :: l₂)} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    exact closure_minimal (fun w hw => hw.2.1 l₁ l₂ a X Y) hcl hv
  · have hcl : IsClosed {w : List (lie (Jm ε)) → E |
        w (l₁ ++ X :: Y :: l₂) - w (l₁ ++ Y :: X :: l₂) = w (l₁ ++ Z :: l₂)} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    exact closure_minimal (fun w hw => hw.2.2 l₁ l₂ X Y Z hZ) hcl hv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductMeasureBasicPropertiesStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrictedProductMeasure_basic_properties : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (ν : Measure (Fin n → Fin M → AF F ⊗[F] E)) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsProd b ν mi mv → IsFiniteMeasureOnCompacts ν ∧ (mi ≠ 0 → (∀ v, mv v ≠ 0) → ν ≠ 0) ∧ (∀ ν', IsProd b ν' mi mv → ν' = ν) ∧ ∀ (Ai : Set (Fin n → Fin M → Ainf F ⊗[F] E)) (Av : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), MeasurableSet Ai → (∀ v, MeasurableSet (Av v)) → mi Aiᶜ = 0 → (∀ v, mv v (Av v)ᶜ = 0) → ν {X | ¬ (projInf X ∈ Ai ∧ ∀ v, projV v (projFin X) ∈ Av v)} = 0 := by
  first | exact @GlobalTheory.GaugeEx.isProd_basic | exact GlobalTheory.GaugeEx.isProd_basic | (intros; apply GlobalTheory.GaugeEx.isProd_basic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchrodingerIntertwinerInjectiveSchwartzBruhat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceModelInj

theorem placeModel_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (e : AE D) (f₀ Φ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → e * e = e → e * cA D e = 0 → infPart D e = 0 → IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → f₀ ≠ 0 → IsSBHalf e (latO S T ΛS ΛT fun _ => True) Φ → Φ ≠ 0 → Tm Φ ≠ 0 :=
  fun _ _ _ _ _ _ _ _ _ _ hψ hS hT he hec hinf hTm hf hΦ h0 =>
    (GlobalTheory.Chain.StepVac.placeModel_span_ne hψ hS hT he hec hinf hTm hΦ).2 hf h0

end GlobalTheory.PlaceModelInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurInnerEqPairClosableNormInvariantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schur_inner_eq_pair_closable_normInvariant : ∀ (ι H E : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (ρ : ι → (H →L[ℂ] H)) (D : Submodule ℂ H), (∀ i v, ‖ρ i v‖ = ‖v‖) → (∀ i, ∃ j, (∀ v, ρ j (ρ i v) = v) ∧ ∀ v, ρ i (ρ j v) = v) → (∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ i, ∀ v ∈ S, ρ i v ∈ S) → S = ⊥ ∨ S = ⊤) → (∀ i, ∀ v ∈ D, ρ i v ∈ D) → ∀ A A' : H →ₗ[ℂ] E, (∀ i, ∀ w ∈ D, ‖A (ρ i w)‖ = ‖A w‖) → (∀ i, ∀ w ∈ D, ‖A' (ρ i w)‖ = ‖A' w‖) → (∀ i, ∀ w ∈ D, ⟪A (ρ i w), A' (ρ i w)⟫_ℂ = ⟪A w, A' w⟫_ℂ) → (∀ (u : ℕ → H) (f : E), (∀ i, u i ∈ D) → Tendsto u atTop (𝓝 0) → Tendsto (fun i => A (u i)) atTop (𝓝 f) → f = 0) → (∀ (u : ℕ → H) (f : E), (∀ i, u i ∈ D) → Tendsto u atTop (𝓝 0) → Tendsto (fun i => A' (u i)) atTop (𝓝 f) → f = 0) → ∃ c : ℂ, ∀ w ∈ D, ∀ w' ∈ D, ⟪A w, A' w'⟫_ℂ = c * ⟪w, w'⟫_ℂ := by
  first | exact @GlobalTheory.ClosableSchur.inner_eq_pair | exact GlobalTheory.ClosableSchur.inner_eq_pair | (intros; apply GlobalTheory.ClosableSchur.inner_eq_pair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothAutomorphicFormRightTranslateFiniteAdelicStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothAutomorphicForm_rightTranslate_finiteAdelic : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (φ : GA D V → ℂ), IsAutFunSm θ V φ → ∀ k ∈ GfC V, IsAutFunSm θ V (rTr V k φ) := by
  first | exact @GlobalTheory.Mem.FinTranslate.isAutFunSm_rTr_fin | exact GlobalTheory.Mem.FinTranslate.isAutFunSm_rTr_fin | (intros; apply GlobalTheory.Mem.FinTranslate.isAutFunSm_rTr_fin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdHermitianFibreProductChangeOfBasisStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stdHermitianFibreProduct_change_of_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J J' : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E) (β : F) (ν' : Measure (Fin 1 → Fin M → AF F ⊗[F] E)), J' = Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin M) (Fin M) E) * J * (P : Matrix (Fin M) (Fin M) E) → IsStdX s σ J' β ν' → IsStdX s σ J β (ν'.map (lrAct ((P : Matrix (Fin M) (Fin M) E).map (inclR (AF F))) 1)) := by
  first | exact @GlobalTheory.GaugeEx.BasisX.isStdX_basis | exact GlobalTheory.GaugeEx.BasisX.isStdX_basis | (intros; apply GlobalTheory.GaugeEx.BasisX.isStdX_basis <;> assumption)
end

