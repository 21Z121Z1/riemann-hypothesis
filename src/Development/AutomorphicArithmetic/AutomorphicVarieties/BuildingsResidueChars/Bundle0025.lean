import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0021
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0022
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.WtMatFix
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0023

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsRestrictionBlockEmbeddingIntertwinesLie
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private noncomputable def extL (K : Type) [Field K] [NumberField K] {a n : ℕ} (e : Fin a ↪ Fin n) :
    archLie K a →ₗ[ℝ] archLie K n where
  toFun Y := (isExpLieAlgebra K n).ofLie (toLie K n (ext0 e (mat Y.1)))
  map_add' X Y := Subtype.ext (matrixExtendByZero_add e (mat X.1) (mat Y.1))
  map_smul' c X := Subtype.ext (by
    change ext0 e (c • mat X.1) = c • ext0 e (mat X.1)
    simp only [ext0, Matrix.mul_smul, Matrix.smul_mul])

private theorem key (K : Type) [Field K] [NumberField K] {a n : ℕ} (e : Fin a ↪ Fin n)
    (g : AdelicGLn.AdelicGL K n) (ψ : AdelicGLn.AdelicGL K n → ℂ) (m : AdelicGLn.AdelicGL K a) (x : archGroup K a)
    (Y : archLie K a) :
    archSlice (fun m => ψ (g * emb e m)) m (x * (isExpLieAlgebra K a).expG Y) =
      archSlice ψ (g * emb e m) (embArch e x * (isExpLieAlgebra K n).expG (extL K e Y)) := by
  obtain ⟨h1, h2⟩ := UpperTheory.blockEmbedding_comm_infEmb_and_exp K a n e
  have h3 : embArch e ((isExpLieAlgebra K a).expG Y) = (isExpLieAlgebra K n).expG (extL K e Y) := h2 (mat Y.1)
  rw [← h3, ← map_mul, archSlice_apply, archSlice_apply, ← h1, map_mul (emb e) m, mul_assoc]

theorem UpperTheory.exists_restriction_blockEmbedding_intertwines_lie :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n) (g : AdelicGLn.AdelicGL K n), ∃ f : archSmooth K n →ₗ[ℂ] archSmooth K a, (∀ ψ m, (f ψ).1 m = ψ.1 (g * emb e m)) ∧ ∀ X ψ, f (lam K n (ext0 e X) ψ) = lam K a X (f ψ) := by
  intro K _ _ a n e g
  have hs : ∀ ψ : archSmooth K n, (fun m => ψ.1 (g * emb e m)) ∈ archSmooth K a := fun ψ m => by
    rw [IsExpLieAlgebra.isSmoothFun_iff]
    intro x
    simp only [key]
    exact (((isExpLieAlgebra K n).isSmoothFun_iff).1 (ψ.2 (g * emb e m)) (embArch e x)).comp
      (LinearMap.toContinuousLinearMap (extL K e)).contDiff
  refine ⟨{ toFun := fun ψ => ⟨_, hs ψ⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl },
    fun _ _ => rfl, fun X ψ => Subtype.ext (funext fun m => ?_)⟩
  have h1 := (isExpLieAlgebra K a).hasDerivAt_rightDeriv (hs ψ m) ((isExpLieAlgebra K a).ofLie (toLie K a X)) 1
  have h2 := (isExpLieAlgebra K n).hasDerivAt_rightDeriv (ψ.2 (g * emb e m))
    (extL K e ((isExpLieAlgebra K a).ofLie (toLie K a X))) 1
  simp only [key, map_one, map_smul] at h1
  exact (uAction_ι_apply (toLie K n (ext0 e X)) ψ (g * emb e m)).trans
    ((h2.unique h1).trans (uAction_ι_apply (toLie K a X) ⟨_, hs ψ⟩ m).symm)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiltrationEntriesOfFrobeniusMatrix
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Polynomial

namespace UpperTheory.V

variable {l : ℕ} [Fact l.Prime]

private def slS (l : ℕ) [Fact l.Prime] : Subring (Bcr l) where
  carrier := {b | (PP l).ιB b ∈ ((PP l).PD (botExt l)).Fil 0}
  mul_mem' := fun {a b} ha hb => by
    have := ((PP l).PD (botExt l)).Fil_mul 0 0 _ _ ha hb
    rw [add_zero, ← map_mul] at this
    exact this
  one_mem' := by
    change (PP l).ιB 1 ∈ ((PP l).PD (botExt l)).Fil 0
    rw [map_one]; exact ((PP l).PD (botExt l)).one_mem
  add_mem' := fun {a b} ha hb => by
    change (PP l).ιB (a + b) ∈ ((PP l).PD (botExt l)).Fil 0
    rw [map_add]; exact Submodule.add_mem _ ha hb
  zero_mem' := by
    change (PP l).ιB 0 ∈ ((PP l).PD (botExt l)).Fil 0
    rw [map_zero]; exact Submodule.zero_mem _
  neg_mem' := fun {a} ha => by
    change (PP l).ιB (-a) ∈ ((PP l).PD (botExt l)).Fil 0
    rw [map_neg]; exact Submodule.neg_mem _ ha

private theorem sl_alg (K : FinExt l) (c : ↥(K0 K)) : algebraMap ↥(K0 K) (Bcr l) c ∈ slS l := by
  have h : (PP l).ιB (algebraMap ↥(K0 K) (Bcr l) c) ∈ ((PP l).PD K).Fil 0 := by
    rw [← (PP l).PD_ι K, AlgHom.commutes, IsScalarTower.algebraMap_apply ↥(K0 K) ↥K.1 (PP l).R.BdR,
      Algebra.algebraMap_eq_smul_one]
    exact (((PP l).PD K).Fil 0).smul_mem _ ((PP l).PD K).one_mem
  have h2 := (PP l).PD_Fil K (botExt l) 0
  change (PP l).ιB _ ∈ (((PP l).PD (botExt l)).Fil 0 : Set (PP l).R.BdR)
  rw [← h2]
  exact h

end UpperTheory.V

open UpperTheory.V in
theorem UpperTheory.filtration_entries_of_frobenius_matrix :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (f : ℕ), 0 < f → (∀ x : ↥(K0 K), (((PP l).PD K).σ)^[f] x = x) → ∀ {d : ℕ} (M M' : Matrix (Fin d) (Fin d) (Bcr l)) (A F : Matrix (Fin d) (Fin d) ↥(K0 K)), M * M' = 1 → IsUnit A.det → M.map (PP l).φB = M * A.map (algebraMap ↥(K0 K) (Bcr l)) → M.map (((PP l).φB)^[f]) = M * F.map (algebraMap ↥(K0 K) (Bcr l)) → ∀ a : ℤ, (∀ i j, (PP l).ιB (M i j) ∈ ((PP l).PD (botExt l)).Fil a) → ∀ β ∈ spectrum (Om l) (F.map (algebraMap ↥(K0 K) (Om l))), ‖((l : Om l) ^ f) ^ (-a) * β‖ ≤ 1 := by
  intro l hl K f hf hσ d M M' A F hMM hA hφ hF a hFil β hβ
  obtain ⟨u, hu, hφu⟩ := UpperTheory.exists_crystalline_unit_frobenius_eigen l (-a)
  have hMM' : M' * M = 1 := mul_eq_one_comm.1 hMM
  have hc : ∀ k : ℕ, ((PP l).φB)^[k] = ⇑((PP l).φB ^ k) := fun k => (AlgHom.coe_pow _ _).symm
  have hit : ∀ k : ℕ, ((PP l).φB)^[k] (u : Bcr l) =
      algebraMap ℚ_[l] (Bcr l) (((l : ℚ_[l]) ^ (-a)) ^ k) * (u : Bcr l) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, map_mul, AlgHom.commutes, hφu, pow_succ, map_mul, mul_assoc]
  have huM : ∀ i j, (u : Bcr l) * M i j ∈ slS l := fun i j => by
    have := ((PP l).PD (botExt l)).Fil_mul _ _ _ _ hu (hFil i j)
    rw [neg_add_cancel, ← map_mul] at this
    exact this
  have key : ∀ (k : ℕ) (E : Matrix (Fin d) (Fin d) ↥(K0 K)),
      M.map (((PP l).φB)^[k]) = M * E.map (algebraMap ↥(K0 K) (Bcr l)) →
      ((u : Bcr l) • M).map (((PP l).φB)^[k]) = ((u : Bcr l) • M) *
        (algebraMap ℚ_[l] ↥(K0 K) (((l : ℚ_[l]) ^ (-a)) ^ k) • E).map (algebraMap ↥(K0 K) (Bcr l)) := by
    intro k E hE
    ext i j
    have h1 := congrFun (congrFun hE i) j
    simp only [Matrix.map_apply, Matrix.mul_apply] at h1
    have h2 : ((PP l).φB)^[k] ((u : Bcr l) * M i j) =
        ((PP l).φB)^[k] (u : Bcr l) * ((PP l).φB)^[k] (M i j) := by
      rw [hc, map_mul]
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
    rw [h2, hit, h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_mul, ← IsScalarTower.algebraMap_apply]
    ring
  have h := UpperTheory.norm_le_one_of_mem_spectrum_frobenius_matrix_fil_zero K f hf hσ ((u : Bcr l) • M) (((u⁻¹ : (Bcr l)ˣ) : Bcr l) • M') _
    (by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Units.inv_mul, one_smul, hMM'])
    (fun k i j => by
      obtain ⟨E, -, hE⟩ := UpperTheory.frobenius_iterate_matrix_form K M A hA hφ k
      have h1 := congrFun (congrFun (key k E hE) i) j
      rw [Matrix.map_apply, Matrix.mul_apply] at h1
      rw [h1]
      exact Subring.sum_mem (slS l) fun r _ => Subring.mul_mem _ (huM _ _) (sl_alg K _))
    (key f F hF)
  apply h
  have hl0 : ((l : Om l) ^ f) ^ (-a) ≠ 0 :=
    zpow_ne_zero _ (pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero))
  have e : (algebraMap ℚ_[l] ↥(K0 K) (((l : ℚ_[l]) ^ (-a)) ^ f) • F).map (algebraMap ↥(K0 K) (Om l)) =
      Units.mk0 _ hl0 • F.map (algebraMap ↥(K0 K) (Om l)) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, map_zpow₀, map_natCast,
      Units.smul_mk0]
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm (f : ℤ)]
  rw [e]
  exact (spectrum.smul_mem_smul_iff (r := Units.mk0 _ hl0)).2 hβ
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteDimensionalSlSpReduction
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem aux {G H G' H' : Type} [Monoid G] [Monoid H] [Monoid G'] [Monoid H'] (E : G →* H) (i : G' → G) (i' : H' → H)
    (j : G' → H') (hj : ∀ k k', j (k * k') = j k * j k') (hi : ∀ k, E (i k) = i' (j k)) (V : Submodule ℂ (H' → ℂ))
    (hst : ∀ f ∈ V, ∀ k', (fun k => f (k * k')) ∈ V) :
    (∀ f ∈ V.map (LinearMap.funLeft ℂ ℂ j), ∀ k', (fun k => f (k * k')) ∈ V.map (LinearMap.funLeft ℂ ℂ j)) ∧
    ∀ (f : G → ℂ) (ψ : H → ℂ) (g₀ : H), (∀ g, (fun k => ψ (g * i' k)) ∈ V) → (∀ m, f m = ψ (g₀ * E m)) →
      ∀ g, (fun k => f (g * i k)) ∈ V.map (LinearMap.funLeft ℂ ℂ j) := by
  constructor
  · rintro _ ⟨f, hf, rfl⟩ k'
    refine ⟨_, hst f hf (j k'), funext fun k => ?_⟩
    simp only [LinearMap.funLeft_apply, hj]
  · intro f ψ g₀ hψ hf g
    refine ⟨_, hψ (g₀ * E g), funext fun k => ?_⟩
    simp only [LinearMap.funLeft_apply]
    rw [hf, map_mul, hi, mul_assoc]

private theorem aux2 (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n) (k : archCompact K a) :
    embArch e k.1 ∈ archCompact K n := by
  have h := UpperTheory.blockEmbedding_adelic_norm_compat K a n e _ (Subgroup.mem_comap.1 k.2)
  rw [(UpperTheory.blockEmbedding_comm_infEmb_and_exp K a n e).1] at h
  exact Subgroup.mem_comap.2 h

private theorem aux3 {G X : Type} (A : Submodule ℂ (G → ℂ)) (s : Set A) (p : X → G) (W : Submodule ℂ (X → ℂ))
    (h : ∀ f ∈ s, (fun k => f.1 (p k)) ∈ W) : ∀ f ∈ Submodule.span ℂ s, (fun k => f.1 (p k)) ∈ W := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    convert W.zero_mem using 1
    funext k
    simp
  | add x y _ _ hx hy =>
    convert W.add_mem hx hy using 1
    funext k
    simp
  | smul c x _ hx =>
    convert W.smul_mem c hx using 1
    funext k
    simp

theorem UpperTheory.finiteDimensional_slSp_reduction :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n) (Γ : Set (AdelicGLn.AdelicGL K n)) (S : Submodule ℂ (archSmooth K n)), Types S → Types (slSp e Γ S) := by
  intro K _ _ a n e Γ S hS
  obtain ⟨V, hVf, hVst, hV⟩ := hS
  let j : archCompact K a → archCompact K n := fun k => ⟨embArch e k.1, aux2 K a n e k⟩
  have hj : ∀ k k', j (k * k') = j k * j k' := fun k k' => Subtype.ext (map_mul (embArch e) k.1 k'.1)
  have hi : ∀ k : archCompact K a, emb e (infEmb K a k.1) = infEmb K n (j k).1 :=
    fun k => (UpperTheory.blockEmbedding_comm_infEmb_and_exp K a n e).1 k.1
  have key := aux (G := AdelicGLn.AdelicGL K a) (H := AdelicGLn.AdelicGL K n) (emb e)
    (fun k : archCompact K a => infEmb K a k.1)
    (fun k : archCompact K n => infEmb K n k.1) j hj hi V hVst
  refine ⟨V.map (LinearMap.funLeft ℂ ℂ j), ?_, key.1, ?_⟩
  · exact Module.Finite.map V _
  · intro f hf g
    unfold slSp at hf
    refine aux3 (archSmooth K a) _ (fun k : archCompact K a => g * infEmb K a k.1)
      (V.map (LinearMap.funLeft ℂ ℂ j)) ?_ f hf
    rintro f' ⟨ψ, hψ, g₀, -, hf'⟩
    exact key.2 f'.1 ψ.1 g₀ (hV ψ hψ) hf' g
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SlSpPreservesGrowthAndLevel
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.slSp_preserves_growth_and_level :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n) (Γ : Set (AdelicGLn.AdelicGL K n)) (S : Submodule ℂ (archSmooth K n)), (Growth S → Growth (slSp e Γ S)) ∧ (Level S → Level (slSp e Γ S)) := by
  intro K _ _ a n e Γ S
  constructor
  · intro hG φ hφ
    induction hφ using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨ψ, hψ, g, -, hfm⟩ := hf
      obtain ⟨C, N, hC⟩ := hG ψ hψ
      have hC0 : 0 ≤ C := by
        have h1 := (norm_nonneg _).trans (hC 1)
        have hp : 0 < height (1 : AdelicGLn.AdelicGL K n) ^ N := pow_pos (height_pos _) N
        exact le_of_mul_le_mul_right (by rw [zero_mul]; exact h1) hp
      have hc : 0 ≤ heightConst K n * height g :=
        mul_nonneg (zero_le_one.trans (one_le_heightConst (K := K) (n := n))) (height_pos g).le
      refine ⟨C * (heightConst K n * height g) ^ N, N, fun m => ?_⟩
      have hh : height (g * emb e m) ≤ heightConst K n * height g * height m :=
        (height_mul_le _ _).trans (mul_le_mul_of_nonneg_left (UpperTheory.height_blockEmbedding_le K a n e m) hc)
      calc ‖(f : AdelicGLn.AdelicGL K a → ℂ) m‖ = ‖(ψ : AdelicGLn.AdelicGL K n → ℂ) (g * emb e m)‖ := by rw [hfm]
        _ ≤ C * height (g * emb e m) ^ N := hC _
        _ ≤ C * (heightConst K n * height g * height m) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos _).le hh N) hC0
        _ = C * (heightConst K n * height g) ^ N * height m ^ N := by rw [mul_pow]; ring
    | zero => simpa using (hasModerateGrowth_zero (K := K) (n := a))
    | add x y _ _ hx hy => simpa using hx.add hy
    | smul c x _ hx => simpa using hx.smul c
  · rintro ⟨L, hL, hinv⟩
    let f : AdelicGLn.FiniteAdelicGL K a →* AdelicGLn.FiniteAdelicGL K n := emb e
    refine ⟨L.comap f, hL.preimage (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous K a n e).2.2, fun φ hφ => ?_⟩
    induction hφ using Submodule.span_induction with
    | mem h hh =>
      obtain ⟨ψ, hψ, g, -, hfm⟩ := hh
      intro u hu m
      rw [hfm, hfm, map_mul, (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous K a n e).1 u, ← mul_assoc]
      exact hinv ψ hψ (f u) hu _
    | zero => intro u _ m; simp
    | add x y _ _ hx hy => intro u hu m; simp [hx u hu m, hy u hu m]
    | smul c x _ hx => intro u hu m; simp [hx u hu m]
end

