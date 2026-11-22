import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0352
import GroundTheory.AutomorphicForms.AnisotropicHeight
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ConstantTerm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0350
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0322
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0344
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPolynomialProjectionInvariant
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusCh

theorem aeval_mulVec_mem_of_stable {K : Type} [Field K] {n : ℕ} (γ : Matrix (Fin n) (Fin n) K)
    (W : Submodule K (Fin n → K)) (hW : W.map (Matrix.toLin' γ) ≤ W) (g : K[X]) :
    ∀ y ∈ W, aeval γ g *ᵥ y ∈ W := by
  have hγ : ∀ y ∈ W, γ *ᵥ y ∈ W := fun y hy =>
    hW ⟨y, hy, by rw [Matrix.toLin'_apply]⟩
  induction g using Polynomial.induction_on with
  | C a =>
    intro y hy
    rw [aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact W.smul_mem a hy
  | add p q hp hq =>
    intro y hy
    rw [map_add, Matrix.add_mulVec]
    exact W.add_mem (hp y hy) (hq y hy)
  | monomial k a ih =>
    intro y hy
    have : aeval γ (C a * X ^ (k + 1)) = aeval γ (C a * X ^ k) * γ := by
      rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
    rw [this, ← Matrix.mulVec_mulVec]
    exact ih _ (hγ y hy)

def stableIdeal {K : Type} [Field K] {n : ℕ} (γ : Matrix (Fin n) (Fin n) K) (v : Fin n → K)
    (W : Submodule K (Fin n → K)) (hW : W.map (Matrix.toLin' γ) ≤ W) : Ideal K[X] where
  carrier := {h | aeval γ h *ᵥ v ∈ W}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_add, Matrix.add_mulVec]
    exact W.add_mem ha hb
  zero_mem' := by
    simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq, smul_eq_mul] at hx ⊢
    rw [map_mul, ← Matrix.mulVec_mulVec]
    exact aeval_mulVec_mem_of_stable γ W hW c _ hx

theorem exists_idem_pol_range_eq : ∀ (K : Type) [Field K] (n : ℕ) (γ : Matrix (Fin n) (Fin n) K) (v : Fin n → K),
    γ.charpoly.Separable → (∀ y : Fin n → K, ∃ h : K[X], y = aeval γ h *ᵥ v) →
    ∀ W : Submodule K (Fin n → K), W.map (Matrix.toLin' γ) ≤ W →
    ∃ π, IsPol γ π ∧ π * π = π ∧ LinearMap.range (Matrix.toLin' π) = W := by
  intro K _ n γ v hsep hcyc W hW
  set I := stableIdeal γ v W hW with hI
  have hmemI : ∀ h : K[X], h ∈ I ↔ aeval γ h *ᵥ v ∈ W := fun h => Iff.rfl
  obtain ⟨w, hw⟩ : ∃ w, I = Ideal.span {w} :=
    ⟨Submodule.IsPrincipal.generator I, (Ideal.span_singleton_generator I).symm⟩
  have hdvd : ∀ h : K[X], aeval γ h *ᵥ v ∈ W ↔ w ∣ h := fun h => by
    rw [← hmemI, hw, Ideal.mem_span_singleton]
  have hχ : aeval γ γ.charpoly = 0 := Matrix.aeval_self_charpoly γ
  obtain ⟨c, hc⟩ : w ∣ γ.charpoly := by
    rw [← hdvd, hχ, Matrix.zero_mulVec]
    exact W.zero_mem
  have hco : IsCoprime w c := Polynomial.Separable.isCoprime (hc ▸ hsep)
  obtain ⟨u, b, hub⟩ := hco
  refine ⟨aeval γ (u * w), ⟨u * w, rfl⟩, ?_, ?_⟩
  · have key : u * w * (u * w) = u * w - u * b * γ.charpoly := by
      linear_combination (u * w) * hub + (u * b) * hc
    rw [← map_mul, key, map_sub, map_mul (aeval γ) (u * b), hχ, mul_zero, sub_zero]
  · apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      obtain ⟨h, rfl⟩ := hcyc y
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← map_mul, hdvd]
      exact ⟨u * h, by ring⟩
    · intro y hy
      obtain ⟨h, rfl⟩ := hcyc y
      obtain ⟨g, rfl⟩ := (hdvd h).1 hy
      refine ⟨aeval γ (w * g) *ᵥ v, ?_⟩
      have key : u * w * (w * g) = w * g - g * b * γ.charpoly := by
        linear_combination (w * g) * hub + (g * b) * hc
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← map_mul, key, map_sub,
        map_mul (aeval γ) (g * b), hχ, mul_zero, sub_zero]

end GlobalTheory.CompanionTheory.TorusCh
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPrimitiveIdempotentsSeparating
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusCh

theorem dvd_of_aeval_eq_zero_of_dvd_charpoly {K : Type} [Field K] {n : ℕ}
    (γ : Matrix (Fin n) (Fin n) K) {p g : K[X]} (hp : Irreducible p) (hpc : p ∣ γ.charpoly)
    (hg : aeval γ g = 0) : p ∣ g := by
  classical
  by_contra hn
  obtain ⟨a, b, hab⟩ := (hp.coprime_iff_not_dvd).2 hn
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure K) p (ne_of_gt (degree_pos_of_irreducible hp))
  have hroot : (γ.map (algebraMap K (AlgebraicClosure K))).charpoly.IsRoot α := by
    obtain ⟨c, hc⟩ := hpc
    rw [Matrix.charpoly_map, hc, IsRoot, eval_map_algebraMap, map_mul, hα, zero_mul]
  have hs : α ∈ spectrum (AlgebraicClosure K) (γ.map (algebraMap K (AlgebraicClosure K))) :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.2 hroot
  have h2 := spectrum.subset_polynomial_aeval (γ.map (algebraMap K (AlgebraicClosure K)))
    (g.map (algebraMap K (AlgebraicClosure K))) ⟨α, hs, rfl⟩
  have h3 : aeval (γ.map (algebraMap K (AlgebraicClosure K))) (g.map (algebraMap K (AlgebraicClosure K))) = 0 := by
    have := aeval_algHom_apply ((Algebra.ofId K (AlgebraicClosure K)).mapMatrix (m := Fin n)) γ g
    rw [hg, map_zero] at this
    rw [aeval_map_algebraMap]
    exact this
  rw [h3] at h2
  have h4 : aeval α g = 0 := by
    by_contra hne
    apply h2
    simp only [eval_map_algebraMap]
    rw [spectrum.mem_resolventSet_iff, sub_zero]
    exact (Ne.isUnit hne).map (algebraMap (AlgebraicClosure K) (Matrix (Fin n) (Fin n) (AlgebraicClosure K)))
  have h5 := congrArg (aeval α) hab
  simp [hα, h4] at h5

theorem exists_prim_of_irreducible {K : Type} [Field K] {n : ℕ}
    (γ : Matrix (Fin n) (Fin n) K) (hs : γ.charpoly.Separable) {p : K[X]} (hp : Irreducible p)
    (hpc : p ∣ γ.charpoly) :
    ∃ e, IsPrim γ e ∧ ∃ f : K[X], e = aeval γ f ∧ p ∣ 1 - f := by
  obtain ⟨q, hq⟩ := hpc
  have hχ : aeval γ (p * q) = 0 := by rw [← hq]; exact Matrix.aeval_self_charpoly γ
  obtain ⟨b, u, hbu⟩ : IsCoprime p q := (hq ▸ hs : (p * q).Separable).isCoprime
  have hnd : ∀ c : K[X], aeval γ (c * (p * q)) = 0 := fun c => by rw [map_mul, hχ, mul_zero]
  have hsub : (1 : K[X]) - u * q = b * p := by rw [← hbu]; ring
  have hdvd : p ∣ 1 - u * q := ⟨b, by rw [hsub]; ring⟩
  refine ⟨aeval γ (u * q), ⟨⟨_, rfl⟩, ?_, ?_, ?_⟩, _, rfl, hdvd⟩
  · rw [← map_mul]
    have : u * q * (u * q) = u * q - (u * b) * (p * q) := by linear_combination (-(u * q)) * hsub
    rw [this, map_sub, hnd, sub_zero]
  · intro h0
    have h1 := dvd_of_aeval_eq_zero_of_dvd_charpoly γ hp ⟨q, hq⟩ h0
    exact hp.not_isUnit (isUnit_of_dvd_one (by simpa using dvd_add hdvd h1))
  · intro h hne
    have hnp : ¬ p ∣ h := by
      rintro ⟨c, rfl⟩
      apply hne
      rw [← map_mul]
      have : p * c * (u * q) = (c * u) * (p * q) := by ring
      rw [this, hnd]
    obtain ⟨a', a, haa⟩ := (hp.coprime_iff_not_dvd).2 hnp
    refine ⟨a, ?_⟩
    rw [← map_mul, ← map_mul]
    have : a * (h * (u * q)) = u * q - (a' * u) * (p * q) := by linear_combination (u * q) * haa
    rw [this, map_sub, hnd, sub_zero]

theorem exists_prim_cover (K : Type) [Field K] (n : ℕ) (γ : Matrix (Fin n) (Fin n) K)
    (hs : γ.charpoly.Separable) :
    ∃ S : Finset (Matrix (Fin n) (Fin n) K), (∀ e ∈ S, IsPrim γ e) ∧
      ∀ x : Fin n → K, x ≠ 0 → ∃ e ∈ S, x ᵥ* e ≠ 0 := by
  classical
  have key : ∀ p : K[X], p ∈ UniqueFactorizationMonoid.normalizedFactors γ.charpoly →
      ∃ e, IsPrim γ e ∧ ∃ f : K[X], e = aeval γ f ∧ p ∣ 1 - f := fun p hp =>
    exists_prim_of_irreducible γ hs (UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp)
      (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hp)
  choose! E hE using key
  have hχ0 : γ.charpoly ≠ 0 := (Matrix.charpoly_monic γ).ne_zero
  refine ⟨(UniqueFactorizationMonoid.normalizedFactors γ.charpoly).toFinset.image E, ?_, ?_⟩
  · intro e he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 he
    exact (hE p (Multiset.mem_toFinset.1 hp)).1
  · intro x hx
    let I : Ideal K[X] :=
      { carrier := {f | x ᵥ* aeval γ f = 0}
        add_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [map_add, Matrix.vecMul_add, ha, hb, add_zero]
        zero_mem' := by simp
        smul_mem' := fun c f hf => by
          simp only [Set.mem_setOf_eq] at hf ⊢
          rw [smul_eq_mul, mul_comm, map_mul, ← Matrix.vecMul_vecMul, hf, Matrix.zero_vecMul] }
    have hmem : ∀ f, f ∈ I ↔ x ᵥ* aeval γ f = 0 := fun f => Iff.rfl
    set a := Submodule.IsPrincipal.generator I with ha
    have hdiv : ∀ f, f ∈ I ↔ a ∣ f := fun f => Submodule.IsPrincipal.mem_iff_generator_dvd I
    have haχ : a ∣ γ.charpoly := (hdiv _).1 (by
      rw [hmem, Matrix.aeval_self_charpoly, Matrix.vecMul_zero])
    have ha0 : a ≠ 0 := fun h => hχ0 (by simpa [h] using haχ)
    have hau : ¬ IsUnit a := fun h => hx (by
      have h1 : (1 : K[X]) ∈ I := (hdiv 1).2 h.dvd
      rw [hmem, map_one, Matrix.vecMul_one] at h1
      exact h1)
    obtain ⟨i, hi, hia⟩ := WfDvdMonoid.exists_irreducible_factor hau ha0
    obtain ⟨p, hp, hip⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hχ0 hi (hia.trans haχ)
    obtain ⟨hprim, f, hf, hpf⟩ := hE p hp
    refine ⟨E p, Finset.mem_image.2 ⟨p, Multiset.mem_toFinset.2 hp, rfl⟩, fun h0 => ?_⟩
    rw [hf] at h0
    have h1 : a ∣ f := (hdiv f).1 h0
    have h2 : p ∣ f := hip.symm.dvd.trans (hia.trans h1)
    have hpi : Irreducible p := UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp
    exact hpi.not_isUnit (isUnit_of_dvd_one (by simpa using dvd_add hpf h2))

end GlobalTheory.CompanionTheory.TorusCh
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericFiniteByInduction
section
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl Topology Matrix GroundTheory.Automorphic
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.AffglAssembly

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem isAutForm_add {φ ψ : Sm E a} (h : IsAutForm φ) (h' : IsAutForm ψ) : IsAutForm (φ + ψ) where
  left γ g := by
    change φ.1 _ + ψ.1 _ = φ.1 _ + ψ.1 _
    rw [h.left, h'.left]
  level := isOpen_stab_of_mem_nhds _ _ <| Filter.mem_of_superset
    ((h.level.inter h'.level).mem_nhds ⟨by simp, by simp⟩) fun k hk => by
      have h1 : finRep E a k φ = φ := hk.1
      have h2 : finRep E a k ψ = ψ := hk.2
      change finRep E a k (φ + ψ) = φ + ψ
      rw [map_add, h1, h2]
  kfin := by
    have := h.kfin
    have := h'.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k => cptRep E a k φ) ⊔
      Submodule.span ℂ (Set.range fun k => cptRep E a k ψ)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    simp only [map_add]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨k, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)
  zfin := by
    have := h.zfin
    have := h'.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) ⊔
        Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z ψ) '' Zalg E a)) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    simp only [map_add]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨z, hz, rfl⟩) (Submodule.subset_span ⟨z, hz, rfl⟩)
  growth g := by
    obtain ⟨C, N, h1⟩ := h.growth g
    obtain ⟨C', N', h2⟩ := h'.growth g
    refine ⟨|C| + |C'|, N + N', fun y => ?_⟩
    have hy := one_le_height y
    have e1 : height y ^ N ≤ height y ^ (N + N') := pow_le_pow_right₀ hy (by omega)
    have e2 : height y ^ N' ≤ height y ^ (N + N') := pow_le_pow_right₀ hy (by omega)
    have hp : 0 ≤ height y ^ N := by positivity
    have hp' : 0 ≤ height y ^ N' := by positivity
    calc ‖(φ + ψ).1 (g * infGL E a y)‖ ≤ ‖φ.1 (g * infGL E a y)‖ + ‖ψ.1 (g * infGL E a y)‖ := norm_add_le _ _
      _ ≤ C * height y ^ N + C' * height y ^ N' := add_le_add (h1 y) (h2 y)
      _ ≤ |C| * height y ^ (N + N') + |C'| * height y ^ (N + N') := by
        refine add_le_add ?_ ?_
        · exact (mul_le_mul_of_nonneg_right (le_abs_self C) hp).trans
            (mul_le_mul_of_nonneg_left e1 (abs_nonneg C))
        · exact (mul_le_mul_of_nonneg_right (le_abs_self C') hp').trans
            (mul_le_mul_of_nonneg_left e2 (abs_nonneg C'))
      _ = (|C| + |C'|) * height y ^ (N + N') := by ring

theorem isAutForm_smul (c : ℂ) {φ : Sm E a} (h : IsAutForm φ) : IsAutForm (c • φ) where
  left γ g := by
    change c • φ.1 _ = c • φ.1 _
    rw [h.left]
  level := isOpen_stab_of_mem_nhds _ _ <| Filter.mem_of_superset
    (h.level.mem_nhds (by simp)) fun k hk => by
      have h1 : finRep E a k φ = φ := hk
      change finRep E a k (c • φ) = c • φ
      rw [map_smul, h1]
  kfin := by
    have := h.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k => cptRep E a k φ))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    simp only [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  zfin := by
    have := h.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a)) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    simp only [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨z, hz, rfl⟩)
  growth g := by
    obtain ⟨C, N, h1⟩ := h.growth g
    refine ⟨‖c‖ * C, N, fun y => ?_⟩
    change ‖c * φ.1 (g * infGL E a y)‖ ≤ _
    rw [norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h1 y) (norm_nonneg c)

def genSub (L : Subgroup (GL (Fin a) (Af E))) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Kinf E a) W) (J : Set (Module.End ℂ (Sm E a))) : Submodule ℂ (Sm E a) where
  carrier := genSpace L ρ J
  zero_mem' := ⟨isAutForm_const (Submodule.zero_mem _), fun k _ => map_zero _, fun g => by
    have e : (fun k : Kinf E a => (cptRep E a k (0 : Sm E a)).1 g) = 0 := by
      funext k; rw [map_zero]; rfl
    rw [e]; exact Submodule.zero_mem _, fun z _ => map_zero z⟩
  add_mem' := by
    rintro φ ψ ⟨h1, h2, h3, h4⟩ ⟨h1', h2', h3', h4'⟩
    refine ⟨isAutForm_add h1 h1', fun k hk => by rw [map_add, h2 k hk, h2' k hk], fun g => ?_,
      fun z hz => by rw [map_add, h4 z hz, h4' z hz, add_zero]⟩
    have e : (fun k : Kinf E a => (cptRep E a k (φ + ψ)).1 g) =
        (fun k : Kinf E a => (cptRep E a k φ).1 g) + fun k : Kinf E a => (cptRep E a k ψ).1 g := by
      funext k; rw [map_add]; rfl
    rw [e]; exact Submodule.add_mem _ (h3 g) (h3' g)
  smul_mem' := by
    rintro c φ ⟨h1, h2, h3, h4⟩
    refine ⟨isAutForm_smul c h1, fun k hk => by rw [map_smul, h2 k hk], fun g => ?_,
      fun z hz => by rw [map_smul, h4 z hz, smul_zero]⟩
    have e : (fun k : Kinf E a => (cptRep E a k (c • φ)).1 g) =
        c • fun k : Kinf E a => (cptRep E a k φ).1 g := by
      funext k; rw [map_smul]; rfl
    rw [e]; exact Submodule.smul_mem _ c (h3 g)

theorem continuous_pInf : Continuous (pInf E) :=
  (continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst

theorem continuous_pFin : Continuous (pFin E) := continuous_snd

theorem continuous_mapInf :
    Continuous (GeneralLinearGroup.map (n := Fin a) (pInf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pInf)

theorem continuous_mapFin :
    Continuous (GeneralLinearGroup.map (n := Fin a) (pFin E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pFin)

theorem continuous_of_level {φ : Sm E a} (h : IsOpen {k | finRep E a k φ = φ}) : Continuous φ.1 := by
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  have hc : Continuous fun g : GA E a => g₀⁻¹ * g := continuous_const.mul continuous_id
  let f : GA E a → ℂ := fun g =>
    chart φ.1 g₀ (toL (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)).val)
  have e1 : ∀ᶠ g in 𝓝 g₀, f g = φ.1 g := by
    have hS : {g : GA E a | GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g) ∈ {k | finRep E a k φ = φ}} ∈ 𝓝 g₀ :=
      ((continuous_mapFin.comp hc).continuousAt).preimage_mem_nhds
        (h.mem_nhds (by simp))
    filter_upwards [hS] with g hg
    have hg' : finRep E a (GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g)) φ = φ := hg
    have e2 := congrFun (congrArg Subtype.val hg') (g₀ * infGL E a (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)))
    have e3 : g₀ * infGL E a (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)) *
        finGL E a (GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g)) = g := by
      rw [mul_assoc, infGL_mul_finGL, mul_inv_cancel_left]
    change φ.1 (_ * finGL E a _) = _ at e2
    rw [e3] at e2
    simp only [f]
    rw [chart_val, e2]
  refine ContinuousAt.congr ?_ e1
  have hx : toL (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g₀)).val ∈ invSet E a := val_mem_invSet _
  have h1 : ContinuousAt (chart φ.1 g₀) (toL (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g₀)).val) :=
    (contDiffAt_chart φ.2 g₀ hx).continuousAt
  have h3 : Continuous fun g : GA E a => ((GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g) : GL (Fin a) (Cinf E)) :
      Matrix (Fin a) (Fin a) (Cinf E)) := Units.continuous_val.comp (continuous_mapInf.comp hc)
  have h2 : Continuous fun g : GA E a => toL (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)).val := h3
  exact ContinuousAt.comp (f := fun g : GA E a => toL (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)).val) h1 h2.continuousAt

theorem unip_eq_unipGL {R : Type} [CommRing R] {r : ℕ} (x : BlockIx a r → R) :
    unip x = AutomorphicForm.unipGL x := Units.ext rfl

theorem pi_eq_borel (r : ℕ) :
    (MeasurableSpace.pi : MeasurableSpace (BlockIx a r → Ad E)) = borel (BlockIx a r → Ad E) :=
  BorelSpace.measurable_eq

theorem isCuspidal_of_constantTerm {φ : GA E a → ℂ} (hl : ∀ γ g, φ (ratGL E a γ * g) = φ g)
    (h0 : ∀ r : ℕ, 0 < r → r < a → ∀ g, ∫ x in AutomorphicForm.unipFundamentalDomain E a r, φ (unip x * g)
      ∂AutomorphicForm.unipMeasure E a r = 0) : IsCuspidal φ := by
  intro r hr hr' inst1 inst2 μ 𝓕 hμ hF g
  obtain rfl : inst1 = MeasurableSpace.pi := inst2.measurable_eq.trans (pi_eq_borel r).symm
  have : (AutomorphicForm.unipMeasure E a r).IsAddHaarMeasure := inferInstance
  have hc := Measure.isAddLeftInvariant_eq_smul μ (AutomorphicForm.unipMeasure E a r)
  have : Countable (ratN E a r) := AutomorphicForm.countable_unipLattice (K := E) (n := a) (r := r)
  have hF0 : IsAddFundamentalDomain (ratN E a r) (AutomorphicForm.unipFundamentalDomain E a r) μ :=
    IsAddFundamentalDomain.mono AutomorphicForm.isAddFundamentalDomain_unipFundamentalDomain
      (hc ▸ Measure.smul_absolutelyContinuous)
  have hinv : ∀ (ξ : ratN E a r) (x : BlockIx a r → Ad E), φ (unip (ξ +ᵥ x) * g) = φ (unip x * g) := by
    rintro ⟨_, ξ, rfl⟩ x
    change φ (unip ((fun p => algebraMap E (Ad E) (ξ p)) + x) * g) = _
    rw [unip_add, unip_algebraMap, mul_assoc, hl]
  rw [hF.setIntegral_eq hF0 hinv, hc, Measure.restrict_smul, integral_smul_nnreal_measure, h0 r hr hr' g, smul_zero]

theorem integrableOn_unip {φ : GA E a → ℂ} (hφ : Continuous φ) (r : ℕ) (g : GA E a) :
    IntegrableOn (fun x => φ (unip x * g)) (AutomorphicForm.unipFundamentalDomain E a r)
      (AutomorphicForm.unipMeasure E a r) := by
  have e : (fun x : BlockIx a r → Ad E => φ (unip x * g)) = fun X => φ (AutomorphicForm.unipGL X * g) :=
    funext fun x => by rw [unip_eq_unipGL]
  rw [e]
  exact AutomorphicForm.integrableOn_constantTerm hφ g

def ctMap (L : Subgroup (GL (Fin a) (Af E))) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Kinf E a) W) (J : Set (Module.End ℂ (Sm E a))) (r : ℕ) :
    genSub L ρ J →ₗ[ℂ] (GA E a → ℂ) where
  toFun ψ g := ∫ x in AutomorphicForm.unipFundamentalDomain E a r, ψ.1.1 (unip x * g)
    ∂AutomorphicForm.unipMeasure E a r
  map_add' ψ ψ' := funext fun g =>
    integral_add (integrableOn_unip (continuous_of_level ψ.2.1.level) r g)
      (integrableOn_unip (continuous_of_level ψ'.2.1.level) r g)
  map_smul' c ψ := funext fun g => integral_smul c _

theorem genFin_step (hC : CuspFin E a) (hT : ∀ r, 0 < r → r < a → CTFin E a r) : GenFin E a := by
  intro L hL W _ _ _ ρ hρ J hJ
  let R := {r : ℕ // 0 < r ∧ r < a}
  have : Finite R := Finite.of_injective (fun r : R => (⟨r.1, r.2.2⟩ : Fin a))
    fun x y h => Subtype.ext (congrArg (fun z : Fin a => z.1) h)
  have ct := fun r : R => hT r.1 r.2.1 r.2.2 L hL W ρ hρ J hJ
  choose V hVf hV using ct
  have : ∀ r, FiniteDimensional ℂ (V r) := hVf
  have hm : ∀ (r : R) (ψ : genSub L ρ J), ctMap L ρ J r.1 ψ ∈ V r := fun r ψ =>
    hV r ψ.1 ψ.2 (AutomorphicForm.unipMeasure E a r.1) (AutomorphicForm.unipFundamentalDomain E a r.1)
      inferInstance AutomorphicForm.isAddFundamentalDomain_unipFundamentalDomain
  let Φ : genSub L ρ J →ₗ[ℂ] (∀ r : R, V r) :=
    LinearMap.pi fun r => (ctMap L ρ J r.1).codRestrict (V r) (hm r)
  have hker : FiniteDimensional ℂ (LinearMap.ker Φ) := by
    have hC' := hC L hL W ρ hρ J hJ
    have hle : (LinearMap.ker Φ).map (genSub L ρ J).subtype ≤
        Submodule.span ℂ {φ | φ ∈ genSpace L ρ J ∧ IsCuspidal φ.1} := by
      rintro _ ⟨ψ, hψ, rfl⟩
      refine Submodule.subset_span ⟨ψ.2, isCuspidal_of_constantTerm ψ.2.1.left fun r h0 h1 g => ?_⟩
      exact congrFun (congrArg Subtype.val (congrFun (LinearMap.mem_ker.1 hψ) ⟨r, h0, h1⟩)) g
    have : FiniteDimensional ℂ ((LinearMap.ker Φ).map (genSub L ρ J).subtype) :=
      Submodule.finiteDimensional_of_le hle
    exact Module.Finite.equiv
      (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) (LinearMap.ker Φ)).symm
  have hfin : FiniteDimensional ℂ (genSub L ρ J) := by
    have : Module.Finite ℂ (genSub L ρ J ⧸ LinearMap.ker Φ) := Module.Finite.equiv Φ.quotKerEquivRange.symm
    exact Module.Finite.of_submodule_quotient (LinearMap.ker Φ)
  rw [show Submodule.span ℂ (genSpace L ρ J) = genSub L ρ J from Submodule.span_eq (genSub L ρ J)]
  exact hfin

theorem genFin_of_chapters :
    (∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), CuspFin E a) →
    (∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), (∀ b < a, GenFin E b) →
      ∀ r, 0 < r → r < a → CTFin E a r) →
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), GenFin E a := by
  intro hC hT E _ _ _ a
  induction a using Nat.strong_induction_on with
  | _ a ih => exact genFin_step (hC E a) (hT E a ih)

end GlobalTheory.CompanionTheory.AffglAssembly

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralFiberDecompositionInvariantStatement
section
open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_fiber_decomposition_invariant : ∀ {H X : Type} [MeasurableSpace H] [MeasurableSpace X] (ν : Measure H) [SFinite ν]
  (act : H → X → X), Measurable (fun p : H × X => act p.1 p.2) →
  ∀ (r : H → H → H), (∀ h₀, MeasurePreserving (r h₀) ν ν) →
  (∀ h₀ h x, act (r h₀ h) x = act h (act h₀ x)) →
  ∀ (D Z : ℕ → Set X), (∀ i, MeasurableSet (D i)) → (∀ i, MeasurableSet (Z i)) →
  (∀ i h x, act h x ∈ Z i ↔ x ∈ Z i) → (∀ x, ∃ i, x ∈ Z i) →
  (∀ i x, ν {h | act h x ∈ D i} ≠ ⊤) → (∀ i x, x ∈ Z i → ν {h | act h x ∈ D i} ≠ 0) →
  ∀ S : Set (X → X), (∀ s ∈ S, ∀ i x, s x ∈ D i ↔ x ∈ D i) → (∀ s ∈ S, ∀ i x, s x ∈ Z i ↔ x ∈ Z i) →
  (∀ s ∈ S, ∀ h, ∃ s' ∈ S, ∀ x, act h (s x) = s' (act h x)) →
  ∃ ρ : X → ℝ≥0∞, Measurable ρ ∧ (∀ x, ∫⁻ h, ρ (act h x) ∂ν = 1) ∧ ∀ s ∈ S, ∀ x, ρ (s x) = ρ x := by
  first | exact @GlobalTheory.CompanionTheory.LocVan.NormaliserAbs.exists_normaliser | exact GlobalTheory.CompanionTheory.LocVan.NormaliserAbs.exists_normaliser | (intros; apply GlobalTheory.CompanionTheory.LocVan.NormaliserAbs.exists_normaliser <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralUnfoldWeightedAverageStatement
section
open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_unfold_weighted_average : ∀ {G H : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ] [MeasurableSpace H] (ν : Measure H) [SFinite ν]
  (u : H → G), Measurable u → ∀ (w ρ : G → ℝ≥0∞) (F : G → ℂ), Measurable w → Measurable ρ → Measurable F →
  (∀ g, ∫⁻ h, w ((u h)⁻¹ * g) ∂ν = 1) → (∀ h g, ρ (u h * g) = ρ g) →
  (∀ q, ∫ h, F (u h * q) ∂ν = 0) → ∫ g, F g * ((ρ g).toReal : ℂ) ∂μ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.LocVan.integral_eq_zero_of_unfolding | exact GlobalTheory.CompanionTheory.LocVan.integral_eq_zero_of_unfolding | (intros; apply GlobalTheory.CompanionTheory.LocVan.integral_eq_zero_of_unfolding <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactParahoricSubgroup
section
open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology

namespace GlobalTheory.CompanionTheory.MoyPrasad

theorem isCompact_Gx : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), IsCompact (Gx k e : Set (GL (Fin n) k)) := by
  intro k _ _ _ _ n s d e
  have hle : PositivityTheory.LowerBoundConstant.Gx k e ≤ GlobalTheory.SplitWeil.KO k (Fin n) := by
    unfold PositivityTheory.LowerBoundConstant.Gx
    exact sup_le GlobalTheory.StepData.KOne_le_KO inf_le_right
  have hopen : IsOpen (PositivityTheory.LowerBoundConstant.Gx k e : Set (GL (Fin n) k)) := by
    unfold PositivityTheory.LowerBoundConstant.Gx
    exact Subgroup.isOpen_mono le_sup_left GlobalTheory.StepData.isOpen_KOne
  exact GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset
    (Subgroup.isClosed_of_isOpen _ hopen) (fun x hx => hle hx)

end GlobalTheory.CompanionTheory.MoyPrasad
end

