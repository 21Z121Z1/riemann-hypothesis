import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0042
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0483
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0477
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0460
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0814
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0470
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0481
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0463
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0821
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0831
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0037
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0426
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0034
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0843
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0845
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0835
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0844
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSeriesVanishesLargeModule

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothRightInv
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

open Topology GlobalTheory.SplitWeil

theorem fibInt_translate : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) [MeasurableSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) (f : cIndSpace (HPG k i t) (hRep τ σ)) (x g : GL (Fin (i + t)) k), fibInt μ (prodPG τ σ (levi k (i + t) x) f) g = fibInt μ f (g * x) := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ _ μ f x g
  have h : fibV (prodPG τ σ (levi k (i + t) x) f) g = fibV f (g * x) := funext fun v =>
    congrArg f.1.1.1 (show uM k (i + t) (midV k i t v) * levi k (i + t) g * levi k (i + t) x =
      uM k (i + t) (midV k i t v) * levi k (i + t) (g * x) by rw [map_mul, mul_assoc])
  exact congrArg (fun φ => clT τ W (smInt μ φ)) h

theorem fibInt_linear : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure] (g : GL (Fin (i + t)) k), (∀ f₁ f₂ : cIndSpace (HPG k i t) (hRep τ σ), fibInt μ (f₁ + f₂) g = fibInt μ f₁ g + fibInt μ f₂ g) ∧ ∀ (a : ℂ) (f : cIndSpace (HPG k i t) (hRep τ σ)), fibInt μ (a • f) g = a • fibInt μ f g := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ hτ hσ _ _ μ _ g
  have hr := fun f => GlobalTheory.T.fibre_function_locally_constant_compact k i t τ σ hτ hσ f g
  have hp := SmIntEl.smInt_properties (W := V ⊗[ℂ] W) (W' := V ⊗[ℂ] W) μ
  refine ⟨fun f₁ f₂ => ?_, fun a f => ?_⟩
  · have h : smInt μ (fibV (f₁ + f₂) g) = smInt μ (fibV f₁ g) + smInt μ (fibV f₂ g) :=
      hp.1 (fibV f₁ g) (fibV f₂ g) (hr f₁).1 (hr f₁).2 (hr f₂).1 (hr f₂).2
    exact (congrArg (clT τ W) h).trans (map_add _ _ _)
  · have e : fibV (a • f) g = (a • (LinearMap.id : (V ⊗[ℂ] W) →ₗ[ℂ] (V ⊗[ℂ] W))) ∘ fibV f g :=
      funext fun v => map_smul (evL (τ := τ) (σ := σ) (uM k (i + t) (midV k i t v) * levi k (i + t) g)) a f
    have h1 := hp.2.1 (a • (LinearMap.id : (V ⊗[ℂ] W) →ₗ[ℂ] (V ⊗[ℂ] W))) (fibV f g) (hr f).1 (hr f).2
    have h : smInt μ (fibV (a • f) g) = a • smInt μ (fibV f g) := (congrArg (smInt μ) e).trans h1
    exact (congrArg (clT τ W) h).trans (map_smul _ _ _)

theorem exists_nhds_prod {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (F : X → Y → Z) (hF : Continuous fun p : X × Y => F p.1 p.2) (x : X) (y : Y) {U : Set Z} (hU : U ∈ 𝓝 (F x y)) :
    ∃ A ∈ 𝓝 x, ∃ B ∈ 𝓝 y, ∀ a ∈ A, ∀ b ∈ B, F a b ∈ U := by
  have h : (fun p : X × Y => F p.1 p.2) ⁻¹' U ∈ 𝓝 (x, y) := hF.continuousAt.preimage_mem_nhds hU
  rw [nhds_prod_eq, Filter.mem_prod_iff] at h
  obtain ⟨A, hA, B, hB, hsub⟩ := h
  exact ⟨A, hA, B, hB, fun a ha b hb => hsub (Set.mk_mem_prod ha hb)⟩

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_latt_nhds {n : ℕ} {U : Set (Mir k n)} (hU : U ∈ 𝓝 (1 : Mir k n)) :
    ∃ c : kˣ, ∃ A ∈ 𝓝 (1 : GL (Fin n) k), ∀ y ∈ latt n c, ∀ b ∈ A, uM k n y * levi k n b ∈ U := by
  have hc := GlobalTheory.T.continuous_levi_unipotent_proj k n
  have hcont : Continuous fun p : (Fin n → k) × GL (Fin n) k => uM k n p.1 * levi k n p.2 :=
    (hc.2.1.comp continuous_fst).mul (hc.1.comp continuous_snd)
  have h00 : uM k n 0 * levi k n 1 = 1 := by rw [uM_zero, map_one, one_mul]
  obtain ⟨A, hA, B, hB, h⟩ := exists_nhds_prod (fun y b => uM k n y * levi k n b) hcont 0 1
    (by rw [h00]; exact hU)
  obtain ⟨c, hcA⟩ := exists_latt_subset hA
  exact ⟨c, B, hB, fun y hy b hb => h y (hcA hy) b hb⟩

theorem exists_level {n : ℕ} {Z : Type} (Zs : Set Z) (hZ : Zs.Finite) (U : Z → Set (Mir k n))
    (hU : ∀ z, U z ∈ 𝓝 (1 : Mir k n)) {A' : Set (GL (Fin n) k)} (hA' : A' ∈ 𝓝 (1 : GL (Fin n) k)) :
    ∃ (c : kˣ) (K₁ : Subgroup (GL (Fin n) k)) (hK : K₁ ≤ KO k (Fin n)), IsOpen (K₁ : Set (GL (Fin n) k)) ∧
      (K₁ : Set (GL (Fin n) k)) ⊆ A' ∧ K₁.relIndex (KO k (Fin n)) ≠ 0 ∧
      (∀ κ ∈ KO k (Fin n), ∀ b ∈ K₁, κ * b * κ⁻¹ ∈ K₁) ∧ ∀ z ∈ Zs, ∀ p ∈ Bgrp n c K₁ hK, p ∈ U z := by
  have hI : (⋂ z ∈ Zs, U z) ∈ 𝓝 (1 : Mir k n) := (Filter.biInter_mem hZ).2 fun z _ => hU z
  obtain ⟨c, A, hA, hcA⟩ := exists_latt_nhds hI
  obtain ⟨K₁, hK, hopen, hsub, hidx, hnorm⟩ := GlobalTheory.T.exists_normal_open_subgroup_compact k n _ (Filter.inter_mem hA hA')
  refine ⟨c, K₁, hK, hopen, fun x hx => (hsub hx).2, hidx, hnorm, ?_⟩
  rintro z hz _ ⟨y, hy, b, hb, rfl⟩
  exact Set.mem_iInter₂.1 (hcA y hy b (hsub hb).1) z hz

variable {i t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def fibLin (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (hτ : IsSmooth τ) (hσ : IsSmooth σ)
    [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k))
    [μ.IsAddHaarMeasure] :
    cIndSpace (HPG k i t) (hRep τ σ) →ₗ[ℂ] (GL (Fin (i + t)) k → Jacquet τ (MirUin k i) ⊗[ℂ] W) where
  toFun f := fun g => fibInt μ f g
  map_add' f₁ f₂ := funext fun g => (fibInt_linear k i t τ σ hτ hσ μ g).1 f₁ f₂
  map_smul' a f := funext fun g => (fibInt_linear k i t τ σ hτ hσ μ g).2 a f

theorem clT_surjective (τ : Representation ℂ (Mir k i) V) (W : Type) [AddCommGroup W] [Module ℂ W] :
    Function.Surjective (clT τ W) :=
  LinearMap.rTensor_surjective W (Submodule.mkQ_surjective _)

theorem exists_bump_fib (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (hτ : IsSmooth τ) (hσ : IsSmooth σ)
    [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k))
    [μ.IsAddHaarMeasure] (c : kˣ) (K₁ : Subgroup (GL (Fin (i + t)) k)) (hK : K₁ ≤ KO k (Fin (i + t)))
    (hopen : IsOpen (K₁ : Set (GL (Fin (i + t)) k))) (z : V ⊗[ℂ] W)
    (hz : ∀ h : HPG k i t, (h : Mir k (i + t)) ∈ Bgrp (i + t) c K₁ hK → hRep τ σ h z = z) :
    ∃ b : cIndSpace (HPG k i t) (hRep τ σ),
      (∀ (q : Qp k i t), ∀ b' ∈ K₁, fibInt μ b ((q : GL (Fin (i + t)) k) * b') =
        (((μ (latt t c : Set (Fin t → k))).toReal : ℝ) : ℂ) • qRep τ σ q (clT τ W z)) ∧
      ∀ g : GL (Fin (i + t)) k, (¬ ∃ q : Qp k i t, ∃ b' ∈ K₁, g = (q : GL (Fin (i + t)) k) * b') → fibInt μ b g = 0 := by
  have hBo := GlobalTheory.T.fibre_subgroup_open_compact k (i + t) c K₁ hK hopen
  obtain ⟨b, hb1, hb2⟩ := GlobalTheory.T.exists_induced_section_supported_open (HPG k i t) (hRep τ σ) (Bgrp (i + t) c K₁ hK) hBo.1 hBo.2 z hz
  have hone : fibInt μ b 1 = (((μ (latt t c : Set (Fin t → k))).toReal : ℝ) : ℂ) • clT τ W z := by
    have h1 := GlobalTheory.T.fibre_integral_vanishing_subgroup k i t τ σ c K₁ hK z b hb1 hb2
    have h2 := (SmIntEl.smInt_properties (W := V ⊗[ℂ] W) (W' := V ⊗[ℂ] W) μ).2.2.2 _ z (isCompact_latt t c)
      (isOpen_latt t c) (isClosed_latt t c)
    exact (congrArg (fun φ => clT τ W (smInt μ φ)) h1).trans ((congrArg (clT τ W) h2).trans (map_smul _ _ _))
  refine ⟨b, fun q b' hb' => ?_, GlobalTheory.T.fibre_integral_support_subgroup k i t τ σ μ c K₁ hK b hb2⟩
  have e1 : fibInt μ b b' = fibInt μ b 1 := by
    have h := GlobalTheory.T.fibre_integral_vanishing_open_subgroup k i t τ σ c K₁ hK z b hb1 hb2 b' hb' 1
    have h' : fibV b b' = fibV b 1 := (congrArg (fibV b) (one_mul b').symm).trans h
    exact congrArg (fun φ => clT τ W (smInt μ φ)) h'
  exact (GlobalTheory.T.fibre_integral_intertwines_unipotent k i t τ σ hτ hσ μ b q b').trans
    ((congrArg (qRep τ σ q) (e1.trans hone)).trans (map_smul _ _ _))

end

end GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

open Topology GlobalTheory.SplitWeil

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {i t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem smooth_right_inv {Γ J : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [AddCommGroup J] [Module ℂ J]
    (H : Subgroup Γ) (π : Representation ℂ H J) (G : smoothPart (ind H π)) :
    {s : Γ | ∀ x, G.1.1 (x * s) = G.1.1 x} ∈ 𝓝 (1 : Γ) := by
  have h1 : {s : Γ | ind H π s G.1 = G.1} ∈ 𝓝 (1 : Γ) := IsOpen.mem_nhds G.2 (by simp)
  exact Filter.mem_of_superset h1 fun s hs x => congrFun (congrArg Subtype.val hs) x

theorem exists_fib_mem (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (hτ : IsSmooth τ) (hσ : IsSmooth σ)
    [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k))
    [μ.IsAddHaarMeasure] (c : kˣ) (K₁ : Subgroup (GL (Fin (i + t)) k)) (hK : K₁ ≤ KO k (Fin (i + t)))
    (hopen : IsOpen (K₁ : Set (GL (Fin (i + t)) k))) (z : V ⊗[ℂ] W) (a : Jacquet τ (MirUin k i) ⊗[ℂ] W)
    (ha : clT τ W z = a)
    (hz : ∀ h : HPG k i t, (h : Mir k (i + t)) ∈ Bgrp (i + t) c K₁ hK → hRep τ σ h z = z) :
    ∃ φ ∈ LinearMap.range (fibLin τ σ hτ hσ μ),
      (∀ (q : Qp k i t), ∀ b' ∈ K₁, φ ((q : GL (Fin (i + t)) k) * b') = qRep τ σ q a) ∧
      ∀ g : GL (Fin (i + t)) k, (¬ ∃ q : Qp k i t, ∃ b' ∈ K₁, g = (q : GL (Fin (i + t)) k) * b') → φ g = 0 := by
  subst ha
  have hcc0 : (((μ (latt t c : Set (Fin t → k))).toReal : ℝ) : ℂ) ≠ 0 := by
    have h1 : 0 < μ (latt t c : Set (Fin t → k)) := (isOpen_latt t c).measure_pos μ ⟨0, zero_mem _⟩
    have h2 : μ (latt t c : Set (Fin t → k)) ≠ ⊤ := (isCompact_latt t c).measure_lt_top.ne
    exact_mod_cast (ENNReal.toReal_pos h1.ne' h2).ne'
  refine Exists.elim (exists_bump_fib τ σ hτ hσ μ c K₁ hK hopen z hz) fun b hb => ?_
  refine ⟨(((μ (latt t c : Set (Fin t → k))).toReal : ℝ) : ℂ)⁻¹ • (fibLin τ σ hτ hσ μ b),
    Submodule.smul_mem _ _ ⟨b, rfl⟩, fun q b' hb' => ?_, fun g hg => ?_⟩
  · exact (congrArg (fun a => (((μ (latt t c : Set (Fin t → k))).toReal : ℝ) : ℂ)⁻¹ • a) (hb.1 q b' hb')).trans
      (inv_smul_smul₀ hcc0 _)
  · exact (congrArg (fun a => (((μ (latt t c : Set (Fin t → k))).toReal : ℝ) : ℂ)⁻¹ • a) (hb.2 g hg)).trans (smul_zero _)

theorem mem_range_fibLin (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (hτ : IsSmooth τ) (hσ : IsSmooth σ)
    [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k))
    [μ.IsAddHaarMeasure] (Gf : GL (Fin (i + t)) k → Jacquet τ (MirUin k i) ⊗[ℂ] W)
    (hlaw : ∀ (q : Qp k i t) (g : GL (Fin (i + t)) k), Gf ((q : GL (Fin (i + t)) k) * g) = qRep τ σ q (Gf g))
    (hinv : {s : GL (Fin (i + t)) k | ∀ x, Gf (x * s) = Gf x} ∈ 𝓝 (1 : GL (Fin (i + t)) k)) :
    Gf ∈ LinearMap.range (fibLin τ σ hτ hσ μ) := by
  have hfin : (Gf '' (KO k (Fin (i + t)) : Set (GL (Fin (i + t)) k))).Finite :=
    GlobalTheory.T.finite_image_compact_right_invariant _ GlobalTheory.SplitFlip.isCompact_KO Gf hinv
  obtain ⟨pre, hpre⟩ : ∃ pre : Jacquet τ (MirUin k i) ⊗[ℂ] W → V ⊗[ℂ] W, ∀ a, clT τ W (pre a) = a :=
    ⟨Function.surjInv (clT_surjective τ W), Function.surjInv_eq _⟩
  choose Ust hUst hUfix using GlobalTheory.T.smooth_tensor_fixed_parabolic_near_one k i t τ σ hτ hσ
  obtain ⟨c, K₁, hK, hopen, hsub, hidx, hnorm, hlev⟩ := exists_level _ (hfin.image pre) Ust hUst hinv
  have hfix : ∀ κ ∈ KO k (Fin (i + t)), ∀ h : HPG k i t,
      (h : Mir k (i + t)) ∈ Bgrp (i + t) c K₁ hK → hRep τ σ h (pre (Gf κ)) = pre (Gf κ) :=
    fun κ hκ h hh => hUfix _ h (hlev _ ⟨_, ⟨κ, hκ, rfl⟩, rfl⟩ _ hh)
  refine GlobalTheory.T.induced_generated_by_K_finite (Qp k i t) (KO k (Fin (i + t))) K₁ (qRep τ σ) (LinearMap.range (fibLin τ σ hτ hσ μ)) Gf hK hidx hnorm
    (fun g => ?_) ?_ ?_ hlaw (fun g b hb => hsub hb g) ?_
  · obtain ⟨q, κ, hκ, e⟩ := GlobalTheory.T.iwasawa_decomp_parabolic_maximal_compact k i t g
    exact ⟨q, κ, hκ, e⟩
  · rintro _ ⟨f, rfl⟩ x
    exact ⟨prodPG τ σ (levi k (i + t) x) f, funext fun g => fibInt_translate k i t τ σ μ f x g⟩
  · rintro _ ⟨f, rfl⟩ q g
    exact GlobalTheory.T.fibre_integral_intertwines_unipotent k i t τ σ hτ hσ μ f q g
  · intro κ hκ
    exact exists_fib_mem τ σ hτ hσ μ c K₁ hK hopen (pre (Gf κ)) (Gf κ) (hpre _) (hfix κ hκ)

end

end GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

namespace GlobalTheory.CompanionTheory.BZPsiPG

open Topology GlobalTheory.SplitWeil FibOnto

theorem exists_fibInt_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure], ∀ G : smoothPart (ind (Qp k i t) (qRep τ σ)), ∃ f : cIndSpace (HPG k i t) (hRep τ σ), ∀ g, fibInt μ f g = G.1.1 g := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ hτ hσ _ _ μ _ G
  have hM := mem_range_fibLin τ σ hτ hσ μ G.1.1 G.1.2 (smooth_right_inv _ _ G)
  exact ⟨Classical.choose hM, fun g => congrFun (Classical.choose_spec hM) g⟩

end GlobalTheory.CompanionTheory.BZPsiPG

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSeriesUniformBoundCompact
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.BasePsi

theorem pure_rv_zero_le {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (G : Ainf F → ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ)
    (hGc : Continuous G) (hGs : HasCompactSupport G)
    (hg : ∀ v ∈ S, Continuous (g v) ∧ HasCompactSupport (g v)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a : (AF F)ˣ, PositivityTheory.Rg.Base1.pure S G g (fun v => rv v 0) a ≤ ENNReal.ofReal M := by
  obtain ⟨MG, hMG⟩ := hGc.bounded_above_of_compact_support hGs
  have hB : ∀ v : HeightOneSpectrum (𝓞 F), ∃ B : ℝ, 0 ≤ B ∧ (v ∈ S → ∀ x, |g v x| ≤ B) := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨B, hB⟩ := (hg v hv).1.bounded_above_of_compact_support (hg v hv).2
      exact ⟨|B|, abs_nonneg _, fun _ x => (hB x).trans (le_abs_self B)⟩
    · exact ⟨0, le_rfl, fun h => absurd h hv⟩
  choose B hB0 hB using hB
  refine ⟨|MG| * ∏ v ∈ S, B v, mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun v _ => hB0 v), fun a => ?_⟩
  rw [GlobalTheory.T.pure_adelic_function_formula]
  split_ifs with h
  · refine ENNReal.ofReal_le_ofReal ?_
    refine (le_abs_self _).trans ?_
    rw [abs_mul, Finset.abs_prod]
    refine mul_le_mul ((hMG _).trans (le_abs_self MG)) ?_
      (Finset.prod_nonneg fun v _ => abs_nonneg _) (abs_nonneg _)
    exact Finset.prod_le_prod (fun v _ => abs_nonneg _) fun v hv => hB v hv _
  · simp

theorem th_pure_rv_zero_bound : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ r : ℝ → (AF F)ˣ, IsRay θ r →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ),
    Continuous G → HasCompactSupport G → (∀ v ∈ S, Continuous (g v) ∧ HasCompactSupport (g v)) →
    ∀ D : Set (AF F)ˣ, IsCompact D → ∃ C : ℝ≥0, ∀ u ∈ D, ∀ δ : ℝ, 0 < δ →
      ENNReal.ofReal (δ ^ Module.finrank ℚ F) * th (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) (u * r δ) ≤ C := by
  intro F _ _ hF θ hθ r hr S G g hGc hGs hg D hD
  obtain ⟨M, hM0, hM⟩ := pure_rv_zero_le S G g hGc hGs hg
  obtain ⟨N, hN, hden⟩ := GlobalTheory.T.bounded_denominators_compact_idele_set F D hD S (fun v => tsupport (g v)) (fun v hv => (hg v hv).2)
  let K : Set (Ainf F) :=
    (fun p : (AF F)ˣ × Ainf F => (((p.1⁻¹ : (AF F)ˣ) : AF F).1) * p.2) '' (D ×ˢ tsupport G)
  have hK : IsCompact K := by
    refine (hD.prod hGs).image ?_
    have c1 : Continuous fun a : AF F => a.1 := continuous_fst
    have c2 : Continuous fun p : (AF F)ˣ × Ainf F => ((p.1⁻¹ : (AF F)ˣ) : AF F) :=
      Units.continuous_val.comp (continuous_inv.comp continuous_fst)
    exact (c1.comp c2).mul continuous_snd
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.CompanionTheory.MassCount.countBd F hF θ hθ K hK N hN
  refine ⟨(max C₀ 0 * M).toNNReal, fun u hu δ hδ => ?_⟩
  obtain ⟨hfin, hle⟩ := hC₀ δ hδ ⊤ top_ne_bot
  set T : Set F := {x : F | x ≠ 0 ∧ (∃ y ∈ (⊤ : Ideal (𝓞 F)), (y : F) = N * x) ∧ θ δ * algebraMap F (Ainf F) x ∈ K} with hT
  have hsupp : ∀ t : Fˣ, PositivityTheory.Rg.Base1.pure S G g (fun v => rv v 0) (pr t * (u * r δ)) ≠ 0 → (t : F) ∈ T := by
    intro t ht
    obtain ⟨hr1, hr2⟩ := hr δ hδ
    rw [GlobalTheory.T.pure_adelic_function_formula] at ht
    have h1 : ∀ v, ((pr t * (u * r δ) : (AF F)ˣ) : AF F).2 v = algebraMap F (Fv F v) (t : F) * (u : AF F).2 v := by
      intro v
      have : ((pr t * (u * r δ) : (AF F)ˣ) : AF F).2 v
          = algebraMap F (Fv F v) (t : F) * ((u : AF F).2 v * (r δ : AF F).2 v) := rfl
      rw [this, hr2]
      simp
    have h0 : ((pr t * (u * r δ) : (AF F)ˣ) : AF F).1 = algebraMap F (Ainf F) (t : F) * ((u : AF F).1 * θ δ) := by
      have : ((pr t * (u * r δ) : (AF F)ˣ) : AF F).1
          = algebraMap F (Ainf F) (t : F) * ((u : AF F).1 * (r δ : AF F).1) := rfl
      rw [this, hr1]
    by_cases hint : ∀ v, v ∉ S → ((pr t * (u * r δ) : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F
    swap
    · exact absurd (if_neg hint) ht
    rw [if_pos hint] at ht
    have hne : G ((pr t * (u * r δ) : (AF F)ˣ) : AF F).1 * ∏ v ∈ S, g v (((pr t * (u * r δ) : (AF F)ˣ) : AF F).2 v) ≠ 0 := by
      intro h
      exact ht (by rw [h]; simp)
    have hG0 := left_ne_zero_of_mul hne
    have hp0 := right_ne_zero_of_mul hne
    have hgS : ∀ v ∈ S, algebraMap F (Fv F v) (t : F) * (u : AF F).2 v ∈ tsupport (g v) := by
      intro v hv
      rw [← h1 v]
      exact subset_tsupport _ (Finset.prod_ne_zero_iff.1 hp0 v hv)
    obtain ⟨y, hy⟩ := hden u hu (t : F) hgS (fun v hv => by rw [← h1 v]; exact hint v hv)
    refine ⟨t.ne_zero, ⟨y, Submodule.mem_top, hy⟩, ?_⟩
    refine ⟨(u, ((pr t * (u * r δ) : (AF F)ˣ) : AF F).1), ⟨hu, subset_tsupport _ hG0⟩, ?_⟩
    have hinv : (((u⁻¹ : (AF F)ˣ) : AF F).1) * (u : AF F).1 = 1 := by
      exact congrArg (fun w : (AF F)ˣ => (w : AF F).1) (inv_mul_cancel u)
    show (((u⁻¹ : (AF F)ˣ) : AF F).1) * ((pr t * (u * r δ) : (AF F)ˣ) : AF F).1 = _
    rw [h0]
    calc _ = ((((u⁻¹ : (AF F)ˣ) : AF F).1) * (u : AF F).1) * (θ δ * algebraMap F (Ainf F) (t : F)) := by ring
      _ = _ := by rw [hinv, one_mul]
  have hfin' : {t : Fˣ | (t : F) ∈ T}.Finite :=
    hfin.preimage (Units.val_injective.injOn)
  have hth : th (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) (u * r δ) ≤ (hfin'.toFinset.card : ℝ≥0∞) * ENNReal.ofReal M := by
    unfold th
    rw [tsum_eq_sum (s := hfin'.toFinset) (fun t ht => by
      by_contra h
      exact ht (hfin'.mem_toFinset.2 (hsupp t h)))]
    calc _ ≤ ∑ t ∈ hfin'.toFinset, ENNReal.ofReal M := Finset.sum_le_sum fun t _ => hM _
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (hfin'.toFinset.card : ℝ) ≤ (T.ncard : ℝ) := by
    have h1 : hfin'.toFinset.card = {t : Fˣ | (t : F) ∈ T}.ncard := (Set.ncard_eq_toFinset_card _ hfin').symm
    rw [h1]
    exact_mod_cast Set.ncard_le_ncard_of_injOn (fun t : Fˣ => (t : F)) (fun t ht => ht) Units.val_injective.injOn hfin
  have hle' : δ ^ Module.finrank ℚ F * (T.ncard : ℝ) ≤ max C₀ 0 := by
    refine hle.trans ?_
    simp
  have hd0 : (0 : ℝ) ≤ δ ^ Module.finrank ℚ F := by positivity
  calc ENNReal.ofReal (δ ^ Module.finrank ℚ F) * th (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) (u * r δ)
      ≤ ENNReal.ofReal (δ ^ Module.finrank ℚ F) * ((hfin'.toFinset.card : ℝ≥0∞) * ENNReal.ofReal M) := by gcongr
    _ = ENNReal.ofReal (δ ^ Module.finrank ℚ F * (hfin'.toFinset.card : ℝ) * M) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hd0, ENNReal.ofReal_natCast, mul_assoc]
    _ ≤ ENNReal.ofReal (max C₀ 0 * M) := by
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ hM0)
        exact (mul_le_mul_of_nonneg_left hcard hd0).trans hle'
    _ = _ := by rw [ENNReal.ofReal]

end GlobalTheory.CompanionTheory.BasePsi

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSeriesVanishesLargeModuleStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_series_vanishes_large_module : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ), HasCompactSupport G → (∀ v ∈ S, HasCompactSupport (g v)) →
    ∃ R : ℝ, ∀ a : (AF F)ˣ, R < md a → th (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) a = 0 := by
  first | exact @GlobalTheory.CompanionTheory.BasePsi.th_pure_vanish | exact GlobalTheory.CompanionTheory.BasePsi.th_pure_vanish | (intros; apply GlobalTheory.CompanionTheory.BasePsi.th_pure_vanish <;> assumption)
end

