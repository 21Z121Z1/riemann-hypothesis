import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0203
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0178
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothCompactSupportFixLowestKType
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0159
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0205
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0204
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteClassSetHermitianUnitaryOpenLevel
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RedivisionStructureEq
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Formalism.LocalToGlobal.NumberFieldFamilies.OwnStruct
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarMeasureGramGL2ActionTensor

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeLeSmoothVectors
section
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff Topology InnerProductSpace

namespace GlobalTheory.SmoothLowType

open Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.GardingVec

section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem exists_bump (n : ℕ) (ε : Fin n → Bool) (U : Set (UJ ε)) (hU : U ∈ nhds (1 : UJ ε)) :
    ∃ a : Matrix (Fin n) (Fin n) ℂ → ℝ,
      (∀ (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] (f : P → Matrix (Fin n) (Fin n) ℂ),
        (∀ i j, ContDiff ℝ ∞ fun p => f p i j) → ContDiff ℝ ∞ fun p => a (f p)) ∧ (∀ y, 0 ≤ a y) ∧ a 1 ≠ 0 ∧
      HasCompactSupport (fun g : UJ ε => a (umat g)) ∧ (∀ g : UJ ε, a (umat g) ≠ 0 → g ∈ U) ∧
      ∀ k ∈ Kset ε, ∀ y, a (k * y) = a (y * k) := by
  obtain ⟨a, ha, h⟩ := GlobalTheory.exists_conjInvariant_bump n ε U hU
  refine ⟨a, fun P _ _ f hf => ha.comp ?_, h⟩
  exact contDiff_pi.2 fun i => contDiff_pi.2 fun j => hf i j
end

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem contDiff_entry {n : ℕ} (i j : Fin n) : ContDiff ℝ ∞ fun x : Matrix (Fin n) (Fin n) ℂ => x i j := by
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun x => x i j
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  exact (LinearMap.toContinuousLinearMap L).contDiff

theorem garding_smooth {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {φ : Matrix (Fin n) (Fin n) ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hψc : HasCompactSupport fun g : UJ ε => φ (umat g)) (w : H)
    (k : ℕ) (x : (Fin k → ℝ) → Matrix (Fin n) (Fin n) ℂ) (hx : ContDiff ℝ ∞ x) (hxG : ∀ t, x t ∈ UJset ε) :
    ContDiff ℝ ∞ fun t => σ (x t) (∫ g : UJ ε, φ (umat g) • σ (umat g) w ∂(muG ε)) := by
  obtain ⟨⟨h1, hmul⟩, -, hcont⟩ := hσ
  obtain ⟨hemb, hrange⟩ := Formalism.REAL.isClosedEmbeddingMatrix n ε
  set μ := Formalism.REAL.muG ε
  have hmem : ∀ g : Formalism.REAL.UJ ε, umat g ∈ UJset ε := fun g => g.2
  have hu : Continuous fun g : Formalism.REAL.UJ ε => umat g := hemb.continuous
  have hb : Continuous fun g : Formalism.REAL.UJ ε => σ (umat g) w := (hcont w).comp_continuous hu hmem
  have hψ : Continuous fun g : Formalism.REAL.UJ ε => φ (umat g) := hφ.continuous.comp hu
  have hint : Integrable (fun g : Formalism.REAL.UJ ε => φ (umat g) • σ (umat g) w) μ :=
    (hψ.smul hb).integrable_of_hasCompactSupport hψc.smul_right
  let y : (Fin k → ℝ) → Matrix (Fin n) (Fin n) ℂ := fun t => Formalism.REAL.Jm ε * (x t)ᴴ * Formalism.REAL.Jm ε
  have hy : ContDiff ℝ ∞ y := (contDiff_const.mul (contDiff_conjTranspose.comp hx)).mul contDiff_const
  have hyx : ∀ t, y t * x t = 1 := fun t => by
    have h : (x t)ᴴ * Formalism.REAL.Jm ε * x t = Formalism.REAL.Jm ε := hxG t
    calc y t * x t = Formalism.REAL.Jm ε * ((x t)ᴴ * Formalism.REAL.Jm ε * x t) := by simp only [y, Matrix.mul_assoc]
      _ = 1 := by rw [h, Formalism.REAL.Jm_mul_self]
  have hxy : ∀ t, x t * y t = 1 := fun t => mul_eq_one_comm.1 (hyx t)
  have hz : ∀ t, ∃ z : UJ ε, umat z = x t := fun t => by
    have : x t ∈ Set.range (fun g : Formalism.REAL.UJ ε => umat g) := by
      rw [show Set.range (fun g : Formalism.REAL.UJ ε => umat g) = _ from hrange]; exact hxG t
    exact this
  have hform : ∀ t, σ (x t) (∫ g : Formalism.REAL.UJ ε, φ (umat g) • σ (umat g) w ∂μ)
      = ∫ g : Formalism.REAL.UJ ε, φ (y t * umat g) • σ (umat g) w ∂μ := by
    intro t
    obtain ⟨z, hz'⟩ := hz t
    rw [← ContinuousLinearMap.integral_comp_comm _ hint,
      ← integral_mul_left_eq_self (fun g : Formalism.REAL.UJ ε => φ (y t * umat g) • σ (umat g) w) z]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have e : umat (z * g) = x t * umat g := by rw [← hz']; rfl
    simp only [e]
    rw [← Matrix.mul_assoc, hyx, Matrix.one_mul, hmul _ (hxG t) _ (hmem g),
      ContinuousLinearMap.map_smul_of_tower]
    rfl
  simp only [hform]
  refine contDiff_iff_contDiffAt.2 fun t₀ => ?_
  have hC : IsCompact (Set.image2 (· * ·) (x '' Metric.closedBall t₀ 1)
      ((fun g : UJ ε => umat g) '' tsupport fun g : UJ ε => φ (umat g))) :=
    ((isCompact_closedBall t₀ 1).image hx.continuous).mul (IsCompact.image hψc hu)
  have hK := hemb.isCompact_preimage hC
  have hs : ContDiff ℝ ∞ fun t => ∫ g in (fun g : Formalism.REAL.UJ ε => umat g) ⁻¹'
      (Set.image2 (· * ·) (x '' Metric.closedBall t₀ 1)
        ((fun g : UJ ε => umat g) '' tsupport fun g : UJ ε => φ (umat g))),
      φ (y t * umat g) • σ (umat g) w ∂μ :=
    contDiff_infty.2 fun m => contDiff_setIntegral_nat μ hK (hu.prodMk hb) m
      (fun z : (Fin k → ℝ) × (Matrix (Fin n) (Fin n) ℂ × H) => φ (y z.1 * z.2.1) • z.2.2)
      ((hφ.comp ((hy.comp contDiff_fst).mul (contDiff_fst.comp contDiff_snd))).smul
        (contDiff_snd.comp contDiff_snd))
  refine hs.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [Metric.closedBall_mem_nhds t₀ one_pos] with t ht
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => ?_).symm
  by_contra hne
  obtain ⟨z, hz'⟩ := hz t
  have e : x t * umat (z⁻¹ * g) = umat g := by
    rw [← hz']
    show umat (z * (z⁻¹ * g)) = _
    rw [mul_inv_cancel_left]
  have e' : umat (z⁻¹ * g) = y t * umat g := by
    rw [← e, ← Matrix.mul_assoc, hyx, Matrix.one_mul]
  refine hg ⟨x t, ⟨t, ht, rfl⟩, umat (z⁻¹ * g), ⟨z⁻¹ * g, subset_tsupport _ fun h => hne ?_, rfl⟩, e⟩
  have h' : φ (umat (z⁻¹ * g)) = 0 := h
  rw [← e', h', zero_smul]

theorem exists_smooth_ktype {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {Λ : Fin n → ℝ} {S : Submodule ℂ H} (hK : IsKTypeOf ε σ Λ S) :
    ∃ S' : Submodule ℂ H, IsKTypeOf ε σ Λ S' ∧ ∀ v ∈ S', ∀ (k : ℕ) (x : (Fin k → ℝ) → Matrix (Fin n) (Fin n) ℂ),
      ContDiff ℝ ∞ x → (∀ t, x t ∈ UJset ε) → ContDiff ℝ ∞ fun t => σ (x t) v := by
  have : (muG ε).IsMulRightInvariant := ⟨fun g => indefinite_unitary_unimodular n ε g⟩
  haveI := hK.1
  obtain ⟨v, hvS, hv0, -⟩ := hK.2.2.2.1
  have humat : Continuous (fun g : UJ ε => umat g) := (isClosedEmbeddingMatrix n ε).1.continuous
  have hcont : ∀ s : H, Continuous (fun g : UJ ε => σ (umat g) s) := fun s =>
    (hσ.2.2 s).comp_continuous humat (fun g => g.2)
  have hre : Continuous (fun g : UJ ε => (⟪v, σ (umat g) v⟫_ℂ).re) :=
    Complex.continuous_re.comp (continuous_const.inner (hcont v))
  have hone : 0 < (⟪v, σ (umat (1 : UJ ε)) v⟫_ℂ).re := by
    have : σ (umat (1 : UJ ε)) = 1 := hσ.1.1
    rw [this]
    exact re_inner_self_pos (𝕜 := ℂ).2 hv0
  obtain ⟨a, ha', ha0, ha1, hac, haU, haK⟩ := exists_bump n ε
    {g | 0 < (⟪v, σ (umat g) v⟫_ℂ).re} ((isOpen_lt continuous_const hre).mem_nhds hone)
  have ha : ContDiff ℝ ∞ a := ha' _ (fun p => p) contDiff_entry
  have hacont : Continuous (fun g : UJ ε => a (umat g)) := ha.continuous.comp humat
  have hacC : Continuous (fun g : UJ ε => (a (umat g) : ℂ)) := Complex.continuous_ofReal.comp hacont
  have hsuppC : HasCompactSupport (fun g : UJ ε => (a (umat g) : ℂ)) :=
    hac.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
  have hint : ∀ s : H, Integrable (fun g : UJ ε => (a (umat g) : ℂ) • σ (umat g) s) (muG ε) :=
    fun s => (hacC.smul (hcont s)).integrable_of_hasCompactSupport hsuppC.smul_right
  let T : S →ₗ[ℂ] H :=
    { toFun := fun s => ∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) s ∂(muG ε)
      map_add' := by
        intro s t
        rw [← integral_add (hint s) (hint t)]
        simp only [Submodule.coe_add, map_add, smul_add]
      map_smul' := by
        intro c s
        rw [RingHom.id_apply, ← integral_smul]
        simp only [Submodule.coe_smul, map_smul, smul_comm c] }
  have hT : ∀ (s : S) (u : H), ⟪u, T s⟫_ℂ =
      ∫ g : UJ ε, (a (umat g) : ℂ) * ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε) := by
    intro s u
    show ⟪u, ∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) s ∂(muG ε)⟫_ℂ = _
    rw [← integral_inner (hint s)]
    simp only [inner_smul_right]
  refine ⟨_, GlobalTheory.Dec.FormF.rangeType n ε Λ H σ S H σ (LinearMap.toContinuousLinearMap T) hK ?_ ?_, ?_⟩
  · intro k hk s s' hs'
    have hu : k ∈ Set.range (fun g : UJ ε => umat g) := by
      rw [(isClosedEmbeddingMatrix n ε).2]
      exact (maximal_compact_facts n ε).1 k hk
    obtain ⟨κ, rfl⟩ := hu
    show ∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) s' ∂(muG ε) =
      σ (umat κ) (∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) s ∂(muG ε))
    rw [← ContinuousLinearMap.integral_comp_comm _ (hint s), hs']
    have e1 : ∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) (σ (umat κ) s) ∂(muG ε) =
        ∫ g : UJ ε, (a (umat (g * κ⁻¹)) : ℂ) • σ (umat g) s ∂(muG ε) := by
      rw [← integral_mul_right_eq_self
        (fun g : UJ ε => (a (umat (g * κ⁻¹)) : ℂ) • σ (umat g) (s : H)) κ]
      congr 1
      funext g
      have : σ (umat (g * κ)) = _ := hσ.1.2 (umat g) g.2 (umat κ) κ.2
      rw [this, mul_inv_cancel_right]
      rfl
    have e2 : ∫ g : UJ ε, σ (umat κ) ((a (umat g) : ℂ) • σ (umat g) s) ∂(muG ε) =
        ∫ g : UJ ε, (a (umat (κ⁻¹ * g)) : ℂ) • σ (umat g) s ∂(muG ε) := by
      rw [← integral_mul_left_eq_self
        (fun g : UJ ε => (a (umat (κ⁻¹ * g)) : ℂ) • σ (umat g) (s : H)) κ]
      congr 1
      funext g
      have : σ (umat (κ * g)) = _ := hσ.1.2 (umat κ) κ.2 (umat g) g.2
      rw [this, inv_mul_cancel_left, map_smul]
      rfl
    refine e1.trans (Eq.trans ?_ e2.symm)
    congr 1
    funext g
    have hk' : umat κ⁻¹ ∈ Kset ε := (KG ε).inv_mem (x := κ) hk
    have : a (umat (κ⁻¹ * g)) = a (umat (g * κ⁻¹)) := haK _ hk' (umat g)
    rw [this]
  · intro h0
    have hc : T ⟨v, hvS⟩ = 0 := congrArg (fun f : S →L[ℂ] H => f ⟨v, hvS⟩) h0
    have h1 := hT ⟨v, hvS⟩ v
    rw [hc, inner_zero_right] at h1
    have hi : Integrable (fun g : UJ ε => (a (umat g) : ℂ) * ⟪v, σ (umat g) v⟫_ℂ) (muG ε) :=
      (hacC.mul (continuous_const.inner (hcont v))).integrable_of_hasCompactSupport hsuppC.mul_right
    have h2 := congrArg Complex.re h1
    have h3 := integral_re (𝕜 := ℂ) hi
    simp only [RCLike.re_to_complex, Complex.re_ofReal_mul] at h3
    rw [← h3] at h2
    have h4 : 0 < ∫ g : UJ ε, a (umat g) * (⟪v, σ (umat g) v⟫_ℂ).re ∂(muG ε) := by
      refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1)
        (hacont.mul hre) hac.mul_right ?_ (mul_ne_zero ha1 hone.ne')
      intro g
      by_cases h : a (umat g) = 0
      · simp [h]
      · exact mul_nonneg (ha0 _) (le_of_lt (haU g h))
    rw [← h2] at h4
    simp at h4
  · rintro _ ⟨s, rfl⟩ k x hx hxG
    have e : (T s : H) = ∫ g : UJ ε, a (umat g) • σ (umat g) (s : H) ∂(muG ε) := by
      show ∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) s ∂(muG ε) = _
      simp only [Complex.coe_smul]
    show ContDiff ℝ ∞ fun t => σ (x t) (T s)
    rw [e]
    exact garding_smooth hσ ha hac s k x hx hxG

theorem exists_smoothVec_ktype {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {Λ : Fin n → ℝ} {S : Submodule ℂ H} (hK : IsKTypeOf ε σ Λ S)
    {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) :
    ∃ S' : Submodule ℂ H, IsKTypeOf ε σ Λ S' ∧
      ∀ v ∈ S', Formalism.L2.Theta.SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) v := by
  obtain ⟨S', hS', hs⟩ := exists_smooth_ktype hσ hK
  have hG : IsUnit G := by
    rw [← h]
    exact (((Matrix.isUnit_conjTranspose _).2 hP).mul
      (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε))).mul hP
  refine ⟨S', hS', fun v hv k Xs hX =>
    hs v hv k _ ((contDiff_const.mul (contDiff_expProd Xs)).mul contDiff_const) fun t => ?_⟩
  refine conj_mem hP h (list_prod_mem _ fun g hg => ?_)
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
  exact exp_mem hG (hX i) _

end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_lowK_le_sm : ∀ (D : D7) (V : HSp D) (Sp : D.what₂.Tau → SPar) (M : DSModel V Sp) (τ : D.what₂.Tau),
    ∃ S : Submodule ℂ (M.H τ), IsKTypeOf (M.ε τ) (M.σ τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) S ∧ S ≤ M.sm τ := by
  intro D V Sp M τ
  obtain ⟨h1, h2, h3, -, -, ⟨S, hS⟩, -⟩ := M.ds τ
  obtain ⟨S', hS', hs⟩ := exists_smoothVec_ktype h3 hS (M.fr_unit τ) (M.fr_gram τ)
  exact ⟨S', hS', fun v hv => Submodule.subset_span (hs v hv)⟩

end GlobalTheory.SmoothLowType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaLiftAdjointScalarOnPart
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ScalChoice

theorem exists_pin (P : ℝ → Prop) (h : ∀ a b, P a → P b → a = b) : ∃ a, ∀ l, P l → a = l := by
  by_cases hP : ∃ a, P a
  · obtain ⟨a, ha⟩ := hP
    exact ⟨a, fun l hl => h a l ha hl⟩
  · exact ⟨0, fun l hl => absurd ⟨l, hl⟩ hP⟩

theorem exists_eig {M : Type*} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) (f : M → M) (c : ℝ) :
    ∃ a : ℝ, (∀ l : ℝ, S ≠ ⊥ → (∀ x ∈ S, f x = (l : ℂ) • x) → a = l) ∧ (S = ⊥ → a = c) := by
  rcases eq_or_ne S ⊥ with hW | hW
  · exact ⟨c, fun l h => absurd hW h, fun _ => rfl⟩
  · obtain ⟨a, ha⟩ := exists_pin (fun l => ∀ x ∈ S, f x = (l : ℂ) • x) (fun a b ha hb => by
        obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
        exact_mod_cast smul_left_injective ℂ hx0 ((ha x hx).symm.trans (hb x hx)))
    exact ⟨a, fun l _ h => ha l h, fun h => absurd h hW⟩

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev withScal (R : RealDat D A Ks) (lam : Fin D.R.m → T → A.fam.base.Ix → InfinitePlace D.what₂.LL → ℝ) (kap : ℝ) :
    RealDat D A Ks := { R with lam := lam, kap := kap }

def OffEq (R : RealDat D A Ks) (F : Face D A) (b : Bool) (i : Fin D.R.m) (p : A.fam.base.Ix)
    (v : InfinitePlace D.what₂.LL) (l : ℝ) : Prop :=
  ∀ x, (R.toCx F).tC F.cr b i A.μ0 (Cx.cpt A.v0.embedding x) ∈ (R.toCx F).Wp i p → ∀ y,
      inner ℂ ((R.toCx F).wC b i v (Cx.cpt v.embedding (((R.toCx F).liftMat F.cr b i A.μ0).mulVec x)))
          ((R.toCx F).wC b i v (Cx.cpt v.embedding (((R.toCx F).liftMat F.cr b i A.μ0).mulVec y))) =
        ((l : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((Cx.lv (F.fc (R.toCx F).zs) b).XT i A.μ0) v x y

theorem OffEq.unique {R : RealDat D A Ks} {F : Face D A} {b : Bool} {i : Fin D.R.m} {p : A.fam.base.Ix}
    {v : InfinitePlace D.what₂.LL} {l l' : ℝ} (hp : R.PartAt F b i p v) (h : OffEq R F b i p v l)
    (h' : OffEq R F b i p v l') : l = l' := by
  obtain ⟨x, hx, hx0⟩ := hp
  have h1 := (h x hx x).symm.trans (h' x hx x)
  have h2 := mul_right_cancel₀ (by exact_mod_cast hx0) h1
  exact_mod_cast h2

theorem zs_withScal (R : RealDat D A Ks) (F : Face D A) (lam) (kap : ℝ) :
    ((withScal R lam kap).toCx F).zs = (R.toCx F).zs := rfl

theorem partAt_withScal (R : RealDat D A Ks) (F : Face D A) (lam) (kap : ℝ) (b i p v) :
    (withScal R lam kap).PartAt F b i p v ↔ R.PartAt F b i p v := Iff.rfl

theorem offEq_withScal (R : RealDat D A Ks) (F : Face D A) (lam) (kap : ℝ) (b i p v l) :
    OffEq (withScal R lam kap) F b i p v l ↔ OffEq R F b i p v l := Iff.rfl

theorem exists_thetaLift_adjoint_scalar_on_part (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (p : A.fam.base.Ix) (c : ℝ) :
    ∃ a : ℝ, (∀ l : ℝ, R.Wp i p ≠ ⊥ →
      (∀ x ∈ R.Wp i p, R.thG i t (LinearMap.adjoint (R.thG i t) x) = (l : ℂ) • x) → a = l) ∧ (R.Wp i p = ⊥ → a = c) :=
  exists_eig (R.Wp i p) (fun x => R.thG i t (LinearMap.adjoint (R.thG i t) x)) c

theorem exists_lamOff (R : RealDat D A Ks) (F : Face D A) (i : Fin D.R.m) (p : A.fam.base.Ix)
    (v : InfinitePlace D.what₂.LL) (c : ℝ) :
    ∃ a : ℝ, (∀ b (l : ℝ), R.PartAt F b i p v → (b = false ∨ ¬ R.PartAt F false i p v) → OffEq R F b i p v l → a = l) ∧
      ((∀ b, ¬ R.PartAt F b i p v) → a = c) := by
  by_cases h0 : R.PartAt F false i p v
  · obtain ⟨a, ha⟩ := exists_pin (OffEq R F false i p v) (fun a b => OffEq.unique h0)
    refine ⟨a, fun b l _ hb h => ?_, fun h => absurd h0 (h false)⟩
    rcases hb with rfl | hb
    · exact ha l h
    · exact absurd h0 hb
  · by_cases h1 : R.PartAt F true i p v
    · obtain ⟨a, ha⟩ := exists_pin (OffEq R F true i p v) (fun a b => OffEq.unique h1)
      refine ⟨a, fun b l hp _ h => ?_, fun h => absurd h1 (h true)⟩
      cases b
      · exact absurd hp h0
      · exact ha l h
    · refine ⟨c, fun b l hp _ _ => ?_, fun _ => rfl⟩
      cases b
      · exact absurd hp h0
      · exact absurd hp h1

theorem exists_isScal : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ F : Face D A, ∃ lam kap, ({ R with lam := lam, kap := kap } : RealDat D A Ks).IsScal F := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F
  classical
  choose f0 hf0 hf0' using fun i t p => exists_thetaLift_adjoint_scalar_on_part R i t p (Real.exp ((F.Zsc (R.toCx F).zs).l6m i))
  choose f1 hf1 hf1' using fun i p v => exists_lamOff R F i p v (Real.exp ((F.Zsc (R.toCx F).zs).l6m i))
  obtain ⟨lam, h0, h1⟩ : ∃ lam : Fin D.R.m → T → A.fam.base.Ix → InfinitePlace D.what₂.LL → ℝ,
      (∀ i t p, lam i t p A.v0 = f0 i t p) ∧ ∀ i t p v, v ≠ A.v0 → lam i t p v = f1 i p v :=
    ⟨fun i t p v => if v = A.v0 then f0 i t p else f1 i p v, fun i t p => if_pos rfl, fun i t p v hv => if_neg hv⟩
  obtain ⟨kap, hk⟩ := exists_pin (fun κ => Lift.IsKap D.R.m (fun t => R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) R.EEp
      (withScal R lam 0).lamN κ ∧ ∃ t p, R.EEp p ≠ ⊥ ∧ ∏ j ∈ Finset.Icc 1 D.R.m, (withScal R lam 0).lamN t j p ≠ 0)
    (fun a b ha hb => by
      obtain ⟨t, p, hp, hl⟩ := ha.2
      exact Lift.IsKap.unique ha.1 hb.1 t p hp hl)
  refine ⟨lam, kap, (?_ : (withScal R lam kap).IsScal F)⟩
  refine ⟨fun i t p l hW h => ?_, fun κ h h' => hk κ ⟨h, h'⟩, fun b i p v l hv hp hb h => ?_, fun i t p hW => ?_,
    fun i p v hv h => ?_, fun i t p v hv => ?_⟩
  · exact (h0 i t p).trans (hf0 i t p l hW h)
  · refine (h1 i _ p v hv).trans (hf1 i p v b l ((partAt_withScal R F lam kap b i p v).1 hp) ?_
      ((offEq_withScal R F lam kap b i p v l).1 h))
    rwa [partAt_withScal] at hb
  · exact (h0 i t p).trans (hf0' i t p hW)
  · exact (h1 i _ p v hv).trans (hf1' i p v fun b hb => h b ((partAt_withScal R F lam kap b i p v).2 hb))
  · exact (h1 i t p v hv).trans (h1 i _ p v hv).symm

end GlobalTheory.ScalChoice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueUnitaryTwoStepPairMeasure
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

section

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (B : Matrix (Fin (M + 1)) (Fin M) E)

theorem pairOf_mul_frame (J' : Matrix (Fin M) (Fin M) E) (y : Fin 1 → Fin (M + 1) → R ⊗[F] E)
    (g h : HA R σ J) (h' : HA R σ J') (hh : FrameRelR R σ J J' B h h')
    (y' : Fin 1 → Fin M → R ⊗[F] E) :
    pairOf R σ J B y (g * h) y' = pairOf R σ J B y g (h' • y') := by
  unfold pairOf
  congr 2
  have h1 : (h' • y') 0 = ((HA.mat R σ J' h' : GL (Fin M) (R ⊗[F] E)) :
      Matrix (Fin M) (Fin M) (R ⊗[F] E)).mulVec (y' 0) := rfl
  have h2 : ((HA.mat R σ J (g * h) : GL (Fin (M + 1)) (R ⊗[F] E)) : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) =
      ((HA.mat R σ J g : GL (Fin (M + 1)) (R ⊗[F] E)) : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) *
      ((HA.mat R σ J h : GL (Fin (M + 1)) (R ⊗[F] E)) : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) := rfl
  unfold FrameRelR at hh
  rw [h1, h2]
  simp only [Matrix.mulVec_mulVec]
  rw [Matrix.mul_assoc]
  exact congrArg (fun A => Matrix.mulVec (((HA.mat R σ J g : GL (Fin (M + 1)) (R ⊗[F] E)) :
    Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) * A) (y' 0)) hh

variable [TopologicalSpace R] [FiniteDimensional F E] [IsTopologicalRing R]

theorem continuous_pairOf : Continuous fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × HA R σ J ×
    (Fin 1 → Fin M → R ⊗[F] E) => pairOf R σ J B p.1 p.2.1 p.2.2 := by
  refine continuous_pi fun a => ?_
  fin_cases a
  · exact (by fun_prop : Continuous fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × HA R σ J ×
      (Fin 1 → Fin M → R ⊗[F] E) => p.1 0)
  · exact ((continuous_mat R σ J).comp (continuous_fst.comp continuous_snd)).matrix_mulVec
      (continuous_const.matrix_mulVec
        ((continuous_apply 0).comp (continuous_snd.comp continuous_snd)))

end

theorem twoStep_existsUnique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (m : Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : Measure (Fin 1 → Fin M → R ⊗[F] E)), StepData σ J x a B J' → OnOrbit R σ J x m → IsFiniteMeasureOnCompacts m → IsFiniteMeasureOnCompacts m' → IsInvTup R σ J' m' → ∃! N, TwoStep R σ J x B m m' N := by
  intro F E _ _ _ _ _ σ hσ R _ _ _ _ _ _ _ _ _ M J x a B J' m m' hd horb hm hm' hinv
  obtain ⟨-, ⟨e, he, -⟩, -⟩ := GlobalTheory.T.unitary_stabilizer_anisotropic_vector_equiv_complement F E σ hσ R M J x a B J' hd
  obtain ⟨-, s₀, hs₀m, hs₀⟩ := GlobalTheory.T.measurableSet_orbit_exists_measurable_section (HA R σ J) (Fin 1 → Fin (M + 1) → R ⊗[F] E)
    (ratTup (F := F) R x)
  have hP : Measurable fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × HA R σ J ×
      (Fin 1 → Fin M → R ⊗[F] E) => pairOf R σ J B p.1 p.2.1 p.2.2 :=
    (continuous_pairOf R σ J B).measurable
  have hΦ : Measurable fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin 1 → Fin M → R ⊗[F] E) =>
      pairOf R σ J B p.1 (s₀ p.1) p.2 :=
    hP.comp (measurable_fst.prodMk ((hs₀m.comp measurable_fst).prodMk measurable_snd))
  have hex : TwoStep R σ J x B m m' ((m.prod m').map fun p => pairOf R σ J B p.1 (s₀ p.1) p.2) := by
    intro f hf s hs
    rw [lintegral_map hf hΦ, lintegral_prod (fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) ×
      (Fin 1 → Fin M → R ⊗[F] E) => f (pairOf R σ J B p.1 (s₀ p.1) p.2)) (hf.comp hΦ).aemeasurable]
    refine lintegral_congr_ae ?_
    have hae : ∀ᵐ y ∂m, ∃ g : HA R σ J, g • ratTup (F := F) R x = y := horb
    filter_upwards [hae] with y hy
    have hst : (s₀ y)⁻¹ * s y ∈ Hstab R σ J x := by
      change ((s₀ y)⁻¹ * s y) • ratTup (F := F) R x = ratTup (F := F) R x
      rw [mul_smul, hs y hy, inv_smul_eq_iff, hs₀ y hy]
    have hfac : s y = s₀ y * ((s₀ y)⁻¹ * s y) := by group
    have hk : Measurable fun y' => f (pairOf R σ J B y (s₀ y) y') :=
      (hf.comp hΦ).comp measurable_prodMk_left
    have hsm : Measurable fun X : Fin 1 → Fin M → R ⊗[F] E => e ⟨_, hst⟩ • X :=
      (continuous_const_smul _).measurable
    calc ∫⁻ y', f (pairOf R σ J B y (s₀ y) y') ∂m'
        = ∫⁻ y', f (pairOf R σ J B y (s₀ y) y') ∂(m'.map fun X => e ⟨_, hst⟩ • X) := by
          rw [hinv]
      _ = ∫⁻ y', f (pairOf R σ J B y (s₀ y) (e ⟨_, hst⟩ • y')) ∂m' := lintegral_map hk hsm
      _ = ∫⁻ y', f (pairOf R σ J B y (s y) y') ∂m' := by
          refine lintegral_congr fun y' => ?_
          rw [← pairOf_mul_frame R σ J B J' y (s₀ y) _ _ (he ⟨_, hst⟩), ← hfac]
  refine ⟨_, hex, fun N hN => ?_⟩
  ext A hA
  rw [← lintegral_indicator_one hA, ← lintegral_indicator_one hA,
    hN _ (measurable_one.indicator hA) s₀ hs₀, hex _ (measurable_one.indicator hA) s₀ hs₀]

end GlobalTheory.GaugeEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteClassSetHermitianUnitaryOpenLevelStatement
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_classSet_hermitianUnitary_openLevel : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ K : Subgroup (HA (Af F) σ J), IsOpen (K : Set (HA (Af F) σ J)) → ∃ S : Finset (HA (Af F) σ J), ∀ g : HA (Af F) σ J, ∃ γ : HFinIn (Af F) σ J, ∃ s ∈ S, ∃ k ∈ K, g = γ • (s * k) := by
  first | exact @GlobalTheory.Mem.ClassFinite.exists_finset_classes | exact GlobalTheory.Mem.ClassFinite.exists_finset_classes | (intros; apply GlobalTheory.Mem.ClassFinite.exists_finset_classes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCovolumeLatticeStabiliserUnitaryRealPointsStatement
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_covolume_latticeStabiliser_unitaryRealPoints : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin M → E)), L.FG → Submodule.span E (L : Set (Fin M → E)) = ⊤ → ∀ ν : Measure (HA (Ainf F) σ J), ν.IsHaarMeasure → ∃ Ω : Set (HA (Ainf F) σ J), MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : HA (Ainf F) σ J, ∃ γ ∈ Formalism.UG.UJ (σ : E →+* E) J, (∀ x, x ∈ L ↔ (γ : Matrix (Fin M) (Fin M) E).mulVec x ∈ L) ∧ ∃ w ∈ Ω, HA.mat (Ainf F) σ J g = Formalism.UG.bc (inclR (F := F) (Ainf F)) γ * HA.mat (Ainf F) σ J w := by
  first | exact @GlobalTheory.MixedSignature.finite_covolume_real_points | exact GlobalTheory.MixedSignature.finite_covolume_real_points | (intros; apply GlobalTheory.MixedSignature.finite_covolume_real_points <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsRe
section
noncomputable section

namespace GlobalTheory.Mem.SRe.ColRe

open Formalism.BasicNotions Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.SRe NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (Z : New D)

set_option maxHeartbeats 4000000 in

def formsRe {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (T : FormsTiedSym D u Ch chOf) :
    FormsTiedSym (reD D Z) u Ch chOf := by kcopy T

end GlobalTheory.Mem.SRe.ColRe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FundamentalDomainUnitaryAdelicExistsMeasureEqStatement
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamentalDomain_unitaryAdelic_exists_measure_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (μ : Measure (HA (AF F) σ J)), μ.IsHaarMeasure → (∃ 𝓕, IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ) ∧ ∀ 𝓕 𝓕', IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ → IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕' μ → μ 𝓕 = μ 𝓕' ∧ μ 𝓕 ≠ 0 := by
  first | exact @GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary | exact GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary | (intros; apply GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarMeasureGramGL2ActionTensorStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_measure_gram_GL2_action_tensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], ∀ (lam : Measure (R ⊗[F] E)) (ν : Measure R) (γ : GL (Fin 2) E), lam.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∃ Φ : (R × (R ⊗[F] E) × R) ≃ₜ (R × (R ⊗[F] E) × R), (∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ X : (Fin 2 → Fin M → R ⊗[F] E), gram3 R σ J (lrAct 1 ((γ : Matrix (Fin 2) (Fin 2) E).map (inclR R)) X) = Φ (gram3 R σ J X)) ∧ ν.prod (lam.prod ν) = (modu (R ⊗[F] E) (inclR R (γ : Matrix (Fin 2) (Fin 2) E).det) ^ 2) • (ν.prod (lam.prod ν)).map Φ := by
  first | exact @GlobalTheory.GaugeEx.HermMod.haar_measure_gram_GL2_action | exact GlobalTheory.GaugeEx.HermMod.haar_measure_gram_GL2_action | (intros; apply GlobalTheory.GaugeEx.HermMod.haar_measure_gram_GL2_action <;> assumption)
end

