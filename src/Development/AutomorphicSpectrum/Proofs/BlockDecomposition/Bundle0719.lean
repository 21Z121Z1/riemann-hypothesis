import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0468
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1576
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0126
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0003
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0063
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0044
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0057
import BuildAid.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0701

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelSetUniformSmoothBound
section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay.Mean

open GlobalTheory.LeviHC GlobalTheory.LeviHC.LineLie GlobalTheory.SmoothForms

section OnePlace

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {w : InfinitePlace F}

theorem norm_le_of_entries {X : Matrix (Fin n) (Fin n) ℂ} {r : ℝ} (hr : 0 ≤ r) (h : ∀ i j, ‖X i j‖ ≤ r) :
    ‖X‖ ≤ n * r := by
  have key : ‖X‖₊ ≤ (n : ℝ≥0) * r.toNNReal := by
    rw [Matrix.linfty_opNNNorm_def]
    refine Finset.sup_le fun i _ => ?_
    calc ∑ j, ‖X i j‖₊ ≤ ∑ _j : Fin n, r.toNNReal :=
          Finset.sum_le_sum fun j _ => by
            rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hr]
            exact h i j
      _ = (n : ℝ≥0) * r.toNNReal := by simp
  have key' := NNReal.coe_le_coe.mpr key
  simpa [Real.coe_toNNReal _ hr] using key'

theorem expMap_zero (h : IsCMExt F E σ) (τ : EmbOver E w) :
    expMap (jA (J.map τ.1)) (secA σ J τ) 0 = 1 := by
  show secA σ J τ (NormedSpace.exp ((jA (J.map τ.1)) 0)) = 1
  rw [map_zero, NormedSpace.exp_zero, ← map_one (archMat σ J τ), secA_archMat h, map_one]

theorem expMap_add (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : EmbOver E w) (Z : LieL (J.map τ.1)) (s t : ℝ) :
    expMap (jA (J.map τ.1)) (secA σ J τ) ((s + t) • Z) =
      expMap (jA (J.map τ.1)) (secA σ J τ) (s • Z) * expMap (jA (J.map τ.1)) (secA σ J τ) (t • Z) := by
  obtain ⟨y1, e1, a1⟩ := isLineOf_expMap h hJ τ Z s
  obtain ⟨y2, e2, a2⟩ := isLineOf_expMap h hJ τ Z t
  obtain ⟨y3, e3, a3⟩ := isLineOf_expMap h hJ τ Z (s + t)
  beta_reduce at e1 e2 e3
  rw [e1, e2, e3, ← map_mul]
  congr 1
  apply archMat_injective h τ
  rw [map_mul, a1, a2, a3, add_smul]
  exact NormedSpace.exp_add_of_commute (((Commute.refl _).smul_left s).smul_right t)

theorem one_place (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : EmbOver E w) :
    ∃ (ι : Type) (_ : Fintype ι) (b : ι → ℝ → GAd σ J) (K : Set (GArch σ J w)) (C δ₁ : ℝ),
      (∀ i, IsRealLine σ J (b i)) ∧ IsCompact K ∧ 1 ∈ K ∧ 0 < δ₁ ∧ 0 ≤ C ∧
      ∀ (y : GArch σ J w) (δ : ℝ), 0 ≤ δ → δ ≤ δ₁ → (∀ i j, ‖(archMat σ J τ y - 1) i j‖ ≤ δ) →
        y ∈ K ∧ ∀ ψ : GAd σ J → ℂ, GlobalTheory.UAut.IsSm σ J ψ → ∀ (g : GAd σ J) (c : ι → ℝ),
          (∀ i, ∀ x ∈ K, ‖lineDer (b i) ψ (g * embArch σ J w x)‖ ≤ c i) →
          ‖ψ (g * embArch σ J w y) - ψ g‖ ≤ C * δ * ∑ i, c i := by
  have hA := isUnit_det_map hJ τ.1
  obtain ⟨δ₁, C₀, h1, hlog⟩ := GlobalTheory.UnitaryLog.exists_log_unitary n (J.map τ.1) hA
  haveI : FiniteDimensional ℝ (LieL (J.map τ.1)) := inferInstance
  haveI : ProperSpace (LieL (J.map τ.1)) := FiniteDimensional.proper_real _
  let b := Module.finBasis ℝ (LieL (J.map τ.1))
  obtain ⟨K₀, hK₀, hco⟩ := GlobalTheory.CuspGeo.MeanValue.exists_coord_bound b
  choose yOf hy1 hy2 using fun Y : LieL (J.map τ.1) => isLineOf_expMap h hJ τ Y 1
  simp only [one_smul] at hy1 hy2
  have hyc : Continuous yOf := (GlobalTheory.Orb.isEmbedding_archMat J h τ).continuous_iff.2 (by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    change Continuous fun Y => archMat σ J τ (yOf Y) i j
    simp only [hy2]
    have : Continuous fun Y : LieL (J.map τ.1) => NormedSpace.exp Y.1 :=
      (NormedSpace.exp_continuous).comp continuous_subtype_val
    exact (continuous_apply j).comp ((continuous_apply i).comp this))
  have hy0 : yOf 0 = 1 := archMat_injective h τ (by
    rw [hy2, map_one]; simp)
  set C₁ : ℝ := n * |C₀| with hC₁
  have hC₁0 : 0 ≤ C₁ := mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
  refine ⟨_, inferInstance, fun i t => expMap (jA (J.map τ.1)) (secA σ J τ) (t • b i),
    yOf '' Metric.closedBall 0 (C₁ * δ₁), K₀ * C₁, δ₁, fun i => (isLineOf_expMap h hJ τ (b i)).isRealLine h,
    (isCompact_closedBall _ _).image hyc, ⟨0, ?_, hy0⟩, h1, mul_nonneg hK₀ hC₁0, fun y δ h0 hδ hy => ?_⟩
  · simpa using mul_nonneg hC₁0 h1.le
  have hU : (archMat σ J τ y)ᴴ * J.map τ.1 * archMat σ J τ y = J.map τ.1 := by
    rw [GlobalTheory.Orb.archMat_eq_archEquiv J h]
    exact (archEquiv J h τ y).2
  obtain ⟨X, hX, hE, hB⟩ := hlog (archMat σ J τ y) δ hU hδ hy
  let Z : LieL (J.map τ.1) := ⟨X, hX⟩
  have hZ : ‖Z‖ ≤ C₁ * δ := by
    have := norm_le_of_entries (mul_nonneg (abs_nonneg C₀) h0) fun i j =>
      (hB i j).trans (mul_le_mul_of_nonneg_right (le_abs_self C₀) h0)
    rw [hC₁, mul_assoc]
    exact this
  have hyZ : yOf Z = y := archMat_injective h τ (by rw [hy2, ← hE])
  have hball : ∀ t ∈ Set.Icc (0 : ℝ) 1, t • Z ∈ Metric.closedBall (0 : LieL (J.map τ.1)) (C₁ * δ₁) := fun t ht => by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans (hZ.trans (mul_le_mul_of_nonneg_left hδ hC₁0))
  refine ⟨⟨Z, by simpa using hball 1 (by simp), hyZ⟩, fun ψ hψ g c hc => ?_⟩
  rw [← hyZ, ← hy1 Z]
  refine GlobalTheory.CuspGeo.MeanValue.norm_sub_le _ (expMap_zero h τ) (expMap_add h hJ τ) b (sm_of_isSm h hJ τ hψ) g Z _
    (fun i => (hco Z i).trans ?_) c fun i t ht => ?_
  · rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hZ hK₀
  · have := hc i (yOf (t • Z)) ⟨_, hball t ht, rfl⟩
    rw [← hy1] at this
    exact this

end OnePlace

section Places

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

def pt (a : ∀ w, GArch σ J w) : GAd σ J := ofInf σ J (embArchPi σ J a)

theorem pt_mul_single [DecidableEq (InfinitePlace F)] (a : ∀ w, GArch σ J w) (w : InfinitePlace F) (x : GArch σ J w) :
    pt (a * Pi.mulSingle w x) = pt a * embArch σ J w x := by
  show ofInf σ J (embArchPi σ J (a * Pi.mulSingle w x)) = ofInf σ J (embArchPi σ J a) * embArch σ J w x
  rw [map_mul, map_mul, embArchPi_mulSingle]
  rfl

theorem pt_one : pt (1 : ∀ w, GArch σ J w) = 1 := by
  simp only [pt, map_one]

theorem pt_proj {u : GAd σ J} (hu : u ∈ infPts σ J) : pt (fun w => projArch σ J w u) = u := by
  refine GAd_ext σ J (fun w' => ?_) (fun v => ?_)
  · rw [pt, projArch_ofInf, projInfArch_embArchPi]
  · rw [pt, proj_ofInf, mem_infPts_iff_forall.mp hu v]

theorem continuous_pt : Continuous (pt : (∀ w, GArch σ J w) → GAd σ J) := by
  show Continuous fun a => ofInf σ J (embArchPi σ J a)
  exact (continuous_ofInf σ J).comp (continuous_embArchPi σ J)

open Classical in

theorem telescope {ι : InfinitePlace F → Type} [∀ w, Fintype (ι w)] {b : ∀ w, ι w → ℝ → GAd σ J}
    {K : ∀ w, Set (GArch σ J w)} {C : InfinitePlace F → ℝ} (h1 : ∀ w, 1 ∈ K w) {ψ : GAd σ J → ℂ} (g : GAd σ J)
    {y : ∀ w, GArch σ J w} (hyK : ∀ w, y w ∈ K w) {δ : ℝ} {c : ∀ w, ι w → ℝ}
    (hstep : ∀ w (g : GAd σ J), (∀ i, ∀ x ∈ K w, ‖lineDer (b w i) ψ (g * embArch σ J w x)‖ ≤ c w i) →
      ‖ψ (g * embArch σ J w (y w)) - ψ g‖ ≤ C w * δ * ∑ i, c w i)
    (hc : ∀ w i, ∀ x ∈ pt '' Set.pi Set.univ K, ‖lineDer (b w i) ψ (g * x)‖ ≤ c w i)
    (S : Finset (InfinitePlace F)) :
    ‖ψ (g * pt fun w => if w ∈ S then y w else 1) - ψ g‖ ≤ ∑ w ∈ S, C w * δ * ∑ i, c w i := by
  induction S using Finset.induction_on with
  | empty =>
    have h0 : (fun w => if w ∈ (∅ : Finset (InfinitePlace F)) then y w else 1) = (1 : ∀ w, GArch σ J w) := by
      funext w
      simp
    rw [h0, pt_one, mul_one, sub_self, norm_zero, Finset.sum_empty]
  | @insert v S hv ih =>
    set a : ∀ w, GArch σ J w := fun w => if w ∈ S then y w else 1 with ha
    have hsplit : (fun w => if w ∈ insert v S then y w else 1) = a * Pi.mulSingle v (y v) := by
      funext w
      by_cases hw : w = v
      · subst hw
        simp [ha, hv]
      · simp only [Pi.mul_apply, Pi.mulSingle_eq_of_ne hw, mul_one, ha, Finset.mem_insert, hw, false_or]
    have hK : ∀ x ∈ K v, a * Pi.mulSingle v x ∈ Set.pi Set.univ K := by
      intro x hx
      rw [Set.mem_univ_pi]
      intro w
      by_cases hw : w = v
      · subst hw
        simp [ha, hv, hx]
      · simp only [Pi.mul_apply, Pi.mulSingle_eq_of_ne hw, mul_one, ha]
        split_ifs
        · exact hyK w
        · exact h1 w
    have step := hstep v (g * pt a) (fun i x hx => by
      rw [mul_assoc, ← pt_mul_single]
      exact hc v i _ ⟨_, hK x hx, rfl⟩)
    rw [hsplit, pt_mul_single, Finset.sum_insert hv, ← mul_assoc]
    calc _ = ‖(ψ (g * pt a * embArch σ J v (y v)) - ψ (g * pt a)) + (ψ (g * pt a) - ψ g)‖ := by
          rw [sub_add_sub_cancel]
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add step ih)

end Places

theorem mean_value : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∃ (m : ℕ) (b : Fin m → ℝ → GAd σ J) (Ω₀ : Set (GAd σ J)) (C δ₁ : ℝ), (∀ i, IsRealLine σ J (b i)) ∧ IsCompact Ω₀ ∧ 0 < δ₁ ∧ 0 ≤ C ∧ ∀ ψ : GAd σ J → ℂ, GlobalTheory.UAut.IsSm σ J ψ → ∀ (g u : GAd σ J) (δ : ℝ), 0 ≤ δ → δ ≤ δ₁ → CloseInf σ J u δ → ∀ c : Fin m → ℝ, (∀ i, ∀ x ∈ Ω₀, ‖lineDer (b i) ψ (g * x)‖ ≤ c i) → ‖ψ (g * u) - ψ g‖ ≤ C * δ * ∑ i, c i := by
  intro F E _ _ _ _ _ σ h n J hJ
  classical
  have τ : ∀ w : InfinitePlace F, EmbOver E w := fun w => Classical.arbitrary _
  choose ι hι b K C d hb hK h1K hd hC key using fun w => one_place (J := J) h hJ (τ w)
  letI : ∀ w, Fintype (ι w) := hι
  obtain ⟨δ₁, hδ₁, hle⟩ : ∃ δ₁ > 0, ∀ w, δ₁ ≤ d w := by
    obtain ⟨w₀, h0⟩ := Finite.exists_min d
    exact ⟨d w₀, hd w₀, h0⟩
  let e := Fintype.equivFin (Σ w, ι w)
  have hCs : 0 ≤ ∑ w, C w := Finset.sum_nonneg fun w _ => hC w
  refine ⟨_, fun i => b (e.symm i).1 (e.symm i).2, pt '' Set.pi Set.univ K, ∑ w, C w, δ₁, fun i => hb _ _,
    (isCompact_univ_pi hK).image continuous_pt, hδ₁, hCs, fun ψ hψ g u δ h0 hδ hu c hc => ?_⟩
  let c' : ∀ w, ι w → ℝ := fun w i => c (e ⟨w, i⟩)
  have hc' : ∀ w i, ∀ x ∈ pt '' Set.pi Set.univ K, ‖lineDer (b w i) ψ (g * x)‖ ≤ c' w i := fun w i x hx => by
    have aux : ∀ p q : Σ w, ι w, p = q → lineDer (b p.1 p.2) ψ = lineDer (b q.1 q.2) ψ := by
      rintro _ _ rfl; rfl
    have := hc (e ⟨w, i⟩) x hx
    rwa [aux _ ⟨w, i⟩ (e.symm_apply_apply _)] at this
  have hnn : ∀ w i, 0 ≤ c' w i := fun w i =>
    (norm_nonneg _).trans (hc' w i 1 ⟨1, fun w _ => h1K w, pt_one⟩)
  have hclose := fun w => key w (projArch σ J w u) δ h0 (hδ.trans (hle w)) (hu.2 w (τ w))
  have T := telescope (b := b) (K := K) (C := C) h1K (ψ := ψ) g (y := fun w => projArch σ J w u)
    (fun w => (hclose w).1) (δ := δ) (c := c') (fun w g' hg' => (hclose w).2 ψ hψ g' (c' w) hg') hc' Finset.univ
  have hfull : (fun w => if w ∈ (Finset.univ : Finset (InfinitePlace F)) then projArch σ J w u else 1) =
      fun w => projArch σ J w u := by
    funext w; simp
  rw [hfull, pt_proj hu.1] at T
  refine T.trans ?_
  have hsum : ∑ i, c i = ∑ w, ∑ i, c' w i := by
    rw [← Equiv.sum_comp e c, Fintype.sum_sigma]
  have hT : ∀ w, ∑ i, c' w i ≤ ∑ i, c i := fun w => by
    rw [hsum]
    exact Finset.single_le_sum (f := fun w => ∑ i, c' w i)
      (fun w _ => Finset.sum_nonneg fun i _ => hnn w i) (Finset.mem_univ w)
  rw [Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (hT w) (mul_nonneg (hC w) h0)

end GlobalTheory.CompanionTheory.RapidDecay.Mean

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeMatrixPermutationEquivsExist
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.CellBij

set_option synthInstance.maxHeartbeats 400000

open scoped TensorProduct

def tensorReindex {α β : Type} (e : β ≃ α) (X : α → Type) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] : (⨂[ℂ] a, X a) ≃ₗ[ℂ] ⨂[ℂ] j, X (e j) :=
  PiTensorProduct.reindex ℂ X e.symm

theorem tensorReindex_tprod {α β : Type} (e : β ≃ α) (X : α → Type) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (z : ∀ a, X a) :
    tensorReindex e X (PiTensorProduct.tprod ℂ z) = PiTensorProduct.tprod ℂ fun j => z (e j) := by
  exact PiTensorProduct.reindex_tprod e.symm z

theorem tensorReindex_piTensor {α β : Type} (e : β ≃ α) {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a))
    (γ : ∀ a, Γ a) (p : ∀ j, Γ (e j)) (h : ∀ j, γ (e j) = p j) (y : ⨂[ℂ] a, X a) :
    tensorReindex e X (piTensor ρ γ y) = (piTensor fun j => ρ (e j)) p (tensorReindex e X y) := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r z =>
    simp only [map_smul, piTensor_tprod, tensorReindex_tprod, h]
  | add x y hx hy =>
    simp only [map_add, hx, hy]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem occursTimes_of_equiv_lemma {G V₁ V₂ Y : Type} [Group G] [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup Y] [Module ℂ Y] (σ : Representation ℂ G Y)
    {ρ₁ : Representation ℂ G V₁} {ρ₂ : Representation ℂ G V₂} (E : ρ₁.Equiv ρ₂) (r : ℕ)
    (h : OccursTimes σ ρ₁ r) : OccursTimes σ ρ₂ r := by
  obtain ⟨S, T, hTS, hST, hq⟩ := h
  let e : V₁ ≃ₗ[ℂ] V₂ := E.toLinearEquiv
  have he : ∀ (g : G) (v : V₁), e (ρ₁ g v) = ρ₂ g (e v) := by
    intro g v
    simp only [e, Representation.Equiv.toLinearEquiv_apply]
    exact Representation.IntertwiningMap.isIntertwining ρ₁ ρ₂ E.toIntertwiningMap g v
  have he' : ∀ (g : G) (w : V₂), e.symm (ρ₂ g w) = ρ₁ g (e.symm w) := by
    intro g w
    apply e.injective
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  let mp : Subrepresentation ρ₁ → Subrepresentation ρ₂ := fun A =>
    { toSubmodule := A.toSubmodule.map (e : V₁ →ₗ[ℂ] V₂)
      apply_mem_toSubmodule := by
        intro g w hw
        rw [Submodule.mem_map_equiv] at hw ⊢
        rw [he']
        exact A.apply_mem_toSubmodule g hw }
  have hmono : ∀ {A B : Subrepresentation ρ₁}, A ≤ B → mp A ≤ mp B := by
    intro A B hAB x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact Submodule.mem_map_of_mem (hAB hy)
  have hQ : ∀ A B : Subrepresentation ρ₁, Nonempty ((subQuot A B).Equiv (subQuot (mp A) (mp B))) := by
    intro A B
    let e1 : A.toSubmodule ≃ₗ[ℂ] (mp A).toSubmodule :=
      LinearEquiv.ofSubmodules e A.toSubmodule (mp A).toSubmodule rfl
    have hP : Submodule.map (e1 : A.toSubmodule →ₗ[ℂ] (mp A).toSubmodule)
        (Submodule.comap A.toSubmodule.subtype B.toSubmodule) =
        Submodule.comap (mp A).toSubmodule.subtype (mp B).toSubmodule := by
      ext x
      rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap]
      show (((e1.symm x) : A.toSubmodule) : V₁) ∈ B.toSubmodule ↔
        (x : V₂) ∈ B.toSubmodule.map (e : V₁ →ₗ[ℂ] V₂)
      rw [Submodule.mem_map_equiv, LinearEquiv.ofSubmodules_symm_apply]
    let qe := Submodule.Quotient.equiv _ _ e1 hP
    refine ⟨Representation.Equiv.mk qe ?_⟩
    intro g
    refine LinearMap.ext fun q => ?_
    refine Submodule.Quotient.induction_on _ q fun x => ?_
    show Submodule.Quotient.mk (e1 ((A.toRepresentation g) x)) =
      Submodule.Quotient.mk (((mp A).toRepresentation g) (e1 x))
    congr 1
    apply Subtype.ext
    show e (ρ₁ g (x : V₁)) = ρ₂ g (e (x : V₁))
    exact he g x
  refine Exists.intro (fun i => mp (S i)) (Exists.intro (fun i => mp (T i))
    ⟨fun i => hmono (hTS i), fun i j hij => hmono (hST i j hij), fun i => ?_⟩)
  obtain ⟨q⟩ := hQ (S i) (T i)
  obtain ⟨f⟩ := hq i
  exact ⟨q.symm.trans f⟩

theorem jhMult_of_nonempty {G V W Y : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup Y] [Module ℂ Y] (σ : Representation ℂ G Y)
    {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W} (h : Nonempty (ρ.Equiv ρ')) :
    jhMult σ ρ = jhMult σ ρ' := by
  obtain ⟨E⟩ := h
  show (⨆ r, ⨆ (_ : OccursTimes σ ρ r), (r : ℕ∞)) = ⨆ r, ⨆ (_ : OccursTimes σ ρ' r), (r : ℕ∞)
  congr 1
  funext r
  rw [show OccursTimes σ ρ r = OccursTimes σ ρ' r from
    propext ⟨occursTimes_of_equiv_lemma σ E r, occursTimes_of_equiv_lemma σ E.symm r⟩]

theorem cell_bij {α β : Type} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β] (e : β ≃ α)
    (d : α → ℕ) {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (ρ : ∀ i, Representation ℂ (GL (Fin (d i)) k) (X i)) (hρ : ∀ i, IsSmooth (ρ i))
    (b : SizeMatrix (fun i => Fin (d i)) (fun j => Fin (d (e j))))
    (hb : ∀ i j, b.1 i j = if e j = i then d i else 0) :
    ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (d i)) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (d (e j))),
      Nonempty ((cellFunctor f g (piTensor ρ)).Equiv (piTensor fun j => ρ (e j))) := by
  have hrz : ∀ i j, j ≠ e.symm i → b.1 i j = 0 := by
    intro i j hj
    rw [hb, if_neg fun h => hj (by rw [← h, Equiv.symm_apply_apply])]
  have hcz : ∀ j i, i ≠ e j → b.1 i j = 0 := by
    intro j i hi
    rw [hb, if_neg fun h => hi h.symm]
  have hrf : ∀ i, b.1 i (e.symm i) = d i := by
    intro i
    rw [hb, if_pos (e.apply_symm_apply i)]
  have hcf : ∀ j, b.1 (e j) j = d (e j) := by
    intro j
    rw [hb, if_pos rfl]
  let f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (d i) := fun i =>
    GlobalTheory.OneBlockCell.valEquiv (e.symm i) (hrf i) (fun j hj => hrz i j hj)
  let g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (d (e j)) := fun j =>
    GlobalTheory.OneBlockCell.valEquiv (e j) (hcf j) (fun i hi => hcz j i hi)
  refine ⟨f, g, ?_⟩
  have hbot : twKer (piTensor ρ) (relUnip k f) 1 = ⊥ := by
    refine eq_bot_iff.2 (Submodule.span_le.2 ?_)
    rintro _ ⟨n, v, rfl⟩
    have : (n : Levi k (fun i => Fin (d i))) = 1 := funext fun i =>
      GlobalTheory.OneBlockCell.eq_one_of_mem_unipRad_single (f i) (e.symm i) (fun j hj => hrz i j hj)
        (n.2 i trivial)
    simp [this]
  have hδ : ∀ z, relDeltaHalf k (fun i j => Fin (b.1 i j)) z = 1 := fun z => by
    rw [relDeltaHalf_apply]
    exact Finset.prod_eq_one fun i _ =>
      GlobalTheory.OneBlockCell.deltaHalf_eq_one_of_single (e.symm i) (fun j hj => hrz i j hj) (z i)
  have hδ' : ∀ z, relDeltaHalf k (fun j i => Fin (b.1 i j)) z = 1 := fun z => by
    rw [relDeltaHalf_apply]
    exact Finset.prod_eq_one fun j _ =>
      GlobalTheory.OneBlockCell.deltaHalf_eq_one_of_single (e j) (fun i hi => hcz j i hi) (z j)
  have hP : ∀ x, x ∈ relParab k g := fun x j _ =>
    GlobalTheory.OneBlockCell.mem_parab_of_single (g j) (e j) (fun i hi => hcz j i hi) (x j)
  have hγ : ∀ (p : relParab k g) j,
      relEmb k f (swapBlocks k (fun i j => Fin (b.1 i j)) (relProj k g p)) (e j) =
        (p : Levi k (fun j => Fin (d (e j)))) j := by
    intro p j
    rw [relEmb_apply]
    refine Units.ext (Matrix.ext fun x y => ?_)
    obtain ⟨⟨a, t⟩, rfl⟩ := (f (e j)).surjective x
    obtain ⟨⟨a', s⟩, rfl⟩ := (f (e j)).surjective y
    have ha : a = j := by
      by_contra hne
      have h1 := hrz (e j) a (by rwa [Equiv.symm_apply_apply])
      have h2 := t.2
      omega
    have ha' : a' = j := by
      by_contra hne
      have h1 := hrz (e j) a' (by rwa [Equiv.symm_apply_apply])
      have h2 := s.2
      omega
    subst ha
    subst ha'
    rw [leviEmb_apply_same]
    rfl
  have hsm : IsSmooth (piTensor fun j => ρ (e j)) := isSmooth_piTensor fun j => hρ (e j)
  let R := tensorReindex e X
  let Ψ : (⨂[ℂ] j, X (e j)) ≃ₗ[ℂ] Jacquet (piTensor ρ) (relUnip k f) :=
    R.symm.trans (Submodule.quotEquivOfEqBot _ hbot).symm
  have hΨ : ∀ u, Ψ u = Submodule.Quotient.mk (R.symm u) := fun u => rfl
  let τ := (twist ((relJac f (piTensor ρ)).comp (swapBlocks k (fun i j => Fin (b.1 i j))))
        (relDeltaHalf k (fun j i => Fin (b.1 i j)))).comp (relProj k g)
  have law : ∀ (p : relParab k g) u, τ p (Ψ u) = Ψ ((piTensor fun j => ρ (e j)) p u) := by
    intro p u
    rw [MonoidHom.comp_apply, twist_apply, MonoidHom.comp_apply, hΨ, relJac_mk, hδ, hδ', hΨ]
    simp only [inv_one, Units.val_one, one_smul]
    congr 1
    apply R.injective
    rw [tensorReindex_piTensor e ρ _ (p : Levi k (fun j => Fin (d (e j)))) (hγ p)]
    exact (congrArg (fun w => (piTensor fun j => ρ (e j))
      (p : Levi k (fun j => Fin (d (e j)))) w) (R.apply_symm_apply u)).trans
        (R.apply_symm_apply _).symm
  let F : (piTensor fun j => ρ (e j)).IntertwiningMap (cellFunctor f g (piTensor ρ)) :=
    { toFun := fun u => ⟨⟨fun x => Ψ ((piTensor fun j => ρ (e j)) x u), fun p x => by
          show Ψ ((piTensor fun j => ρ (e j)) (↑p * x) u) = _
          rw [map_mul, Module.End.mul_apply]
          exact (law p _).symm⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset ((hsm u).mem_nhds (by simp)) fun x hx => by
          have hx' : (piTensor fun j => ρ (e j)) x u = u := hx
          refine Subtype.ext (funext fun y => ?_)
          show Ψ ((piTensor fun j => ρ (e j)) (y * x) u) = Ψ ((piTensor fun j => ρ (e j)) y u)
          rw [map_mul, Module.End.mul_apply, hx'])⟩
      map_add' := fun u w => Subtype.ext (Subtype.ext (funext fun x => by simp))
      map_smul' := fun c u => Subtype.ext (Subtype.ext (funext fun x => by simp))
      isIntertwining' := fun h => LinearMap.ext fun u => Subtype.ext (Subtype.ext (funext fun x => by
        show Ψ ((piTensor fun j => ρ (e j)) x ((piTensor fun j => ρ (e j)) h u)) =
          Ψ ((piTensor fun j => ρ (e j)) (x * h) u)
        rw [map_mul, Module.End.mul_apply])) }
  refine ⟨(LocGL.equivOfBijective F ⟨fun u w hw => ?_, fun φ => ⟨Ψ.symm (φ.1.1 1),
    Subtype.ext (Subtype.ext (funext fun x => ?_))⟩⟩).symm⟩
  · have h1 : Ψ ((piTensor fun j => ρ (e j)) 1 u) = Ψ ((piTensor fun j => ρ (e j)) 1 w) :=
      congrArg (fun φ => φ.1.1 1) hw
    simpa using h1
  · show Ψ ((piTensor fun j => ρ (e j)) x (Ψ.symm (φ.1.1 1))) = φ.1.1 x
    refine (law ⟨x, hP x⟩ (Ψ.symm (φ.1.1 1))).symm.trans ?_
    refine (congrArg (τ ⟨x, hP x⟩) (Ψ.apply_symm_apply (φ.1.1 1))).trans ?_
    refine (φ.1.2 ⟨x, hP x⟩ 1).symm.trans ?_
    exact congrArg φ.1.1 (mul_one x)

theorem isIrreducible_piTensor (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {β : Type} [Fintype β]
    (x : β → IrrGL k) : (piTensor fun j => (x j).rep).IsIrreducible := by
  exact GlobalTheory.ExtTensorIrr.piTensor_isIrreducible GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k β
    (fun j => Fin (x j).1) (fun j => (x j).2.rep)

theorem jhMult_cell_comp (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {l c : ℕ} (x : Fin l → IrrGL k)
    (e : Fin c ≃ Fin l)
    (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (x (e j)).1))
    (hb : ∀ i j, b.1 i j = if e j = i then (x i).1 else 0) :
    ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (x i).1) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (x (e j)).1),
      jhMult (piTensor fun j => (x (e j)).rep) (cellFunctor f g (piTensor fun i => (x i).rep)) = 1 := by
  have T4 := @cell_bij k _ _ _ _ (Fin l) (Fin c) _ _ _ _ e (fun i => (x i).1)
    (fun i => (x i).2.rep.V) _ _ (fun i => (x i).rep) (fun i => (x i).2.rep.smooth) b hb
  obtain ⟨f, hf⟩ := T4
  obtain ⟨g, hg⟩ := hf
  refine ⟨f, g, ?_⟩
  have h1 := jhMult_self (isIrreducible_piTensor hA fun j => x (e j))
  have h2 := jhMult_of_nonempty (piTensor fun j => (x (e j)).rep) hg
  exact h2.trans h1

theorem jhMult_cell_bij : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL →
    ∀ {l c : ℕ} (x : Fin l → IrrGL k) (y : Fin c → IrrGL k) (e : Fin c ≃ Fin l),
      (∀ a, y a = x (e a)) →
      ∀ (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1)),
        (∀ i j, b.1 i j = if e j = i then (x i).1 else 0) →
        ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (x i).1) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (y j).1),
          jhMult (piTensor fun j => (y j).rep) (cellFunctor f g (piTensor fun i => (x i).rep)) = 1 := by
  intro k _ _ _ _ hA l c x y e hy b hb
  obtain rfl : y = fun a => x (e a) := funext hy
  exact jhMult_cell_comp hA x e b hb

end GlobalTheory.CompanionTheory.CellBij

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportInducedFunctionClosed
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

theorem isClosed_support_smooth_ind {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {W₁ : Type}
    [AddCommGroup W₁] [Module ℂ W₁] {Q : Subgroup G} (σ : Representation ℂ Q W₁) (f : smoothPart (ind Q σ)) :
    IsClosed {g : G | f.1.1 g ≠ 0} := by
  have hT : IsOpen {g : G | ind Q σ g f.1 = f.1} := f.2
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro g hg
  have hg0 : f.1.1 g = 0 := by simpa using hg
  have hc : Continuous fun h : G => g⁻¹ * h := continuous_const.mul continuous_id
  have hm : {h : G | g⁻¹ * h ∈ {κ : G | ind Q σ κ f.1 = f.1}} ∈ 𝓝 g :=
    (hT.preimage hc).mem_nhds (by
      show ind Q σ (g⁻¹ * g) f.1 = f.1
      simp)
  filter_upwards [hm] with h hh
  have e : (ind Q σ (g⁻¹ * h) f.1).1 g = f.1.1 g := congrArg (fun F : indSpace Q σ => F.1 g) hh
  have e' : f.1.1 (g * (g⁻¹ * h)) = f.1.1 g := e
  rw [mul_inv_cancel_left] at e'
  simpa [e', hg0] using hg0

end GlobalTheory.CompanionTheory.BZRes
end

