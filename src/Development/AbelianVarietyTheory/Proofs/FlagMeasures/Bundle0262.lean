import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0258
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
import Formalism.LocalToGlobal.HermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordOfMemXa
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerHaarUnimodularNormal
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairCommonUnipotentStabiliserSummary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0094
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairInnerLatticesUnimodularPrimitive
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0191
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0254
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0256
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LiftRowMiddleSpaceIntegralPoint
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0250
import Formalism.SharpRestriction.CuspSpanNormBounds.NonGenericAndKTwoTheorems
import Formalism.SharpRestriction.CuspSpanNormBounds.UniformConstantsAndStatements
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0257
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitalSquareEqHilbertSchmidtNormalisedVector
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLocalLevelUnitriangularIff
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.St.G.FirstColumn

section Abstract

variable {K A : Type} [Field K] [CommRing A] {n : ℕ}

theorem columns_iff (sp : A ≃+* K × K) (I : Subring A) (Λ : Submodule I (Fin n → A)) (O : Subring K) (g : ℕ)
    (hint : ∀ x, x ∈ I ↔ (sp x).1 ∈ O ∧ (sp x).2 ∈ O)
    (hΛ : ∀ y : Fin n → A, y ∈ Λ ↔ (∃ y₁ ∈ Λ, ∀ b, (sp (y₁ b)).1 = (sp (y b)).1) ∧
      ∃ y₂ ∈ Λ, ∀ b, (sp (y₂ b)).2 = (sp (y b)).2)
    (c : Fin n → Fin n → A) (hc : ∀ j, c j ∈ Λ) (hc2 : ∀ j a, (sp (c j a)).2 = 0)
    (fr fri : Matrix (Fin n) (Fin n) K) (hinv : fri * fr = 1) (hinv' : fr * fri = 1)
    (hfr0 : fr = Matrix.of (fun a j => (sp (c j a)).1))
    (hfr : ∀ x : Fin n → K, (∃ y ∈ Λ, ∀ a, (sp (y a)).1 = x a) ↔ ∀ a, (fri *ᵥ x) a ∈ O)
    (y : Matrix (Fin n) (Fin n) A) (hy : ∀ x ∈ Λ, y *ᵥ x ∈ Λ) :
    (∀ a b, (fri * y.map ((RingHom.fst K K).comp sp.toRingHom) * fr) a b ∈ O) ∧
    ((∀ i : Fin n, InModL Λ g (c '' {j | j.1 < i.1}) ((y - 1) *ᵥ c i)) ↔
      ∀ a b : Fin n, b ≤ a → ∃ w ∈ O,
        (fri * y.map ((RingHom.fst K K).comp sp.toRingHom) * fr) a b - (if a = b then 1 else 0) = (g : K) * w) := by
  set φ : A →+* K := (RingHom.fst K K).comp sp.toRingHom with hφ
  set ψ : A →+* K := (RingHom.snd K K).comp sp.toRingHom with hψ
  have hφa : ∀ x, φ x = (sp x).1 := fun _ => rfl
  have hψa : ∀ x, ψ x = (sp x).2 := fun _ => rfl
  set M := fri * y.map φ * fr with hM

  have hcol : ∀ j, (φ ∘ c j) = fr *ᵥ Pi.single j 1 := by
    intro j
    funext a
    rw [Matrix.mulVec_single_one, hfr0]
    rfl
  have hgen : ∀ (Z : Matrix (Fin n) (Fin n) A) (i : Fin n),
      fri *ᵥ (φ ∘ (Z *ᵥ c i)) = fun a => (fri * Z.map φ * fr) a i := by
    intro Z i
    have h1 : φ ∘ (Z *ᵥ c i) = Z.map φ *ᵥ (fr *ᵥ Pi.single i 1) := by
      funext a
      rw [← hcol i]
      exact RingHom.map_mulVec φ Z (c i) a
    rw [h1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
    rfl
  have hbasis : ∀ j, fri *ᵥ (φ ∘ c j) = Pi.single j 1 := by
    intro j
    rw [hcol j, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hmap1 : (y - 1).map φ = y.map φ - 1 := by
    ext a b
    simp [Matrix.one_apply, apply_ite φ]
  have hD : ∀ i, fri *ᵥ (φ ∘ ((y - 1) *ᵥ c i)) = fun a => M a i - if a = i then 1 else 0 := by
    intro i
    rw [hgen, hmap1, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hinv]
    funext a
    simp [Matrix.sub_apply, Matrix.one_apply, hM]
  have hMO : ∀ a b, M a b ∈ O := by
    intro a b
    have h := (hfr (φ ∘ (y *ᵥ c b))).1 ⟨y *ᵥ c b, hy _ (hc b), fun _ => rfl⟩ a
    rw [hgen] at h
    exact h
  refine ⟨hMO, ?_, ?_⟩
  · intro h a b hba
    have hspan : ∀ s ∈ Submodule.span I (c '' {j | j.1 < b.1}), (fri *ᵥ (φ ∘ s)) a = 0 := by
      intro s hs
      induction hs using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨j, hj, rfl⟩ := hx
        rw [hbasis j]
        have : a ≠ j := by
          intro h'
          subst h'
          exact absurd hba (not_le.2 hj)
        simp [Pi.single_apply, this]
      | zero =>
        have : (φ ∘ (0 : Fin n → A)) = 0 := by funext; simp
        rw [this]
        simp
      | add x x' _ _ hx hx' =>
        have : (φ ∘ (x + x')) = φ ∘ x + φ ∘ x' := by funext; simp
        rw [this, Matrix.mulVec_add, Pi.add_apply, hx, hx', add_zero]
      | smul r x _ hx =>
        have : (φ ∘ (r • x)) = φ (r : A) • (φ ∘ x) := by
          funext b
          simp [Subring.smul_def]
        rw [this, Matrix.mulVec_smul, Pi.smul_apply, hx, smul_zero]
    obtain ⟨s, hs, z, hz, e⟩ := h b
    have hs0 := hspan s hs
    refine ⟨(fri *ᵥ (φ ∘ z)) a, (hfr _).1 ⟨z, hz, fun _ => rfl⟩ a, ?_⟩
    have h1 : φ ∘ ((y - 1) *ᵥ c b) = φ ∘ s + (g : K) • (φ ∘ z) := by
      rw [e]
      funext b
      simp
    have h2 := congrFun (hD b) a
    rw [h1, Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, hs0, zero_add] at h2
    simpa using h2.symm
  · intro h i
    have h' : ∀ a : Fin n, ∃ w ∈ O, (i ≤ a → M a i - (if a = i then 1 else 0) = (g : K) * w) ∧ (a < i → w = 0) := by
      intro a
      by_cases hia : i ≤ a
      · obtain ⟨w, hw, e⟩ := h a i hia
        exact ⟨w, hw, fun _ => e, fun h'' => absurd h'' (not_lt.2 hia)⟩
      · exact ⟨0, O.zero_mem, fun h'' => absurd h'' hia, fun _ => rfl⟩
    choose W hWO hW hW0 using h'
    have hri : ∀ j, sp.symm (M j i, 0) ∈ I := by
      intro j
      rw [hint]
      simp only [RingEquiv.apply_symm_apply]
      exact ⟨hMO j i, O.zero_mem⟩
    have hz0 : ∀ a, ψ (sp.symm ((fr *ᵥ W) a, 0)) = 0 := by
      intro a
      simp [hψa]
    set z : Fin n → A := fun a => sp.symm ((fr *ᵥ W) a, 0) with hz
    have hzΛ : z ∈ Λ := by
      rw [hΛ]
      refine ⟨?_, 0, Λ.zero_mem, fun b => ?_⟩
      · obtain ⟨y₁, hy₁, e⟩ := (hfr (fr *ᵥ W)).2 (fun a => by
          rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
          exact hWO a)
        exact ⟨y₁, hy₁, fun b => by rw [e b]; simp [hz]⟩
      · simp [hz]
    set s : Fin n → A := ∑ j ∈ Finset.univ.filter (· < i), (⟨sp.symm (M j i, 0), hri j⟩ : I) • c j with hs
    have hsm : s ∈ Submodule.span I (c '' {j | j.1 < i.1}) := by
      refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, ?_, rfl⟩)
      simpa using hj
    have hs1 : φ ∘ s = fr *ᵥ (fun b => if b < i then M b i else 0) := by
      funext a
      show φ (s a) = _
      rw [hs, Finset.sum_apply, map_sum, Finset.sum_filter]
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hb : b < i
      · rw [if_pos hb, if_pos hb]
        show φ ((sp.symm (M b i, 0) : A) * c b a) = _
        rw [map_mul, hφa, RingEquiv.apply_symm_apply, hfr0, mul_comm]
        rfl
      · rw [if_neg hb, if_neg hb, mul_zero]
    have hs2 : ∀ a, ψ (s a) = 0 := by
      intro a
      rw [hs, Finset.sum_apply, map_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      show ψ ((sp.symm (M j i, 0) : A) * c j a) = 0
      rw [map_mul, hψa (c j a), hc2, mul_zero]
    have hcolD : φ ∘ ((y - 1) *ᵥ c i) = fr *ᵥ (fun b => if b < i then M b i else 0) + (g : K) • (fr *ᵥ W) := by
      have h1 : (fun a => M a i - if a = i then (1 : K) else 0) = (fun b => if b < i then M b i else 0) + (g : K) • W := by
        funext a
        by_cases hia : i ≤ a
        · have := hW a hia
          simp [not_lt.2 hia, this]
        · have hai := not_le.1 hia
          simp [hai, hW0 a hai, ne_of_lt hai]
      rw [← Matrix.mulVec_smul, ← Matrix.mulVec_add, ← h1, ← hD i, Matrix.mulVec_mulVec, hinv', Matrix.one_mulVec]
    refine ⟨s, hsm, z, hzΛ, ?_⟩
    funext a
    apply sp.injective
    refine Prod.ext ?_ ?_
    · have h1 : φ (((y - 1) *ᵥ c i) a) = (fr *ᵥ (fun b => if b < i then M b i else 0)) a + (g : K) * (fr *ᵥ W) a :=
        congrFun hcolD a
      have h2 : φ (s a) = (fr *ᵥ (fun b => if b < i then M b i else 0)) a := congrFun hs1 a
      have h3 : φ (z a) = (fr *ᵥ W) a := by simp [hz, hφa]
      show φ (((y - 1) *ᵥ c i) a) = φ (s a + (g : A) * z a)
      rw [map_add, map_mul, map_natCast, h1, h2, h3]
    · have h1 : ψ (((y - 1) *ᵥ c i) a) = 0 := by
        rw [RingHom.map_mulVec]
        have : ψ ∘ c i = 0 := by
          funext b
          exact hc2 i b
        rw [this, Matrix.mulVec_zero]
        rfl
      show ψ (((y - 1) *ᵥ c i) a) = ψ (s a + (g : A) * z a)
      rw [h1, map_add, map_mul, hs2 a, hz0 a, mul_zero, add_zero]

end Abstract

section Residue

theorem inJ_red_iff (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (g : ℕ)
    (hg : IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) =
      Ideal.span {((g : ℕ) : v.adicCompletionIntegers F)})
    {n : ℕ} (t : ℕ) (X : Matrix (Fin n) (Fin n) (v.adicCompletion F))
    (hX : ∀ a b, X a b ∈ v.adicCompletionIntegers F) :
    InJ n t n false (redM F v X) ↔ ∀ a b : Fin n, b ≤ a → ∃ w ∈ (v.adicCompletionIntegers F).toSubring,
      X a b - (if a = b then 1 else 0) = (g : v.adicCompletion F) * w := by
  have hiff : ∀ a b, (∃ w ∈ (v.adicCompletionIntegers F).toSubring,
      X a b - (if a = b then 1 else 0) = (g : v.adicCompletion F) * w) ↔
      redM F v X a b = if a = b then 1 else 0 := by
    intro a b
    have hred : redM F v X a b = IsLocalRing.residue _ ⟨X a b, hX a b⟩ := dif_pos (hX a b)
    obtain ⟨d, hd1, hd2⟩ : ∃ d : v.adicCompletionIntegers F,
        IsLocalRing.residue (v.adicCompletionIntegers F) d = (if a = b then 1 else 0) ∧
        (d : v.adicCompletion F) = if a = b then 1 else 0 := by
      by_cases h : a = b
      · exact ⟨1, by simp [h], by simp [h]⟩
      · exact ⟨0, by simp [h], by simp [h]⟩
    rw [hred, ← hd1, ← hd2, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, hg,
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨w, hw, e⟩
      refine ⟨⟨w, hw⟩, ?_⟩
      apply Subtype.ext
      show w * (g : v.adicCompletion F) = X a b - d
      rw [e, mul_comm]
    · rintro ⟨w, e⟩
      refine ⟨w, w.2, ?_⟩
      have h := congrArg Subtype.val e
      have h' : (w : v.adicCompletion F) * (g : v.adicCompletion F) = X a b - d := h
      rw [← h', mul_comm]
  have hblk : ∀ x : Fin n, blkOf n t x = x := fun x => if_pos x.2
  constructor
  · rintro ⟨h1, h2, -, -⟩ a b hba
    rw [hiff]
    rcases eq_or_lt_of_le hba with e | e
    · subst e
      rw [if_pos rfl]
      exact h2 b b.2
    · rw [if_neg e.ne']
      exact h1 a b (by rw [hblk, hblk]; exact e)
  · intro h
    refine ⟨fun x y hxy => ?_, fun x _ => ?_, fun x y hy => absurd y.2 (by omega), fun h' => by cases h'⟩
    · have hlt : y < x := by
        rw [hblk, hblk] at hxy
        exact hxy
      have h3 := (hiff x y).1 (h x y hlt.le)
      rwa [if_neg hlt.ne'] at h3
    · have h3 := (hiff x x).1 (h x x le_rfl)
      rwa [if_pos rfl] at h3

end Residue

theorem unitriangular_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → (∀ x, x ∈ intV E v ↔ (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F) → ∀ (g : ℕ), IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((g : ℕ) : v.adicCompletionIntegers F)} → ∀ (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → ∀ (c : Fin n → Fin n → E ⊗[F] v.adicCompletion F) (fr : GL (Fin n) (v.adicCompletion F)), (∀ j, c j ∈ loc v L) → (∀ j a, (sp (c j a)).2 = 0) → (fr : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = Matrix.of (fun a j => (sp (c j a)).1) → (∀ x : Fin n → v.adicCompletion F, (∃ y ∈ loc v L, ∀ a, (sp (y a)).1 = x a) ↔ ∀ a, ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x a ∈ v.adicCompletionIntegers F) → ∀ (t : ℕ), ∀ y ∈ levelVL cm.sig J v L, (∀ a b, ((fr⁻¹ * bc ((RingHom.fst _ _).comp sp.toRingHom) y * fr : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b ∈ v.adicCompletionIntegers F) ∧ ((∀ i : Fin n, InModL (loc v L) g (c '' {j | j.1 < i.1}) ((y.1 - 1) *ᵥ c i)) ↔ InJ n t n false (redM F v ((fr⁻¹ * bc ((RingHom.fst _ _).comp sp.toRingHom) y * fr : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)))) := by
  intro F E _ _ _ _ _ _ cm n J hH hJ v sp hsig halg hint g hg L hL c fr hc hc2 hfr0 hfr t y hy
  have hsplit := (GlobalTheory.St.G.split_components F E cm n J hH hJ v sp hsig halg).1 L
  have hy' : ∀ x ∈ loc v L, y.1 *ᵥ x ∈ loc v L := fun x hx => (hy.2 x).1 hx
  have hinv : ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * fr.1 = 1 :=
    Units.inv_mul fr
  have hinv' : fr.1 * ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = 1 :=
    Units.mul_inv fr
  obtain ⟨h1, h2⟩ := columns_iff sp (intV E v) (loc v L) (v.adicCompletionIntegers F).toSubring g hint hsplit c hc hc2
    fr.1 _ hinv hinv' hfr0 hfr y.1 hy'
  exact ⟨h1, h2.trans (inJ_red_iff F v g hg t _ h1).symm⟩

end GlobalTheory.St.G.FirstColumn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianStabiliserCovolumeLe
section
noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegVol.Cov

theorem covol_of_act {G α : Type} [Group G] [MeasurableSpace α] (act : G → α → α) (h1 : ∀ x, act 1 x = x)
    (h2 : ∀ s t x, act (s * t) x = act s (act t x)) (μ : Measure α) (R : Set α) (A B : Subgroup G) (Ω K : Set α)
    (hm : ∀ s, Measurable (act s)) (cA : Countable A) (cB : Countable B) (hR : μ Rᶜ = 0)
    (hinv : ∀ s ∈ A ⊔ B, (∀ x ∈ R, act s x ∈ R) ∧ μ.map (act s) = μ) (hAB : A.relIndex B ≠ 0) (hBA : B.relIndex A ≠ 0)
    (hΩ : MeasurableSet Ω) (hK : MeasurableSet K) (fA : ∀ x ∈ R, ∃! s, s ∈ A ∧ act s x ∈ Ω)
    (fB : ∀ x ∈ R, ∃! s, s ∈ B ∧ act s x ∈ K) : μ K = ENNReal.ofReal (GlobalTheory.HL.invVol A B) * μ Ω := by
  letI : MulAction G α := { smul := act, one_smul := h1, mul_smul := h2 }
  exact GlobalTheory.T.fundamental_set_measure_commensurable_index_ratio G α μ R A B Ω K hm cA cB hR hinv hAB hBA hΩ hK fA fB

theorem continuous_lmulM {k r : ℕ} (a : Mat k r) : Continuous (lmulM (k := k) (r := r) a) := by
  unfold lmulM
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem rset_mul {k r : ℕ} {γ : Mat k r} (hu : IsUnit γ.det) {a b : Mat k r} (ha : a ∈ Rset k r γ) (hb : b ∈ Rset k r γ) :
    a * b ∈ Rset k r γ := by
  refine ⟨WeylGroupFacts.mem_n_mul ha.1 hb.1, ?_⟩
  have e : γ * (a * b) * γ⁻¹ = (γ * a * γ⁻¹) * (γ * b * γ⁻¹) := by
    have : (γ * a * γ⁻¹) * (γ * b * γ⁻¹) = γ * a * (γ⁻¹ * γ) * b * γ⁻¹ := by simp only [Matrix.mul_assoc]
    rw [this, nonsing_inv_mul _ hu, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  rw [e]
  exact WeylGroupFacts.mem_n_mul ha.2 hb.2

theorem countable_aut (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] :
    Countable (V ≃ₗ[K] V) := by
  haveI : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable
  haveI : Countable V := (Module.finBasis K V).equivFun.injective.countable
  let b := Module.finBasis K V
  refine Function.Injective.countable (f := fun s : V ≃ₗ[K] V => fun i => s (b i)) fun s t e => ?_
  exact LinearEquiv.toLinearMap_injective (b.ext fun i => congrFun e i)

theorem cov_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (N : NF H r) (k : ℕ) (ι : Type) [Fintype ι] (σ : ι → (K →+* ℂ)) (β : Fin r → ℕ) (Φ : ι → V → Fin (2 * r + k + 1) → ℂ) (z z' : ι → Fin (2 * r + k + 1) → ℂ) (g : ι → Mat k r), IsPlaces σ → Module.finrank K V = 2 * r + k + 1 → (∀ v, IsFrameOf N k (σ v) (2 * Formalism.HermitianLatticesTheory.vInv K) β (Φ v) (z v) (z' v) (g v)) → (Ideal.absNorm N.𝔡 : ℝ) = (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * Fintype.card ι) → 1 ≤ Formalism.HermitianLatticesTheory.vInv K → ∀ (gg : ℕ) (Λ : Submodule (𝓞 K) V) (Kf : Set (ι → Mt k r)), 1 ≤ gg → N.IsTerm gg Λ → IsFund (realPts Φ (N.Gam Λ : Set (V ≃ₗ[K] V))) (RP k r g) Kf → Measure.pi (fun _ : ι => lebR0 k r N.j β) Kf ≤ ENNReal.ofReal (N.om Λ * (Formalism.HermitianLatticesTheory.vInv K ^ (k * (r - N.j) * Fintype.card ι) * (8 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * (r + 1) ^ 2 * Fintype.card ι))) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N k ι _ σ β Φ z z' g hP hd hF hN hv gg Λ Kf hgg hT hKf
  obtain ⟨hex, hsep, hsub, -⟩ := RealMat.real_points K V H hK r N k ι σ β Φ z z' g hP hd hF
  have hι : Nonempty ι := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
    exact ⟨(hP.2 w).choose⟩
  obtain ⟨v0⟩ := id hι
  choose m hm using fun s => (hex s).exists
  have hmu : ∀ (s : V ≃ₗ[K] V) (y : ι → Mt k r), (∀ v x, Matrix.of (y v) *ᵥ Φ v x = Φ v (s x)) → y = m s :=
    fun s y hy => (hex s).unique hy (hm s)
  have hH : ∀ v, IsHaarOn (Rset k r (g v)) (lebR0 k r N.j β) := fun v => by
    obtain ⟨-, hz, hz', hT0, ⟨c, hc⟩, -⟩ := hF v
    exact (GlobalTheory.Amp.StabHaar.lebesgue_haar_unimodular_stabilizer k r N.j N.j_le (z v) (z' v) (g v) β c hz hz' hT0 hc).1
  haveI : SigmaFinite (lebR0 k r N.j β) := (hH v0).1
  have hu : ∀ v, IsUnit (g v).det := fun v => RealMat.isUnit_det (hF v).2.2.2.2.1.choose_spec.1
  have hone : m 1 = fun _ => Matrix.of.symm (1 : Mat k r) :=
    (hmu 1 _ fun v x => by simp).symm
  have hmul : ∀ s t, m (s * t) = fun v => Matrix.of.symm (Matrix.of (m s v) * Matrix.of (m t v)) := fun s t =>
    (hmu (s * t) _ fun v x => by
      simp only [Equiv.apply_symm_apply]
      rw [← mulVec_mulVec, hm, hm]; rfl).symm
  have h1 : ∀ x : ι → Mt k r, mulP (m 1) x = x := fun x => by
    rw [hone]; funext v
    show (1 : Mat k r) * Matrix.of (x v) = x v
    rw [Matrix.one_mul]; rfl
  have h2 : ∀ s t (x : ι → Mt k r), mulP (m (s * t)) x = mulP (m s) (mulP (m t) x) := fun s t x => by
    rw [hmul]; funext v
    show (Matrix.of (m s v) * Matrix.of (m t v)) * Matrix.of (x v) = Matrix.of (m s v) * (Matrix.of (m t v) * Matrix.of (x v))
    rw [Matrix.mul_assoc]
  have hmeas : ∀ s, Measurable (mulP (k := k) (r := r) (m s)) := fun s =>
    measurable_pi_lambda _ fun v => (continuous_lmulM _).measurable.comp (measurable_pi_apply v)
  have hmR : ∀ s ∈ N.R, m s ∈ RP k r g := fun s hs => hsub ⟨s, hs, hm s⟩
  have hnull : Measure.pi (fun _ : ι => lebR0 k r N.j β) (RP k r g)ᶜ = 0 := by
    refine measure_mono_null (t := ⋃ v, Function.eval v ⁻¹' {x : Mt k r | Matrix.of x ∉ Rset k r (g v)}) ?_
      (measure_iUnion_null fun v => Measure.pi_eval_preimage_null _ (hH v).2.2.1)
    intro x hx
    simp only [RP, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hx
    obtain ⟨v, hv'⟩ := hx
    exact Set.mem_iUnion.2 ⟨v, hv'⟩
  have hpres : ∀ s ∈ N.R, (Measure.pi fun _ : ι => lebR0 k r N.j β).map (mulP (m s)) =
      Measure.pi fun _ : ι => lebR0 k r N.j β := fun s hs => by
    have e : ∀ v, (lebR0 k r N.j β).map (lmulM (Matrix.of (m s v))) = lebR0 k r N.j β :=
      fun v => (hH v).2.2.2 _ (hmR s hs v)
    haveI : ∀ v, SigmaFinite ((lebR0 k r N.j β).map (lmulM (Matrix.of (m s v)))) := fun v => by rw [e]; infer_instance
    have := Measure.pi_map_pi (μ := fun _ : ι => lebR0 k r N.j β)
      (f := fun v => lmulM (Matrix.of (m s v))) fun v => (continuous_lmulM _).measurable.aemeasurable
    simp only [e] at this
    exact this
  have conv : ∀ (Γ : Subgroup (V ≃ₗ[K] V)) (Ω : Set (ι → Mt k r)), IsFund (realPts Φ (Γ : Set (V ≃ₗ[K] V))) (RP k r g) Ω →
      ∀ x ∈ RP k r g, ∃! s, s ∈ Γ ∧ mulP (m s) x ∈ Ω := by
    intro Γ Ω h x hx
    obtain ⟨m0, ⟨⟨s, hs, hsm⟩, hΩ⟩, hun⟩ := h.2 x hx
    have e : m0 = m s := hmu s m0 hsm
    refine ⟨s, ⟨hs, e ▸ hΩ⟩, fun t ht => ?_⟩
    have e2 : m t = m0 := hun _ ⟨⟨t, ht.1, hm t⟩, ht.2⟩
    exact hsep t s hι fun v x => by rw [← hm t v x, ← hm s v x, e2, e]
  obtain ⟨hLU, -, hz1, -, hRefLat, -⟩ := GlobalTheory.DegCnt.InnerLat.main K V H hK r N gg Λ hgg hT
  have hzL : N.F.z ∈ latL N.F N.F' Λ := by
    have := (hz1 1).2 (Submodule.mem_one.2 ⟨1, map_one _⟩)
    simpa using this
  have hΛ : Submodule.IsLattice K Λ := ((GlobalTheory.HermLat.isUnimod_iff H Λ).1 hT.1.1).1
  obtain ⟨Ω, hΩ, -, hΩle⟩ := GlobalTheory.T.covolume_referenceLattice_stabiliser_bounds K V H hK r N k ι σ β Φ z z' g hP hd hF hN hv (latL N.F N.F' Λ) hLU hzL
  have hnil := (GlobalTheory.UnipStab.common_unipotent_stabiliser K V H hK r N).2.2.2.2
  have hc1 := (GlobalTheory.DegCnt.Unimod.invVol_smul K V N.R (2 * r + 1) hnil _ _ hRefLat hΛ).1
  have hc2 := (GlobalTheory.DegCnt.Unimod.invVol_smul K V N.R (2 * r + 1) hnil _ _ hΛ hRefLat).1
  haveI := countable_aut K V
  have key := covol_of_act (fun s x => mulP (m s) x) h1 h2 (Measure.pi fun _ : ι => lebR0 k r N.j β) (RP k r g)
    (N.Gam (N.Ref (latL N.F N.F' Λ))) (N.Gam Λ) Ω Kf hmeas inferInstance inferInstance hnull
    (fun s hs => by
      have hsR : s ∈ N.R := (sup_le inf_le_left inf_le_left : _ ≤ N.R) hs
      exact ⟨fun x hx v => rset_mul (hu v) (hmR s hsR v) (hx v), hpres s hsR⟩)
    hc1 hc2 hΩ.1 hKf.1 (conv _ _ hΩ) (conv _ _ hKf)
  have hom : 0 ≤ N.om Λ := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rw [key, ENNReal.ofReal_mul hom]
  exact mul_le_mul_right hΩle _

end GlobalTheory.DegVol.Cov
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerBesselFunctionalEqIntegralSubgroupStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inner_besselFunctional_eq_integral_subgroup : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, ∀ x : Mt k r, Matrix.of x ∈ GG k r → ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of x), Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)⟫_ℂ = ∫ s, coef σ u v (Matrix.of (lmulM (Matrix.of s) x)) * ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of (lmulM (Matrix.of s) x)), ξ⟫_ℂ ∂μS := by
  first | exact @GlobalTheory.SgInf.afun_inner_eq_integral | exact GlobalTheory.SgInf.afun_inner_eq_integral | (intros; apply GlobalTheory.SgInf.afun_inner_eq_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFdegFdegOfLowest
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace GlobalTheory.LowestVectorDegree

theorem isFdeg_fdegOf_lowest : ∀ (D : D7) (X : HidaSetting D) (v : InfinitePlace X.B.I.F),
    IsFdeg (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v)
      (fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)) :=
  fun _ X v => isFdeg_fdegOf_of_isDS (X.ds v) (X.low v).1

end GlobalTheory.LowestVectorDegree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LiftRowMiddleSpaceIntegralPointStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_row_middleSpace_integralPoint : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (a : Fin r) (l : InfinitePlace E → Fin (k + 1) → ℂ), l ∈ homLat (σ : E →+* E) J Λ P f A (dInv E (r - a.val)) (s a) → ∃ γ ∈ GN (σ : E →+* E) J Λ P, (∀ w, cM k r (.inr (.inl a)) (Matrix.of.symm (gM A γ w)) = l w) ∧ ∀ β : Bk r, β ≠ (.inr (.inl a)) → degB r β ≤ degB r (.inr (.inl a)) → ∀ w, cM k r β (Matrix.of.symm (gM A γ w)) = 0 := by
  first | exact @GlobalTheory.SnMass.VolN.RowLift.lift_row | exact GlobalTheory.SnMass.VolN.RowLift.lift_row | (intros; apply GlobalTheory.SnMass.VolN.RowLift.lift_row <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalNongenericBoundRecordFamily
section
open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem local_nongeneric_bound_record_family :
    ∀ (C : ℝ), 39 ≤ C → (∀ k r : ℕ, 4 * r + 7 ≤ k → Formalism.MainNotions.NonGenericAndKTwoTheorems.NonGenericLocalBound k r C) ∧
      (∀ D : D7, Formalism.MainNotions.NonGenericAndKTwoTheorems.Conclusion1 D C ∧ Formalism.MainNotions.NonGenericAndKTwoTheorems.NonGenericLocalBoundOfLargeRank D C ∧ Formalism.MainNotions.UniformConstantsAndStatements.adm5 D C) ∧
      ∀ {eps : ℝ} (Fm : FamP eps), Formalism.MainNotions.NonGenericAndKTwoTheorems.FamilyNonGenericLocalBound Fm C ∧ Formalism.MainNotions.UniformConstantsAndStatements.admF5 Fm C := by
  intro C hC
  have h1 : ∀ k r : ℕ, 4 * r + 7 ≤ k → Formalism.MainNotions.NonGenericAndKTwoTheorems.NonGenericLocalBound k r C := by
    intro k r hk F _ _ _ E _ _ _ _ M hM V _ _ H hV P hP
    exact GlobalTheory.T.hermitianDoubleCoset_amplitude_bound_local C hC M hM H r k P hk hV hP
  have h2 : ∀ D : D7, Formalism.MainNotions.NonGenericAndKTwoTheorems.Conclusion1 D C := fun D hk => h1 _ _ hk
  have h3 : ∀ D : D7, Formalism.MainNotions.UniformConstantsAndStatements.adm5 D C := fun D => h2 D
  exact ⟨h1, fun D => ⟨h2 D, h2 D, h3 D⟩, fun Fm => ⟨fun x i => h2 _, fun x i => h3 _⟩⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatrixCoeffMulInnerBesselFunctionalEqIntegralStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixCoeff_mul_inner_besselFunctional_eq_integral : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, ∀ y : Mt k r, Matrix.of y ∈ GG k r → coef σ u v (Matrix.of y) * ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y), ξ⟫_ℂ = ∫ t, coef σ u v (Matrix.of y) * star (coef σ u₁ v (Matrix.of t * Matrix.of y)) * ⟪PiS (psiGen k r z c) π (Matrix.of t)⁻¹ ξ, ξ⟫_ℂ ∂μS := by
  first | exact @GlobalTheory.SgInf.coef_mul_inner_Afun_eq_integral | exact GlobalTheory.SgInf.coef_mul_inner_Afun_eq_integral | (intros; apply GlobalTheory.SgInf.coef_mul_inner_Afun_eq_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormRootMeasureHaarUnimodularStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalFormRootMeasure_haar_unimodular : ∀ (k r : ℕ) (γ : Mat k r) (s : ℝ) (μR : Measure (Mt k r)), 0 < s → NormR k r γ s μR → IsClosedSub k r (Rset k r γ) ∧ IsHaarOn (Rset k r γ) μR ∧ IsUnimod (Rset k r γ) μR ∧ NormR k r γ⁻¹ s (μR.map (conjM γ)) := by
  first | exact @GlobalTheory.Amp.RootMeas.normR_facts | exact GlobalTheory.Amp.RootMeas.normR_facts | (intros; apply GlobalTheory.Amp.RootMeas.normR_facts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitalSquareEqHilbertSchmidtNormalisedVectorStatement
section
open Formalism.FourierDecayAlt Formalism.MainNotions.S GlobalTheory.ThA Formalism.QuantumDeterminants MeasureTheory Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitalSquare_eq_hilbertSchmidt_normalisedVector : ∃ c₃ : ℝ, ∀ (k r : ℕ) (L : LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (Bs : B.RealPlaceData k r L.Wp L.Wq) (cN A : ℝ) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (F : B.Mat k r → (L.Wq →L[ℂ] L.Wp)), IsStdOf L μsec Bs → IsRatioN k r cN → L.c = cStd → L.κN ≠ 0 → L.κN ≠ ⊤ → D.IsBaseFrame Bs ν' m₀ → c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A → B.InCC A 1 F → ∀ γ : Point ℂ (r + 1), 0 < ThB.Gpt (Tz k r L.z) (Tz k r L.z') γ → ThB.orbSq L F γ = ENNReal.ofReal ((L.κN.toReal * cN) ^ 4 * (Real.pi ^ (rootPat γ).card) ^ 2 * ‖B.hsVec (D.vecV Bs ν' m₀ F (γ.1.map fun b => (b.2, b.1)))‖ ^ 2) := by
  first | exact @GlobalTheory.ThA.OrbSq.orbSq_eq_vecV | exact GlobalTheory.ThA.OrbSq.orbSq_eq_vecV | (intros; apply GlobalTheory.ThA.OrbSq.orbSq_eq_vecV <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthTransversalFlagsInfIsotropicEqBotStatement
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orth_transversal_flags_inf_isotropic_eq_bot : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E) (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T'), Submodule.IsLattice E Λ → IsLift Λ F → IsLift Λ F' → Gval F F' ≠ 0 → Hp Λ F F' ≤ orth S (Xplus F) ∧ Hp Λ F F' ≤ orth S (Xplus F') ∧ Hp Λ F F' ⊓ Xsp F = ⊥ := by
  first | exact @GlobalTheory.LoopC.PerpFlags.main | exact GlobalTheory.LoopC.PerpFlags.main | (intros; apply GlobalTheory.LoopC.PerpFlags.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairIsometryUniqueOnOrthModIsotropicStatement
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_isometry_unique_on_orth_mod_isotropic : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E) (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (A B : LFlag S r T') (β₁ β₂ : S.V ≃ₗ[E] S.V), Submodule.IsLattice E Λ → Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ → 3 ≤ g → T' ≠ 0 → (∀ x ∈ orth S (Xplus A), x ∉ Xsp A → 0 < Algebra.trace ℚ E (S.hT x x)) → XLam Λ F ≤ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ A → XLam Λ F ≤ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ B → IsAutLam S Λ β₁ → (Xsp A).map (β₁ : S.V →ₗ[E] S.V) = Xsp B → β₁ A.fl.z - B.fl.z ∈ Xsp B → IotaCompat Λ F A B β₁ g → IsAutLam S Λ β₂ → (Xsp A).map (β₂ : S.V →ₗ[E] S.V) = Xsp B → β₂ A.fl.z - B.fl.z ∈ Xsp B → IotaCompat Λ F A B β₂ g → ∀ x ∈ orth S (Xsp A), β₁ x - β₂ x ∈ Xsp B := by
  first | exact @GlobalTheory.LoopC.BetaUniq.main | exact GlobalTheory.LoopC.BetaUniq.main | (intros; apply GlobalTheory.LoopC.BetaUniq.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RootMeasureEqNormalFormRootMeasureStatement
section
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootMeasure_eq_normalFormRootMeasure : ∀ (D : D7) (z z' : (Fin (2 * D.R.rS + D.R.k + 1) → ℂ)) (p : Point ℂ (D.R.rS + 1)) (γ : MatKR D.R.k D.R.rS) (μR : Measure (Mt D.R.k D.R.rS)) (θ' : ℝ), TwoFl D.R.k D.R.rS z z' γ → IsRootMeasR D z z' p γ μR → 0 ≤ θ' → 0 ≤ D.host.ka / gg D → (rootPat p).card ≤ D.R.rS ^ 2 ∧ NormR D.R.k D.R.rS γ (θ' * (2 * D.host.ka / gg D / (2 * Real.pi)) ^ (rootPat p).card) (ENNReal.ofReal θ' • μR) := by
  first | exact @GlobalTheory.Amp.RootNormal.rootMeas_normR | exact GlobalTheory.Amp.RootNormal.rootMeas_normR | (intros; apply GlobalTheory.Amp.RootNormal.rootMeas_normR <;> assumption)
end

