import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiagMatLower
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0033
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0032
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsClosedFlagsIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniMatBlockTriangular
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0034
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
import Formalism.GL3MeanSquares.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0035

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdaptedFrameBigCell
section
open Module TopologicalSpace GlobalTheory.FlagPts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagPts.SphericalEisensteinCover

variable {k W : Type} [Field k] [AddCommGroup W] [Module k W]

theorem two_avoid (S H₁ H₂ : Submodule k W) (h₁ : ¬ S ≤ H₁) (h₂ : ¬ S ≤ H₂) :
    ∃ v ∈ S, v ∉ H₁ ∧ v ∉ H₂ := by
  obtain ⟨x, hxS, hx1⟩ := SetLike.not_le_iff_exists.1 h₁
  obtain ⟨y, hyS, hy2⟩ := SetLike.not_le_iff_exists.1 h₂
  by_cases hx2 : x ∈ H₂
  · by_cases hy1 : y ∈ H₁
    · refine ⟨x + y, S.add_mem hxS hyS, fun h => hx1 ?_, fun h => hy2 ?_⟩
      · simpa using H₁.sub_mem h hy1
      · simpa using H₂.sub_mem h hx2
    · exact ⟨y, hyS, hy1, hy2⟩
  · exact ⟨x, hxS, hx1, hx2⟩

theorem disj_sup (P G : Submodule k W) (v : W) (hPG : Disjoint P G) (hv : v ∉ P ⊔ G) :
    Disjoint P (G ⊔ k ∙ v) := by
  rw [Submodule.disjoint_def]
  intro x hxP hx
  obtain ⟨g, hg, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  by_cases hc : c = 0
  · subst hc
    rw [zero_smul, add_zero] at hxP ⊢
    exact Submodule.disjoint_def.1 hPG _ hxP hg
  · exfalso
    apply hv
    have h1 : g + c • v ∈ P ⊔ G := Submodule.mem_sup_left hxP
    have h2 : g ∈ P ⊔ G := Submodule.mem_sup_right hg
    have h3 : v = c⁻¹ • ((g + c • v) - g) := by
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [h3]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ h1 h2)

theorem finrank_sup_span [FiniteDimensional k W] (G : Submodule k W) (v : W) (hv : v ∉ G) :
    finrank k (G ⊔ k ∙ v : Submodule k W) = finrank k G + 1 := by
  have hv0 : v ≠ 0 := fun h => hv (h ▸ G.zero_mem)
  have h := Submodule.finrank_sup_add_finrank_inf_eq G (k ∙ v)
  rw [((Submodule.disjoint_span_singleton' hv0).2 hv).eq_bot, finrank_bot, add_zero,
    finrank_span_singleton hv0] at h
  exact h

theorem not_le_of_finrank [FiniteDimensional k W] (B H G : Submodule k W) (hGB : ¬ G ≤ B) (hGH : G ≤ H)
    (hd : finrank k H ≤ finrank k B) : ¬ B ≤ H := fun hBH => hGB
  (hGH.trans (Submodule.eq_of_le_of_finrank_le hBH hd).symm.le)

variable (k) in

def spanFrom (f : ℕ → W) (N m : ℕ) : Submodule k W := Submodule.span k (f '' {a | m ≤ a ∧ a < N})

theorem spanFrom_update_of_lt (f : ℕ → W) (N m m' : ℕ) (v : W) (h : m < m') :
    spanFrom k (Function.update f m v) N m' = spanFrom k f N m' := by
  unfold spanFrom
  congr 1
  refine Set.image_congr fun a ha => ?_
  rw [Function.update_of_ne]
  exact (lt_of_lt_of_le h ha.1).ne'

theorem spanFrom_update_self (f : ℕ → W) (N m : ℕ) (v : W) (h : m < N) :
    spanFrom k (Function.update f m v) N m = spanFrom k f N (m + 1) ⊔ k ∙ v := by
  rw [← spanFrom_update_of_lt (k := k) f N m (m + 1) v (Nat.lt_succ_self m)]
  unfold spanFrom
  have : {a | m ≤ a ∧ a < N} = insert m {a | m + 1 ≤ a ∧ a < N} := by
    ext a; simp only [Set.mem_setOf_eq, Set.mem_insert_iff]; omega
  rw [this, Set.image_insert_eq, Submodule.span_insert, Function.update_self, sup_comm]

theorem spanFrom_ge (f : ℕ → W) (N m : ℕ) (h : N ≤ m) : spanFrom k f N m = ⊥ := by
  unfold spanFrom
  have : {a | m ≤ a ∧ a < N} = ∅ := by ext a; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_lt]; omega
  rw [this, Set.image_empty, Submodule.span_empty]

end GlobalTheory.FlagPts.SphericalEisensteinCover

namespace GlobalTheory.FlagPts.SphericalEisensteinCover

variable {k W : Type} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]

theorem mem_spanFrom_update (f : ℕ → W) (N m : ℕ) (v : W) (h : m < N) :
    v ∈ spanFrom k (Function.update f m v) N m := by
  rw [spanFrom_update_self f N m v h]
  exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)

theorem image_fin (f : ℕ → W) (N m : ℕ) :
    (fun i : Fin N => f i) '' {a : Fin N | m ≤ (a : ℕ)} = f '' {a | m ≤ a ∧ a < N} := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ⟨ha, a.2⟩, rfl⟩
  · rintro ⟨a, ⟨h1, h2⟩, rfl⟩
    exact ⟨⟨a, h2⟩, h1, rfl⟩

def Inv (Fs : ℕ → Submodule k W) (A : Submodule k W) (f : ℕ → W) (m : ℕ) : Prop :=
  ∀ m', m ≤ m' → Disjoint (Fs m') (spanFrom k f (finrank k W) m') ∧
    Disjoint A (spanFrom k f (finrank k W) m') ∧
    finrank k (spanFrom k f (finrank k W) m') = finrank k W - m'

theorem step_core (Fs : ℕ → Submodule k W) (hmono : ∀ m, Fs m ≤ Fs (m + 1)) (A : Submodule k W)
    (f : ℕ → W) (m : ℕ) (hmN : m < finrank k W) (v : W)
    (hv1 : v ∉ Fs m ⊔ spanFrom k f (finrank k W) (m + 1))
    (hv2 : v ∉ A ⊔ spanFrom k f (finrank k W) (m + 1)) (hinv : Inv Fs A f (m + 1)) :
    Inv Fs A (Function.update f m v) m := by
  intro m' hm'
  rcases hm'.eq_or_lt with rfl | hlt
  · rw [spanFrom_update_self f _ _ v hmN]
    obtain ⟨h1, h2, h3⟩ := hinv (_ + 1) le_rfl
    refine ⟨disj_sup _ _ _ (Disjoint.mono_left (hmono _) h1) hv1, disj_sup _ _ _ h2 hv2, ?_⟩
    rw [finrank_sup_span _ _ (fun h => hv2 (Submodule.mem_sup_right h)), h3]
    omega
  · rw [spanFrom_update_of_lt f _ _ _ v hlt]
    exact hinv m' hlt

theorem exists_basis (Fs : ℕ → Submodule k W) (hmono : ∀ m, Fs m ≤ Fs (m + 1))
    (hdim : ∀ m, finrank k (Fs m) = min m (finrank k W)) (A B : Submodule k W) (hN : 2 ≤ finrank k W)
    (hAB : A ≤ B) (hA : finrank k A = 1) (hB : finrank k B + 1 = finrank k W) :
    ∃ b : Basis (Fin (finrank k W)) k W, (∀ a : Fin (finrank k W), (a : ℕ) = 0 → b a ∈ A) ∧
      (∀ a : Fin (finrank k W), (a : ℕ) + 1 < finrank k W → b a ∈ B) ∧
      ∀ m, Disjoint (Fs m) (Submodule.span k (b '' {a : Fin (finrank k W) | m ≤ (a : ℕ)})) := by
  set N := finrank k W with hNdef
  let Q : ℕ → Prop := fun m => ∃ f : ℕ → W, ¬ spanFrom k f N m ≤ B ∧
    (∀ a, m ≤ a → a + 1 < N → f a ∈ B) ∧ Inv Fs A f m
  have base : Q (N - 1) := by
    have hF : ¬ (⊤ : Submodule k W) ≤ Fs (N - 1) := fun h => by
      have := Submodule.finrank_mono h
      rw [finrank_top, hdim] at this
      omega
    have hBt : ¬ (⊤ : Submodule k W) ≤ B := fun h => by
      have := Submodule.finrank_mono h
      rw [finrank_top] at this
      omega
    obtain ⟨v, -, hv1, hvB⟩ := two_avoid ⊤ _ _ hF hBt
    let f0 : ℕ → W := fun _ => 0
    have hG : spanFrom k f0 N (N - 1 + 1) = ⊥ := spanFrom_ge f0 N _ (by omega)
    refine ⟨Function.update f0 (N - 1) v, fun h => hvB (h (mem_spanFrom_update f0 N _ v (by omega))),
      fun a h1 h2 => by omega, step_core Fs hmono A f0 (N - 1) (by omega) v ?_ ?_ ?_⟩
    · rw [hG, sup_bot_eq]; exact hv1
    · rw [hG, sup_bot_eq]; exact fun h => hvB (hAB h)
    · intro m' hm'
      rw [spanFrom_ge f0 N m' (by omega)]
      refine ⟨disjoint_bot_right, disjoint_bot_right, ?_⟩
      rw [finrank_bot]
      omega
  have step : ∀ m, 1 ≤ m → m + 1 < N → Q (m + 1) → Q m := by
    rintro m hm1 hmN ⟨f, hfB, hmem, hinv⟩
    set G := spanFrom k f N (m + 1) with hGdef
    obtain ⟨-, -, hGd⟩ := hinv (m + 1) le_rfl
    have h1 : ¬ B ≤ Fs m ⊔ G := by
      refine not_le_of_finrank B _ G hfB le_sup_right ?_
      have := Submodule.finrank_add_le_finrank_add_finrank (Fs m) G
      rw [hdim, hGd] at this
      have : min m N = m := min_eq_left (by omega)
      omega
    have h2 : ¬ B ≤ A ⊔ G := by
      refine not_le_of_finrank B _ G hfB le_sup_right ?_
      have := Submodule.finrank_add_le_finrank_add_finrank A G
      rw [hA, hGd] at this
      omega
    obtain ⟨v, hvB, hv1, hv2⟩ := two_avoid B _ _ h1 h2
    refine ⟨Function.update f m v, fun h => hfB ?_, fun a ha1 ha2 => ?_,
      step_core Fs hmono A f m (by omega) v hv1 hv2 hinv⟩
    · rw [spanFrom_update_self f N m v (by omega)] at h
      exact le_sup_left.trans h
    · rcases ha1.eq_or_lt with rfl | hlt
      · rw [Function.update_self]; exact hvB
      · rw [Function.update_of_ne hlt.ne']; exact hmem a hlt ha2
  have all : ∀ t, t + 2 ≤ N → Q (N - 1 - t) := by
    intro t
    induction t with
    | zero => intro _; simpa using base
    | succ t ih =>
      intro ht
      have := step (N - 1 - (t + 1)) (by omega) (by omega)
      rw [show N - 1 - (t + 1) + 1 = N - 1 - t by omega] at this
      exact this (ih (by omega))
  obtain ⟨f, -, hmem, hinv⟩ : Q 1 := by
    have := all (N - 2) (by omega)
    rwa [show N - 1 - (N - 2) = 1 by omega] at this
  have hAne : A ≠ ⊥ := fun h => by rw [h, finrank_bot] at hA; omega
  obtain ⟨a, haA, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hAne
  obtain ⟨-, hA1, hd1⟩ := hinv 1 le_rfl
  have haG : a ∉ spanFrom k f N 1 := fun h => ha0 (Submodule.disjoint_def.1 hA1 a haA h)
  have hF0 : Fs 0 = ⊥ := Submodule.finrank_eq_zero.1 (by rw [hdim]; simp)
  set f' := Function.update f 0 a with hf'
  have htop : spanFrom k f' N 0 = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hf', spanFrom_update_self f N 0 a (by omega), finrank_sup_span _ _ haG]
    change finrank k (spanFrom k f (finrank k W) 1) + 1 = _
    omega
  have hdisj : ∀ m, Disjoint (Fs m) (spanFrom k f' N m) := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [hF0]; exact disjoint_bot_left
    · rw [hf', spanFrom_update_of_lt f N 0 m a hm]
      exact (hinv m hm).1
  have hspan : ⊤ ≤ Submodule.span k (Set.range (fun i : Fin N => f' i)) := by
    rw [← Set.image_univ, show (Set.univ : Set (Fin N)) = {a : Fin N | 0 ≤ (a : ℕ)} by ext; simp, image_fin]
    exact htop.ge
  refine ⟨basisOfTopLeSpanOfCardEqFinrank (fun i : Fin N => f' i) hspan (Fintype.card_fin _), fun i hi => ?_,
    fun i hi => ?_, fun m => ?_⟩
  · rw [coe_basisOfTopLeSpanOfCardEqFinrank]
    simp only [hi, hf', Function.update_self]
    exact haA
  · rw [coe_basisOfTopLeSpanOfCardEqFinrank]
    rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hpos
    · simp only [h0, hf', Function.update_self]
      exact hAB haA
    · simp only [hf']
      rw [Function.update_of_ne hpos.ne']
      exact hmem i hpos hi
  · rw [coe_basisOfTopLeSpanOfCardEqFinrank, image_fin]
    exact hdisj m

end GlobalTheory.FlagPts.SphericalEisensteinCover

namespace GlobalTheory.FlagPts

end GlobalTheory.FlagPts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalEigenspaceSumSqInvariantFieldsAStatement
section
open MeasureTheory Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_eigenspace_sum_sq_invariantFields_alt : ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K] (L : Type) [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L] (S : Submodule ℂ (K → ℂ)), (∀ f ∈ S, Continuous f) → ∀ e : L → K, (∀ X : L, Continuous fun t : ℝ => e (t • X)) → e 0 = 1 → (∀ r : ℝ, 0 < r → e '' Metric.ball 0 r ∈ 𝓝 (1 : K)) → ∀ d : L → Module.End ℂ S, (∀ X Y, d (X + Y) = d X + d Y) → (∀ (a : ℝ) X, d (a • X) = (a : ℂ) • d X) → (∀ (X : L) (f : S) (x : K) (t : ℝ), HasDerivAt (fun t : ℝ => f.1 (x * e (t • X))) ((d X f).1 (x * e (t • X))) t) → ∀ (ι : Type) [Fintype ι] (X : ι → L), Submodule.span ℝ (Set.range X) = ⊤ → ∀ lam : ℂ, FiniteDimensional ℂ (Module.End.eigenspace (∑ i, d (X i) * d (X i)) lam) := by
  first | exact @GlobalTheory.finiteDimensional_eigenspace_sum_sq_invariantFields | exact GlobalTheory.finiteDimensional_eigenspace_sum_sq_invariantFields | (intros; apply GlobalTheory.finiteDimensional_eigenspace_sum_sq_invariantFields <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankEigenspaceEmbeddingOne
section
open scoped TensorProduct NumberField
open GlobalTheory.EigenSplit

namespace GlobalTheory
namespace EigenSplit

section RankOne

variable {E : Type} [Field E] [NumberField E] {K : Type} [CommRing K]

theorem baseChangeAction_toModuleEnd_apply (a : 𝓞 E) (x : K ⊗[ℤ] 𝓞 E) :
    baseChangeAction K (Module.toModuleEnd ℤ (𝓞 E) : 𝓞 E →+* Module.End ℤ (𝓞 E)) a x
      = (1 ⊗ₜ a) * x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r b => simp
  | add x y hx hy => simp only [map_add, mul_add, hx, hy]

theorem tensorAction_baseChangeAction_toModuleEnd (t x : K ⊗[ℤ] 𝓞 E) :
    tensorAction (baseChangeAction K
      (Module.toModuleEnd ℤ (𝓞 E) : 𝓞 E →+* Module.End ℤ (𝓞 E))) t x = t * x := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r a =>
    rw [tensorAction_tmul, baseChangeAction_toModuleEnd_apply, ← smul_mul_assoc,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add s t hs ht => simp [add_mul, hs, ht]

variable {ι : Type} [DecidableEq ι] {τ : ι → 𝓞 E →+* K}

theorem idem_ne_zero [Nontrivial K] (h : IsSplitting τ) (i : ι) : idem h i ≠ 0 := by
  intro h0
  have := congrFun (splitMap_idem h i) i
  rw [h0, map_zero] at this
  simp at this

theorem eigenSub_toModuleEnd_eq_span (h : IsSplitting τ) (i : ι) :
    eigenSub (baseChangeAction K (Module.toModuleEnd ℤ (𝓞 E) : 𝓞 E →+* Module.End ℤ (𝓞 E)))
      (τ i) = Submodule.span K {idem h i} := by
  apply le_antisymm
  · intro x hx
    have h1 := tensorAction_of_mem (σ := τ) hx (idem h i)
    rw [tensorAction_baseChangeAction_toModuleEnd, splitMap_idem, Pi.single_eq_same, one_smul,
      mul_comm, mul_idem] at h1
    rw [← h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact mem_eigenSub.2 fun a => by rw [baseChangeAction_toModuleEnd_apply, one_tmul_mul_idem]

end RankOne

theorem finrank_eigenSub_toModuleEnd_eq_one_of_isSplitting {E V : Type} [Field E] [NumberField E]
    [CommRing V] [IsDomain V] [ValuationRing V] {ι : Type} [Fintype ι] [DecidableEq ι]
    (σ : ι → 𝓞 E →+* V) (K : Type) [Field K] [Algebra V K] [IsFractionRing V K]
    (h : IsSplitting fun i => (algebraMap V K).comp (σ i)) (i₀ : ι) :
    Module.finrank V (eigenSub (baseChangeAction V
      (Module.toModuleEnd ℤ (𝓞 E) : 𝓞 E →+* Module.End ℤ (𝓞 E))) (σ i₀)) = 1 := by
  have : FaithfulSMul V K :=
    (faithfulSMul_iff_algebraMap_injective V K).2 (IsFractionRing.injective V K)
  have : Module.Flat V K := flat_of_valuationRing V K
  rw [← finrank_eigenSub_of_flat (R' := K) (extendTensor_equivariant V K _)
    (isBaseChange_extendTensor ℤ V K (𝓞 E)) (σ i₀)]
  have hs := eigenSub_toModuleEnd_eq_span h i₀
  beta_reduce at hs
  rw [hs]
  exact finrank_span_singleton (idem_ne_zero h i₀)

theorem finrank_eigenSub_toModuleEnd_eq_one {E V : Type} [Field E] [NumberField E] [CommRing V]
    [IsDomain V] [ValuationRing V] [CharZero V]
    {ι : Type} [Fintype ι] (σ : ι → 𝓞 E →+* V) (hσ : Function.Injective σ)
    (hc : Fintype.card ι = Module.finrank ℚ E) (i₀ : ι) :
    Module.finrank V (eigenSub (baseChangeAction V
      (Module.toModuleEnd ℤ (𝓞 E) : 𝓞 E →+* Module.End ℤ (𝓞 E))) (σ i₀)) = 1 := by
  classical
  exact finrank_eigenSub_toModuleEnd_eq_one_of_isSplitting σ (FractionRing V)
    (isSplitting_fractionRing hσ hc) i₀

end EigenSplit
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlueOfDenseOpenImmersionStatement
section
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_extending_of_dense_openImmersion : ∀ {T Z : Scheme.{0}} [IsReduced Z] (j : T ⟶ Z) [IsOpenImmersion j], Dense (Set.range j) →
    ∀ (U : Z.Opens) (s : Γ(T, j ⁻¹ᵁ U)), (∀ u ∈ U, ∃ (W : Z.Opens) (hWU : W ≤ U), u ∈ W ∧
      ∃ h : Γ(Z, W), j.app W h = T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s) →
    ∃ h : Γ(Z, U), j.app U h = s := by
  first | exact @GlobalTheory.glue_of_dense_openImmersion | exact GlobalTheory.glue_of_dense_openImmersion | (intros; apply GlobalTheory.glue_of_dense_openImmersion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InjectiveCellMap
section
set_option autoImplicit false

noncomputable section

open Module TopologicalSpace

namespace GlobalTheory.FlagPts

theorem toMatrix_cellFrame {k : Type} [Field k] {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] (b : Frames k V) (u : AffPts k (CellIdx k V)) (i : ι) :
    (b i).toMatrix (cellFrame b u i) = uniMat u i := by
  ext a c
  rw [Basis.toMatrix_apply, cellFrame_apply, map_sum]
  simp [Finsupp.single_apply]

theorem cellMap_injective (k : Type) [Field k] (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (b : Frames k V) :
    Function.Injective (cellMap b) := by
  intro u u' h
  have key : ∀ i, uniMat u i = uniMat u' i := by
    intro i
    have hflag : (cellFrame b u i).flag = (cellFrame b u' i).flag :=
      congrArg FullFlag.sub (congrFun h i)
    set B := cellFrame b u i
    set B' := cellFrame b u' i
    set Y := B.toMatrix B'
    have hmul : uniMat u i * Y = uniMat u' i := by
      rw [← toMatrix_cellFrame b u i, ← toMatrix_cellFrame b u' i, Basis.toMatrix_mul_toMatrix]
    have hup : ∀ j c, c < j → Y j c = 0 := by
      intro j c hcj
      have hm : B' c ∈ B'.flag c.succ := B'.self_mem_flag Fin.castSucc_lt_succ
      rw [← hflag] at hm
      exact (mem_basis_flag_iff B _ _).1 hm j (Fin.succ_le_castSucc_iff.mpr hcj)
    have hdet : IsUnit (uniMat u i).det := by rw [det_uniMat]; exact isUnit_one
    have hY : Y = (uniMat u i)⁻¹ * uniMat u' i := by
      rw [← hmul, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
    have hlow : ∀ j c, j < c → Y j c = 0 := by
      letI := (uniMat u i).invertibleOfIsUnitDet hdet
      have h1 := Matrix.blockTriangular_inv_of_blockTriangular (uniMat_blockTriangular u i)
      have h2 := h1.mul (uniMat_blockTriangular u' i)
      intro j c hjc
      rw [hY]
      exact h2 (by simpa using hjc)
    have hdiag : ∀ c, Y c c = 1 := by
      intro c
      have := congrFun (congrFun hmul c) c
      rw [Matrix.mul_apply, Finset.sum_eq_single c, uniMat_apply_self, uniMat_apply_self, one_mul] at this
      · exact this
      · intro j _ hj
        rcases lt_or_gt_of_ne hj with hj | hj
        · rw [hlow j c hj, mul_zero]
        · rw [hup j c hj, mul_zero]
      · intro hc; exact absurd (Finset.mem_univ c) hc
    have hY1 : Y = 1 := by
      ext j c
      rcases lt_trichotomy j c with hjc | rfl | hjc
      · rw [hlow j c hjc, Matrix.one_apply_ne hjc.ne]
      · rw [hdiag, Matrix.one_apply_eq]
      · rw [hup j c hjc, Matrix.one_apply_ne hjc.ne']
    rw [← hmul, hY1, Matrix.mul_one]
  funext x
  obtain ⟨i, ⟨a, c⟩, hac⟩ := x
  have := congrFun (congrFun (key i) a) c
  rwa [uniMat_apply_of_lt u i hac, uniMat_apply_of_lt u' i hac] at this

end GlobalTheory.FlagPts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherianStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNoetherianRing_adicCompletion_of_noetherian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsNoetherianRing (AdicCompletion I R) := by
  first | exact @GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion | exact GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion | (intros; apply GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRegularLocalRingAdicCompletion
section
open IsLocalRing

namespace GlobalTheory.RegularCompletion

theorem isRegularLocalRing_adicCompletion :
    ∀ (T : Type) [CommRing T] [IsRegularLocalRing T],
      IsRegularLocalRing (AdicCompletion (maximalIdeal T) T) := by
  intro T _ _
  haveI : IsNoetherianRing (AdicCompletion (maximalIdeal T) T) :=
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion T (maximalIdeal T)
  set S := AdicCompletion (maximalIdeal T) T

  obtain ⟨s, hcard, hs⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank (maximalIdeal T).fg_of_isNoetherianRing
  set xs := s.toList
  have hofl : Ideal.ofList xs = maximalIdeal T := by
    rw [← hs]; unfold Ideal.ofList; congr 1; ext x; simp [xs]
  have hlen : xs.length = (maximalIdeal T).spanFinrank := by simp [xs, hcard]
  have hreg : RingTheory.Sequence.IsRegular T xs := GlobalTheory.isRegular_of_length_eq_spanFinrank hofl hlen
  have hmem : ∀ r ∈ xs.map (algebraMap T S), r ∈ maximalIdeal S := by
    intro r hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.mem_map_of_mem _ (hofl ▸ Ideal.subset_span hx)
  have hregS : RingTheory.Sequence.IsRegular S (xs.map (algebraMap T S)) :=
    (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem).mpr
      (hreg.toIsWeaklyRegular.of_flat)
  have hdim := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular _ hregS
  have hnt : Nontrivial (S ⧸ Ideal.ofList (xs.map (algebraMap T S))) := by
    rw [Ideal.Quotient.nontrivial_iff]
    intro htop
    apply hregS.2
    simp [htop]
  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
  rw [AdicCompletion.spanFinrank_maximalIdeal_eq, ← hdim]
  have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (S ⧸ Ideal.ofList (xs.map (algebraMap T S))) :=
    ringKrullDim_nonneg_of_nontrivial
  rw [List.length_map, hlen]
  calc ((Submodule.spanFinrank (maximalIdeal T) : ℕ) : WithBot ℕ∞)
      = 0 + ((Submodule.spanFinrank (maximalIdeal T) : ℕ) : WithBot ℕ∞) := (zero_add _).symm
    _ ≤ _ := add_le_add_left h0 _

end GlobalTheory.RegularCompletion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeThetaAsymptoticsStatement
section
open Complex Filter Asymptotics
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_theta_asymptotics : ∀ (w₁ w₂ x₀ : ℂ), (starRingEnd ℂ w₁ * w₂).im ≠ 0 → (∀ m n : ℤ, x₀ + m * w₁ + n * w₂ ≠ 0) → ∃ c : ℝ, 0 < c ∧ (fun t : ℝ => ∑' p : ℤ × ℤ, Real.exp (-Real.pi * t * ‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2)) =O[atTop] (fun t => Real.exp (-c * t)) ∧ (fun t : ℝ => (∑' p : ℤ × ℤ, Real.exp (-Real.pi * t * ‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2)) - 1 / (t * |(starRingEnd ℂ w₁ * w₂).im|)) =O[nhdsWithin 0 (Set.Ioi 0)] (fun t => Real.exp (-c / t)) := by
  first | exact @GlobalTheory.PlaneTheta.theta_asymptotics | exact GlobalTheory.PlaneTheta.theta_asymptotics | (intros; apply GlobalTheory.PlaneTheta.theta_asymptotics <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalLocalIsLocalisationOfFiniteOverPolynomialAStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_and_isLocalization_of_finite_over_mvPolynomial : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [CharZero A] [Algebra.EssFiniteType ℤ A], ∃ (r : ℕ) (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsIntegrallyClosed B) (_ : Algebra (MvPolynomial (Fin r) ℤ) B) (_ : Module.Finite (MvPolynomial (Fin r) ℤ) B) (_ : Algebra B A) (𝔫 : Ideal B) (_ : 𝔫.IsPrime), Function.Injective (algebraMap (MvPolynomial (Fin r) ℤ) B) ∧ IsLocalization.AtPrime A 𝔫 := by
  first | exact @GlobalTheory.normal_local_is_localisation_of_finite_over_polynomial | exact GlobalTheory.normal_local_is_localisation_of_finite_over_polynomial | (intros; apply GlobalTheory.normal_local_is_localisation_of_finite_over_polynomial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiZeroConstOfIntegrableOn
section
open Finset ArithmeticFunction Filter Topology MeasureTheory Asymptotics
open Formalism.HermitianLattices.GL2PrimeSums Formalism.HermitianLattices.GL2a2

noncomputable section

namespace GlobalTheory.Mem.An.PsiZero

def err (u : ℝ) : ℝ := (psumR (fun n => Λ n) u - u) / u ^ 2

end GlobalTheory.Mem.An.PsiZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothOfFiniteDimensionalTranslationStableStatement
section
open MeasureTheory Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deriv_mem_and_contDiff_of_translation_stable : ∀ (G : Type) [Group G] (M : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ M] (ι : Type) (c : ι → ℝ → G), (∀ i s t, c i (s + t) = c i s * c i t) → (∀ i t, ∀ f ∈ M, (fun g => f (g * c i t)) ∈ M) → (∀ i, ∀ f ∈ M, ∀ g, Continuous fun t : ℝ => f (g * c i t)) → (∀ i, ∀ f ∈ M, (fun g => deriv (fun t : ℝ => f (g * c i t)) 0) ∈ M) ∧ ∀ (k : ℕ) (I : Fin k → ι), ∀ f ∈ M, ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun a => c (I a) (t a)).prod) := by
  first | exact @GlobalTheory.smooth_of_finiteDimensional_translation_stable | exact GlobalTheory.smooth_of_finiteDimensional_translation_stable | (intros; apply GlobalTheory.smooth_of_finiteDimensional_translation_stable <;> assumption)
end

