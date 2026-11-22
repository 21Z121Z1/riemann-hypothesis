import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0043
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0026
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0013
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0038
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0025

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOverStableSubmodulePiTensor
section
open scoped TensorProduct

namespace GlobalTheory.PiSimple

open GlobalTheory.TensHead

theorem simpleOver_of_equiv {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (e : V ≃ₗ[ℂ] W) (G : Set (Module.End ℂ V)) (G' : Set (Module.End ℂ W))
    (K : Submodule ℂ V) (K' : Submodule ℂ W) (hK : K.map (e : V →ₗ[ℂ] W) = K')
    (hG : ∀ g' ∈ G', ∃ g ∈ G, ∀ x, g' (e x) = e (g x)) (h : SimpleOver G' K') :
    SimpleOver G K := by
  intro N hN hKN
  have hs : Stab G' (N.map (e : V →ₗ[ℂ] W)) := by
    rintro g' hg' _ ⟨x, hx, rfl⟩
    obtain ⟨g, hg, hc⟩ := hG g' hg'
    exact ⟨g x, hN g hg x hx, by simpa using (hc x).symm⟩
  have hle : K' ≤ N.map (e : V →ₗ[ℂ] W) := hK ▸ Submodule.map_mono hKN
  have key : ∀ P : Submodule ℂ V, (P.map (e : V →ₗ[ℂ] W)).comap (e : V →ₗ[ℂ] W) = P := by
    intro P; ext x; simp
  rcases h _ hs hle with h1 | h1
  · left
    have := congrArg (Submodule.comap (e : V →ₗ[ℂ] W)) h1
    rwa [← hK, key, key] at this
  · right
    have := congrArg (Submodule.comap (e : V →ₗ[ℂ] W)) h1
    rwa [key, Submodule.comap_top] at this

def PP (σ : Type) : Prop :=
  ∀ [DecidableEq σ] (M : σ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (Op : ∀ i, Set (Module.End ℂ (M i))) (K : ∀ i, Submodule ℂ (M i)),
    (∀ i, Module.rank ℂ (M i) ≤ Cardinal.aleph0) → (∀ i, Stab (Op i) (K i)) →
    (∀ i, SimpleOver (Op i) (K i)) → SimpleOver (piOps Op) (piKer K)

theorem pp_empty : PP PEmpty := by
  intro _ M _ _ Op K _ _ _
  refine simpleOver_of_equiv (PiTensorProduct.isEmptyEquiv PEmpty) _ (∅ : Set (Module.End ℂ ℂ))
    _ ⊥ ?_ (by simp) ?_
  · have : piKer K = ⊥ := by
      rw [piKer, Submodule.span_eq_bot]
      rintro _ ⟨y, ⟨i, _⟩, _⟩
      exact i.elim
    rw [this, Submodule.map_bot]
  · intro N _ _
    rcases Ideal.eq_bot_or_top (N : Ideal ℂ) with h | h
    · exact Or.inl h
    · exact Or.inr h

theorem pp_unit : PP PUnit := by
  intro _ M _ _ Op K _ _ hso
  let e := PiTensorProduct.subsingletonEquiv (R := ℂ) (s := M) PUnit.unit
  refine simpleOver_of_equiv e _ (Op PUnit.unit) _ (K PUnit.unit) ?_ ?_ (hso _)
  · apply le_antisymm
    · rw [piKer, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨y, ⟨i, hi⟩, rfl⟩, rfl⟩
      cases i
      simpa [e] using hi
    · intro x hx
      refine ⟨e.symm x, Submodule.subset_span ⟨_, ⟨PUnit.unit, by simpa using hx⟩, rfl⟩, by simp⟩
  · intro g hg
    refine ⟨piOp PUnit.unit g, ⟨PUnit.unit, g, hg, rfl⟩, fun x => ?_⟩
    have H : g ∘ₗ (e : _ →ₗ[ℂ] M PUnit.unit) = (e : _ →ₗ[ℂ] M PUnit.unit) ∘ₗ piOp PUnit.unit g := by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro y
      simp [e, piOp, PiTensorProduct.map_tprod]
    exact LinearMap.congr_fun H x

theorem pp_of_equiv {σ ι : Type} (f : σ ≃ ι) (hσ : PP σ) : PP ι := by
  intro _ M _ _ Op K hr hs hso
  classical
  have H := hσ (fun s => M (f s)) (fun s => Op (f s)) (fun s => K (f s)) (fun s => hr _)
    (fun s => hs _) (fun s => hso _)
  refine simpleOver_of_equiv (PiTensorProduct.reindex ℂ M f.symm) _ _ _ _ ?_ ?_ H
  · apply le_antisymm
    · rw [piKer, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨y, ⟨i, hi⟩, rfl⟩, rfl⟩
      obtain ⟨s, rfl⟩ := f.surjective i
      exact Submodule.subset_span ⟨fun s => y (f s), ⟨s, hi⟩, by simp⟩
    · rw [piKer, Submodule.span_le]
      rintro _ ⟨z, ⟨s, hz⟩, rfl⟩
      refine ⟨PiTensorProduct.tprod ℂ (Equiv.piCongrLeft M f z),
        Submodule.subset_span ⟨_, ⟨f s, by simpa using hz⟩, rfl⟩, ?_⟩
      simp
  · rintro _ ⟨s, g, hg, rfl⟩
    refine ⟨piOp (f s) g, ⟨f s, g, hg, rfl⟩, fun x => ?_⟩
    have hu : (Function.update (fun j => (LinearMap.id : M (f j) →ₗ[ℂ] M (f j))) s g) =
        fun j => Function.update (fun i => (LinearMap.id : M i →ₗ[ℂ] M i)) (f s) g (f.symm.symm j) := by
      funext j
      by_cases h : j = s
      · subst h; simp
      · rw [Function.update_of_ne h]
        exact (Function.update_of_ne (β := fun i => M i →ₗ[ℂ] M i) (a := f j) (a' := f s)
          (fun h' => h (f.injective h')) g (fun i => LinearMap.id)).symm
    simp only [piOp, LinearEquiv.coe_coe]
    rw [hu, PiTensorProduct.map_reindex]

theorem simpleOver_sum {α β : Type} (hα : PP α) (hβ : PP β) [DecidableEq (α ⊕ β)]
    (N : α ⊕ β → Type) [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)]
    (Op : ∀ i, Set (Module.End ℂ (N i))) (K : ∀ i, Submodule ℂ (N i))
    (hr : ∀ i, Module.rank ℂ (N i) ≤ Cardinal.aleph0)
    (hrl : Module.rank ℂ (⨂[ℂ] a, N (.inl a)) ≤ Cardinal.aleph0)
    (hs : ∀ i, Stab (Op i) (K i)) (hso : ∀ i, SimpleOver (Op i) (K i)) :
    SimpleOver (piOps Op) (piKer K) := by
  classical
  have hA := hα (fun a => N (.inl a)) (fun a => Op (.inl a)) (fun a => K (.inl a))
    (fun a => hr _) (fun a => hs _) (fun a => hso _)
  have hB := hβ (fun b => N (.inr b)) (fun b => Op (.inr b)) (fun b => K (.inr b))
    (fun b => hr _) (fun b => hs _) (fun b => hso _)
  have hT := GlobalTheory.T.simpleOverStableSubmodule_tensorPureKernelSpan (piOps (fun a => Op (.inl a))) (piOps (fun b => Op (.inr b)))
    (piKer (fun a => K (.inl a))) (piKer (fun b => K (.inr b))) hrl
    (GlobalTheory.T.operatorStable_piTensorPureKernelSpan _ _ (fun a => hs _)) (GlobalTheory.T.operatorStable_piTensorPureKernelSpan _ _ (fun b => hs _)) hA hB
  let e := (PiTensorProduct.tmulEquivDep ℂ N).symm
  refine simpleOver_of_equiv e _ _ _ _ ?_ ?_ hT
  · apply le_antisymm
    · rw [piKer, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨y, ⟨i, hi⟩, rfl⟩, rfl⟩
      refine Submodule.subset_span ⟨PiTensorProduct.tprod ℂ (fun a => y (.inl a)),
        PiTensorProduct.tprod ℂ (fun b => y (.inr b)), ?_, by simp [e]⟩
      cases i with
      | inl a => exact Or.inl (Submodule.subset_span ⟨_, ⟨a, hi⟩, rfl⟩)
      | inr b => exact Or.inr (Submodule.subset_span ⟨_, ⟨b, hi⟩, rfl⟩)
    · set Q := (piKer K).map e.toLinearMap with hQ
      have pure : ∀ (y₁ : ∀ a, N (.inl a)) (y₂ : ∀ b, N (.inr b)),
          ((∃ a, y₁ a ∈ K (.inl a)) ∨ (∃ b, y₂ b ∈ K (.inr b))) →
          PiTensorProduct.tprod ℂ y₁ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ y₂ ∈ Q := by
        intro y₁ y₂ h
        refine ⟨PiTensorProduct.tprod ℂ (fun i => Sum.rec y₁ y₂ i),
          Submodule.subset_span ⟨_, ?_, rfl⟩, by simp [e]⟩
        rcases h with ⟨a, ha⟩ | ⟨b, hb⟩
        · exact ⟨.inl a, ha⟩
        · exact ⟨.inr b, hb⟩
      have left : ∀ (y₁ : ∀ a, N (.inl a)), (∃ a, y₁ a ∈ K (.inl a)) →
          ∀ z, PiTensorProduct.tprod ℂ y₁ ⊗ₜ[ℂ] z ∈ Q := by
        intro y₁ h z
        have : (⊤ : Submodule ℂ (⨂[ℂ] b, N (.inr b))) ≤
            Q.comap (TensorProduct.mk ℂ _ _ (PiTensorProduct.tprod ℂ y₁)) := by
          rw [← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
          rintro _ ⟨y₂, rfl⟩
          exact pure y₁ y₂ (Or.inl h)
        exact this Submodule.mem_top
      have right : ∀ (y₂ : ∀ b, N (.inr b)), (∃ b, y₂ b ∈ K (.inr b)) →
          ∀ x, x ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ y₂ ∈ Q := by
        intro y₂ h x
        have : (⊤ : Submodule ℂ (⨂[ℂ] a, N (.inl a))) ≤
            Q.comap ((TensorProduct.mk ℂ _ _).flip (PiTensorProduct.tprod ℂ y₂)) := by
          rw [← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
          rintro _ ⟨y₁, rfl⟩
          exact pure y₁ y₂ (Or.inr h)
        exact this Submodule.mem_top
      rw [tensKer, Submodule.span_le]
      rintro _ ⟨x, z, hxz, rfl⟩
      rcases hxz with hx | hz
      · have : piKer (fun a => K (.inl a)) ≤ Q.comap ((TensorProduct.mk ℂ _ _).flip z) := by
          rw [piKer, Submodule.span_le]
          rintro _ ⟨y₁, h, rfl⟩
          exact left y₁ h z
        exact this hx
      · have : piKer (fun b => K (.inr b)) ≤ Q.comap (TensorProduct.mk ℂ _ _ x) := by
          rw [piKer, Submodule.span_le]
          rintro _ ⟨y₂, h, rfl⟩
          exact right y₂ h x
        exact this hz
  · rintro _ (⟨_, ⟨a, g, hg, rfl⟩, rfl⟩ | ⟨_, ⟨b, g, hg, rfl⟩, rfl⟩)
    · refine ⟨piOp (Sum.inl a) g, ⟨_, g, hg, rfl⟩, fun x => ?_⟩
      have H : (TensorProduct.map (piOp a g) LinearMap.id) ∘ₗ e.toLinearMap =
          e.toLinearMap ∘ₗ piOp (Sum.inl a) g := by
        apply PiTensorProduct.ext
        apply MultilinearMap.ext
        intro y
        simp only [e, piOp, LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
          LinearEquiv.coe_coe, PiTensorProduct.map_tprod, PiTensorProduct.tmulEquivDep_symm_apply,
          TensorProduct.map_tmul, LinearMap.id_apply]
        congr 2
        · funext a'
          by_cases h : a' = a
          · subst h; simp
          · rw [Function.update_of_ne h, Function.update_of_ne (fun h' => h (Sum.inl_injective h'))]
        · funext b'
          rw [Function.update_of_ne (Sum.inr_ne_inl)]
          rfl
      exact LinearMap.congr_fun H x
    · refine ⟨piOp (Sum.inr b) g, ⟨_, g, hg, rfl⟩, fun x => ?_⟩
      have H : (TensorProduct.map LinearMap.id (piOp b g)) ∘ₗ e.toLinearMap =
          e.toLinearMap ∘ₗ piOp (Sum.inr b) g := by
        apply PiTensorProduct.ext
        apply MultilinearMap.ext
        intro y
        simp only [e, piOp, LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
          LinearEquiv.coe_coe, PiTensorProduct.map_tprod, PiTensorProduct.tmulEquivDep_symm_apply,
          TensorProduct.map_tmul, LinearMap.id_apply]
        congr 2
        · funext a'
          rw [Function.update_of_ne (Sum.inl_ne_inr)]
          rfl
        · funext b'
          by_cases h : b' = b
          · subst h; simp
          · rw [Function.update_of_ne h, Function.update_of_ne (fun h' => h (Sum.inr_injective h'))]
      exact LinearMap.congr_fun H x

theorem pp_unit_sum {α : Type} (hα : PP α) : PP (PUnit ⊕ α) := by
  intro _ N _ _ Op K hr hs hso
  refine simpleOver_sum pp_unit hα N Op K hr ?_ hs hso
  rw [(PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun u : PUnit => N (Sum.inl u))
    PUnit.unit).rank_eq]
  exact hr _

theorem pp_option {α : Type} (hα : PP α) : PP (Option α) :=
  pp_of_equiv ((Equiv.optionEquivSumPUnit α).trans (Equiv.sumComm _ _)).symm (pp_unit_sum hα)

theorem pp_finite (σ : Type) [Finite σ] : PP σ :=
  Finite.induction_empty_option (P := PP) (fun f h => pp_of_equiv f h) pp_empty
    (fun h => pp_option h) σ

theorem simpleOver_piKer : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M : ι → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (Op : ∀ i, Set (Module.End ℂ (M i)))
    (K : ∀ i, Submodule ℂ (M i)),
    (∀ i, Module.rank ℂ (M i) ≤ Cardinal.aleph0) → (∀ i, GlobalTheory.TensHead.Stab (Op i) (K i)) →
    (∀ i, GlobalTheory.TensHead.SimpleOver (Op i) (K i)) →
    GlobalTheory.TensHead.SimpleOver (GlobalTheory.TensHead.piOps Op) (GlobalTheory.TensHead.piKer K) := by
  intro ι _ _ M _ _ Op K hr hs hso
  exact pp_finite ι M Op K hr hs hso

end GlobalTheory.PiSimple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransposeInvariantOfConjInvariantDistributionGL
section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology

noncomputable section

namespace GlobalTheory.GelfandKazhdan

section General

variable {G : Type} [Group G] [TopologicalSpace G]

def pull (t : G ≃ₜ G) : SB G →ₗ[ℂ] SB G where
  toFun φ := ⟨fun x => φ.1 (t x), φ.2.1.comp_continuous t.continuous, φ.2.2.comp_homeomorph t⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [TopologicalSpace G] in
theorem anti_one {t : G → G} (hm : ∀ x y, t (x * y) = t y * t x) : t 1 = 1 := by
  have := hm 1 1
  rw [one_mul] at this
  exact left_eq_mul.1 this

omit [TopologicalSpace G] in
theorem anti_inv {t : G → G} (hm : ∀ x y, t (x * y) = t y * t x) (x : G) : t x⁻¹ = (t x)⁻¹ := by
  have := hm x x⁻¹
  rw [mul_inv_cancel, anti_one hm] at this
  exact eq_inv_of_mul_eq_one_left this.symm

theorem exists_stable (t : G ≃ₜ G) (hm : ∀ x y, t (x * y) = t y * t x) (ht : ∀ x, t (t x) = x)
    (K₀ : Subgroup G) (hK : ∀ x ∈ K₀, t x ∈ K₀)
    (hb : ∀ U ∈ 𝓝 (1 : G), ∃ J : Subgroup G, IsOpen (J : Set G) ∧
      (J : Set G) ⊆ U ∧ J ≤ K₀ ∧ ∀ x ∈ K₀, ∀ j ∈ J, x * j * x⁻¹ ∈ J) :
    ∀ U ∈ 𝓝 (1 : G), ∃ J : Subgroup G, IsOpen (J : Set G) ∧
      (J : Set G) ⊆ U ∧ J ≤ K₀ ∧ (∀ x ∈ K₀, ∀ j ∈ J, x * j * x⁻¹ ∈ J) ∧ ∀ j ∈ J, t j ∈ J := by
  intro U hU
  obtain ⟨J, ho, hJU, hJK, hn⟩ := hb U hU
  refine ⟨{ carrier := {y | y ∈ J ∧ t y ∈ J}
            mul_mem' := fun ha hb => ⟨mul_mem ha.1 hb.1, by rw [hm]; exact mul_mem hb.2 ha.2⟩
            one_mem' := ⟨one_mem _, by rw [anti_one hm]; exact one_mem _⟩
            inv_mem' := fun ha => ⟨inv_mem ha.1, by rw [anti_inv hm]; exact inv_mem ha.2⟩ },
    ho.inter (ho.preimage t.continuous), fun y hy => hJU hy.1, fun y hy => hJK hy.1,
    fun x hx j hj => ⟨hn x hx j hj.1, ?_⟩, fun j hj => ⟨hj.2, by rw [ht]; exact hj.1⟩⟩
  have := hn _ (inv_mem (hK x hx)) _ hj.2
  rw [hm, hm, anti_inv hm, ← mul_assoc]
  rwa [inv_inv] at this

theorem invariant_of_anti [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [SecondCountableTopology G] (t : G ≃ₜ G) (hm : ∀ x y, t (x * y) = t y * t x)
    (ht : ∀ x, t (t x) = x) (K₀ : Subgroup G) (hKo : IsOpen (K₀ : Set G))
    (hKc : IsCompact (K₀ : Set G)) (hK : ∀ x ∈ K₀, t x ∈ K₀)
    (hb : ∀ U ∈ 𝓝 (1 : G), ∃ J : Subgroup G, IsOpen (J : Set G) ∧
      (J : Set G) ⊆ U ∧ J ≤ K₀ ∧ ∀ x ∈ K₀, ∀ j ∈ J, x * j * x⁻¹ ∈ J)
    (hs : ∀ x, ∃ s, t s = s ∧ s * x = t x * s) (T : SB G →ₗ[ℂ] ℂ)
    (hT : ∀ (g : G) (φ ψ : SB G), (∀ x, ψ.1 x = φ.1 (g * x * g⁻¹)) → T ψ = T φ) (φ : SB G) :
    T (pull t φ) = T φ := by
  obtain ⟨U, hU⟩ := (𝓝 (1 : G)).exists_antitone_basis
  choose J hJo hJU hJK hJn hJt using fun m =>
    exists_stable t hm ht K₀ hK hb (U m) (hU.1.mem_of_mem trivial)
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense G
  have : Countable S := hSc.to_subtype
  let K : S → ℕ → Subgroup G := fun c m => J m ⊓ (J m).comap (MulAut.conj (c : G)).toMonoidHom
  have hKm : ∀ c m y, y ∈ K c m ↔ y ∈ J m ∧ (c : G) * y * (c : G)⁻¹ ∈ J m := fun c m y => Iff.rfl
  have hD : T - T.comp (pull t) = 0 := by
    refine GlobalTheory.T.schwartzBruhat_distribution_eq_zero_baire G S K (fun c m => ?_) (fun c V hV => ?_) _ fun x => ?_
    · have ho : IsOpen (K c m : Set G) :=
        (hJo m).inter ((hJo m).preimage (f := fun y => (c : G) * y * (c : G)⁻¹) (by fun_prop))
      exact ⟨ho, hKc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho) fun y hy => hJK m hy.1⟩
    · obtain ⟨m, -, hm⟩ := hU.1.mem_iff.1 hV
      exact ⟨m, fun y hy => hm (hJU m hy.1)⟩
    · obtain ⟨s, hts, hsx⟩ := hs x
      obtain ⟨c, hc, hcS⟩ := hSd.inter_open_nonempty _
        (hKo.preimage (f := fun y => y * s⁻¹) (by fun_prop)) ⟨s, by simp⟩
      have hc' : c * s⁻¹ ∈ K₀ := hc
      refine ⟨⟨c, hcS⟩, fun m ψ hψ => ?_⟩
      have hK' : ∀ y, y ∈ K ⟨c, hcS⟩ m ↔ y ∈ J m ∧ s * y * s⁻¹ ∈ J m := fun y => by
        rw [hKm]
        refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
        · have := hJn m _ (inv_mem hc') _ h
          convert this using 1
          simp only []
          group
        · have := hJn m _ hc' _ h
          convert this using 1
          simp only []
          group
      have hτ : ∀ y, t (s * y * s⁻¹) = s⁻¹ * t y * s := fun y => by
        rw [hm, hm, anti_inv hm, hts, mul_assoc]
      have hτK : ∀ y ∈ K ⟨c, hcS⟩ m, s⁻¹ * t y * s ∈ K ⟨c, hcS⟩ m := fun y hy => by
        rw [hK'] at hy ⊢
        refine ⟨hτ y ▸ hJt m _ hy.2, ?_⟩
        convert hJt m _ hy.1 using 1
        group
      have h1 : ∀ y, y ∈ {g : G | ∃ a ∈ K ⟨c, hcS⟩ m, ∃ b ∈ K ⟨c, hcS⟩ m, g = a * x * b} →
          s⁻¹ * t y * s ∈ {g : G | ∃ a ∈ K ⟨c, hcS⟩ m, ∃ b ∈ K ⟨c, hcS⟩ m, g = a * x * b} := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨_, hτK b hb, _, hτK a ha, ?_⟩
        have : t x = s * x * s⁻¹ := by rw [hsx]; group
        rw [hm, hm, this]
        group
      have h2 : ∀ y, s⁻¹ * t (s⁻¹ * t y * s) * s = y := fun y => by
        rw [hm, hm, anti_inv hm, hts, ht]
        group
      have h3 : T ψ = T (pull t ψ) := hT s _ _ fun y => by
        show ψ.1 y = ψ.1 (t (s * y * s⁻¹))
        rw [hτ, hψ]
        by_cases hy : y ∈ {g : G | ∃ a ∈ K ⟨c, hcS⟩ m, ∃ b ∈ K ⟨c, hcS⟩ m, g = a * x * b}
        · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (h1 y hy)]
        · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem fun h => hy (h2 y ▸ h1 _ h)]
      exact sub_eq_zero.2 h3
  exact (sub_eq_zero.1 (LinearMap.congr_fun hD φ)).symm

end General

section Transpose

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

def trGL (g : GL n R) : GL n R :=
  ⟨g.val.transpose, g.inv.transpose, by rw [← Matrix.transpose_mul, g.inv_val, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, g.val_inv, Matrix.transpose_one]⟩

theorem trGL_trGL (g : GL n R) : trGL (trGL g) = g := rfl

theorem trGL_mul (g h : GL n R) : trGL (g * h) = trGL h * trGL g :=
  Units.ext (Matrix.transpose_mul _ _)

theorem continuous_trGL [TopologicalSpace R] : Continuous (trGL : GL n R → GL n R) :=
  Units.continuous_iff.2 ⟨Units.continuous_val.matrix_transpose,
    Units.continuous_coe_inv.matrix_transpose⟩

def trHomeo [TopologicalSpace R] : GL n R ≃ₜ GL n R where
  toFun := trGL
  invFun := trGL
  left_inv := trGL_trGL
  right_inv := trGL_trGL
  continuous_toFun := continuous_trGL
  continuous_invFun := continuous_trGL

end Transpose

theorem transpose_invariant (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (T : SB (GL n k) →ₗ[ℂ] ℂ)
    (hT : ∀ (g : GL n k) (φ ψ : SB (GL n k)), (∀ x, ψ.1 x = φ.1 (g * x * g⁻¹)) → T ψ = T φ)
    (φ ψ : SB (GL n k)) (h : ∀ x y : GL n k, y.val = x.val.transpose → ψ.1 x = φ.1 y) :
    T ψ = T φ := by
  have e : ψ = pull trHomeo φ := Subtype.ext (funext fun x => h x (trGL x) rfl)
  rw [e]
  refine invariant_of_anti trHomeo trGL_mul trGL_trGL (KO k n) SplitFlip.isOpen_KO
    SplitFlip.isCompact_KO (fun x hx => ?_) (exists_open_normalised_subgroup_subset k n)
    (fun x => ?_) T hT φ
  · obtain ⟨h1, h2⟩ := (SplitFlip.mem_KO_iff _).1 hx
    exact (SplitFlip.mem_KO_iff _).2 ⟨fun i j => h1 j i, fun i j => h2 j i⟩
  · obtain ⟨P, ⟨s, rfl⟩, h1, h2⟩ := GlobalTheory.T.matrix_conj_transpose_by_symmetric_taussky_zassenhaus k n x.val
    exact ⟨s, Units.ext h1, Units.ext h2⟩

end GlobalTheory.GelfandKazhdan
end
end

