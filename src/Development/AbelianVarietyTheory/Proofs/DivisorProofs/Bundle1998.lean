import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1983
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1964
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1986
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupsSchroedingerFixStandardChar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.SchrFixNbhd

open Matrix

def fixTrans {M : Type} [AddCommGroup M] (g : M → ℂ) : AddSubgroup M where
  carrier := {u | ∀ x, g (x + u) = g x}
  zero_mem' := fun x => by rw [add_zero]
  add_mem' := fun {a b} ha hb x => by rw [← add_assoc, hb, ha]
  neg_mem' := fun {a} ha x => by
    have := ha (x + -a)
    rw [neg_add_cancel_right] at this
    exact this.symm

theorem isOpen_fixTrans {M : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] {g : M → ℂ}
    (h1 : IsLocallyConstant g) (h2 : HasCompactSupport g) : IsOpen (fixTrans g : Set M) := by
  have h : ∀ᶠ u in nhds (0 : M), ∀ x ∈ tsupport g, g (x + u) = g x ∧ g (x - u) = g x := by
    apply h2.isCompact.eventually_forall_of_forall_eventually
    intro x _
    have a1 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 + z.1 by fun_prop)).eventually_eq (0, x)
    have a2 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 - z.1 by fun_prop)).eventually_eq (0, x)
    have a3 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 by fun_prop)).eventually_eq (0, x)
    filter_upwards [a1, a2, a3] with z b1 b2 b3
    simp only [Function.comp, add_zero, sub_zero] at b1 b2 b3
    exact ⟨b1.trans b3.symm, b2.trans b3.symm⟩
  have key : ∀ᶠ u in nhds (0 : M), ∀ x, g (x + u) = g x := by
    filter_upwards [h] with u hu x
    by_cases hx : x ∈ tsupport g
    · exact (hu x hx).1
    · by_cases hx' : x + u ∈ tsupport g
      · have := (hu _ hx').2
        rw [add_sub_cancel_right] at this
        exact this.symm
      · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']
  exact AddSubgroup.isOpen_of_mem_nhds _ key

theorem exists_dot_ker {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    (χ : AddChar K ℂ) (hχ : IsLocallyConstant χ) (κ : Type) [Fintype κ] [NonarchimedeanAddGroup (κ → K)]
    (C : Set (κ → K)) (hC : IsCompact C) :
    ∃ H : OpenAddSubgroup (κ → K), ∀ z ∈ C, ∀ a ∈ H, ∀ b ∈ H, χ (z ⬝ᵥ b + a ⬝ᵥ b) = 1 := by
  let V : Set K := {t | χ t = 1}
  have hV : IsOpen V := hχ.isOpen_fiber 1
  have h0 : (0 : K) ∈ V := AddChar.map_zero_eq_one χ
  have hadd : ∀ s t, s ∈ V → t ∈ V → s + t ∈ V := fun s t hs ht => by
    show χ (s + t) = 1
    rw [AddChar.map_add_eq_mul, show χ s = 1 from hs, show χ t = 1 from ht, one_mul]
  have hc1 : Continuous fun p : (κ → K) × (κ → K) => p.2 ⬝ᵥ p.1 := continuous_snd.dotProduct continuous_fst
  have hc2 : Continuous fun p : (κ → K) × (κ → K) => p.1 ⬝ᵥ p.2 := continuous_fst.dotProduct continuous_snd
  have N0 : ∀ᶠ b in nhds (0 : κ → K), ∀ z ∈ C, z ⬝ᵥ b ∈ V := by
    refine hC.eventually_forall_of_forall_eventually fun z _ => ?_
    exact hc1.tendsto ((0 : κ → K), z) (hV.mem_nhds (by simpa using h0))
  have N1 : {p : (κ → K) × (κ → K) | p.1 ⬝ᵥ p.2 ∈ V} ∈ nhds ((0 : κ → K), (0 : κ → K)) :=
    hc2.tendsto ((0 : κ → K), (0 : κ → K)) (hV.mem_nhds (by simpa using h0))
  rw [nhds_prod_eq, Filter.mem_prod_iff] at N1
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := N1
  obtain ⟨H, hH⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ (Filter.inter_mem (Filter.inter_mem N0 ht₁) ht₂)
  refine ⟨H, fun z hz a ha b hb => hadd _ _ ((hH hb).1.1 z hz) ?_⟩
  exact hsub (Set.mk_mem_prod (hH ha).1.2 (hH hb).2)

variable {F : Type} [Field F] [NumberField F]

theorem adeleJoin_zero_apply {κ : Type} (y : κ → FiniteAdeleRing (𝓞 F) F) (i : κ) :
    GlobalTheory.WeilCont.adeleJoin F 0 y i = ((0 : InfiniteAdeleRing F), y i) := by
  refine Prod.ext ?_ rfl
  show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm 0 = 0
  exact map_zero _

theorem dotProduct_adeleJoin_zero {κ : Type} [Fintype κ] (v : κ → AdeleRing (𝓞 F) F)
    (y : κ → FiniteAdeleRing (𝓞 F) F) :
    v ⬝ᵥ GlobalTheory.WeilCont.adeleJoin F 0 y = ((0 : InfiniteAdeleRing F), (fun i => (v i).2) ⬝ᵥ y) := by
  let q1 : AdeleRing (𝓞 F) F →+* InfiniteAdeleRing F := RingHom.fst _ _
  let q2 : AdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd _ _
  have e1 : ∀ s : AdeleRing (𝓞 F) F, s.1 = q1 s := fun _ => rfl
  have e2 : ∀ s : AdeleRing (𝓞 F) F, s.2 = q2 s := fun _ => rfl
  refine Prod.ext ?_ ?_
  · rw [e1, dotProduct, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_mul, adeleJoin_zero_apply]
    exact mul_zero _
  · rw [e2, dotProduct, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, adeleJoin_zero_apply]
    rfl

theorem exists_fix_pure [Invertible (2 : AdeleRing (𝓞 F) F)] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : Continuous ψ)
    (κ : Type) [Fintype κ] (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ L₁ L₂ : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F),
      IsOpen (L₁ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧ IsOpen (L₂ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      ∀ x ∈ L₁, ∀ y ∈ L₂, GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilCont.adeleJoin F 0 x, GlobalTheory.WeilCont.adeleJoin F 0 y)
        (GlobalTheory.WeilM.pureA F f g) = GlobalTheory.WeilM.pureA F f g := by
  haveI := GlobalTheory.HeisSchA.nonarch_finiteAdeleRing (F := F)
  haveI : NonarchimedeanAddGroup (κ → FiniteAdeleRing (𝓞 F) F) := GlobalTheory.HeisSchA.nonarch_pi
  obtain ⟨H, hH⟩ := exists_dot_ker (GlobalTheory.HeisSchA.finChar ψ) (GlobalTheory.HeisSchA.finChar_isLocallyConstant ψ hψ) κ
    (tsupport g) hg.2.isCompact
  let c : FiniteAdeleRing (𝓞 F) F := (⅟(2 : AdeleRing (𝓞 F) F)).2
  refine ⟨fixTrans g ⊓ (H : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)).comap
    (DistribSMul.toAddMonoidHom (κ → FiniteAdeleRing (𝓞 F) F) c), H, ?_, H.isOpen, ?_⟩
  · rw [AddSubgroup.coe_inf]
    exact (isOpen_fixTrans hg.1 hg.2).inter (H.isOpen.preimage (continuous_const_smul c))
  rintro x ⟨hx1, hx2⟩ y hy
  funext z
  have hf : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((z + GlobalTheory.WeilCont.adeleJoin F 0 x) i).1) =
      fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1 := by
    funext i
    rw [Pi.add_apply, adeleJoin_zero_apply]
    exact congrArg _ (add_zero (z i).1)
  have hgz : (fun i => ((z + GlobalTheory.WeilCont.adeleJoin F 0 x) i).2) = (fun i => (z i).2) + x := by
    funext i
    rw [Pi.add_apply, adeleJoin_zero_apply]
    rfl
  have hz : GlobalTheory.WeilM.pureA F f g (z + GlobalTheory.WeilCont.adeleJoin F 0 x) = GlobalTheory.WeilM.pureA F f g z := by
    simp only [GlobalTheory.WeilM.pureA]
    rw [hf, hgz, hx1]
  simp only [GlobalTheory.WeilM.schr]
  rw [hz]
  by_cases hg0 : g (fun i => (z i).2) = 0
  · simp only [GlobalTheory.WeilM.pureA, hg0, mul_zero]
  have hzc : (fun i => (z i).2) ∈ tsupport g := subset_tsupport _ hg0
  have harg : z ⬝ᵥ GlobalTheory.WeilCont.adeleJoin F 0 y + ⅟(2 : AdeleRing (𝓞 F) F) *
      (GlobalTheory.WeilCont.adeleJoin F 0 x ⬝ᵥ GlobalTheory.WeilCont.adeleJoin F 0 y) =
      ((0 : InfiniteAdeleRing F), (fun i => (z i).2) ⬝ᵥ y + (c • x) ⬝ᵥ y) := by
    rw [dotProduct_adeleJoin_zero, dotProduct_adeleJoin_zero, smul_dotProduct]
    refine Prod.ext ?_ ?_
    · show (0 : InfiniteAdeleRing F) + (⅟(2 : AdeleRing (𝓞 F) F)).1 * 0 = 0
      rw [mul_zero, add_zero]
    · show (fun i => (z i).2) ⬝ᵥ y + c * ((fun i => (GlobalTheory.WeilCont.adeleJoin F 0 x i).2) ⬝ᵥ y) = _
      rfl
  rw [harg]
  have h1 : ψ ((0 : InfiniteAdeleRing F), (fun i => (z i).2) ⬝ᵥ y + (c • x) ⬝ᵥ y) = 1 :=
    hH _ hzc (c • x) hx2 y hy
  rw [h1, one_mul]

theorem exists_fix (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : Continuous ψ) (κ : Type) [Fintype κ]
    (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) :
    ∃ L₁ L₂ : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F),
      IsOpen (L₁ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧ IsOpen (L₂ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      ∀ x ∈ L₁, ∀ y ∈ L₂, GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilCont.adeleJoin F 0 x, GlobalTheory.WeilCont.adeleJoin F 0 y) Φ = Φ := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact exists_fix_pure ψ hψ κ f g hg
  | zero =>
    refine ⟨⊤, ⊤, isOpen_univ, isOpen_univ, fun x _ y _ => ?_⟩
    funext z
    simp [GlobalTheory.WeilM.schr]
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨L₁, L₂, o₁, o₂, h⟩ := h1
    obtain ⟨M₁, M₂, p₁, p₂, h'⟩ := h2
    refine ⟨L₁ ⊓ M₁, L₂ ⊓ M₂, by rw [AddSubgroup.coe_inf]; exact o₁.inter p₁,
      by rw [AddSubgroup.coe_inf]; exact o₂.inter p₂, fun x hx y hy => ?_⟩
    have e1 := h x hx.1 y hy.1
    have e2 := h' x hx.2 y hy.2
    funext z
    have a1 := congrFun e1 z
    have a2 := congrFun e2 z
    simp only [GlobalTheory.WeilM.schr, Pi.add_apply] at a1 a2 ⊢
    rw [mul_add, a1, a2]
  | smul a Φ _ h =>
    obtain ⟨L₁, L₂, o₁, o₂, h⟩ := h
    refine ⟨L₁, L₂, o₁, o₂, fun x hx y hy => ?_⟩
    funext z
    have a1 := congrFun (h x hx y hy) z
    simp only [GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul] at a1 ⊢
    rw [mul_left_comm, a1]

theorem schr_fix_nbhd : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (κ : Type) [Fintype κ], ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
      ∃ L₁ L₂ : AddSubgroup (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F),
        IsOpen (L₁ : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
        IsOpen (L₂ : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
        ∀ x ∈ L₁, ∀ y ∈ L₂, GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilCont.adeleJoin D.host.F 0 x, GlobalTheory.WeilCont.adeleJoin D.host.F 0 y) Φ = Φ := by
  intro D ψ hψ κ _ Φ hΦ
  exact exists_fix D.host.F ψ hψ.1.1 κ Φ hΦ

end GlobalTheory.SchrFixNbhd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicDualBasisIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.WeilL2Words

open MeasureTheory

theorem enorm_sum_mul_sq_le {m : ℕ} (a b : Fin m → ℂ) :
    ‖∑ i, a i * b i‖ₑ ^ 2 ≤ (∑ i, ‖b i‖ₑ ^ 2) * ∑ i, ‖a i‖ₑ ^ 2 := by
  have h1 : ‖∑ i, a i * b i‖₊ ≤ ∑ i, ‖b i‖₊ * ‖a i‖₊ := by
    refine (nnnorm_sum_le _ _).trans (le_of_eq ?_)
    simp [nnnorm_mul, mul_comm]
  have h2 : ‖∑ i, a i * b i‖₊ ^ 2 ≤ (∑ i, ‖b i‖₊ ^ 2) * ∑ i, ‖a i‖₊ ^ 2 :=
    (pow_le_pow_left₀ (by positivity) h1 2).trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
  simp only [enorm_eq_nnnorm]
  exact_mod_cast h2

theorem slice_le_l2A (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (m : ℕ)
    (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (yy : Fin m → (κ → FiniteAdeleRing (𝓞 F) F))
    (hg : ∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) (hyy : ∀ i j, g i (yy j) = if i = j then 1 else 0)
    (μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _))
    (hμ : @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ)
    (y : κ → FiniteAdeleRing (𝓞 F) F) : ∃ C : ENNReal, C ≠ ⊤ ∧
      ∀ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      ∫⁻ x, ‖(∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2 ≤
        C * GlobalTheory.WeilL2Words.l2A F μ (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) := by
  have hmeas : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, Measurable fun x => ‖f x‖ₑ ^ 2 :=
    fun f => by
      haveI : OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
      exact (f.continuous.measurable.enorm).pow_const 2
  letI : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI := hμ
  have hev : ∀ (f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) x y',
      (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) (GlobalTheory.WeilCont.adeleJoin F x y') = ∑ i, f i x * g i y' := by
    intro f x y'
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => GlobalTheory.WeilCont.pureA_adeleJoin F _ _ x y'

  let U : Fin m → Set (κ → FiniteAdeleRing (𝓞 F) F) := fun j => ⋂ i, {y' | g i y' = g i (yy j)}
  have hUo : ∀ j, IsOpen (U j) := fun j => isOpen_iInter_of_finite fun i => (hg i).1.isOpen_fiber _
  have hUm : ∀ j, yy j ∈ U j := fun j => Set.mem_iInter.2 fun i => rfl
  have hUv : ∀ j, ∀ y' ∈ U j, ∀ i, g i y' = if i = j then 1 else 0 := fun j y' hy' i => by
    rw [← hyy]; exact Set.mem_iInter.1 hy' i
  have hU0 : ∀ j, μ (U j) ≠ 0 := fun j => (hUo j).measure_ne_zero μ ⟨_, hUm j⟩
  have hUt : ∀ j, μ (U j) ≠ ⊤ := by
    intro j
    refine ne_top_of_le_ne_top ((hg j).2.isCompact.measure_lt_top).ne (measure_mono ?_)
    intro y' hy'
    apply subset_tsupport
    rw [Function.mem_support, hUv j y' hy' j, if_pos rfl]
    exact one_ne_zero
  have hB : (∑ i, ‖g i y‖ₑ ^ 2) ≠ ⊤ := ENNReal.sum_ne_top.2 fun i _ => ENNReal.pow_ne_top enorm_ne_top
  refine ⟨(∑ i, ‖g i y‖ₑ ^ 2) * ∑ j, (μ (U j))⁻¹, ENNReal.mul_ne_top hB
    (ENNReal.sum_ne_top.2 fun j _ => ENNReal.inv_ne_top.2 (hU0 j)), ?_⟩
  intro f
  have hA : ∀ j, ∫⁻ x, ‖f j x‖ₑ ^ 2 ≤ (μ (U j))⁻¹ * GlobalTheory.WeilL2Words.l2A F μ (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) := by
    intro j
    rw [← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (Or.inl (hU0 j)) (Or.inl (hUt j))]
    have e : ∫⁻ y' in U j, (∫⁻ x, ‖(∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) (GlobalTheory.WeilCont.adeleJoin F x y')‖ₑ ^ 2) ∂μ
        = ∫⁻ y' in U j, (∫⁻ x, ‖f j x‖ₑ ^ 2) ∂μ := by
      refine setLIntegral_congr_fun (hUo j).measurableSet (fun y' hy' => ?_)
      refine lintegral_congr fun x => ?_
      rw [hev, Finset.sum_eq_single j]
      · rw [hUv j y' hy' j, if_pos rfl, mul_one]
      · intro i _ hij
        rw [hUv j y' hy' i, if_neg hij, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    rw [setLIntegral_const] at e
    rw [← e]
    exact setLIntegral_le_lintegral _ _
  calc ∫⁻ x, ‖(∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2
      ≤ ∫⁻ x, (∑ i, ‖g i y‖ₑ ^ 2) * ∑ i, ‖f i x‖ₑ ^ 2 := by
        refine lintegral_mono fun x => ?_
        rw [hev]
        exact enorm_sum_mul_sq_le _ _
    _ = (∑ i, ‖g i y‖ₑ ^ 2) * ∑ i, ∫⁻ x, ‖f i x‖ₑ ^ 2 := by
        rw [lintegral_const_mul' _ _ hB, lintegral_finset_sum]
        intro i _
        exact hmeas (f i)
    _ ≤ (∑ i, ‖g i y‖ₑ ^ 2) * ∑ j, (μ (U j))⁻¹ * GlobalTheory.WeilL2Words.l2A F μ (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) := by
        gcongr with j
        exact hA j
    _ = _ := by rw [← Finset.sum_mul, mul_assoc]

end GlobalTheory.WeilL2Words

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarVectorScalingIdele
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open GlobalTheory.ThK.LemF.QuotInv

noncomputable section

namespace GlobalTheory.ThK.LemF.QuotInv

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (tensNU)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem at_vec_iff {m : ℕ} {v : Pl F} {w : Fin m → AE F E} :
    At (evFin F v) w ↔ ∀ i, At (evFin F v) (w i) := by
  constructor
  · intro h i u hu
    exact congrFun (h u hu) i
  · intro h u hu
    funext i
    exact h i u hu

theorem at_liftFin (v : Pl F) (y : Fv F v ⊗[F] E) :
    At (evFin F v) (tensNU (E := E) (GlobalTheory.Doubling.inFin v) (GlobalTheory.Doubling.inFin_mul v) y) := by
  refine at_evFin_iff.2 ⟨fun w => ?_, fun w hw => ?_⟩
  · exact GlobalTheory.AutFunCompare.map_tensNU_zero (evInf F w) _ _ (fun _ => rfl) y
  · exact GlobalTheory.AutFunCompare.map_tensNU_zero (evFin F w) _ _ (evalV_singleFin_ne hw) y

theorem compFin_liftFin (v : Pl F) (y : Fv F v ⊗[F] E) :
    compFin F E v (tensNU (E := E) (GlobalTheory.Doubling.inFin v) (GlobalTheory.Doubling.inFin_mul v) y) = y :=
  GlobalTheory.AutFunCompare.map_tensNU_self (evFin F v) _ _ (evalV_singleFin_self v) y

theorem liftFin_compFin {v : Pl F} {z : AE F E} (hz : At (evFin F v) z) :
    tensNU (E := E) (GlobalTheory.Doubling.inFin v) (GlobalTheory.Doubling.inFin_mul v) (compFin F E v z) = z := by
  obtain ⟨h1, h2⟩ := at_evFin_iff.1 hz
  obtain ⟨g1, g2⟩ := at_evFin_iff.1 (at_liftFin v (compFin F E v z))
  refine GlobalTheory.Doubling.adele_ext (fun w => (g1 w).trans (h1 w).symm) fun w => ?_
  by_cases hw : w = v
  · subst hw
    exact compFin_liftFin w _
  · exact (g2 w hw).trans (h2 w hw).symm

theorem continuous_compFinV (v : Pl F) : Continuous (compFin F E v) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact GlobalTheory.AutFunCompare.continuous_tensNU (E := E) (evFin F v).toLinearMap (map_mul (evFin F v))
    ((RestrictedProduct.continuous_eval v).comp continuous_snd)

theorem continuous_liftFinV (v : Pl F) :
    Continuous (tensNU (E := E) (GlobalTheory.Doubling.inFin v) (GlobalTheory.Doubling.inFin_mul v)) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact GlobalTheory.AutFunCompare.continuous_tensNU _ _ (continuous_const.prodMk (continuous_singleFin v))

variable (F E) in

def vecAtEquiv (m : ℕ) (v : Pl F) : vecAt F E m (evFin F v) ≃ₜ+ (Fin m → Fv F v ⊗[F] E) where
  toFun w i := compFin F E v (w.1 i)
  invFun y := ⟨fun i => tensNU (E := E) (GlobalTheory.Doubling.inFin v) (GlobalTheory.Doubling.inFin_mul v) (y i),
    at_vec_iff.2 fun i => at_liftFin v (y i)⟩
  left_inv w := Subtype.ext (funext fun i => liftFin_compFin (at_vec_iff.1 w.2 i))
  right_inv y := funext fun i => compFin_liftFin v (y i)
  map_add' a b := funext fun i => map_add _ _ _
  continuous_toFun :=
    continuous_pi fun i => (continuous_compFinV v).comp ((continuous_apply i).comp continuous_subtype_val)
  continuous_invFun :=
    (continuous_pi fun i => (continuous_liftFinV v).comp (continuous_apply i)).subtype_mk _

def vecAtSmulCE {m : ℕ} {v : Pl F} (s : (AE F E)ˣ) : vecAt F E m (evFin F v) ≃ₜ+ vecAt F E m (evFin F v) where
  toFun := vecAtSmul (s : AE F E)
  invFun := vecAtSmul ((s⁻¹ : (AE F E)ˣ) : AE F E)
  left_inv w := Subtype.ext (show ((s⁻¹ : (AE F E)ˣ) : AE F E) • (s : AE F E) • w.1 = w.1 by
    rw [smul_smul, Units.inv_mul, one_smul])
  right_inv w := Subtype.ext (show (s : AE F E) • ((s⁻¹ : (AE F E)ˣ) : AE F E) • w.1 = w.1 by
    rw [smul_smul, Units.mul_inv, one_smul])
  map_add' := map_add _
  continuous_toFun := by
    haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
    haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
    exact ((continuous_const_smul (s : AE F E)).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
    haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
    exact ((continuous_const_smul ((s⁻¹ : (AE F E)ˣ) : AE F E)).comp continuous_subtype_val).subtype_mk _

theorem cA_eq_sigR (σ : E →ₐ[F] E) (z : AE F E) : cA σ z = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem map_vecAtSmul_cA_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (m : ℕ) (v : Pl F)
    (t : (AE F E)ˣ), t ∈ idelesAt E (evFin F v) → ∀ ν : Measure (vecAt F E m (evFin F v)), ν.IsAddHaarMeasure →
      ν.map (vecAtSmul (cA σ (t⁻¹ : (AE F E)ˣ).1)) = (absE F E t ^ m) • ν := by
  intro F E _ _ _ _ _ σ m v t ht ν hν
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : SecondCountableTopology (AE F E) := e0.secondCountableTopology
  haveI : T2Space (AE F E) := e0.isEmbedding.t2Space
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI := GlobalTheory.LocTateInt.isTopologicalRing_Ev (E := E) v
  haveI := GlobalTheory.LocTateInt.t2Space_Fv_tensor (E := E) v
  haveI := GlobalTheory.LocTateInt.locallyCompactSpace_Ev (E := E) v
  haveI := GlobalTheory.LocTateInt.secondCountable_Ev (E := E) v
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  set e1 := vecAtEquiv F E m v
  haveI : LocallyCompactSpace (vecAt F E m (evFin F v)) := e1.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  haveI := hν
  haveI : SecondCountableTopology (vecAt F E m (evFin F v)) := e1.toHomeomorph.isEmbedding.secondCountableTopology
  haveI : BorelSpace (vecAt F E m (evFin F v)) := inferInstance
  haveI : T2Space (vecAt F E m (evFin F v)) := inferInstance
  haveI : ν.Regular := inferInstance
  set s : (AE F E)ˣ := GlobalTheory.Doubling.conjUnit σ t⁻¹ with hs
  have hf : ⇑(vecAtSmul (m := m) (ev := evFin F v) (cA σ (t⁻¹ : (AE F E)ˣ).1)) =
      ⇑(vecAtSmulCE (m := m) (v := v) s) := by
    funext w
    apply Subtype.ext
    show cA σ (t⁻¹ : (AE F E)ˣ).1 • w.1 = (s : AE F E) • w.1
    rw [cA_eq_sigR]
    rfl
  rw [hf]
  have h1 := addEquivAddHaarChar_smul_map ν (vecAtSmulCE (m := m) (v := v) s)
  rw [← GlobalTheory.ModuLR.addEquivAddHaarChar_transport e1] at h1
  set U0 : (Fv F v ⊗[F] E)ˣ := GlobalTheory.Doubling.unitFin F E v s with hU0
  set Uc : (Fin m → Fv F v ⊗[F] E)ˣ := Units.map (Pi.constRingHom (Fin m) (Fv F v ⊗[F] E)).toMonoidHom U0
  have hg : (e1.symm.trans (vecAtSmulCE (m := m) (v := v) s)).trans e1 = GlobalTheory.ModuNorm.mulUnitCE Uc := by
    ext y i
    show compFin F E v ((s : AE F E) * tensNU (E := E) (GlobalTheory.Doubling.inFin v) (GlobalTheory.Doubling.inFin_mul v) (y i)) =
      (U0 : Fv F v ⊗[F] E) * y i
    rw [map_mul, compFin_liftFin]
    rfl
  have hc : distribHaarChar (Fin m → Fv F v ⊗[F] E) Uc = ‖Algebra.norm (Fv F v) (U0 : Fv F v ⊗[F] E)‖₊ ^ m := by
    rw [GlobalTheory.ModuPiLocal.distribHaarChar_pi (fun _ : Fin m => Fv F v ⊗[F] E) Uc]
    have hU : ∀ i, Units.map (Pi.evalRingHom (fun _ : Fin m => Fv F v ⊗[F] E) i).toMonoidHom Uc = U0 :=
      fun i => Units.ext rfl
    simp only [hU, GlobalTheory.LocTateInt.distribHaarChar_Ev, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hg, ← GlobalTheory.ModuNorm.distribHaarChar_eq_addEquivAddHaarChar, hc] at h1
  have hn : ‖Algebra.norm (Fv F v) (U0 : Fv F v ⊗[F] E)‖₊ = (absE F E t)⁻¹ := by
    change GlobalTheory.Doubling.absEv F E v (GlobalTheory.Doubling.unitFin F E v s) = _
    rw [GlobalTheory.Doubling.absEv_unitFin, hs,
      show Algebra.norm (AF F) (GlobalTheory.Doubling.conjUnit σ t⁻¹ : AE F E) = Algebra.norm (AF F) ((t⁻¹ : (AE F E)ˣ) : AE F E)
        from GlobalTheory.Doubling.norm_sigR σ _,
      ← GlobalTheory.Doubling.absEv_unitFin, map_inv, map_inv, ← absE_of_mem ht]
  rw [hn] at h1
  have h0 : absE F E t ≠ 0 := fun h => by
    have := congrArg (absE F E) (mul_inv_cancel t)
    rw [map_mul, h, zero_mul, map_one] at this
    exact zero_ne_one this
  calc ν.map ⇑(vecAtSmulCE (m := m) (v := v) s)
      = (absE F E t ^ m * (absE F E t)⁻¹ ^ m) • ν.map ⇑(vecAtSmulCE (m := m) (v := v) s) := by
        rw [← mul_pow, mul_inv_cancel₀ h0, one_pow, one_smul]
    _ = absE F E t ^ m • ((absE F E t)⁻¹ ^ m • ν.map ⇑(vecAtSmulCE (m := m) (v := v) s)) := (smul_smul _ _ _).symm
    _ = absE F E t ^ m • ν := by rw [h1]

end GlobalTheory.ThK.LemF.QuotInv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicCuspSectionsLeSpanAlgebraicCuspFormsStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicCuspSections_le_span_algebraicCuspForms : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j → ∀ w : WeightFamilies.Wt D j, w.LastPos → 8 * D.R.f * D.R.r + 4 ≤ w.n → ∀ σ, GoodEmb T.Q.c σ → Formalism.L2.Pj.holSub0 (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) ≤ Submodule.span ℂ (rdU (T.U j σ) '' (T.cuspA j (wtA w) w.n : Set (T.R j))) := by
  first | exact @GlobalTheory.OntoCore.holSub0_le_span_cuspA | exact GlobalTheory.OntoCore.holSub0_le_span_cuspA | (intros; apply GlobalTheory.OntoCore.holSub0_le_span_cuspA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweSplittingActsFockActionPlusTraceMultiplesStatement
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.howeSplitting_acts_fockAction_plus_traceMultiples : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ)
    (om : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)), IsCMExt F E σ → IsStd ψ →
    FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ → IsUSplitting (adeleClass F) ψ d (actB (cA σ)) om →
    ∃ c, ActsByD τ C om Φ (fun w => fockAct2 (P w) (Q w) (R w) (S w)) c := by
  first | exact @GlobalTheory.HoweD.lieScalarD | exact GlobalTheory.HoweD.lieScalarD | (intros; apply GlobalTheory.HoweD.lieScalarD <;> assumption)
end

