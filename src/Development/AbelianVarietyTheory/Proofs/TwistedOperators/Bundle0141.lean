import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmRep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0061
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0038
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0046
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0080

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHarishChandraParamGridColumnRealParameter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Grid

open GlobalTheory.SignedHC

theorem isHCParam_parP : ∀ (D : D7), HostHyp D → ∀ (i : ℕ), i ≤ D.R.m → ∀ (τ : D.what₂.Tau) (n : ℕ) (lam : Fin n → ℝ) (ε : Fin n → Bool), n = GlobalTheory.Grid.rkP D i → IsEnum (GlobalTheory.Grid.parP D i τ) lam ε → Formalism.QuantumDeterminants.IsHCParam lam := by
  intro D _ i _ τ n lam ε hn hE
  obtain ⟨hanti, q, hq, hS⟩ := hE
  refine ⟨hanti, fun a => ?_⟩
  have hmem : q a ∈ (grid D τ).weightX 0 := by
    have h0 : (q a, ε a) ∈ parP D i τ := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    rcases GridData.mem_parPi.1 h0 with ⟨l, hl, h⟩ | ⟨h1, _⟩ | ⟨l, h1, h2, h3, _⟩
    · exact GridData.mem_weightX.2 (Or.inl (GridData.mem_tops.2 ⟨l, hl, (Prod.ext_iff.1 h).1⟩))
    · exact GridData.mem_weightX.2 (Or.inr (Or.inl h1))
    · exact GridData.mem_weightX.2 (Or.inr (Or.inr (Or.inl ⟨l, by omega, h2, h3⟩)))
  have hs : Odd (grid D τ).s := GlobalTheory.ChiGrid.odd_sLen D
  obtain ⟨z, hz⟩ := GlobalTheory.ChiGrid.inCoset_weightX_zero hs _ hmem
  obtain ⟨u, hu⟩ := GlobalTheory.ChiGrid.even_rankP D i
  have hn' : (n : ℝ) = (u : ℝ) + u := by
    have : n = u + u := hn.trans hu
    rw [this]; push_cast; ring
  refine ⟨z + 1 - u, ?_⟩
  rw [hq a, hz, hn']
  push_cast
  ring

end GlobalTheory.Grid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHarishChandraParamGridRowRealParameter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridHC

open GlobalTheory.SignedHC Finset

theorem inCoset_weightX (D : D7) (τ : D.what₂.Tau) (j : ℕ) : InCoset (1 / 2) ((GlobalTheory.Grid.grid D τ).weightX j) := by
  induction j with
  | zero => exact GlobalTheory.ChiGrid.inCoset_weightX_zero (GlobalTheory.ChiGrid.odd_sLen D)
  | succ j ih =>
    rw [(GlobalTheory.Grid.grid D τ).weightX_succ]
    intro x hx
    rcases mem_union.1 hx with h | h
    · exact ih x h
    · obtain ⟨a, -, rfl⟩ := GlobalTheory.SignedHC.mem_block.1 h
      obtain ⟨u, hu⟩ := D.R.t_odd
      have e : ((GlobalTheory.Grid.grid D τ).t : ℚ) = 2 * u + 1 := by
        have : ((GlobalTheory.Grid.grid D τ).t : ℚ) = D.R.t := rfl
        rw [this, hu]; push_cast; ring
      refine ⟨-(GlobalTheory.Grid.grid D τ).e (j + 1) + u - a, ?_⟩
      push_cast
      rw [e]
      ring

theorem even_rkX (D : D7) (j : ℕ) : Even (GlobalTheory.Grid.rkX D j) := GlobalTheory.ChiGrid.even_rankX D j

theorem isHCParam_parXp : ∀ (D : D7), HostHyp D → ∀ (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ (τ : D.what₂.Tau) (n : ℕ) (lam : Fin n → ℝ)
    (ε : Fin n → Bool), n = GlobalTheory.Grid.rkX D j → IsEnum (GlobalTheory.Grid.parXp D j τ) lam ε → Formalism.QuantumDeterminants.IsHCParam lam := by
  intro D _ j _ _ τ n lam ε hn hE
  obtain ⟨hanti, q, hq, hS⟩ := hE
  refine ⟨hanti, fun a => ?_⟩
  have hmem : (q a, ε a) ∈ GlobalTheory.Grid.parXp D j τ := by
    rw [hS]; exact mem_image.2 ⟨a, mem_univ _, rfl⟩
  have hx : q a ∈ (GlobalTheory.Grid.grid D τ).weightX j := by
    obtain ⟨x, hx, hxe⟩ := mem_image.1 hmem
    have : x = q a := congrArg Prod.fst hxe
    exact this ▸ hx
  obtain ⟨z, hz⟩ := inCoset_weightX D τ j (q a) hx
  obtain ⟨k, hk⟩ := even_rkX D j
  refine ⟨z - k + 1, ?_⟩
  rw [hq a, hz, hn, hk]
  push_cast
  ring

end GlobalTheory.GridHC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHarishChandraParamGridVertexRealParameter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Grid

open GlobalTheory.SignedHC

theorem parD_entry_int (D : D7) (τ : D.what₂.Tau) (i j : ℕ) {x : ℚ × Bool} (hx : x ∈ (grid D τ).parD i j) :
    ∃ z : ℤ, x.1 = z := by
  obtain ⟨c, hc⟩ := D.R.t_odd
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  have hk := D.R.m_add_three_le_k
  have hs : ∃ d : ℕ, sLen D = 2 * d + 1 := ⟨a + b + 2, by unfold sLen Formalism.BasicNotions.Ranks.r; omega⟩
  obtain ⟨d, hd⟩ := hs
  rcases GridData.mem_parD.1 hx with ⟨h1, -⟩ | ⟨l, -, -, rfl⟩ | ⟨l, -, -, h3, -⟩ | ⟨l, -, -, h4, -⟩
  · obtain ⟨i', -, -, h⟩ := GridData.mem_cloud.1 h1
    exact ⟨_, h⟩
  · exact ⟨-(grid D τ).b l, by push_cast; rfl⟩
  · simp only [GridData.blockM, TPar.block, Finset.mem_image, Finset.mem_range] at h3
    obtain ⟨a', -, h⟩ := h3
    refine ⟨-((grid D τ).e l) + c - a', ?_⟩
    rw [← h]
    have ht : ((grid D τ).t : ℚ) = 2 * c + 1 := by exact_mod_cast hc
    rw [ht]; push_cast; ring
  · simp only [GridData.blockC, TPar.block, Finset.mem_image, Finset.mem_range] at h4
    obtain ⟨a', -, h⟩ := h4
    refine ⟨(grid D τ).cen l + d - a', ?_⟩
    rw [← h]
    have ht : ((grid D τ).s : ℚ) = 2 * d + 1 := by exact_mod_cast hd
    rw [ht]; push_cast; ring

theorem even_rkV_iff (D : D7) (i j : ℕ) : Even (rkV D i j) ↔ Odd (i + j) := by
  obtain ⟨c, hc⟩ := D.R.t_odd
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  have hk := D.R.m_add_three_le_k
  obtain ⟨u, hu⟩ : ∃ u, a + b = u + 1 := ⟨a + b - 1, by omega⟩
  have hr : D.R.r = 2 * u + 1 := by unfold Formalism.BasicNotions.Ranks.r; omega
  have e : rkV D i j = 2 * (u + j * c + i * (u + 3)) + (1 + j + i) := by
    unfold rkV sLen; rw [hr, hc]; ring
  rw [e, Nat.even_add, Nat.odd_add]
  simp only [even_two, Even.mul_right, true_iff, Nat.even_add, Nat.odd_add]
  simp only [Nat.odd_iff, Nat.even_iff]; omega

theorem isHCParam_parV : ∀ (D : D7), HostHyp D → ∀ (i j : ℕ), 1 ≤ i → i ≤ D.R.m → j ≤ D.R.m → ∀ (τ : D.what₂.Tau) (n : ℕ) (lam : Fin n → ℝ) (ε : Fin n → Bool), n = GlobalTheory.Grid.rkV D i j → IsEnum (GlobalTheory.Grid.parV D i j τ) lam ε → Formalism.QuantumDeterminants.IsHCParam lam := by
  intro D _ i j _ _ _ τ n lam ε hn hE
  refine ⟨hE.1, fun a' => ?_⟩
  obtain ⟨-, q, hq, hS⟩ := hE
  have hmem : (q a', ε a') ∈ parV D i j τ := by rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  simp only [parV, dualPar, GlobalTheory.SignedHC.shift, Finset.mem_image, Prod.mk.injEq] at hmem
  obtain ⟨y, ⟨x, hx, rfl⟩, hy1, -⟩ := hmem
  obtain ⟨z, hz⟩ := parD_entry_int D τ i j hx
  have hpar := even_rkV_iff D i j
  rw [hq a', ← hy1]
  by_cases ho : Odd (i + j)
  · obtain ⟨N, hN⟩ := hpar.2 ho
    rw [if_pos ho] at *
    refine ⟨-z + 1 - N, ?_⟩
    have : (n : ℝ) = N + N := by rw [hn, hN]; push_cast; ring
    simp only [hz, this]; push_cast; ring
  · have hne : ¬ Even (rkV D i j) := fun h => ho (hpar.1 h)
    obtain ⟨N, hN⟩ := Nat.not_even_iff_odd.1 hne
    rw [if_neg ho] at *
    refine ⟨-z - N, ?_⟩
    have : (n : ℝ) = 2 * N + 1 := by rw [hn, hN]; push_cast; ring
    simp only [hz, this]; push_cast; ring

end GlobalTheory.Grid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultNormalisedInductionExact
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.SmGL.IndExact

section General

variable {G X U : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module ℂ X]
  [AddCommGroup U] [Module ℂ U] {P : Subgroup G} {σ : Representation ℂ P X} {ρ : Representation ℂ P U}

theorem smIndMap_injective (ι : σ.IntertwiningMap ρ) (hι : Function.Injective ι) :
    Function.Injective (smIndMap ι) := fun φ ψ h =>
  Subtype.ext (Subtype.ext (funext fun g =>
    hι (congrFun (congrArg (fun χ : smoothPart (ind P ρ) => χ.1.1) h) g)))

theorem exists_smIndMap_eq (ι : σ.IntertwiningMap ρ) (hι : Function.Injective ι)
    (F : smoothPart (ind P ρ)) (hF : ∀ g, ∃ u, ι u = F.1.1 g) : ∃ F', smIndMap ι F' = F := by
  choose u hu using hF
  refine ⟨⟨⟨u, fun h g => hι ?_⟩, mem_smoothPart_of_nhds (Filter.mem_of_superset
    (IsOpen.mem_nhds F.2 (by simp)) fun g hg => ?_)⟩, Subtype.ext (Subtype.ext (funext hu))⟩
  · rw [ι.isIntertwining, hu, hu, F.1.2 h g]
  · have hg' : ind P ρ g F.1 = F.1 := hg
    refine Subtype.ext (funext fun x => hι ?_)
    show ι (u (x * g)) = ι (u x)
    rw [hu, hu]
    exact congrFun (congrArg Subtype.val hg') x

theorem exists_normalised_pi {α : Type} [Finite α] {Γ : α → Type} [∀ i, Group (Γ i)]
    [∀ i, TopologicalSpace (Γ i)] (K : ∀ i, Subgroup (Γ i))
    (h : ∀ i, ∀ U ∈ nhds (1 : Γ i), ∃ J : Subgroup (Γ i), IsOpen (J : Set (Γ i)) ∧ (J : Set (Γ i)) ⊆ U ∧
      J ≤ K i ∧ ∀ x ∈ K i, ∀ j ∈ J, x * j * x⁻¹ ∈ J) :
    ∀ U ∈ nhds (1 : ∀ i, Γ i), ∃ J : Subgroup (∀ i, Γ i), IsOpen (J : Set (∀ i, Γ i)) ∧
      (J : Set (∀ i, Γ i)) ⊆ U ∧ J ≤ Subgroup.pi Set.univ K ∧
        ∀ x ∈ Subgroup.pi Set.univ K, ∀ j ∈ J, x * j * x⁻¹ ∈ J := by
  intro U hU
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, -, t, ht, hI⟩ := hU
  choose J h1 h2 h3 h4 using fun i => h i (t i) (ht i)
  exact ⟨Subgroup.pi Set.univ J, isOpen_set_pi Set.finite_univ fun i _ => h1 i,
    fun x hx => hI fun i _ => h2 i (hx i trivial), fun x hx i _ => h3 i (hx i trivial),
    fun x hx j hj i _ => h4 i _ (hx i trivial) _ (hj i trivial)⟩

end General

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β : Type} [Fintype α] [Fintype β] [LinearOrder β]
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {c : α → β → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
  {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

theorem isSmoothChar_relDeltaHalf : IsSmoothChar (relDeltaHalf k c) := by
  unfold relDeltaHalf
  refine Finset.prod_induction _ IsSmoothChar (fun _ _ => IsSmoothChar.mul) isSmoothChar_one
    fun a _ => ?_
  exact (isSmoothChar_deltaHalf k).comp _ (continuous_apply a)

theorem relInd_surjective (f : ∀ i, (Σ j, c i j) ≃ m i)
    {π : Representation ℂ (∀ i, Levi k (c i)) W} {π' : Representation ℂ (∀ i, Levi k (c i)) W'}
    (p : π.IntertwiningMap π') (hp : Function.Surjective p) (hπ : IsSmooth π) :
    Function.Surjective (smIndMap (compMap (twistMap p (relDeltaHalf k c)) (relProj k f))) := by
  have H := fun i => GlobalTheory.SmGL.LeviInt.levi_integral_facts k β (m i) (c i) (f i)
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hP : IsClosed (relParab k f : Set (Levi k m)) :=
    isClosed_set_pi fun i _ => (H i).2.2.2.2.2.2.1
  have hK : IsCompact (Subgroup.pi Set.univ (fun i => KO k (m i)) : Set (Levi k m)) :=
    isCompact_univ_pi fun i => SplitFlip.isCompact_KO
  have hPK : ∀ g : Levi k m, ∃ q ∈ relParab k f, ∃ x ∈ Subgroup.pi Set.univ (fun i => KO k (m i)),
      g = q * x := fun g => by
    choose q hq x hx e using fun i => (H i).2.2.2.2.2.2.2.2 (g i)
    exact ⟨q, fun i _ => hq i, x, fun i _ => hx i, funext e⟩
  have hcont : Continuous (relProj k f) := continuous_pi fun i =>
    (H i).2.2.2.2.2.1.comp (((continuous_apply i).comp continuous_subtype_val).subtype_mk _)
  let σ₀ : Representation ℂ (relParab k f) W := (twist π (relDeltaHalf k c)).comp (relProj k f)
  let z : Representation.IntertwiningMap σ₀ σ₀ :=
    { toLinearMap := 0, isIntertwining' := fun _ => by ext; simp }
  refine (GlobalTheory.SmGL.IndCoinv.smInd_coinvariants (Levi k m) (relParab k f) _ hP hK hPK
    (exists_normalised_pi _ fun i => GlobalTheory.SmGL.exists_open_normalised_subgroup_subset k (m i)) _ _ _ _
    (isSmooth_comp (isSmooth_twist hπ isSmoothChar_relDeltaHalf) _ hcont)
    (compMap (twistMap p _) _) Unit (fun _ => z) hp ?_).1
  intro x _
  refine Submodule.subset_span ⟨(), -x, ?_⟩
  show x = (0 : _) - -x
  simp

end Local

theorem jhMult_relInd_exact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α β : Type) [Fintype α] [Fintype β] [LinearOrder β] (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (c : α → β → Type) [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (f : ∀ i, (Σ j, c i j) ≃ m i) (W W₁ W₂ : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂] (π : Representation ℂ (∀ i, GlobalTheory.SmGL.Levi k (c i)) W) (π₁ : Representation ℂ (∀ i, GlobalTheory.SmGL.Levi k (c i)) W₁) (π₂ : Representation ℂ (∀ i, GlobalTheory.SmGL.Levi k (c i)) W₂) (ι : π₁.IntertwiningMap π) (p : π.IntertwiningMap π₂), Function.Injective ι → Function.Surjective p → (∀ u, p (ι u) = 0) → (∀ v, p v = 0 → ∃ u, ι u = v) → GlobalTheory.PRep.IsSmooth π → ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (GlobalTheory.SmGL.Levi k m) Y), τ.IsIrreducible → GlobalTheory.SmGL.jhMult τ (GlobalTheory.SmGL.relInd f π) = GlobalTheory.SmGL.jhMult τ (GlobalTheory.SmGL.relInd f π₁) + GlobalTheory.SmGL.jhMult τ (GlobalTheory.SmGL.relInd f π₂) := by
  intro k _ _ _ _ α β _ _ _ m _ _ c _ _ f W W₁ W₂ _ _ _ _ _ _ π π₁ π₂ ι p hι hp h0 hker hπ Y _ _ τ hτ
  refine GlobalTheory.JHMult.jhMult_exact
    (smIndMap (compMap (twistMap ι (relDeltaHalf k c)) (relProj k f)))
    (smIndMap (compMap (twistMap p (relDeltaHalf k c)) (relProj k f))) hτ
    (smIndMap_injective _ hι) (relInd_surjective f p hp hπ)
    (fun u => Subtype.ext (Subtype.ext (funext fun g => h0 _))) fun F hF => ?_
  exact exists_smIndMap_eq _ hι F fun g =>
    hker _ (congrFun (congrArg (fun χ => χ.1.1) hF) g)

end GlobalTheory.SmGL.IndExact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicitySpaceEqZeroOfApplyNonzeroTensorZero
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

noncomputable def tprodInnerFun {ι : Type} [Fintype ι] {E : ι → Type} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℂ (E i)] (w : ∀ i, E i) : (⨂[ℂ] i, E i) →ₗ[ℂ] ℂ :=
  PiTensorProduct.lift
    ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap (fun i => (innerSL ℂ (w i)).toLinearMap))

theorem tprodInnerFun_tprod {ι : Type} [Fintype ι] {E : ι → Type} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℂ (E i)] (w v : ∀ i, E i) :
    tprodInnerFun w (PiTensorProduct.tprod ℂ v) = ∏ i, ⟪w i, v i⟫_ℂ := by
  simp [tprodInnerFun]

theorem eq_zero_of_tprodInnerFun {ι : Type} [Fintype ι] {E : ι → Type} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℂ (E i)] (x : ⨂[ℂ] i, E i) (h : ∀ w, tprodInnerFun w x = 0) : x = 0 := by
  classical
  have hx : x ∈ Submodule.span ℂ (Set.range (PiTensorProduct.tprod ℂ (s := E))) := by
    rw [PiTensorProduct.span_tprod_eq_top]; trivial
  obtain ⟨n, f, g, hg⟩ := Submodule.mem_span_set'.1 hx
  choose v hv using fun j => (g j).2
  let W : ∀ i, Submodule ℂ (E i) := fun i => Submodule.span ℂ (Set.range fun j => v j i)
  haveI : ∀ i, FiniteDimensional ℂ (W i) := fun i =>
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  let b := fun i => stdOrthonormalBasis ℂ (W i)
  have hexp : ∀ j i, v j i = ∑ k, ⟪(b i k : E i), v j i⟫_ℂ • (b i k : E i) := by
    intro j i
    have hm : v j i ∈ W i := Submodule.subset_span ⟨j, rfl⟩
    have := congrArg (fun z : W i => (z : E i)) ((b i).sum_repr' ⟨v j i, hm⟩)
    simpa using this.symm
  have hj : ∀ j, PiTensorProduct.tprod ℂ (v j) =
      ∑ k : ∀ i, Fin (Module.finrank ℂ (W i)),
        (∏ i, ⟪(b i (k i) : E i), v j i⟫_ℂ) • PiTensorProduct.tprod ℂ (fun i => (b i (k i) : E i)) := by
    intro j
    have e : v j = fun i => ∑ k, ⟪(b i k : E i), v j i⟫_ℂ • (b i k : E i) := funext (hexp j)
    conv_lhs => rw [e]
    rw [MultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [MultilinearMap.map_smul_univ]
  have hx' : x = ∑ j, f j • PiTensorProduct.tprod ℂ (v j) := by
    rw [← hg]; simp [hv]
  have key : x = ∑ k : ∀ i, Fin (Module.finrank ℂ (W i)),
      tprodInnerFun (fun i => (b i (k i) : E i)) x • PiTensorProduct.tprod ℂ (fun i => (b i (k i) : E i)) := by
    conv_rhs => rw [hx']
    simp only [map_sum, map_smul, tprodInnerFun_tprod, Finset.sum_smul]
    rw [Finset.sum_comm, hx']
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hj j, Finset.smul_sum]
    simp [smul_smul]
  rw [key]; simp [h]

theorem eq_zero_of_integral_fundDomain {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure]
    (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (F : G → ℂ) (hc : Continuous F)
    (hinv : ∀ γ ∈ Γ, ∀ g, F (γ * g) = F g) (hi : IntegrableOn (fun g => star (F g) * F g) 𝓕 μ)
    (h0 : ∫ g in 𝓕, star (F g) * F g ∂μ = 0) : F = 0 := by
  have e : ∀ g, star (F g) * F g = ((‖F g‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    rw [Complex.star_def, Complex.conj_mul']; simp
  simp only [e] at hi h0
  rw [integral_complex_ofReal] at h0
  have h0' : ∫ g in 𝓕, ‖F g‖ ^ 2 ∂μ = 0 := by exact_mod_cast h0
  have hi' : Integrable (fun g => ‖F g‖ ^ 2) (μ.restrict 𝓕) := by
    have := Integrable.re hi
    simpa only [RCLike.re_to_complex, Complex.ofReal_re] using this
  have hae := (integral_eq_zero_iff_of_nonneg (fun g => by positivity) hi').1 h0'
  have hae' : ∀ᵐ g ∂μ.restrict 𝓕, F g = 0 := hae.mono fun g hg => by simpa using hg
  have ho : IsOpen {g | F g ≠ 0} := isOpen_ne_fun hc continuous_const
  have hz : μ {g | F g ≠ 0} = 0 := by
    refine h𝓕.measure_zero_of_invariant _ (fun γ => ?_) ?_
    · ext g
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      simp only [Set.mem_setOf_eq]
      rw [Subgroup.smul_def, smul_eq_mul, hinv _ (γ⁻¹).2]
    · rw [← Measure.restrict_apply ho.measurableSet]
      exact hae'
  have := (ho.measure_eq_zero_iff μ).1 hz
  funext g
  by_contra hg
  have : g ∈ {g | F g ≠ 0} := hg
  simp_all

theorem multT_eq_zero_of_apply_eq_zero : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S), ∀ J χ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), IsInfFam θ → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → SchurMult θ M J χ μ 𝓕 → ∀ u ∈ MultT θ M J χ, ∀ x : ⨂[ℂ] τ, M.sm τ, x ≠ 0 → u x = 0 → u = 0 := by
  intro D V S θ M J χ μ 𝓕 hθ hμ h𝓕 hS u hu x hx hux
  obtain ⟨-, -, -, hB, hG, -, hC⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  rw [mem_multT] at hu
  set T : MMap M := PiTensorProduct.lift.symm u with hT
  have hTv : ∀ v, T v = u (PiTensorProduct.tprod ℂ v) := fun v => by simp [hT]
  obtain ⟨c, hc⟩ := hS hθ hμ h𝓕 T hu T hu
  have hall : ∀ (w : M.Vec) (y : ⨂[ℂ] τ, M.sm τ), IntegrableOn (fun g => star (T w g) * u y g) 𝓕 μ ∧
      ∫ g in 𝓕, star (T w g) * u y g ∂μ = c * tprodInnerFun w y := by
    intro w y
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      obtain ⟨h1, h2⟩ := hc w v
      have e : (fun g => star (T w g) * u (r • PiTensorProduct.tprod ℂ v) g) =
          fun g => r * (star (T w g) * T v g) := by
        funext g; rw [map_smul, ← hTv]; simp only [Pi.smul_apply, smul_eq_mul]; ring
      rw [e]
      refine ⟨h1.const_mul r, ?_⟩
      rw [integral_const_mul, h2, map_smul, tprodInnerFun_tprod]
      simp only [Submodule.coe_inner, smul_eq_mul]; ring
    | add y z hy hz =>
      have e : (fun g => star (T w g) * u (y + z) g) =
          fun g => star (T w g) * u y g + star (T w g) * u z g := by
        funext g; rw [map_add]; simp only [Pi.add_apply]; ring
      rw [e]
      refine ⟨hy.1.add hz.1, ?_⟩
      rw [integral_add hy.1 hz.1, hy.2, hz.2, map_add]; ring
  have hc0 : c = 0 := by
    by_contra hne
    refine hx (eq_zero_of_tprodInnerFun x fun w => ?_)
    have := (hall w x).2
    rw [hux] at this
    simp only [Pi.zero_apply, mul_zero, integral_zero] at this
    exact (mul_eq_zero.1 this.symm).resolve_left hne
  have hT0 : ∀ v, T v = 0 := by
    intro v
    obtain ⟨h1, h2, -⟩ := GlobalTheory.mult_value_left_cont_level θ M J χ T hu v
    refine eq_zero_of_integral_fundDomain (GQ V) μ 𝓕 h𝓕 (T v) h2 h1 (hc v v).1 ?_
    rw [(hc v v).2, hc0, zero_mul]
  refine PiTensorProduct.ext ?_
  ext v g
  simp [← hTv, hT0]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FiniteFock

variable {D : D7}

theorem compAt_mt_of_finite (θ : InfFam D) (τ : D.what₂.Tau) {S : HSp D} {k : GA D S} (hk : k ∈ GfC S) :
    compAt θ τ (Formalism.L2.Theta.mt S k) = 1 := by
  have h1 : (Formalism.L2.Theta.mt S k).map (infPart D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hk)
  have h2 : compAt θ τ (Formalism.L2.Theta.mt S k) = ((Formalism.L2.Theta.mt S k).map (infPart D)).map (θ τ) := rfl
  rw [h2, h1]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem dRho_smul (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (c : ℂ) (f : WO S T → ℂ) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (c • f) = c • Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f := by
  funext x
  unfold Formalism.IndefR.Datum.dRho
  rw [Pi.smul_apply, smul_eq_mul, ← deriv_const_mul_field]
  congr 1
  funext t
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem pureTensorO_smul (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS sT BS BT) (c : ℂ)
    (f : WO S T → ℂ) (P) :
    pureTensorO ψ θ S T sS sT BS BT (c • f) P = c • pureTensorO ψ θ S T sS sT BS BT f P := by
  refine (GlobalTheory.OrientedHeis.pureTensorL_intertwine (fun _ => True) trivial (fun _ _ _ _ => trivial)
    (fun _ _ _ => trivial) _ _ (c • (1 : Module.End ℂ (WO S T → ℂ))) (fun k g _ => ⟨trivial, ?_⟩) f trivial P).2.symm
  simp only [aPlusAll, aPlus, crea, LinearMap.smul_apply, Module.End.one_apply]
  rw [dRho_smul, dRho_smul, smul_comm Complex.I c, ← smul_sub, smul_comm]

theorem pureTensorO_one (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS sT BS BT)
    (f : WO S T → ℂ) : pureTensorO ψ θ S T sS sT BS BT f 1 = f := by
  have e : (1 : MvPolynomial (FVar D T.rank S.rank) ℂ) = MvPolynomial.basisMonomials _ ℂ 0 := by
    rw [MvPolynomial.coe_basisMonomials]
    rfl
  unfold pureTensorO pureTensorL
  rw [e, Module.Basis.constr_basis]
  simp [opPow]

theorem om_pureTensorO_of_finite : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ sS sT BS BT f, (∀ P, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f P)) → ∀ k ∈ GfC S, ∀ k' ∈ GfC T, ∀ c : ℂ, om (k, k') f = c • f → ∀ P, om (k, k') (pureTensorO ψ θ S T sS sT BS BT f P) = c • pureTensorO ψ θ S T sS sT BS BT f P := by
  intro D ψ θ S T χS χT om hθ hom sS sT BS BT f hf k hk k' hk' c hc P
  have hf0 : IsThetaFunO ψ S T f := by simpa only [pureTensorO_one] using hf 1
  rw [(GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hom hθ sS sS BS BS sT sT BT BT k k'
    (fun τ => by rw [compAt_mt_of_finite θ τ hk, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [compAt_mt_of_finite θ τ hk', Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [compAt_mt_of_finite θ τ hk, Matrix.one_mul])
    (fun τ => by rw [compAt_mt_of_finite θ τ hk', Matrix.one_mul]) f hf0 P).2, hc, pureTensorO_smul]

end GlobalTheory.FiniteFock
end

