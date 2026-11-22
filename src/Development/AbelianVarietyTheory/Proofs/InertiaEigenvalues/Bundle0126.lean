import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSelfDualOfDualSubgroups
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0080
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0059
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0109
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Sl2PresentationRelations
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0110
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0111
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComapInlMemStLat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLatticePairsIndexRpowLe

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualMeasureExistsUniqueFourierInversion
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.SelfDualUniq

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]

theorem fourB_nnsmul (μ : Measure V) (c : NNReal) (B : V → V → ℂ) (f : V → ℂ) (y : V) :
    fourB (c • μ) B f y = ((c : ℝ) : ℂ) * fourB μ B f y := by
  simp only [fourB, integral_smul_nnreal_measure]
  rw [NNReal.smul_def, Complex.real_smul]

theorem fourB_const_mul (μ : Measure V) (a : ℂ) (B : V → V → ℂ) (g : V → ℂ) (y : V) :
    fourB μ B (fun z => a * g z) y = a * fourB μ B g y := by
  simp only [fourB, mul_assoc]
  exact integral_const_mul a _

theorem selfDual_unique [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [BorelSpace V] {B : V → V → ℂ} {μ ν : Measure V}
    (hμ : SelfDual μ B) (hν : SelfDual ν B) (f : V → ℂ) (hf : IsTest f) (h0 : f 0 ≠ 0) : ν = μ := by
  obtain ⟨hμH, hμI⟩ := hμ
  obtain ⟨hνH, hνI⟩ := hν
  have hc := Measure.isAddLeftInvariant_eq_smul ν μ
  set c := Measure.addHaarScalarFactor ν μ
  have key := hνI f hf 0
  rw [hc] at key
  have e : fourB (c • μ) B f = fun y => ((c : ℝ) : ℂ) * fourB μ B f y := funext (fourB_nnsmul μ c B f)
  rw [e, fourB_nnsmul, fourB_const_mul, hμI f hf 0, neg_zero] at key
  have hsq : (((c : ℝ) : ℂ) * ((c : ℝ) : ℂ) - 1) * f 0 = 0 := by linear_combination key
  have h1 : ((c : ℝ) : ℂ) * ((c : ℝ) : ℂ) = 1 := by
    have := (mul_eq_zero.1 hsq).resolve_right h0
    linear_combination this
  have h2 : (c : ℝ) * (c : ℝ) = 1 := by exact_mod_cast h1
  have h3 : (c : ℝ) = 1 := by nlinarith [c.coe_nonneg]
  have h4 : c = 1 := by exact_mod_cast h3
  rw [hc, h4, one_smul]

end GlobalTheory.JR.SelfDualUniq

namespace GlobalTheory.JR.SelfDualUniq

theorem isTest_fourB {F : Type} [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F]
    (ψ : AddChar F ℂ) (hψ : IsStdChar ψ)
    (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V]
    [MeasurableSpace V] [BorelSpace V] (β : LinearMap.BilinForm F V) (hs : β.IsSymm) (hn : β.Nondegenerate)
    (μ : Measure V) [μ.IsAddHaarMeasure] (f : V → ℂ) (hf : IsTest f) :
    IsTest (fourB μ (fun x y => ψ (β x y)) f) := by
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F V
  obtain ⟨-, hl⟩ := GlobalTheory.JR.exists_small_dual_lattices F ψ hψ V β hs hn
  obtain ⟨U, hU, hUinv⟩ := AbsInv.exists_nhds_invariant hf
  obtain ⟨M, N, hMU, -, -, -, hNc, hN, -⟩ := hl U hU
  have hβ : Continuous (fun p : V × V => β p.1 p.2) :=
    IsModuleTopology.continuous_bilinear_of_finite_left β
  have hev : ∀ᶠ w in 𝓝 (0 : V), ∀ x ∈ tsupport f, ψ (β x w) = 1 := by
    refine hf.2.isCompact.eventually_forall_of_forall_eventually fun x _ => ?_
    have hc : Continuous (fun z : V × V => β z.2 z.1) := hβ.comp continuous_swap
    have ho : IsOpen {z : V × V | ‖β z.2 z.1‖ < 1} := isOpen_lt (continuous_norm.comp hc) continuous_const
    have hmem : ((0 : V), x) ∈ {z : V × V | ‖β z.2 z.1‖ < 1} := by simp
    filter_upwards [ho.mem_nhds hmem] with z hz
    exact hψ.1 _ hz.le
  constructor
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro y
    have hev' : ∀ᶠ y' in 𝓝 y, ∀ x ∈ tsupport f, ψ (β x (y' - y)) = 1 := by
      have ht : Tendsto (fun y' : V => y' - y) (𝓝 y) (𝓝 0) := by
        have h := (continuous_sub_right y).tendsto y
        rwa [sub_self] at h
      exact ht.eventually hev
    filter_upwards [hev'] with y' hy'
    simp only [fourB]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport f
    · have : β x y' = β x y + β x (y' - y) := by simp
      simp only [this, AddChar.map_add_eq_mul, hy' x hx, mul_one]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · refine HasCompactSupport.intro hNc fun y hy => ?_
    have : ¬ ∀ x ∈ M, ψ (β x y) = 1 := fun h => hy ((hN y).2 h)
    push_neg at this
    obtain ⟨m, hm, hne⟩ := this
    refine AbsInv.integral_eq_zero_of_translate μ _ m _ hne fun x => ?_
    simp only [map_add, LinearMap.add_apply, AddChar.map_add_eq_mul, hUinv M hMU x m hm]
    ring

theorem selfDual_exists_unique_isTest : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] (β : LinearMap.BilinForm F V), β.IsSymm → β.Nondegenerate → (∃! μ : Measure V, SelfDual μ (fun x y => ψ (β x y))) ∧ ∀ μ : Measure V, μ.IsAddHaarMeasure → ∀ f, IsTest f → IsTest (fourB μ (fun x y => ψ (β x y)) f) := by
  intro F E _ _ _ _ hU ψ hψ V _ _ _ _ _ _ _ β hs hn
  haveI := hU.ultraF
  haveI := hU.lcF
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F V
  obtain ⟨-, hl⟩ := GlobalTheory.JR.exists_small_dual_lattices F ψ hψ V β hs hn
  obtain ⟨M, N, -, hMo, hMc, -, -, -, -⟩ := hl Set.univ Filter.univ_mem
  have hM1 : IsClopen (M : Set V) := ⟨AddSubgroup.isClosed_of_isOpen M hMo, hMo⟩
  set f : V → ℂ := ⇑(LocallyConstant.charFn ℂ hM1) with hfdef
  have hf : IsTest f := ⟨(LocallyConstant.charFn ℂ hM1).isLocallyConstant,
    HasCompactSupport.intro hMc fun x hx => by simp [f, LocallyConstant.coe_charFn, hx]⟩
  have hf0 : f 0 ≠ 0 := by simp [f, LocallyConstant.coe_charFn, M.zero_mem]
  refine ⟨?_, fun μ hμ g hg => isTest_fourB ψ hψ V β hs hn μ g hg⟩
  obtain ⟨μ, hμ⟩ := EtMeas.exists_selfDual F ψ hψ V β hs hn
  exact ⟨μ, hμ, fun ν hν => selfDual_unique hμ hν f hf hf0⟩

end GlobalTheory.JR.SelfDualUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultiplicityLatticeCountRelation
section
noncomputable section
namespace GlobalTheory.PhiGam.Count
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

section
variable {k U : Type} [Field k] [AddCommGroup U] [Module k U]

theorem exists_le_sup (P Q : Submodule k U) [FiniteDimensional k (P.map Q.mkQ)] :
    ∃ F : Submodule k U, FiniteDimensional k F ∧ P ≤ F ⊔ Q := by
  obtain ⟨σ, hσ⟩ := Q.mkQ.exists_rightInverse_of_surjective (Submodule.range_mkQ Q)
  refine ⟨(P.map Q.mkQ).map σ, inferInstance, fun p hp => ?_⟩
  refine Submodule.mem_sup.2 ⟨σ (Q.mkQ p), ⟨_, ⟨p, hp, rfl⟩, rfl⟩, p - σ (Q.mkQ p), ?_, by abel⟩
  have h : Q.mkQ (σ (Q.mkQ p)) = Q.mkQ p := LinearMap.congr_fun hσ _
  exact (Submodule.Quotient.eq _).mp h.symm

theorem finite_of_le_sup {P Q F : Submodule k U} [FiniteDimensional k F] (h : P ≤ F ⊔ Q) :
    FiniteDimensional k (↥P ⧸ Q.submoduleOf P) := by
  have hker : LinearMap.ker (Q.mkQ ∘ₗ P.subtype) = Q.submoduleOf P := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]; rfl
  have hle : LinearMap.range (Q.mkQ ∘ₗ P.subtype) ≤ F.map Q.mkQ := by
    rintro _ ⟨⟨p, hp⟩, rfl⟩
    obtain ⟨f, hf, q, hq, rfl⟩ := Submodule.mem_sup.1 (h hp)
    refine ⟨f, hf, ?_⟩
    change Q.mkQ f = Q.mkQ (f + q)
    rw [map_add, show Q.mkQ q = 0 from (Submodule.Quotient.mk_eq_zero _).mpr hq, add_zero]
  haveI : FiniteDimensional k (LinearMap.range (Q.mkQ ∘ₗ P.subtype)) :=
    Submodule.finiteDimensional_of_le hle
  rw [← hker]
  exact LinearEquiv.finiteDimensional (LinearMap.quotKerEquivRange _).symm

theorem gmult_eq_zero (T : Module.End k U) {P Q M : Submodule k U} (hPM : P ≤ M) (hM : ∀ p ∈ M, T p ∈ M)
    (x : k) (h : ∀ p ∈ M, T p - x • p ∈ Q → p ∈ Q) (hQ : ∀ p ∈ Q, T p ∈ Q) : gmult T P Q x = 0 := by
  set S : Module.End k U := T - algebraMap k (Module.End k U) x with hS
  have hSa : ∀ p, S p = T p - x • p := fun p => by simp [hS, Module.algebraMap_end_apply]
  have key : ∀ m : ℕ, ∀ p ∈ M, (S ^ m) p ∈ Q → p ∈ Q := by
    intro m
    induction m with
    | zero => intro p _ hp; simpa using hp
    | succ m ih =>
      intro p hp hq
      rw [pow_succ, Module.End.mul_apply] at hq
      have h1 : S p ∈ M := by rw [hSa]; exact M.sub_mem (hM p hp) (M.smul_mem _ hp)
      exact h p hp (hSa p ▸ ih _ h1 hq)
  have hmono : Monotone fun m : ℕ => Q.comap (S ^ m) := by
    refine monotone_nat_of_le_succ fun m p hp => ?_
    rw [Submodule.mem_comap] at hp ⊢
    rw [pow_succ', Module.End.mul_apply, hSa]
    exact Q.sub_mem (hQ _ hp) (Q.smul_mem _ hp)
  have hle : P ⊓ ⨆ m : ℕ, Q.comap (S ^ m) ≤ Q := by
    rintro p ⟨hp, hq⟩
    obtain ⟨m, hm⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).1 hq
    exact key m p (hPM hp) hm
  unfold gmult
  rw [← hS, Submodule.submoduleOf_eq_top.2 hle]
  exact Module.finrank_zero_of_subsingleton

end

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

theorem exists_le_sup_sh {N : Submodule k⟦X⟧ V} (hN : IsLat N) (m : ℕ) :
    ∃ F : Submodule k V, FiniteDimensional k F ∧
      N.restrictScalars k ≤ F ⊔ (sh m N).restrictScalars k := by
  induction m with
  | zero => exact ⟨⊥, inferInstance, by simp [sh_zero_eq]⟩
  | succ m ih =>
    obtain ⟨F, hF, h⟩ := ih
    haveI := Window.finite_quot (hN.shift m).1
    obtain ⟨F', hF', h'⟩ := exists_le_sup ((sh m N).restrictScalars k) ((sh 1 (sh m N)).restrictScalars k)
    rw [sh_sh_eq, add_comm] at h'
    refine ⟨F ⊔ F', inferInstance, h.trans ?_⟩
    rw [sup_assoc, Nat.cast_succ]
    exact sup_le_sup_left h' _

theorem graded_inj {l : ℕ} (R : RingPG k l) {g : V →ₗ[k] V} (hg : Semi R.γ g) {N : Submodule k⟦X⟧ V}
    (hN : N.FG) (hC : CondC g N) (b : ℤ) (x : k) (h : sen g N (x + b) = 0) :
    ∀ y ∈ sh b N, nab g y - x • y ∈ sh (b + 1) N → y ∈ sh (b + 1) N := by
  haveI := Window.finite_quot hN
  obtain ⟨h1, -⟩ := Window.bij_of_gmult_zero (nab g) (N.restrictScalars k) ((sh 1 N).restrictScalars k)
    (fun p hp => Window.nab_mem hC hp) (fun p hp => Window.nab_mem_sh R hg hC 1 hp) (x + b) h
  have hv : vv k ≠ 0 := vv_ne_zero k
  intro y hx hx'
  obtain ⟨n, hn, rfl⟩ := mem_sh_iff_exists.mp hx
  obtain ⟨n', hn', e⟩ := Window.nab_shift R hg hC b hn
  obtain ⟨t, ht, e'⟩ := mem_sh_iff_exists.mp hx'
  have hc : x • vv k ^ b • n = vv k ^ b • x • n := by
    rw [← smul_assoc, const_smul_eq, mul_comm, mul_smul, ← mul_one (algebraMap k k⸨X⸩ x), ← const_smul_eq,
      smul_assoc, one_smul]
  rw [e, hc, zpow_add_one₀ hv, mul_smul, ← smul_sub] at e'
  have e2 := smul_right_injective V (zpow_ne_zero b hv) e'
  have : n ∈ sh 1 N := h1 n hn (mem_sh_iff_exists.mpr ⟨t - n', N.sub_mem ht hn', by
    rw [zpow_one, smul_sub, e2, add_smul]; abel⟩)
  obtain ⟨r, hr, rfl⟩ := mem_sh_iff_exists.mp this
  exact mem_sh_iff_exists.mpr ⟨r, hr, by rw [zpow_add₀ hv, mul_smul]⟩

theorem window_inj {l : ℕ} (R : RingPG k l) {g : V →ₗ[k] V} (hg : Semi R.γ g) {N : Submodule k⟦X⟧ V}
    (hN : N.FG) (hC : CondC g N) (x : k) (s : ℕ) (h : ∀ j : ℕ, 1 ≤ j → j ≤ s → sen g N (x - j) = 0) :
    ∀ y ∈ sh (-s) N, nab g y - x • y ∈ N → y ∈ N := by
  induction s with
  | zero => intro y hy _; simpa [sh_zero_eq] using hy
  | succ s ih =>
    intro y hy hy'
    refine ih (fun j h1 h2 => h j h1 (Nat.le_succ_of_le h2)) y ?_ hy'
    have e : (-((s + 1 : ℕ) : ℤ)) + 1 = -(s : ℤ) := by push_cast; ring
    have := graded_inj R hg hN hC (-((s + 1 : ℕ) : ℤ)) x (by
      rw [Int.cast_neg, Int.cast_natCast, ← sub_eq_add_neg]; exact h _ (Nat.succ_pos s) le_rfl) y hy
    rw [e] at this
    refine this (sh_le_sh_of_le (a := 0) (by omega) N ?_)
    rwa [sh_zero_eq]

theorem sen_count : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ P Q : Submodule k⟦X⟧ V, IsLat P → IsLat Q → Q ≤ P → CondC g P → CondC g Q → ∀ s : ℕ, P ≤ sh (-s) Q → ∀ x : k, sen g P x + qmult g P Q (x + 1) = sen g Q x + qmult g P Q x ∧ (qmult g P Q x ≠ 0 → ∃ j : ℕ, 1 ≤ j ∧ j ≤ s ∧ sen g Q (x - j) ≠ 0) := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ g hg P Q hP hQ hQP cP cQ s hs x
  constructor
  · have h1 : ∀ N : Submodule k⟦X⟧ V, sh 1 N ≤ N := fun N => by
      have := sh_le_sh_of_le (a := 1) (b := 0) (by norm_num) N
      rwa [sh_zero_eq] at this
    obtain ⟨F, hF, hle⟩ := exists_le_sup_sh hP (s + 1)
    have h2 : sh ((s + 1 : ℕ) : ℤ) P ≤ sh 1 Q := by
      have := sh_le_sh ((s + 1 : ℕ) : ℤ) hs
      rwa [sh_sh_eq, show ((s + 1 : ℕ) : ℤ) + -(s : ℤ) = 1 by push_cast; ring] at this
    have hfin : FiniteDimensional k (↥(P.restrictScalars k) ⧸
        ((sh 1 Q).restrictScalars k).submoduleOf (P.restrictScalars k)) :=
      finite_of_le_sup (F := F) (hle.trans (sup_le_sup_left (fun _ hy => h2 hy) _))
    have a1 := GlobalTheory.PhiGam.GmultAdd.main (nab g) (P.restrictScalars k) ((sh 1 P).restrictScalars k)
      ((sh 1 Q).restrictScalars k) (fun _ hy => sh_le_sh 1 hQP hy) (fun _ hy => h1 P hy)
      (fun _ hy => Window.nab_mem cP hy) (fun _ hy => Window.nab_mem_sh R hg cP 1 hy)
      (fun _ hy => Window.nab_mem_sh R hg cQ 1 hy) hfin x
    have a2 := GlobalTheory.PhiGam.GmultAdd.main (nab g) (P.restrictScalars k) (Q.restrictScalars k)
      ((sh 1 Q).restrictScalars k) (fun _ hy => h1 Q hy) (fun _ hy => hQP hy)
      (fun _ hy => Window.nab_mem cP hy) (fun _ hy => Window.nab_mem cQ hy)
      (fun _ hy => Window.nab_mem_sh R hg cQ 1 hy) hfin x
    rw [← GlobalTheory.T.quotientMultiplicity_shift_lattice_quotient R g hg P Q hP hQ hQP cP cQ x]
    unfold sen qmult
    omega
  · intro hne
    by_contra hno
    push Not at hno
    exact hne (gmult_eq_zero (nab g) (M := (sh (-s) Q).restrictScalars k) (fun _ hy => hs hy)
      (fun _ hy => Window.nab_mem_sh R hg cQ _ hy) x (window_inj R hg hQ.1 cQ x s hno)
      (fun _ hy => Window.nab_mem cQ hy))

end GlobalTheory.PhiGam.Count
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SingleMemOfSupportSubset
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.Per

theorem single_mem_of_support_subset {LL D : Type} [Field LL] [AddCommGroup D] [Module LL D]
    (u : LL) (Λ : Submodule LL (ℤ → D)) (hu : u ≠ 0) (hr : ∀ k : ℤ, k ≠ 0 → u ^ k ≠ 1)
    (hγ : ∀ x ∈ Λ, (fun k => u ^ k • x k) ∈ Λ) (S : Finset ℤ) :
    ∀ x ∈ Λ, (∀ k, k ∉ S → x k = 0) → ∀ k, Pi.single k (x k) ∈ Λ := by
  induction S using Finset.induction_on with
  | empty =>
    intro x _ hx k
    rw [hx k (by simp), Pi.single_zero]
    exact Λ.zero_mem
  | insert a S' ha ih =>
    intro x hxΛ hx

    have hne : ∀ k, k ≠ a → u ^ k - u ^ a ≠ 0 := by
      intro k hk h
      apply hr (k - a) (sub_ne_zero.mpr hk)
      rw [zpow_sub₀ hu, sub_eq_zero.mp h, div_self (zpow_ne_zero a hu)]
    have hyΛ : (fun k => u ^ k • x k) - u ^ a • x ∈ Λ := Λ.sub_mem (hγ x hxΛ) (Λ.smul_mem _ hxΛ)
    have hyv : ∀ k, ((fun k => u ^ k • x k) - u ^ a • x) k = (u ^ k - u ^ a) • x k := by
      intro k
      simp [sub_smul]
    have hy : ∀ k, k ∉ S' → ((fun k => u ^ k • x k) - u ^ a • x) k = 0 := by
      intro k hk
      rw [hyv]
      by_cases hka : k = a
      · rw [hka, sub_self, zero_smul]
      · rw [hx k (by simp [hka, hk]), smul_zero]
    have hoff : ∀ k, k ≠ a → Pi.single k (x k) ∈ Λ := by
      intro k hk
      have h1 := ih _ hyΛ hy k
      rw [hyv] at h1
      have e : Pi.single k (x k) =
          (u ^ k - u ^ a)⁻¹ • (Pi.single k ((u ^ k - u ^ a) • x k) : ℤ → D) := by
        rw [Pi.single_smul, smul_smul, inv_mul_cancel₀ (hne k hk), one_smul]
      rw [e]
      exact Λ.smul_mem _ h1
    intro k
    by_cases hka : k = a
    · rw [hka]
      have hsum : (∑ j ∈ S', Pi.single j (x j)) ∈ Λ :=
        Λ.sum_mem (fun j hj => hoff j (by rintro rfl; exact ha hj))
      have e : Pi.single a (x a) = x - ∑ j ∈ S', Pi.single j (x j) := by
        funext j
        rw [Pi.sub_apply, Finset.sum_apply, Finset.sum_pi_single]
        by_cases hjS : j ∈ S'
        · have hja : j ≠ a := by rintro rfl; exact ha hjS
          simp [hjS, hja]
        · by_cases hja : j = a
          · rw [hja]
            simp [ha]
          · simp [hjS, hja, hx j (by simp [hja, hjS])]
      rw [e]
      exact Λ.sub_mem hxΛ hsum
    · exact hoff k hka

end GlobalTheory.Per
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Sl2PresentationRelationsStatement
section
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hom_specialLinearGroup_of_relations : ∀ (K : Type) [CommRing K], IsField K → ∀ (M : Type) [Monoid M] (n : K → M) (m : Kˣ → M) (t : M), n 0 = 1 → (∀ a b, n (a + b) = n a * n b) → m 1 = 1 → (∀ a b, m (a * b) = m a * m b) → (∀ s z, m s * n z = n ((s : K) ^ 2 * z) * m s) → t * t = m (-1) → (∀ s, t * m s = m s⁻¹ * t) → (∀ u : Kˣ, t * n u * t = n (-((u⁻¹ : Kˣ) : K)) * m (-u⁻¹) * t * n (-((u⁻¹ : Kˣ) : K))) → ∃ ρ : SpecialLinearGroup (Fin 2) K →* M, (∀ z, ρ (nS z) = n z) ∧ (∀ s, ρ (mS s) = m s) ∧ ρ (wS K) = t := by
  first | exact @GlobalTheory.BruhatRep.exists_hom_of_bruhat | exact GlobalTheory.BruhatRep.exists_hom_of_bruhat | (intros; apply GlobalTheory.BruhatRep.exists_hom_of_bruhat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanPowGeneratorEqTopOfCharpolySeparableStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_pow_generator_eq_top_of_charpoly_separable : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → Submodule.span K.E (Set.range fun i : ℕ => B.g ^ i) = ⊤ := by
  first | exact @GlobalTheory.UnitLemma.Unr.span_pow_eq_top_of_separable | exact GlobalTheory.UnitLemma.Unr.span_pow_eq_top_of_separable | (intros; apply GlobalTheory.UnitLemma.Unr.span_pow_eq_top_of_separable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StabilizerStableLatticeLeIntegralUnitsSubgroupStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_stableLattice_le_integralUnitsSubgroup : ∀ (O E A : Type) [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A] (g : A) (L : stLat O E g), MulAction.stabilizer Aˣ L ≤ intUnits O A := by
  first | exact @GlobalTheory.UnitLemma.stabilizer_le_intUnits | exact GlobalTheory.UnitLemma.stabilizer_le_intUnits | (intros; apply GlobalTheory.UnitLemma.stabilizer_le_intUnits <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StabilizerStableLatticePairRelIndexIntegralUnitsStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_stableLatticePair_relIndex_integralUnits : ∀ (O E A₁ A₂ : Type) [CommRing O] [Field E] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂] (g₁ : A₁) (g₂ : A₂) (y : LatPair O E g₁ g₂), MulAction.stabilizer A₁ˣ y.1 ≤ intUnits O A₁ → MulAction.stabilizer A₂ˣ y.2 ≤ intUnits O A₂ → MulAction.stabilizer (A₁ × A₂)ˣ y ≤ intUnits O (A₁ × A₂) ∧ (MulAction.stabilizer (A₁ × A₂)ˣ y).relIndex (intUnits O (A₁ × A₂)) = (MulAction.stabilizer A₁ˣ y.1).relIndex (intUnits O A₁) * (MulAction.stabilizer A₂ˣ y.2).relIndex (intUnits O A₂) := by
  first | exact @GlobalTheory.UnitLemma.PairStab.stabilizer_pair_relIndex | exact GlobalTheory.UnitLemma.PairStab.stabilizer_pair_relIndex | (intros; apply GlobalTheory.UnitLemma.PairStab.stabilizer_pair_relIndex <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableLatticeOrbitCountEqSumOrbitsStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stableLatticeOrbitCount_eq_sum_orbits : ∀ (O E A : Type) [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A] (g : A), countGL O E g = ∑ᶠ o : MulAction.orbitRel.Quotient Aˣ (stLat O E g), ((MulAction.stabilizer Aˣ (Quotient.out o)).relIndex (intUnits O A) : ℚ) := by
  first | exact @GlobalTheory.UnitLemma.countGL_eq_sum_orbits | exact GlobalTheory.UnitLemma.countGL_eq_sum_orbits | (intros; apply GlobalTheory.UnitLemma.countGL_eq_sum_orbits <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableLatticePairOrbitsFiniteAndCardProdStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stableLatticePair_orbits_finite_and_card_prod : ∀ (O E A₁ A₂ : Type) [CommRing O] [Field E] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂] (g₁ : A₁) (g₂ : A₂), Finite (MulAction.orbitRel.Quotient A₁ˣ (stLat O E g₁)) → Finite (MulAction.orbitRel.Quotient A₂ˣ (stLat O E g₂)) → Finite (MulAction.orbitRel.Quotient (A₁ × A₂)ˣ (LatPair O E g₁ g₂)) ∧ ∀ (f₁ : stLat O E g₁ → ℚ) (f₂ : stLat O E g₂ → ℚ), (∀ (t : A₁ˣ) (y : stLat O E g₁), f₁ (t • y) = f₁ y) → (∀ (t : A₂ˣ) (y : stLat O E g₂), f₂ (t • y) = f₂ y) → ∑ᶠ o : MulAction.orbitRel.Quotient (A₁ × A₂)ˣ (LatPair O E g₁ g₂), f₁ (Quotient.out o).1 * f₂ (Quotient.out o).2 = (∑ᶠ o : MulAction.orbitRel.Quotient A₁ˣ (stLat O E g₁), f₁ (Quotient.out o)) * (∑ᶠ o : MulAction.orbitRel.Quotient A₂ˣ (stLat O E g₂), f₂ (Quotient.out o)) := by
  first | exact @GlobalTheory.UnitLemma.latPair_orbit_finite_and_sum | exact GlobalTheory.UnitLemma.latPair_orbit_finite_and_sum | (intros; apply GlobalTheory.UnitLemma.latPair_orbit_finite_and_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableLatticePairProjectionSmulUnitsStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stableLatticePair_projection_smul_units : ∀ (O E A₁ A₂ : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂] (g₁ : A₁) (g₂ : A₂) (t : (A₁ × A₂)ˣ) (M : stLat O E ((g₁, g₂) : A₁ × A₂)), latProj O E g₁ g₂ (t • M) = t • latProj O E g₁ g₂ M := by
  first | exact @GlobalTheory.UnitLemma.latProj_smul | exact GlobalTheory.UnitLemma.latProj_smul | (intros; apply GlobalTheory.UnitLemma.latProj_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableQuadraticGaussIntegralMulNorm
section
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open scoped Pointwise ENNReal NNReal

namespace GlobalTheory.JR.WeilQuad.GaussTrans

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ (t s : A.Kˣ), (∃ ℓ : A.L, A.NL ℓ = s) → ∀ G : ℂ, IsStableGauss A ψ x μ t G → IsStableGauss A ψ x μ ((t * s : A.Kˣ) : A.K) (G * ((A.absK s : ℂ))⁻¹) := by
  intro F E _ _ _ _ U A ψ x μ ω hH t s ⟨ℓ, hℓ⟩ G ⟨Λ₀, ho₀, hc₀, hG⟩
  have := U.charZero; have := U.ultraF; have := U.lcF
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  have := EtMeas.finite_L A
  obtain ⟨⟨b⟩, hinj, hN, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.K
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.L
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  have : ContinuousStar A.L := ⟨IsModuleTopology.continuous_of_linearMap (EtMeas.starF A)⟩
  have hμ : μ.IsAddHaarMeasure := hH.2.2.2.1.1
  have hs' : algebraMap A.K A.L (s : A.K) = ℓ * star ℓ := by rw [← hℓ, hN]
  have hu : IsUnit ℓ := isUnit_of_mul_isUnit_left (hs' ▸ (s.isUnit.map (algebraMap A.K A.L)))
  set u : A.Lˣ := hu.unit with hu_def
  have hul : (u : A.L) = ℓ := hu.unit_spec
  have hmod : distribHaarChar A.L u = distribHaarChar A.K s :=
    GlobalTheory.JR.ModuleNorm.distribHaarChar_eq_norm A.K A.L b.equivFun.symm
      (IsModuleTopology.continuous_of_linearMap (b.equivFun.symm.toLinearMap.restrictScalars F))
      (IsModuleTopology.continuous_of_linearMap (b.equivFun.toLinearMap.restrictScalars F)) u s
      (by rw [hul]; exact hs')
  have hmap : μ.map (fun y => u • y) = (distribHaarChar A.L u⁻¹ : ℝ≥0∞) • μ := by
    ext S hS
    rw [Measure.map_apply (measurable_const_smul u) hS, Set.preimage_smul, Measure.smul_apply, smul_eq_mul,
      distribHaarChar_mul]
  have hemb : MeasurableEmbedding (fun y : A.L => u • y) :=
    (Homeomorph.smul u).measurableEmbedding
  have key : ∀ Λ : AddSubgroup A.L, gaussInt A ψ x μ ((t * s : A.Kˣ) : A.K) Λ =
      ((A.absK s : ℂ))⁻¹ * gaussInt A ψ x μ t (u • Λ : AddSubgroup A.L) := by
    intro Λ
    have h1 : gaussInt A ψ x μ ((t * s : A.Kˣ) : A.K) Λ =
        ∫ y in (Λ : Set A.L), A.psiK ψ ((t : A.K) * x * A.NL (u • y)) ∂μ := by
      unfold gaussInt
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      have hNm : A.NL (u • y) = s * A.NL y := by
        rw [Units.smul_def, hul, smul_eq_mul]
        unfold Et.NL
        rw [map_mul]
        exact congrArg (· * _) hℓ
      simp only
      rw [hNm]
      push_cast; ring_nf
    have h2 := hemb.setIntegral_map (μ := μ) (fun z => A.psiK ψ ((t : A.K) * x * A.NL z)) ((u • Λ : AddSubgroup A.L) : Set A.L)
    have hpre : (fun y => u • y) ⁻¹' ((u • Λ : AddSubgroup A.L) : Set A.L) = Λ := by
      ext y
      simp only [Set.mem_preimage, SetLike.mem_coe]
      exact ⟨fun h => by simpa using (AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem.1 h),
        fun h => AddSubgroup.smul_mem_pointwise_smul _ _ _ h⟩
    rw [hpre, hmap, Measure.restrict_smul, integral_smul_measure] at h2
    rw [h1, ← h2]
    unfold gaussInt
    rw [Complex.real_smul, EtMeas.absK_unit, ENNReal.coe_toReal, map_inv, hmod]
    congr 1
    push_cast
    rfl
  have hcoe : ∀ (v : A.Lˣ) (M : AddSubgroup A.L), ((v • M : AddSubgroup A.L) : Set A.L) = v • (M : Set A.L) :=
    fun v M => AddSubgroup.coe_pointwise_smul v M
  refine ⟨u⁻¹ • Λ₀, ?_, ?_, fun Λ hoΛ hcΛ hle => ?_⟩
  · rw [hcoe]; exact ho₀.smul _
  · rw [hcoe]; exact hc₀.smul _
  · rw [key, hG (u • Λ) (by rw [hcoe]; exact hoΛ.smul _) (by rw [hcoe]; exact hcΛ.smul _) ?_, mul_comm]
    intro z hz
    have : u⁻¹ • z ∈ Λ := hle (AddSubgroup.smul_mem_pointwise_smul _ _ _ hz)
    exact AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem.2 this

end GlobalTheory.JR.WeilQuad.GaussTrans
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLatticePairsIndexRpowLeStatement
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_lattice_pairs_index_rpow_le : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (σ : ℝ), (r : ℝ) - 1 < σ → ∀ C : Finset (GL (Fin r) K), (∀ g ∈ C, ∀ g' ∈ C, (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) = (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((g' : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) → g = g') → ∑ g ∈ C, (((((Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O)).toAddSubgroup.relIndex (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).toAddSubgroup : ℕ) : ℝ) * (((Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).toAddSubgroup.relIndex ((Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O)).toAddSubgroup : ℕ) : ℝ)) ^ (-σ) ≤ (∏ i ∈ Finset.range r, (1 - (Nat.card (IsLocalRing.ResidueField O) : ℝ) ^ ((i : ℝ) - σ))⁻¹) ^ 2 := by
  first | exact @GlobalTheory.LatticePairSum.sum_index_pairs_le | exact GlobalTheory.LatticePairSum.sum_index_pairs_le | (intros; apply GlobalTheory.LatticePairSum.sum_index_pairs_le <;> assumption)
end

