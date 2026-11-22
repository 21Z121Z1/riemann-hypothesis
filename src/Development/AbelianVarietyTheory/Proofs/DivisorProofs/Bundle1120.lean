import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianInvariantFormsProportionalFinitePlace
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0925
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1074
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1032
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1081
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1035
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1082
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagCoIsotropic
section
open scoped Matrix
open GlobalTheory.WeilM GlobalTheory.LinPair

noncomputable section

namespace GlobalTheory.LagrFormLine

open MeasureTheory ValuativeRel

theorem finrank_le {k : Type} [Field k] {κ : Type} [Fintype κ] (Λ : Submodule k ((κ → k) × (κ → k)))
    (h : ∀ a ∈ Λ, ∀ b ∈ Λ, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) : Module.finrank k Λ ≤ Fintype.card κ := by
  have hle : Λ ≤ (GlobalTheory.LagrInvForm.symp k κ).orthogonal Λ := fun b hb a ha => sub_eq_zero.2 (h a ha b hb)
  have hr := LinearMap.BilinForm.finrank_orthogonal (GlobalTheory.LagrInvForm.symp_nondeg k κ) Λ
  have h3 := Submodule.finrank_mono hle
  rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card] at hr
  omega

theorem finrank_eq {k : Type} [Field k] {κ : Type} [Fintype κ] (Λ Λ' : Submodule k ((κ → k) × (κ → k)))
    (h : ∀ a ∈ Λ, ∀ b ∈ Λ, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) (h' : ∀ a ∈ Λ', ∀ b ∈ Λ', a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2)
    (hs : Λ ⊔ Λ' = ⊤) : Module.finrank k Λ = Fintype.card κ := by
  have h1 := finrank_le Λ h
  have h2 := finrank_le Λ' h'
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq Λ Λ'
  rw [hs, finrank_top, Module.finrank_prod, Module.finrank_fintype_fun_eq_card] at h3
  omega

theorem isLocallyConstant_char (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k ℂ) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) : IsLocallyConstant (ψ : k → ℂ) := by
  let χ : AddChar k Circle :=
    { toFun := fun x => ⟨ψ x, mem_sphere_zero_iff_norm.2 (GlobalTheory.norm_addChar_nonarch ψ hψ x)⟩
      map_zero_eq_one' := Circle.ext (by simp)
      map_add_eq_mul' := fun a b => Circle.ext (AddChar.map_add_eq_mul ψ a b) }
  have hχ : ∀ x, (χ x : ℂ) = ψ x := fun _ => rfl
  have hχc : Continuous χ := continuous_induced_rng.2 hψ
  have hχ1 : χ ≠ 1 := fun h => hψ1 (by
    ext x
    rw [← hχ, h]
    simp)
  obtain ⟨c0, hc0⟩ := GlobalTheory.SplitWeil.exists_hasConductor_of_continuous χ hχc hχ1
  exact hc0.isLocallyConstant.comp (fun z : Circle => (z : ℂ))

theorem exists_compact_open (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (κ : Type) [Fintype κ] : ∃ U : Set (κ → k), IsOpen U ∧ IsCompact U ∧ 0 ∈ U := by
  have h1 : IsCompact (𝒪[k] : Set k) := isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace 𝒪[k]))
  have h2 : IsOpen (𝒪[k] : Set k) := by
    letI := IsTopologicalAddGroup.rightUniformSpace k
    haveI := isUniformAddGroup_of_addCommGroup (G := k)
    exact Valued.isOpen_integer k
  exact ⟨Set.pi Set.univ fun _ => (𝒪[k] : Set k), isOpen_set_pi Set.finite_univ fun _ _ => h2,
    isCompact_univ_pi fun _ => h1, fun _ _ => zero_mem _⟩

theorem exists_form (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Invertible (2 : k)] (ψ : AddChar k ℂ) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (κ : Type) [Fintype κ] (Λ : Submodule k ((κ → k) × (κ → k)))
    (hiso : ∀ a ∈ Λ, ∀ b ∈ Λ, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) (hdim : Module.finrank k Λ = Fintype.card κ) :
    ∃ l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ, (∀ w ∈ Λ, ∀ φ ∈ SB (κ → k), l (schr ψ w φ) = l φ) ∧ ∃ φ ∈ SB (κ → k), l φ ≠ 0 := by
  classical
  haveI := GlobalTheory.SplitWeil.t2Space k
  have hlc := isLocallyConstant_char k ψ hψ hψ1
  obtain ⟨n, m, e, s, hs, hb⟩ := GlobalTheory.LagrInvForm.exists_coord Λ hiso hdim
  letI : MeasurableSpace (Fin m → k) := borel _
  haveI : BorelSpace (Fin m → k) := ⟨rfl⟩
  let ν : Measure (Fin m → k) := Measure.addHaar
  let j : (Fin m → k) →ₗ[k] (κ → k) := e.toLinearMap ∘ₗ LinearMap.inr k _ _
  have hj : ∀ a, j a = e (0, a) := fun _ => rfl
  let p : (κ → k) →ₗ[k] (Fin m → k) := LinearMap.snd k _ _ ∘ₗ e.symm.toLinearMap
  have hpj : ∀ a, p (j a) = a := fun a => by simp [p, hj]
  have hjc : Continuous j := LinearMap.continuous_on_pi j
  have hpc : Continuous p := LinearMap.continuous_on_pi p
  have hsc : Continuous s := LinearMap.continuous_on_pi s
  let q : (Fin m → k) → k := fun a => ⅟(2 : k) * (j a ⬝ᵥ s a)
  have hqc : Continuous q := continuous_const.mul (hjc.dotProduct hsc)
  have hw : ∀ w ∈ Λ, j (p w.1) = w.1 := fun w hw => by
    have h0 : (e.symm w.1).1 = 0 := by
      funext i
      obtain ⟨b', h1, h2⟩ := hb (Pi.single i 1)
      have h3 := hiso w hw _ h1
      simp only [zero_dotProduct] at h3
      rw [h2] at h3
      simpa using h3
    rw [hj, ← h0]
    exact e.apply_symm_apply w.1
  have hcs : ∀ φ ∈ SB (κ → k), HasCompactSupport (φ ∘ j) := fun φ hφ => by
    refine IsCompact.of_isClosed_subset (hφ.2.image hpc) isClosed_closure ?_
    refine closure_minimal ?_ (hφ.2.image hpc).isClosed
    intro x hx
    exact ⟨j x, subset_tsupport _ hx, hpj x⟩
  have hint : ∀ φ ∈ SB (κ → k), Integrable (fun a => ψ (q a) * φ (j a)) ν := fun φ hφ =>
    ((hψ.comp hqc).mul (hφ.1.continuous.comp hjc)).integrable_of_hasCompactSupport (hcs φ hφ).mul_left
  let f : SB (κ → k) →ₗ[ℂ] ℂ :=
    { toFun := fun φ => ∫ a, ψ (q a) * φ.1 (j a) ∂ν
      map_add' := fun φ φ' => by
        simp only [Submodule.coe_add, Pi.add_apply, mul_add]
        exact integral_add (hint _ φ.2) (hint _ φ'.2)
      map_smul' := fun c φ => by
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_left_comm _ c]
        exact integral_const_mul c _ }
  obtain ⟨l, hl⟩ := LinearMap.exists_extend f
  have hl' : ∀ φ ∈ SB (κ → k), l φ = ∫ a, ψ (q a) * φ (j a) ∂ν := fun φ hφ => LinearMap.congr_fun hl ⟨φ, hφ⟩
  refine ⟨l, fun w hwΛ φ hφ => ?_, ?_⟩
  · have hm : schr ψ w φ ∈ SB (κ → k) :=
      ⟨(hlc.comp_continuous ((continuous_id.dotProduct continuous_const).add continuous_const)).mul
        (hφ.1.comp_continuous (continuous_id.add continuous_const)),
        (hφ.2.comp_homeomorph (Homeomorph.addRight w.1)).mul_left⟩
    rw [hl' _ hm, hl' _ hφ, ← integral_add_right_eq_self (μ := ν) (fun a => ψ (q a) * φ (j a)) (p w.1)]
    congr 1
    funext a
    have h1 := hw w hwΛ
    have h2 := hiso _ (hs a) _ hwΛ
    have h3 := hiso _ (hs (p w.1)) _ hwΛ
    have h4 := hiso _ (hs a) _ (hs (p w.1))
    have h5 : (2 : k) * ⅟(2 : k) = 1 := mul_invOf_self _
    simp only [← hj, h1] at h2 h3 h4
    simp only [schr, q, map_add j, map_add s, h1, add_dotProduct, dotProduct_add]
    rw [← mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    linear_combination h2 + ⅟(2 : k) * h3 - ⅟(2 : k) * h4 - (w.1 ⬝ᵥ s a) * h5
  · obtain ⟨U, hUo, hUc, hU0⟩ := exists_compact_open k κ
    have hUl : IsLocallyConstant (U.indicator fun _ => (1 : ℂ)) :=
      (LocallyConstant.charFn ℂ (⟨hUc.isClosed, hUo⟩ : IsClopen U)).isLocallyConstant
    have hm : (fun x => ψ (-q (p x)) * U.indicator (fun _ => (1 : ℂ)) x) ∈ SB (κ → k) :=
      ⟨(hlc.comp_continuous (hqc.comp hpc).neg).mul hUl,
        (HasCompactSupport.intro hUc fun x hx => Set.indicator_of_notMem hx _).mul_left⟩
    refine ⟨_, hm, ?_⟩
    rw [hl' _ hm]
    have hSo : IsOpen (j ⁻¹' U) := hUo.preimage hjc
    have hfin : ν (j ⁻¹' U) < ⊤ :=
      lt_of_le_of_lt (measure_mono (show j ⁻¹' U ⊆ p '' U from fun y hy => ⟨j y, hy, hpj y⟩)) ((hUc.image hpc).measure_lt_top)
    have hpos : 0 < ν (j ⁻¹' U) := hSo.measure_pos ν ⟨0, by simpa using hU0⟩
    have heq : (fun a => ψ (q a) * (ψ (-q (p (j a))) * U.indicator (fun _ => (1 : ℂ)) (j a))) =
        (j ⁻¹' U).indicator (fun _ => (1 : ℂ)) := by
      funext a
      rw [hpj, ← mul_assoc, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, one_mul]
      rfl
    rw [heq, integral_indicator_const _ hSo.measurableSet]
    exact smul_ne_zero (ENNReal.toReal_ne_zero.mpr ⟨hpos.ne', hfin.ne⟩) one_ne_zero

section Pair

variable {k : Type} [Field k] [Invertible (2 : k)] {E : Type} [Field E] [Algebra k E] {c : E →ₐ[k] E}
  {α β ν κ : Type} [Fintype α] [Fintype β] [Fintype ν] [Fintype κ] {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E}

theorem hTens_eq_zero {C : Matrix β ν E} (h : Cᵀ * JB * C.map c = 0) (z z' : Matrix α ν E) :
    hTens c JA JB (z * Cᵀ) (z' * Cᵀ) = 0 := by
  have h1 : ∀ x y : Matrix α β E, hTens c JA JB x y = ∑ i, ∑ i', JA i i' * (x * JB * (y.map c)ᵀ) i i' := fun x y => by
    unfold hTens
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [Finset.sum_comm]
    simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, Matrix.transpose_apply, Matrix.map_apply]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  have h2 : (z' * Cᵀ).map c = z'.map c * (C.map c)ᵀ := Matrix.map_mul (f := c.toRingHom)
  have h3 : z * Cᵀ * JB * (z'.map c * (C.map c)ᵀ)ᵀ = z * (Cᵀ * JB * C.map c) * (z'.map c)ᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [h1, h2, h3, h]
  simp

def lagCo (co : Darboux (symp c ξ JA JB) κ) (C : Matrix β ν E) : Submodule k ((κ → k) × (κ → k)) where
  carrier := Set.range fun z : Matrix α ν E => co.e (z * Cᵀ)
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨z, rfl⟩ ⟨z', rfl⟩
    exact ⟨z + z', by simp only [Matrix.add_mul, map_add]⟩
  smul_mem' := by
    rintro a _ ⟨z, rfl⟩
    exact ⟨a • z, by simp only [Matrix.smul_mul, map_smul]⟩

theorem lagCo_isotropic (co : Darboux (symp c ξ JA JB) κ) {C : Matrix β ν E} (h : Cᵀ * JB * C.map c = 0) :
    ∀ a ∈ lagCo co C, ∀ b ∈ lagCo co C, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2 := by
  rintro _ ⟨z, rfl⟩ _ ⟨z', rfl⟩
  rw [← sub_eq_zero, ← co.form, symp, hTens_eq_zero h, mul_zero, map_zero]

theorem finrank_lagCo [DecidableEq β] [DecidableEq ν] (co : Darboux (symp c ξ JA JB) κ) {C : Matrix β ν E}
    (h : IsLagr c JB C) : Module.finrank k (lagCo co C) = Fintype.card κ := by
  obtain ⟨h0, Cx, M, hx, h1, -⟩ := h
  refine finrank_eq _ (lagCo co Cx) (lagCo_isotropic co h0) (lagCo_isotropic co hx) ?_
  rw [← Matrix.fromRows_toRows M, Matrix.fromCols_mul_fromRows] at h1
  rw [eq_top_iff]
  intro w _
  obtain ⟨u, rfl⟩ := co.e.surjective w
  have hu : u = u * M.toRows₁ᵀ * Cᵀ + u * M.toRows₂ᵀ * Cxᵀ := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add, ← Matrix.transpose_mul, ← Matrix.transpose_mul,
      ← Matrix.transpose_add, h1, Matrix.transpose_one, Matrix.mul_one]
  rw [hu, map_add]
  exact Submodule.add_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩

end Pair

theorem yform_line : ∀ (k : Type) [Field k] [CharZero k] [Invertible (2 : k)] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (E : Type) [Field E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E] (c : E →ₐ[k] E) (δ : E), IsQuad c δ →
  ∀ ψ : AddChar k ℂ, Continuous ψ → (∀ t, ‖ψ t‖ = 1) → ψ ≠ 1 →
  ∀ (α β ν κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν] [Fintype κ]
    (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (co : Darboux (symp c ξ JA JB) κ) (Cy : Matrix β ν E), IsLagr c JB Cy →
    (∃ l, IsYForm c ψ co Cy l) ∧ ∀ l₁ l₂, IsYInv c ψ co Cy l₁ → IsYForm c ψ co Cy l₂ → ∃ z : ℂ, ∀ φ ∈ SB (κ → k), l₁ φ = z * l₂ φ := by
  intro k _ _ _ _ _ _ E _ _ _ _ c δ _ ψ hψ _ hψ1 α β ν κ _ _ _ _ _ _ _ ξ JA JB co Cy hC
  have hiso := lagCo_isotropic co hC.1
  have hdim := finrank_lagCo co hC
  have hinv : ∀ l, IsYInv c ψ co Cy l → ∀ w ∈ lagCo co Cy, ∀ φ ∈ SB (κ → k), l (schr ψ w φ) = l φ := by
    rintro l hl _ ⟨z, rfl⟩ φ hφ
    exact hl z φ hφ
  refine ⟨?_, fun l₁ l₂ h₁ h₂ => GlobalTheory.LagrInvForm.proportional k ψ hψ hψ1 κ _ hiso hdim l₁ l₂ (hinv _ h₁) (hinv _ h₂.1) h₂.2⟩
  obtain ⟨l, h1, h2⟩ := exists_form k ψ hψ hψ1 κ _ hiso hdim
  exact ⟨l, fun z φ hφ => h1 _ ⟨z, rfl⟩ φ hφ, h2⟩

end GlobalTheory.LagrFormLine

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelRowsEqTypeVectorsOfLevel
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.LevelRows3

theorem eel_eq_typeSp3 : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → (R.toCx3 F).EEl false = typeSp3 A3 (R.toCx3 F) (R.gEx F) F.P0 F.ψ0 ∧ (R.toCx3 F).EEl true = typeSp3 A3 (R.toCx3 F) (R.gEx F) F.P1 F.ψ1 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F h
  have key : GlobalTheory.IndefiniteRowSideFullHecke.TypeCharacterLevelRows.RowsOfLevel R.toRealDat F.lv2 :=
    GlobalTheory.LevelRows.rowsOfLevel_of_models R.toRealDat F.lv2 h.base.models.HE h.base.models.gE
  have aux : ∀ (b : Bool) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ),
      (∀ x : R.HE.H, R.HE.e x ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 b) ↔
        ∀ g : P, R.gE (g : G) x = D.what₂.embLL ((ψ g : D.what₂.LLˣ) : D.what₂.LL) • x) →
      (R.toCx3 F).EEl b = typeSp3 A3 (R.toCx3 F) (R.gEx F) P ψ := by
    intro b P ψ hx
    ext x
    simp only [typeSp3, Submodule.mem_iInf, LinearMap.mem_ker]
    refine Iff.trans (hx x) (forall_congr' fun g => ?_)
    rw [LinearMap.sub_apply, sub_eq_zero]
    rw [LinearMap.smul_apply, LinearMap.id_apply]
    have e : cj (twAt D.what₂.embLL A3.A.v0) (A3.A.v0.embedding ((ψ g : D.what₂.LLˣ) : D.what₂.LL)) =
        D.what₂.embLL ((ψ g : D.what₂.LLˣ) : D.what₂.LL) := by
      simp only [R.emb0, cj_cj]
    have e' : A3.A.fam.v0.embedding ((ψ g : D.what₂.LLˣ) : D.what₂.LL) • x =
        Tw.mk (twAt D.what₂.embLL A3.A.v0) (D.what₂.embLL ((ψ g : D.what₂.LLˣ) : D.what₂.LL) • Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) x) := by
      rw [← e]
      rfl
    rw [e']
    exact Iff.rfl
  exact ⟨aux false _ _ (key false), aux true _ _ (key true)⟩

end GlobalTheory.LevelRows3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieMultLabelRank
section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical

namespace GlobalTheory.TorCls

theorem exists_open_psiAway_mem_conj_level : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (β : G.Cˣ)
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (y : G.C) (r₁ : G.GAf),
    letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C);
    ∃ O : Set ((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ), IsOpen O ∧ 1 ∈ O ∧ ∀ z ∈ O, InT G (AfP p) β y z →
      ∃ k ∈ L.K.toSubgroup, ((r₁ * k * r₁⁻¹ : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) = psiAway G x z := by
  intro p _ G L β x t hx y r₁
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (AfP p ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (AfP p) (AfP p ⊗[ℚ] G.C)
  let K' : Set G.GAf := (fun g : G.GAf => r₁⁻¹ * g * r₁) ⁻¹' (L.K : Set G.GAf)
  have hK'o : IsOpen K' :=
    L.K.isOpen.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.1 hK'o
  refine ⟨psiAway G x ⁻¹' V, hVo.preimage ?_, ?_, ?_⟩
  · show Continuous (fun z : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ => ((x * z.1 * x⁻¹, z.2) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ))
    exact ((continuous_const.mul continuous_fst).mul continuous_const).prodMk continuous_snd
  · have h1 : (1 : G.GAf) ∈ K' := by
      show r₁⁻¹ * 1 * r₁ ∈ (L.K : Set G.GAf)
      rw [mul_one, inv_mul_cancel]
      exact L.K.one_mem
    rw [← hV] at h1
    show psiAway G x 1 ∈ V
    rw [map_one]
    exact h1
  · intro z hz hT
    have hw : psiAway G x z ∈ UPts G.star (AfP p) := by
      rw [psiAway_apply]
      exact conj_mul_star (starT G.star (AfP p)) (inC G (AfP p) (β : G.C)) x z.1 t (z.2 : AfP p) hx hT.1
    let g : G.GAf := ⟨psiAway G x z, hw⟩
    have hg : g ∈ K' := by
      rw [← hV]
      exact hz
    refine ⟨r₁⁻¹ * g * r₁, hg, ?_⟩
    have : r₁ * (r₁⁻¹ * g * r₁) * r₁⁻¹ = g := by group
    rw [this]

end GlobalTheory.TorCls
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftModelParameterDecreasingHalfIntegralWidth
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow.ParWidth

theorem mem_holPar_kapW {Rk : Ranks} (h : HCParam Rk) (p q : ℕ) (hpq : Odd (p + q)) {x : ℚ} {b : Bool}
    (hx : (x, b) ∈ Formalism.L2.NTheta.holPar p q (Formalism.L2.NTheta.kapW h p q)) :
    ∃ n < p + q, x = Formalism.L2.NTheta.lamAt h n := by
  unfold Formalism.L2.NTheta.holPar at hx
  obtain ⟨a, -, ha⟩ := Finset.mem_image.1 hx
  have e := Formalism.L2.NTheta.holEnt_kapW h p q hpq a
  have hx' : x = Formalism.L2.NTheta.holEnt p q (Formalism.L2.NTheta.kapW h p q) a := (congrArg Prod.fst ha).symm
  rcases a with i | c
  · exact ⟨i, by omega, hx'.trans (by simpa using e)⟩
  · exact ⟨p + c, by omega, hx'.trans (by simpa using e)⟩

theorem lamAt_anti {Rk : Ranks} (h : HCParam Rk) {n n' : ℕ} (hnn : n ≤ n') (hn : n' < Rk.r) :
    Formalism.L2.NTheta.lamAt h n' ≤ Formalism.L2.NTheta.lamAt h n := by
  have mono : ∀ d : ℕ, n + d < Rk.r → Formalism.L2.NTheta.lamAt h (n + d) ≤ Formalism.L2.NTheta.lamAt h n := by
    intro d
    induction d with
    | zero => intro _; exact le_rfl
    | succ d ih =>
      intro hd
      exact (Formalism.L2.NTheta.lamAt_lt h (n + d) (by omega)).le.trans (ih (by omega))
  have := mono (n' - n) (by omega)
  rwa [show n + (n' - n) = n' by omega] at this

theorem lamAt_b {Rk : Ranks} (h : HCParam Rk) (c : ℕ) (hc : c < Rk.m) :
    Formalism.L2.NTheta.lamAt h (Rk.k - 1 + c) = -h.b ⟨c, hc⟩ := by
  unfold Formalism.L2.NTheta.lamAt
  rw [dif_neg (by omega), dif_pos (by omega)]
  simp

theorem le_toNat_floor (x : ℚ) : x ≤ ((⌊x⌋.toNat : ℕ) : ℚ) + 1 := by
  have h1 := Int.lt_floor_add_one x
  have h2 : ((⌊x⌋ : ℤ) : ℚ) ≤ (((⌊x⌋.toNat : ℕ) : ℤ) : ℚ) := by exact_mod_cast Int.self_le_toNat _
  rw [Int.cast_natCast] at h2
  linarith

end GlobalTheory.LowRow.ParWidth

namespace GlobalTheory.LowRow.ParWidth

theorem width_le (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) :
    Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) 0 - Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) (D.R.r - 1) ≤
      (degAt D i σ ρ : ℚ) + D.R.nV + 1 := by
  have hsig : (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (Nat.le_add_left _ _) i.2 _
  have hp : pW D i ρ = D.R.k + i := by simp only [pW, hsig, Ranks.sigW]; omega
  have hq : qW D i ρ = D.R.m - (i + 1) := by simp only [qW, hsig, Ranks.sigW]
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  set h := D.hc (lab σ ρ) with hh
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hnV : (D.R.nV : ℚ) = (D.R.k : ℚ) + D.R.m - 1 + D.R.t := by
    simp only [Ranks.nV, Ranks.r]; push_cast [show 1 ≤ D.R.k + D.R.m by omega]; ring

  have hP0 : (aPlAt D i σ ρ 0 : ℚ) + 1 ≥
      Formalism.L2.NTheta.lamAt h 0 + h.e i - ((D.R.k + i : ℕ) - (0 + 1) : ℚ) - ((D.R.t : ℚ) + 1) / 2 := by
    have := le_toNat_floor (Formalism.L2.NTheta.lamAt h 0 + h.e i - ((D.R.k + i : ℕ) - ((0 : ℕ) + 1) : ℚ) - ((D.R.t : ℚ) + 1) / 2)
    unfold aPlAt aPl
    rw [hp, if_pos (by omega)]
    simpa using this
  have hdeg : (aPlAt D i σ ρ 0 : ℚ) + (if 0 < qW D i ρ then (aMiAt D i σ ρ 0 : ℚ) else 0) ≤ degAt D i σ ρ := by
    have e1 : aPlAt D i σ ρ 0 ≤ ∑ n ∈ Finset.range (pW D i ρ), aPlAt D i σ ρ n :=
      Finset.single_le_sum (f := aPlAt D i σ ρ) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (by omega))
    have e2 : (if 0 < qW D i ρ then aMiAt D i σ ρ 0 else 0) ≤ ∑ n ∈ Finset.range (qW D i ρ), aMiAt D i σ ρ n := by
      split_ifs with hq0
      · exact Finset.single_le_sum (f := aMiAt D i σ ρ) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hq0)
      · exact Nat.zero_le _
    have e3 := Nat.add_le_add e1 e2
    unfold degAt
    have : ((aPlAt D i σ ρ 0 + (if 0 < qW D i ρ then aMiAt D i σ ρ 0 else 0) : ℕ) : ℚ) ≤
        ((∑ n ∈ Finset.range (pW D i ρ), aPlAt D i σ ρ n + ∑ n ∈ Finset.range (qW D i ρ), aMiAt D i σ ρ n : ℕ) : ℚ) := by
      exact_mod_cast e3
    push_cast at this
    split_ifs at this ⊢ <;> simpa using this
  by_cases hq0 : (i : ℕ) + 1 < D.R.m
  · have hqpos : 0 < qW D i ρ := by rw [hq]; omega
    rw [if_pos hqpos] at hdeg
    have hM0 : (aMiAt D i σ ρ 0 : ℚ) + 1 ≥
        -(h.e i + Formalism.L2.NTheta.lamAt h (D.R.r - 1) + ((D.R.m - (i + 1) : ℕ) : ℚ) + ((D.R.t : ℚ) - 1) / 2) := by
      have := le_toNat_floor (-(h.e i + Formalism.L2.NTheta.lamAt h (D.R.r - 1) + ((D.R.m - (i + 1) : ℕ) : ℚ) + ((D.R.t : ℚ) - 1) / 2))
      unfold aMiAt aMi
      rw [hp, hq, if_pos (by omega), show D.R.k + ↑i + (D.R.m - (↑i + 1) - 0) - 1 = D.R.r - 1 by omega]
      simpa using this
    have c1 : (((D.R.k + i : ℕ) : ℚ)) = D.R.k + (i : ℚ) := by push_cast; ring
    have c2 : (((D.R.m - (i + 1) : ℕ) : ℚ)) = D.R.m - (i : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [c1] at hP0
    rw [c2] at hM0
    rw [hnV]
    linarith
  · have him : (i : ℕ) = D.R.m - 1 := by omega
    rw [if_neg (by rw [hq]; omega), add_zero] at hdeg
    have hb : Formalism.L2.NTheta.lamAt h (D.R.r - 1) = -h.b i := by
      rw [show D.R.r - 1 = D.R.k - 1 + (i : ℕ) by omega, lamAt_b h i i.2]
    have hg := h.gap_be i
    have c1 : (((D.R.k + i : ℕ) : ℚ)) = D.R.k + (i : ℚ) := by push_cast; ring
    rw [c1] at hP0
    have hmi : (i : ℚ) = D.R.m - 1 := by
      rw [him, Nat.cast_sub (by omega)]; simp
    rw [hnV, hb]
    have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
    linarith

end GlobalTheory.LowRow.ParWidth

open GlobalTheory.LowRow.ParWidth in

theorem GlobalTheory.LowRow.lam_par_width : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ i σ s, IsEmbOverK D σ s → ∀ ρ, StrictAnti ((R.MW i σ).lam ρ) ∧ (∀ a, ∃ z : ℤ, (R.MW i σ).lam ρ a - (((Wc D i).rank : ℝ) - 1) / 2 = (z : ℝ)) ∧ ∀ a b, |(R.MW i σ).lam ρ a - (R.MW i σ).lam ρ b| ≤ (degAt D i σ ρ : ℝ) + D.R.nV + 3 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _hC i σ s hσ ρ
  have hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ := hσ.2
  have hat : labE σ (lab σ ρ) = tauE D ρ := ((GlobalTheory.GalLift.labels_overK σ).1 hK).2 ρ
  obtain ⟨hanti, qv, hqv, hS⟩ := (R.MW i σ).enum ρ
  have hpar : parAt (Wc D i) σ ρ = Formalism.L2.NTheta.holPar _ _ (kapAt (Wc D i) σ ρ) := if_pos hat
  have hsig : (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (Nat.le_add_left _ _) i.2 _
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  have hr : ((Wc D i).sig (tauE D ρ)).1 + ((Wc D i).sig (tauE D ρ)).2 = D.R.r := by
    rw [hsig]; simp only [Ranks.sigW, Ranks.r]; omega
  have hrodd : Odd D.R.r := by
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    exact ⟨a + b - 1, by simp only [Ranks.r]; omega⟩
  have hodd : Odd (((Wc D i).sig (tauE D ρ)).1 + ((Wc D i).sig (tauE D ρ)).2) := hr ▸ hrodd
  have hent : ∀ a, ∃ n < D.R.r, (R.MW i σ).lam ρ a = ((Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) n : ℚ) : ℝ) := by
    intro a
    have hmem : (qv a, (R.MW i σ).ε ρ a) ∈ parAt (Wc D i) σ ρ := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    rw [hpar] at hmem
    obtain ⟨n, hn, e⟩ := mem_holPar_kapW _ _ _ hodd hmem
    exact ⟨n, hr ▸ hn, by rw [hqv a, e]⟩
  have hrank : (Wc D i).rank = D.R.r := by
    rw [← hr]; exact (Formalism.BasicNotions.sig_sum _ (D.sp.W_sig _) _).symm
  refine ⟨hanti, fun a => ?_, fun a b => ?_⟩
  · obtain ⟨n, -, e⟩ := hent a
    obtain ⟨z, hz⟩ := Formalism.L2.NTheta.lamAt_int (D.hc (lab σ ρ)) n
    obtain ⟨w, hw⟩ := hrodd
    refine ⟨z - w, ?_⟩
    rw [e, hz, hrank, hw]
    push_cast
    ring
  · obtain ⟨n, hn, ea⟩ := hent a
    obtain ⟨n', hn', eb⟩ := hent b
    have hW := width_le D i σ ρ
    have l1 := lamAt_anti (D.hc (lab σ ρ)) (Nat.zero_le n) hn
    have l2 := lamAt_anti (D.hc (lab σ ρ)) (Nat.zero_le n') hn'
    have u1 := lamAt_anti (D.hc (lab σ ρ)) (show n ≤ D.R.r - 1 by omega) (by omega)
    have u2 := lamAt_anti (D.hc (lab σ ρ)) (show n' ≤ D.R.r - 1 by omega) (by omega)
    have key : |Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) n - Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) n'| ≤
        (degAt D i σ ρ : ℚ) + D.R.nV + 3 := by
      rw [abs_sub_le_iff]; constructor <;> linarith
    rw [ea, eb, ← Rat.cast_sub, ← Rat.cast_abs]
    exact_mod_cast key
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTensorCenterInclusionInjectiveCentralFinranStatement
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localTensorCenterInclusion_injective_central_finrank : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), Function.Injective (iotaF G v) ∧ (∀ z x, Commute (iotaF G v z) x) ∧ Module.finrank (Qv v) (Qv v ⊗[ℚ] G.C) = G.n ^ 2 * Module.finrank (Qv v) (Qv v ⊗[ℚ] G.F) := by
  first | (exact @GlobalTheory.OrbFinAf.iotaF_props) | (exact GlobalTheory.OrbFinAf.iotaF_props) | (intros; apply GlobalTheory.OrbFinAf.iotaF_props  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkNormSqEqSimilitudeFactorStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mark_norm_sq_eq_similitudeFactor : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ), P.Mark μ → ‖μ‖ ^ 2 = ((P.c : ℚ) : ℝ) := by
  first | (exact @GlobalTheory.LKMid.Pair.mark_norm_sq) | (exact GlobalTheory.LKMid.Pair.mark_norm_sq) | (intros; apply GlobalTheory.LKMid.Pair.mark_norm_sq  <;> assumption)
end

