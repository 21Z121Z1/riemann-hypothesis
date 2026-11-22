import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0374
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorEigen
section
open TensorProduct

namespace GlobalTheory.CompanionTheory.TensContr

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

noncomputable def contr (v : V ⊗[ℂ] W) : Module.Dual ℂ W →ₗ[ℂ] V where
  toFun l := TensorProduct.rid ℂ V (LinearMap.lTensor V l v)
  map_add' l m := by
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [add_smul]
    | add s t hs ht =>
      simp only [map_add] at hs ht ⊢
      rw [hs, ht]; abel
  map_smul' c l := by
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [mul_smul]
    | add s t hs ht =>
      simp only [map_add, RingHom.id_apply, smul_add] at hs ht ⊢
      rw [hs, ht]

@[simp] theorem contr_tmul (a : V) (b : W) (l : Module.Dual ℂ W) :
    contr (a ⊗ₜ[ℂ] b) l = l b • a := by
  show TensorProduct.rid ℂ V (LinearMap.lTensor V l (a ⊗ₜ[ℂ] b)) = l b • a
  rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul]

theorem contr_apply (v : V ⊗[ℂ] W) (l : Module.Dual ℂ W) :
    contr v l = TensorProduct.rid ℂ V (LinearMap.lTensor V l v) := rfl

theorem contr_add (s t : V ⊗[ℂ] W) (l : Module.Dual ℂ W) :
    contr (s + t) l = contr s l + contr t l := by
  simp only [GlobalTheory.CompanionTheory.TensContr.contr_apply, map_add]

theorem contr_smul (c : ℂ) (t : V ⊗[ℂ] W) (l : Module.Dual ℂ W) :
    contr (c • t) l = c • contr t l := by
  simp only [GlobalTheory.CompanionTheory.TensContr.contr_apply, map_smul]

theorem contr_map (f : V →ₗ[ℂ] V) (g : W →ₗ[ℂ] W) (t : V ⊗[ℂ] W) (l : Module.Dual ℂ W) :
    contr (TensorProduct.map f g t) l = f (contr t (l ∘ₗ g)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, GlobalTheory.CompanionTheory.TensContr.contr_apply]
  | tmul a b =>
    rw [TensorProduct.map_tmul, GlobalTheory.CompanionTheory.TensContr.contr_tmul, GlobalTheory.CompanionTheory.TensContr.contr_tmul,
      LinearMap.comp_apply, map_smul]
  | add s t hs ht =>
    rw [map_add, GlobalTheory.CompanionTheory.TensContr.contr_add, GlobalTheory.CompanionTheory.TensContr.contr_add, hs, ht, map_add]

theorem exists_finset_contr (v : V ⊗[ℂ] W) :
    ∃ s : Finset V, ∀ l, contr v l ∈ Submodule.span ℂ (s : Set V) := by
  classical
  induction v using TensorProduct.induction_on with
  | zero =>
    refine ⟨∅, fun l => ?_⟩
    simp only [GlobalTheory.CompanionTheory.TensContr.contr_apply, map_zero]
    exact Submodule.zero_mem _
  | tmul a b =>
    refine ⟨{a}, fun l => ?_⟩
    rw [GlobalTheory.CompanionTheory.TensContr.contr_tmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  | add s t hs ht =>
    obtain ⟨S, hS⟩ := hs
    obtain ⟨T, hT⟩ := ht
    refine ⟨S ∪ T, fun l => ?_⟩
    rw [GlobalTheory.CompanionTheory.TensContr.contr_add]
    refine Submodule.add_mem _ (Submodule.span_mono ?_ (hS l)) (Submodule.span_mono ?_ (hT l))
    · exact_mod_cast Finset.subset_union_left
    · exact_mod_cast Finset.subset_union_right

theorem finiteDimensional_range_contr (v : V ⊗[ℂ] W) :
    FiniteDimensional ℂ (LinearMap.range (contr v)) := by
  obtain ⟨s, hs⟩ := GlobalTheory.CompanionTheory.TensContr.exists_finset_contr v
  haveI := FiniteDimensional.span_finset ℂ s
  have hle : LinearMap.range (GlobalTheory.CompanionTheory.TensContr.contr v) ≤ Submodule.span ℂ (s : Set V) := by
    rintro _ ⟨l, rfl⟩
    exact hs l
  exact Submodule.finiteDimensional_of_le hle

theorem eq_zero_of_contr (v : V ⊗[ℂ] W) (h : ∀ l, contr v l = 0) : v = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace ℂ W
  let e := TensorProduct.equivFinsuppOfBasisRight (M := V) b
  have key : ∀ (t : V ⊗[ℂ] W) i, e t i = GlobalTheory.CompanionTheory.TensContr.contr t (b.coord i) := by
    intro t i
    induction t using TensorProduct.induction_on with
    | zero =>
      simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply, GlobalTheory.CompanionTheory.TensContr.contr_apply]
    | tmul a w =>
      rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, GlobalTheory.CompanionTheory.TensContr.contr_tmul,
        Module.Basis.coord_apply]
    | add s t hs ht =>
      rw [map_add, Finsupp.add_apply, hs, ht, GlobalTheory.CompanionTheory.TensContr.contr_add]
  have he : e v = 0 := by
    ext i
    rw [key, h, Finsupp.coe_zero, Pi.zero_apply]
  exact (LinearEquiv.map_eq_zero_iff e).mp he

end GlobalTheory.CompanionTheory.TensContr

namespace GlobalTheory.CompanionTheory.TensContr

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable {X Y : Type*}

theorem exists_contr_eigen [Nonempty Y]
    (A : X → V →ₗ[ℂ] V) (B : Y → W →ₗ[ℂ] W) (lam : X → ℂ) (mu : Y → ℂ)
    (hlam : ∀ x, lam x ≠ 0) (hmu : ∀ y, mu y ≠ 0)
    (v : V ⊗[ℂ] W) (hv : v ≠ 0)
    (heig : ∀ x y, TensorProduct.map (A x) (B y) v = (lam x * mu y) • v) :
    ∃ (l : Module.Dual ℂ W) (c : ℂ), c ≠ 0 ∧
      TensorProduct.rid ℂ V (LinearMap.lTensor V l v) ≠ 0 ∧
      ∀ x, A x (TensorProduct.rid ℂ V (LinearMap.lTensor V l v)) =
        (c * lam x) • TensorProduct.rid ℂ V (LinearMap.lTensor V l v) := by
  simp only [← GlobalTheory.CompanionTheory.TensContr.contr_apply]
  set φ := GlobalTheory.CompanionTheory.TensContr.contr v with hφ
  have hne : ∃ l, φ l ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hv (GlobalTheory.CompanionTheory.TensContr.eq_zero_of_contr v hcon)
  obtain ⟨l₀, hl₀⟩ := hne
  by_cases hX : IsEmpty X
  · exact ⟨l₀, 1, one_ne_zero, hl₀, fun x => (hX.false x).elim⟩
  obtain ⟨x₀⟩ := not_isEmpty_iff.mp hX
  obtain ⟨y₀⟩ := ‹Nonempty Y›
  have rel : ∀ x l, A x (φ (l ∘ₗ B y₀)) = (lam x * mu y₀) • φ l := by
    intro x l
    rw [hφ, ← GlobalTheory.CompanionTheory.TensContr.contr_map, heig, GlobalTheory.CompanionTheory.TensContr.contr_smul]
  let U := LinearMap.range φ
  haveI : FiniteDimensional ℂ U := GlobalTheory.CompanionTheory.TensContr.finiteDimensional_range_contr v
  let U' := LinearMap.range (φ ∘ₗ (B y₀).dualMap)
  have hU'U : U' ≤ U := LinearMap.range_comp_le_range _ _
  have hmapU' : U ≤ Submodule.map (A x₀) U' := by
    rintro _ ⟨l, rfl⟩
    have hk : lam x₀ * mu y₀ ≠ 0 := mul_ne_zero (hlam x₀) (hmu y₀)
    refine ⟨φ (((lam x₀ * mu y₀)⁻¹ • l) ∘ₗ B y₀), ⟨(lam x₀ * mu y₀)⁻¹ • l, ?_⟩, ?_⟩
    · rw [LinearMap.comp_apply, LinearMap.dualMap_apply']
    · rw [rel, map_smul, smul_smul, mul_inv_cancel₀ hk, one_smul]
  haveI : FiniteDimensional ℂ U' := Submodule.finiteDimensional_of_le hU'U
  have hUU' : U' = U := by
    refine Submodule.eq_of_le_of_finrank_le hU'U ?_
    calc Module.finrank ℂ U ≤ Module.finrank ℂ (Submodule.map (A x₀) U') :=
          Submodule.finrank_mono hmapU'
      _ ≤ Module.finrank ℂ U' := Submodule.finrank_map_le _ _
  have hrepr : ∀ u ∈ U, ∃ l, u = φ (l ∘ₗ B y₀) := by
    intro u hu
    rw [← hUU'] at hu
    obtain ⟨l, rfl⟩ := hu
    exact ⟨l, by rw [LinearMap.comp_apply, LinearMap.dualMap_apply']⟩
  have hmaps : ∀ x, ∀ u ∈ U, A x u ∈ U := by
    intro x u hu
    obtain ⟨l, rfl⟩ := hrepr u hu
    rw [rel]
    exact Submodule.smul_mem _ _ ⟨l, rfl⟩
  have hprop : ∀ x, ∀ u ∈ U, A x u = (lam x * (lam x₀)⁻¹) • A x₀ u := by
    intro x u hu
    obtain ⟨l, rfl⟩ := hrepr u hu
    rw [rel, rel, smul_smul]
    congr 1
    field_simp [hlam x₀, hmu y₀]
  let T : Module.End ℂ U := (A x₀).restrict (hmaps x₀)
  have hsurj : Function.Surjective T := by
    rintro ⟨u, hu⟩
    obtain ⟨w, hw, hwu⟩ := hmapU' hu
    exact ⟨⟨w, hU'U hw⟩, Subtype.ext (by simpa [T, LinearMap.restrict_apply] using hwu)⟩
  have hinj : Function.Injective T := LinearMap.injective_iff_surjective.mpr hsurj
  haveI : Nontrivial U := nontrivial_of_ne (⟨φ l₀, ⟨l₀, rfl⟩⟩ : U) 0
    (fun h => hl₀ (congrArg Subtype.val h))
  obtain ⟨t, ht⟩ := Module.End.exists_eigenvalue T
  obtain ⟨u, hu⟩ := ht.exists_hasEigenvector
  have hTu := hu.apply_eq_smul
  have hu0 : u ≠ 0 := hu.2
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hTu
    exact hu0 (hinj (by rw [hTu, map_zero]))
  have hAu : A x₀ u = t • (u : V) := by
    have := congrArg Subtype.val hTu
    simpa [T, LinearMap.restrict_apply] using this
  obtain ⟨l, hl⟩ := u.2
  refine ⟨l, t * (lam x₀)⁻¹, mul_ne_zero ht0 (inv_ne_zero (hlam x₀)), ?_, fun x => ?_⟩
  · rw [hl]
    exact fun h => hu0 (Subtype.ext h)
  · rw [hl, hprop x _ u.2, hAu, smul_smul]
    congr 1
    ring

end GlobalTheory.CompanionTheory.TensContr

namespace GlobalTheory.CompanionTheory.TensContr

theorem tensEig : PositivityTheory.Rg.BcB.F.Tail.PExp.TensEig := by
  intro V W X Y _ _ _ _ A B lam mu v hv hY hlam hmu heig
  exact GlobalTheory.CompanionTheory.TensContr.exists_contr_eigen A B lam mu hlam hmu v hv heig

end GlobalTheory.CompanionTheory.TensContr
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorEigenReal
section
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.TensEigSecond

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

noncomputable def contr (v : V ⊗[ℂ] W) : Module.Dual ℂ V →ₗ[ℂ] W where
  toFun l := TensorProduct.lid ℂ W (LinearMap.rTensor W l v)
  map_add' l m := by simp [LinearMap.rTensor_add]
  map_smul' c l := by simp [LinearMap.rTensor_smul]

theorem contr_apply (v : V ⊗[ℂ] W) (l : Module.Dual ℂ V) :
    contr v l = TensorProduct.lid ℂ W (LinearMap.rTensor W l v) := rfl

theorem contr_tmul (a : V) (b : W) (l : Module.Dual ℂ V) : contr (a ⊗ₜ[ℂ] b) l = l a • b := by
  simp [contr_apply]

theorem contr_add (v w : V ⊗[ℂ] W) (l : Module.Dual ℂ V) : contr (v + w) l = contr v l + contr w l := by
  simp [contr_apply]

theorem contr_smul (c : ℂ) (v : V ⊗[ℂ] W) (l : Module.Dual ℂ V) : contr (c • v) l = c • contr v l := by
  simp [contr_apply]

theorem contr_map (A : Module.End ℂ V) (B : Module.End ℂ W) (v : V ⊗[ℂ] W) (l : Module.Dual ℂ V) :
    B (contr v (l ∘ₗ A)) = contr (TensorProduct.map A B v) l := by
  induction v using TensorProduct.induction_on with
  | zero => simp [contr_apply]
  | tmul a b => simp [contr_tmul]
  | add x y hx hy => simp only [map_add, contr_add, hx, hy]

theorem exists_finiteDimensional (v : V ⊗[ℂ] W) :
    ∃ T : Submodule ℂ W, FiniteDimensional ℂ T ∧ ∀ l, contr v l ∈ T := by
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨⊥, inferInstance, fun l => by simp [contr_apply]⟩
  | tmul a b =>
    exact ⟨ℂ ∙ b, inferInstance, fun l => by
      rw [contr_tmul]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self b)⟩
  | add x y hx hy =>
    obtain ⟨T, hT, h⟩ := hx
    obtain ⟨T', hT', h'⟩ := hy
    exact ⟨T ⊔ T', inferInstance, fun l => by
      rw [contr_add]; exact Submodule.add_mem_sup (h l) (h' l)⟩

theorem exists_contr_ne_zero {v : V ⊗[ℂ] W} (hv : v ≠ 0) : ∃ l, contr v l ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  apply hv
  let b := Module.Free.chooseBasis ℂ V
  have key : ∀ (w : V ⊗[ℂ] W) i, TensorProduct.equivFinsuppOfBasisLeft b w i = contr w (b.coord i) := by
    intro w i
    induction w using TensorProduct.induction_on with
    | zero => simp [contr_apply]
    | tmul a c => simp [contr_tmul, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, contr_add, hx, hy]
  apply (TensorProduct.equivFinsuppOfBasisLeft (N := W) b).injective
  ext i : 1
  rw [key, hcon]
  simp

theorem core {Y : Type} (A : Module.End ℂ V) (B : Y → Module.End ℂ W) (a : ℂ) (ha : a ≠ 0) (mu : Y → ℂ)
    (hmu : ∀ y, mu y ≠ 0) (v : V ⊗[ℂ] W) (hv : v ≠ 0)
    (h : ∀ y, TensorProduct.map A (B y) v = (a * mu y) • v) :
    ∃ (l : Module.Dual ℂ V) (c : ℂ), c ≠ 0 ∧ contr v l ≠ 0 ∧
      ∀ y, B y (contr v l) = (c * mu y) • contr v l := by
  obtain ⟨l₀, hl₀⟩ := exists_contr_ne_zero hv
  rcases isEmpty_or_nonempty Y with hY | ⟨⟨y0⟩⟩
  · exact ⟨l₀, 1, one_ne_zero, hl₀, fun y => isEmptyElim y⟩
  have key : ∀ y l, B y (contr v (l ∘ₗ A)) = (a * mu y) • contr v l := by
    intro y l
    rw [contr_map, h, contr_smul]
  let S := LinearMap.range (contr v)
  obtain ⟨T, hT, hST⟩ := exists_finiteDimensional v
  have hSfd : FiniteDimensional ℂ S :=
    Submodule.finiteDimensional_of_le (S₂ := T) (by rintro _ ⟨l, rfl⟩; exact hST l)
  let b : Module.Dual ℂ V →ₗ[ℂ] W := contr v ∘ₗ A.dualMap
  have hb : ∀ l, b l = contr v (l ∘ₗ A) := fun l => rfl
  let S' := LinearMap.range b
  have hle : S' ≤ S := LinearMap.range_comp_le_range _ _
  have hS'fd : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hle
  have hne : a * mu y0 ≠ 0 := mul_ne_zero ha (hmu y0)
  have hmap : S ≤ S'.map (B y0) := by
    rintro _ ⟨l, rfl⟩
    refine ⟨b ((a * mu y0)⁻¹ • l), ⟨_, rfl⟩, ?_⟩
    rw [hb, key, map_smul, smul_smul, mul_inv_cancel₀ hne, one_smul]
  have hfr : Module.finrank ℂ S ≤ Module.finrank ℂ S' :=
    (Submodule.finrank_mono hmap).trans (Submodule.finrank_map_le _ _)
  have hSS' : S' = S := Submodule.eq_of_le_of_finrank_le hle hfr
  have hrep : ∀ s ∈ S, ∃ l, s = contr v (l ∘ₗ A) := by
    intro s hs
    rw [← hSS'] at hs
    obtain ⟨l, rfl⟩ := hs
    exact ⟨l, hb l⟩
  have hform : ∀ s ∈ S, ∀ y, mu y0 • B y s = mu y • B y0 s := by
    intro s hs y
    obtain ⟨l, rfl⟩ := hrep s hs
    rw [key, key, smul_smul, smul_smul]
    congr 1
    ring
  have hinv : ∀ s ∈ S, B y0 s ∈ S := by
    intro s hs
    obtain ⟨l, rfl⟩ := hrep s hs
    rw [key]
    exact S.smul_mem _ ⟨l, rfl⟩
  let R : Module.End ℂ S := (B y0).restrict hinv
  have hsurj : Function.Surjective R := by
    rintro ⟨s, hs⟩
    obtain ⟨t, ht, rfl⟩ := hmap hs
    exact ⟨⟨t, hle ht⟩, rfl⟩
  have hinj : Function.Injective R := LinearMap.injective_iff_surjective.mpr hsurj
  have hnt : Nontrivial S :=
    ⟨⟨⟨contr v l₀, ⟨l₀, rfl⟩⟩, 0, fun e => hl₀ (congrArg Subtype.val e)⟩⟩
  obtain ⟨γ, hγ⟩ := Module.End.exists_eigenvalue R
  obtain ⟨u, hu⟩ := hγ.exists_hasEigenvector
  have hRu : R u = γ • u := hu.apply_eq_smul
  have hu0 : u ≠ 0 := hu.2
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    apply hu0
    apply hinj
    rw [hRu]
    simp
  have hBu : B y0 (u : W) = γ • (u : W) := congrArg Subtype.val hRu
  obtain ⟨l, hl⟩ := u.2
  refine ⟨l, γ / mu y0, div_ne_zero hγ0 (hmu y0), ?_, fun y => ?_⟩
  · rw [hl]
    exact fun e => hu0 (Subtype.ext e)
  · rw [hl]
    have e := hform u u.2 y
    rw [hBu] at e
    have e2 : B y (u : W) = (mu y0)⁻¹ • mu y0 • B y (u : W) := by
      rw [smul_smul, inv_mul_cancel₀ (hmu y0), one_smul]
    rw [e2, e, smul_smul, smul_smul]
    congr 1
    field_simp [hmu y0]

theorem tensEigR : PositivityTheory.Rg.BcB.F.Tail.PExp.TensEigR := by
  intro V W X Y _ _ _ _ A B lam mu v hv hX hlam hmu hAB
  obtain ⟨x0⟩ := hX
  exact core (A x0) B (lam x0) (hlam x0) mu hmu v hv (hAB x0)

end GlobalTheory.CompanionTheory.TensEigSecond
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorProductDropZeroFactors
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.FineProd.TensorLine

theorem exists_line {G V : Type} [Group G] [Subsingleton G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (hi : ρ.IsIrreducible) : Nonempty (V ≃ₗ[ℂ] ℂ) := by
  have := nontrivial_of_irreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let S : Subrepresentation ρ := ⟨Submodule.span ℂ {v}, fun g w hw => by
    rw [Subsingleton.elim g 1, map_one]; exact hw⟩
  have hvS : v ∈ S.toSubmodule := Submodule.mem_span_singleton_self v
  have hS : S = ⊤ := by
    rcases hi.eq_bot_or_eq_top S with h | h
    · exfalso
      rw [h] at hvS
      exact hv ((Submodule.mem_bot ℂ).1 hvS)
    · exact h
  have htop : ∀ w : V, w ∈ Submodule.span ℂ {v} := fun w => by
    have : w ∈ S.toSubmodule := by
      rw [hS]
      exact (Submodule.mem_top : w ∈ (⊤ : Submodule ℂ V))
    exact this
  refine ⟨(LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℂ V v) ⟨?_, ?_⟩).symm⟩
  · exact LinearMap.ker_eq_bot.1 (LinearMap.ker_toSpanSingleton ℂ hv)
  · intro w
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (htop w)
    exact ⟨c, by simpa using hc⟩

theorem subsingleton_GL {k : Type} [Field k] {n : ℕ} (h : n = 0) : Subsingleton (GL (Fin n) k) := by
  subst h
  exact ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩

variable {r r' : ℕ}

abbrev Off (o : Fin r' → Fin r) : Type := {j : Fin r // j ∉ Set.range o}

def blockEquiv (o : Fin r' → Fin r) (ho : Function.Injective o) : Fin r' ⊕ Off o ≃ Fin r :=
  Equiv.ofBijective (Sum.elim o Subtype.val) (by
    constructor
    · rintro (a | a) (b | b) h
      · exact congrArg Sum.inl (ho h)
      · exact absurd ⟨a, h⟩ b.2
      · exact absurd ⟨b, h.symm⟩ a.2
      · exact congrArg Sum.inr (Subtype.ext h)
    · intro j
      by_cases hj : j ∈ Set.range o
      · obtain ⟨a, rfl⟩ := hj
        exact ⟨Sum.inl a, rfl⟩
      · exact ⟨Sum.inr ⟨j, hj⟩, rfl⟩)

variable {X : Fin r → Type} [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)]

open scoped Classical in

def dropEquiv (o : Fin r' → Fin r) (ho : Function.Injective o) (φ : ∀ c : Off o, X c ≃ₗ[ℂ] ℂ) :
    (⨂[ℂ] j, X j) ≃ₗ[ℂ] ⨂[ℂ] a, X (o a) :=
  (PiTensorProduct.reindex ℂ X (blockEquiv o ho).symm).trans <|
    ((PiTensorProduct.tmulEquivDep ℂ fun i => X (blockEquiv o ho i)).symm).trans <|
      (TensorProduct.congr (LinearEquiv.refl ℂ (⨂[ℂ] a, X (o a)))
        ((PiTensorProduct.congr fun c : Off o => φ c).trans
          (PiTensorProduct.constantBaseRingEquiv (Off o) ℂ).toLinearEquiv)).trans
        (TensorProduct.rid ℂ _)

open scoped Classical in

theorem dropEquiv_tprod (o : Fin r' → Fin r) (ho : Function.Injective o)
    (φ : ∀ c : Off o, X c ≃ₗ[ℂ] ℂ) (x : ∀ j, X j) :
    dropEquiv o ho φ (PiTensorProduct.tprod ℂ x) =
      (∏ c : Off o, φ c (x c)) • PiTensorProduct.tprod ℂ fun a => x (o a) := by
  have h1 : PiTensorProduct.reindex ℂ X (blockEquiv o ho).symm (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.tprod ℂ fun i => x (blockEquiv o ho i) :=
    PiTensorProduct.reindex_tprod _ _
  have h2 := PiTensorProduct.tmulEquivDep_symm_apply ℂ (fun i => X (blockEquiv o ho i))
    (fun i => x (blockEquiv o ho i))
  have h3 : (PiTensorProduct.congr fun c : Off o => φ c)
      (PiTensorProduct.tprod ℂ fun c : Off o => x c) = PiTensorProduct.tprod ℂ fun c : Off o => φ c (x c) :=
    PiTensorProduct.congr_tprod _ _
  have ht : ((PiTensorProduct.tmulEquivDep ℂ fun i => X (blockEquiv o ho i)).symm
      (PiTensorProduct.reindex ℂ X (blockEquiv o ho).symm (PiTensorProduct.tprod ℂ x)) :
        TensorProduct ℂ (⨂[ℂ] a, X (o a)) (⨂[ℂ] c : Off o, X c)) =
      (PiTensorProduct.tprod ℂ fun a => x (o a)) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun c : Off o => x c) :=
    (congrArg _ h1).trans h2
  show (TensorProduct.rid ℂ _) ((TensorProduct.congr (LinearEquiv.refl ℂ (⨂[ℂ] a, X (o a)))
        ((PiTensorProduct.congr fun c : Off o => φ c).trans
          (PiTensorProduct.constantBaseRingEquiv (Off o) ℂ).toLinearEquiv))
      ((PiTensorProduct.tmulEquivDep ℂ fun i => X (blockEquiv o ho i)).symm
        (PiTensorProduct.reindex ℂ X (blockEquiv o ho).symm (PiTensorProduct.tprod ℂ x)) :
        TensorProduct ℂ (⨂[ℂ] a, X (o a)) (⨂[ℂ] c : Off o, X c))) = _
  rw [ht, TensorProduct.congr_tmul, LinearEquiv.trans_apply, h3, TensorProduct.rid_tmul]
  congr 1
  exact PiTensorProduct.constantBaseRingEquiv_tprod _

theorem piTensor_drop_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r r' : ℕ} (y : Fin r → IrrGL k) (o : Fin r' → Fin r), StrictMono o → (∀ j, (y j).1 ≠ 0 → j ∈ Set.range o) → Nonempty ((piTensor fun j => (y j).rep).Equiv ((piTensor fun a => (y (o a)).rep).comp (GlobalTheory.CompanionTheory.FineProd.dropHom (k := k) (fun j => (y j).1) o) : Representation ℂ (Levi k fun j => Fin (y j).1) _)) := by
  intro k _ _ _ _ r r' y o ho hy
  have hz : ∀ c : Off o, (y c).1 = 0 := fun c => by
    by_contra h
    exact c.2 (hy c h)
  have hφ : ∀ c : Off o, Nonempty ((y c).2.rep.V ≃ₗ[ℂ] ℂ) := fun c => by
    haveI := subsingleton_GL (k := k) (hz c)
    exact exists_line (y c).2.rep.irr
  let φ : ∀ c : Off o, (y c).2.rep.V ≃ₗ[ℂ] ℂ := fun c => (hφ c).some
  refine ⟨Representation.Equiv.mk (dropEquiv o ho.injective φ) fun g => ?_⟩
  refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
  have hc : ∀ c : Off o, (y c).rep (g c) (x c) = x c := fun c => by
    haveI := subsingleton_GL (k := k) (hz c)
    rw [Subsingleton.elim (g c) 1, map_one]
    rfl
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    piTensor_tprod, dropEquiv_tprod, hc, map_smul]
  congr 1
  exact (piTensor_tprod (fun a => (y (o a)).rep) (fun a => g (o a)) (fun a => x (o a))).symm

end GlobalTheory.CompanionTheory.FineProd.TensorLine

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransposeInverseInvolutionApply
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
open scoped Matrix

namespace GlobalTheory.CompanionTheory.ThetaInv

theorem thetaW_val_apply {A : Type} [CommRing A] (N : ℕ) (g : GL (Fin N) A) (i j : Fin N) :
    (thetaW A N g).1 i j = (g⁻¹).1 (Fin.rev j) (Fin.rev i) := by
  simp [thetaW, invT, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix,
    Matrix.transpose_apply, Fin.revPerm]

theorem thetaW_thetaW_ring {A : Type} [CommRing A] (N : ℕ) (g : GL (Fin N) A) :
    thetaW A N (thetaW A N g) = g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [thetaW_val_apply, ← map_inv, thetaW_val_apply, inv_inv, Fin.rev_rev, Fin.rev_rev]

theorem thetaW_thetaW {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (g : GL (Fin N) k) :
    thetaW k N (thetaW k N g) = g :=
  thetaW_thetaW_ring N g

end GlobalTheory.CompanionTheory.ThetaInv

end
end

