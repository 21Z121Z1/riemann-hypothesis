import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0701
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0694
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0034
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantMultiplierMirabolic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0706
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0689
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle0003

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionProductRankZeroLeft
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.CompanionTheory.BZRes
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibRes0Left

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def evalTop (H : Subgroup G) (hH : ∀ g, g ∈ H) (σ : Representation ℂ H W) (hσ : IsSmooth σ) :
    smoothPart (ind H σ) ≃ₗ[ℂ] W where
  toFun f := f.1.1 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun w := ⟨⟨fun g => σ ⟨g, hH g⟩ w, by
      intro h g
      show σ ⟨(h : G) * g, hH _⟩ w = σ h (σ ⟨g, hH g⟩ w)
      rw [← Module.End.mul_apply, ← map_mul]
      rfl⟩, by
      have hop : IsOpen {g : G | σ ⟨g, hH g⟩ w = w} :=
        (hσ w).preimage (continuous_id.subtype_mk hH)
      have h1 : (1 : G) ∈ {g : G | σ ⟨g, hH g⟩ w = w} := by
        show σ ⟨1, hH 1⟩ w = w
        rw [show (⟨1, hH 1⟩ : H) = 1 from rfl, map_one, Module.End.one_apply]
      refine mem_smoothPart_of_nhds (Filter.mem_of_superset (hop.mem_nhds h1) fun g hg => ?_)
      refine Subtype.ext (funext fun x => ?_)
      show σ ⟨x * g, hH _⟩ w = σ ⟨x, hH x⟩ w
      rw [show (⟨x * g, hH _⟩ : H) = ⟨x, hH x⟩ * ⟨g, hH g⟩ from rfl, map_mul, Module.End.mul_apply]
      exact congrArg _ hg⟩
  left_inv f := by
    refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    show σ ⟨g, hH g⟩ (f.1.1 1) = f.1.1 g
    have := f.1.2 ⟨g, hH g⟩ 1
    rw [← this, mul_one]
  right_inv w := by
    show σ ⟨1, hH 1⟩ w = w
    rw [show (⟨1, hH 1⟩ : H) = 1 from rfl, map_one, Module.End.one_apply]

theorem mem_cIndSpace_top (H : Subgroup G) (hH : ∀ g, g ∈ H) (σ : Representation ℂ H W) (f : smoothPart (ind H σ)) :
    f ∈ cIndSpace H σ := by
  exact ⟨{1}, isCompact_singleton, fun g _ => ⟨g, hH g, 1, Set.mem_singleton 1, (mul_one g).symm⟩⟩

def cTop (H : Subgroup G) (hH : ∀ g, g ∈ H) (σ : Representation ℂ H W) :
    cIndSpace H σ ≃ₗ[ℂ] smoothPart (ind H σ) where
  toFun f := f.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨f, mem_cIndSpace_top H hH σ f⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {P W₂ : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [AddCommGroup W₂] [Module ℂ W₂]

theorem equiv_of_top (ι : P →* G) (hι : Continuous ι) (Q : Subgroup G) (H : Subgroup P) (hQ : ∀ g, g ∈ Q)
    (hH : ∀ p, p ∈ H) (σ : Representation ℂ Q W) (τ : Representation ℂ H W₂) (E : W ≃ₗ[ℂ] W₂) (hσ : IsSmooth σ)
    (hE : ∀ (h : H) (v : W), τ h (E v) = E (σ ⟨ι h, hQ _⟩ v)) :
    Nonempty (Representation.Equiv ((smInd Q σ).comp ι) (cInd H τ)) := by
  have hτ : IsSmooth τ := by
    intro w
    obtain ⟨v, rfl⟩ := E.surjective w
    have hset : {h : H | τ h (E v) = E v} =
        (fun h : H => (⟨ι h, hQ _⟩ : Q)) ⁻¹' {q : Q | σ q v = v} := by
      ext h
      show τ h (E v) = E v ↔ σ ⟨ι h, hQ _⟩ v = v
      rw [hE h v]
      exact E.injective.eq_iff
    rw [hset]
    exact (hσ v).preimage ((hι.comp continuous_subtype_val).subtype_mk _)
  let L : smoothPart (ind Q σ) ≃ₗ[ℂ] cIndSpace H τ :=
    ((evalTop Q hQ σ hσ).trans E).trans ((evalTop H hH τ hτ).symm.trans (cTop H hH τ).symm)
  refine ⟨Representation.Equiv.mk L fun p => ?_⟩
  refine LinearMap.ext fun f => ?_
  refine Subtype.ext (Subtype.ext (Subtype.ext (funext fun x => ?_)))
  show τ ⟨x, hH x⟩ (E (f.1.1 (1 * ι p))) = τ ⟨x * p, hH _⟩ (E (f.1.1 1))
  have hf : f.1.1 (ι p) = σ ⟨ι p, hQ _⟩ (f.1.1 1) := by
    have := f.1.2 ⟨ι p, hQ _⟩ 1
    rw [mul_one] at this
    exact this
  rw [one_mul, hf, show E (σ ⟨ι p, hQ _⟩ (f.1.1 1)) = τ ⟨p, hH p⟩ (E (f.1.1 1)) from (hE ⟨p, hH p⟩ _).symm,
    ← Module.End.mul_apply, ← map_mul]
  rfl

end Abstract

section Concrete

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem hgp_twist_tE {m j : ℕ}
    (π₁ : Representation ℂ (GL (Fin m) k) V) (π₂ : Representation ℂ (GL (Fin (j + 1)) k) W) (g : MirabolicParabolic k m j)
    (hq : ((g : Mir k (m + j)) : GL (Fin (m + j + 1)) k) ∈
      parab k (two (stdSum (rfl : m + (j + 1) = m + j + 1))))
    (v : ⨂[ℂ] x, TwoT V W x) :
    ((extTensor (GRep.tw (⟨V, π₁⟩ : GRep k m) (((j + 1 : ℕ) : ℝ) / 2)).ρ
        (mtw (gres (⟨W, π₂⟩ : GRep k (j + 1))) (-((m : ℕ) : ℝ) / 2)).ρ).comp (gpProj k m j)) g (tE V W v) =
      tE V W (sQ (rfl : m + (j + 1) = m + j + 1) π₁ π₂ ⟨_, hq⟩ v) := by
  set L := leviProj k (two (stdSum (rfl : m + (j + 1) = m + j + 1))) ⟨_, hq⟩ with hL
  have hL2 : leviTwo k (Fin m) (Fin (j + 1)) (L false, L true) = L := by
    funext b
    cases b <;> rfl
  have hδ := GlobalTheory.SmGL.deltaHalf_two (k := k) (a := Fin m) (b := Fin (j + 1)) (L false, L true)
  rw [hL2] at hδ
  have hc : (((dpow m (((j + 1 : ℕ) : ℝ) / 2)) (L false) : ℂˣ) : ℂ) *
      (((dpow (j + 1) (-((m : ℕ) : ℝ) / 2)) (L true) : ℂˣ) : ℂ) =
      ((deltaHalf k (Two (Fin m) (Fin (j + 1))) L : ℂˣ) : ℂ) := by
    rw [hδ, Units.val_mul]
    simp only [dpow, GlobalTheory.SmGL.detChar_apply, Fintype.card_fin]
    congr 4 <;> push_cast <;> ring
  have key : ∀ x : (b : Bool) → TwoT V W b,
      ((extTensor (GRep.tw (⟨V, π₁⟩ : GRep k m) (((j + 1 : ℕ) : ℝ) / 2)).ρ
        (mtw (gres (⟨W, π₂⟩ : GRep k (j + 1))) (-((m : ℕ) : ℝ) / 2)).ρ).comp (gpProj k m j)) g
          (tE V W (PiTensorProduct.tprod ℂ x)) =
      tE V W (sQ (rfl : m + (j + 1) = m + j + 1) π₁ π₂ ⟨_, hq⟩ (PiTensorProduct.tprod ℂ x)) := by
    intro x
    have e1 : tE V W (PiTensorProduct.tprod ℂ x) = x false ⊗ₜ[ℂ] x true :=
      GlobalTheory.SmGL.Exponents.boolTensorEquiv_tprod x
    have e2 : sQ (rfl : m + (j + 1) = m + j + 1) π₁ π₂ ⟨_, hq⟩ (PiTensorProduct.tprod ℂ x) =
        ((deltaHalf k (Two (Fin m) (Fin (j + 1))) L : ℂˣ) : ℂ) •
          PiTensorProduct.tprod ℂ (fun b => twoRep π₁ π₂ b (L b) (x b)) := by
      show ((deltaHalf k (Two (Fin m) (Fin (j + 1))) L : ℂˣ) : ℂ) •
          (piTensor (twoRep π₁ π₂) L) (PiTensorProduct.tprod ℂ x) = _
      rw [GlobalTheory.SmGL.piTensor_tprod]
    have e3 : tE V W (PiTensorProduct.tprod ℂ (fun b => twoRep π₁ π₂ b (L b) (x b))) =
        π₁ (L false) (x false) ⊗ₜ[ℂ] π₂ (L true) (x true) :=
      GlobalTheory.SmGL.Exponents.boolTensorEquiv_tprod _
    rw [e1, e2, map_smul, e3, MonoidHom.comp_apply]
    erw [GlobalTheory.SmGL.extTensor_tmul]
    show ((((dpow m (((j + 1 : ℕ) : ℝ) / 2)) (L false) : ℂˣ) : ℂ) • π₁ (L false) (x false)) ⊗ₜ[ℂ]
        ((((dpow (j + 1) (-((m : ℕ) : ℝ) / 2)) (L true) : ℂˣ) : ℂ) • π₂ (L true) (x true)) = _
    rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, hc]
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [LinearEquiv.map_smul (tE V W) r,
      LinearMap.map_smul (sQ (rfl : m + (j + 1) = m + j + 1) π₁ π₂ ⟨_, hq⟩) r,
      LinearEquiv.map_smul (tE V W), ← key x]
    exact LinearMap.map_smul _ _ _
  | add a b ha hb =>
    rw [LinearEquiv.map_add (tE V W) a b,
      LinearMap.map_add (sQ (rfl : m + (j + 1) = m + j + 1) π₁ π₂ ⟨_, hq⟩) a b,
      LinearEquiv.map_add (tE V W), ← ha, ← hb]
    exact LinearMap.map_add _ _ _

theorem mem_parab_zero {j : ℕ} (g : GL (Fin (0 + j + 1)) k) :
    g ∈ parab k (two (stdSum (rfl : 0 + (j + 1) = 0 + j + 1))) := by
  intro a b hab
  have key : ∀ x : Fin (0 + j + 1), GlobalTheory.SmGL.blk (two (stdSum (rfl : 0 + (j + 1) = 0 + j + 1))) x = true := by
    intro x
    unfold GlobalTheory.SmGL.blk
    rcases (two (stdSum (rfl : 0 + (j + 1) = 0 + j + 1))).symm x with ⟨b, y⟩
    cases b
    · exact Fin.elim0 y
    · rfl
  rw [key, key] at hab
  exact absurd hab (lt_irrefl _)

theorem isSmooth_sQ {r t N : ℕ} (h : r + t = N) {π₁ : Representation ℂ (GL (Fin r) k) V}
    {π₂ : Representation ℂ (GL (Fin t) k) W} (h₁ : IsSmooth π₁) (h₂ : IsSmooth π₂) : IsSmooth (sQ h π₁ π₂) := by
  refine GlobalTheory.SmGL.isSmooth_comp (GlobalTheory.SmGL.isSmooth_twist (GlobalTheory.SmGL.isSmooth_piTensor fun b => ?_)
    (GlobalTheory.SmGL.isSmoothChar_deltaHalf k)) _ ?_
  · cases b
    · exact h₁
    · exact h₂
  · refine continuous_pi fun b => Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact (Units.continuous_val.comp continuous_subtype_val).matrix_submatrix
        (fun i => (two (stdSum h)) ⟨b, i⟩) (fun i => (two (stdSum h)) ⟨b, i⟩)
    · have hinv : Continuous fun p : parab k (two (stdSum h)) =>
          (((p⁻¹ : parab k (two (stdSum h))) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) :=
        (Units.continuous_val.comp continuous_subtype_val).comp continuous_inv
      refine (hinv.matrix_submatrix (fun i => (two (stdSum h)) ⟨b, i⟩)
        (fun i => (two (stdSum h)) ⟨b, i⟩)).congr fun p => ?_
      rw [← Pi.inv_apply, ← map_inv]
      rfl

theorem gres_prod_zero_left (j n : ℕ) (π₁ : GRep k 0) (π₂ : GRep k (j + 1)) (h : 0 + (j + 1) = n + 1) (h' : 0 + j = n)
    (h₁ : IsSmooth π₁.ρ) (h₂ : IsSmooth π₂.ρ) :
    MIso (gres ((π₁.prod π₂).cast h)) (mcast h' (prodGPn π₁ (gres π₂))) := by
  subst h'
  exact equiv_of_top (Mir k (0 + j)).subtype continuous_subtype_val
    (parab k (two (stdSum (rfl : 0 + (j + 1) = 0 + j + 1)))) (MirabolicParabolic k 0 j)
    (fun g => mem_parab_zero g) (fun p => mem_parab_zero (p : GL (Fin (0 + j + 1)) k))
    (sQ (rfl : 0 + (j + 1) = 0 + j + 1) π₁.ρ π₂.ρ)
    ((extTensor (π₁.tw (((j + 1 : ℕ) : ℝ) / 2)).ρ (mtw (gres π₂) (-((0 : ℕ) : ℝ) / 2)).ρ).comp (gpProj k 0 j))
    (tE π₁.V π₂.V) (isSmooth_sQ rfl h₁ h₂)
    (fun hh v => hgp_twist_tE π₁.ρ π₂.ρ hh (mem_parab_zero _) v)

theorem gres_prod_zero_left' : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (j n : ℕ) (π₁ : GRep k 0) (π₂ : GRep k (j + 1)) (h : 0 + (j + 1) = n + 1) (h' : 0 + j = n),
    IsSmooth π₁.ρ → IsSmooth π₂.ρ → MIso (gres ((π₁.prod π₂).cast h)) (mcast h' (prodGPn π₁ (gres π₂))) := by
  intro k _ _ _ _ j n π₁ π₂ h h' h₁ h₂
  exact gres_prod_zero_left j n π₁ π₂ h h' h₁ h₂

end Concrete

end GlobalTheory.CompanionTheory.LeibRes0Left

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionConstructedFromDoubleCoset
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

theorem exists_nhds_one_tube {G : Type} [Group G] [TopologicalSpace G] {C : Set G} (hC : IsCompact C)
    {n : Set (G × G)} (hn : IsOpen n) (h : ∀ c ∈ C, (c, (1 : G)) ∈ n) :
    ∃ O ∈ 𝓝 (1 : G), ∀ c ∈ C, ∀ u ∈ O, (c, u) ∈ n :=
  _root_.UpperTheory.Reformulated.B.Ylb7.main hC hn h

theorem finite_image_of_rightInvariant {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] {W : Type}
    (φ : P → W) (K' : Subgroup P) (hK' : IsOpen (K' : Set P)) (hinv : ∀ (p : P), ∀ κ ∈ K', φ (p * κ) = φ p)
    {C : Set P} (hC : IsCompact C) : (φ '' C).Finite := by
  obtain ⟨t, -, ht⟩ := hC.elim_nhds_subcover (fun c => {p : P | c⁻¹ * p ∈ K'}) (fun c _ => by
    have ho : IsOpen {p : P | c⁻¹ * p ∈ K'} := hK'.preimage (continuous_const.mul continuous_id)
    exact ho.mem_nhds (by simp [K'.one_mem]))
  refine (t.finite_toSet.image φ).subset ?_
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨c, hc, hcp⟩ := Set.mem_iUnion₂.1 (ht hp)
  refine ⟨c, hc, ?_⟩
  have := hinv c _ hcp
  rw [mul_inv_cancel_left] at this
  exact this.symm

theorem exists_openSubgroup_consistent {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [NonarchimedeanGroup G] {W₁ : Type} [AddCommGroup W₁] [Module ℂ W₁] {Q P : Subgroup G} {x : G} :
    LocSec Q P x → ∀ (σ : Representation ℂ Q W₁), IsSmooth σ → ∀ (φ : P → W₁),
    (∀ (q : Q) (p p' : P), (q : G) * x * (p : G) = x * (p' : G) → φ p' = σ q (φ p)) →
    ∀ (K' : Subgroup P), IsOpen (K' : Set P) → (∀ (p : P), ∀ κ ∈ K', φ (p * κ) = φ p) →
    ∀ (C : Set P), IsCompact C → ∀ (Y : Set G), IsOpen Y → (∀ c ∈ C, x * (c : G) ∈ Y) →
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ (∀ c ∈ C, ∀ κ ∈ K, x * (c : G) * κ ∈ Y) ∧
      ∀ c ∈ C, ∀ κ ∈ K, ∀ (q : Q) (p' : P), (q : G) * x * (c : G) * κ = x * (p' : G) → φ p' = σ q (φ c) := by
  intro hL σ hσ φ hφ K' hK' hinv C hC Y hY hCY
  have hfin : (φ '' C).Finite := finite_image_of_rightInvariant φ K' hK' hinv hC

  have hopenQ : IsOpen {q : Q | ∀ v ∈ φ '' C, σ q v = v} := by
    have e : {q : Q | ∀ v ∈ φ '' C, σ q v = v} = ⋂ v ∈ φ '' C, {q : Q | σ q v = v} := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [e]
    exact hfin.isOpen_biInter fun v _ => hσ v
  obtain ⟨UQ, hUQ, hUQe⟩ := isOpen_induced_iff.1 hopenQ
  have h1UQ : (1 : G) ∈ UQ := by
    have : (1 : Q) ∈ (Subtype.val : Q → G) ⁻¹' UQ := by
      rw [hUQe]
      intro v _
      simp
    exact this
  have hfix : ∀ s : Q, (s : G) ∈ UQ → ∀ c ∈ C, σ s (φ c) = φ c := by
    intro s hs c hc
    have : s ∈ (Subtype.val : Q → G) ⁻¹' UQ := hs
    rw [hUQe] at this
    exact this _ ⟨c, hc, rfl⟩

  obtain ⟨U, hU, hUe⟩ := isOpen_induced_iff.1 hK'
  have h1U : (1 : G) ∈ U := by
    have : (1 : P) ∈ (Subtype.val : P → G) ⁻¹' U := by
      rw [hUe]
      exact K'.one_mem
    exact this
  have hC' : IsCompact ((Subtype.val : P → G) '' C) := hC.image continuous_subtype_val
  obtain ⟨OP, hOP, hOPc⟩ := exists_nhds_one_tube hC' (n := {z : G × G | z.1⁻¹ * z.2 * z.1 ∈ U})
    (hU.preimage (by fun_prop)) (by
      rintro _ ⟨c, -, rfl⟩
      simpa using h1U)
  obtain ⟨O, hO, hOs⟩ := hL UQ (hUQ.mem_nhds h1UQ) OP hOP
  obtain ⟨O₁, hO₁, hO₁c⟩ := exists_nhds_one_tube hC'
    (n := {z : G × G | z.1 * z.2 * z.1⁻¹ ∈ interior O ∧ x * z.1 * z.2 ∈ Y})
    ((isOpen_interior.preimage (by fun_prop)).inter (hY.preimage (by fun_prop))) (by
      rintro _ ⟨c, hc, rfl⟩
      refine ⟨?_, ?_⟩
      · simpa using mem_interior_iff_mem_nhds.2 hO
      · simpa using hCY c hc)
  obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean O₁ hO₁
  have hVc : ∀ c ∈ C, ∀ κ ∈ (V : Subgroup G),
      (c : G) * κ * (c : G)⁻¹ ∈ interior O ∧ x * (c : G) * κ ∈ Y := fun c hc κ hκ =>
    hO₁c _ ⟨c, hc, rfl⟩ κ (hV hκ)
  refine ⟨(V : Subgroup G), V.isOpen, fun c hc κ hκ => (hVc c hc κ hκ).2, ?_⟩
  intro c hc κ hκ q p' hq
  have huO : (c : G) * κ * (c : G)⁻¹ ∈ O := interior_subset (hVc c hc κ hκ).1

  have hmem : x * ((c : G) * κ * (c : G)⁻¹) ∈ dcos Q P x := by
    refine ⟨(q : G)⁻¹, Q.inv_mem q.2, (p' : G) * (c : G)⁻¹, P.mul_mem p'.2 (P.inv_mem c.2), ?_⟩
    calc x * ((c : G) * κ * (c : G)⁻¹) = (q : G)⁻¹ * ((q : G) * x * (c : G) * κ) * (c : G)⁻¹ := by group
      _ = (q : G)⁻¹ * x * ((p' : G) * (c : G)⁻¹) := by rw [hq]; group
  obtain ⟨s, hsQ, hsU, p₂, hp₂, hp₂O, he⟩ := hOs _ huO hmem

  have hconj : (c : G)⁻¹ * p₂ * (c : G) ∈ U := hOPc _ ⟨c, hc, rfl⟩ p₂ hp₂O
  have hκ' : (c⁻¹ * ⟨p₂, hp₂⟩ * c : P) ∈ K' := by
    have : (c⁻¹ * ⟨p₂, hp₂⟩ * c : P) ∈ (Subtype.val : P → G) ⁻¹' U := hconj
    rw [hUe] at this
    exact this
  have hval : φ (⟨p₂, hp₂⟩ * c) = φ c := by
    have := hinv c _ hκ'
    rwa [show c * (c⁻¹ * ⟨p₂, hp₂⟩ * c) = ⟨p₂, hp₂⟩ * c by group] at this
  have hrel : (((⟨(q : G) * s, Q.mul_mem q.2 hsQ⟩ : Q)) : G) * x * ((⟨p₂, hp₂⟩ * c : P) : G) = x * (p' : G) := by
    have : (q : G) * s * x * (p₂ * (c : G)) = (q : G) * (s * x * p₂) * (c : G) := by group
    show (q : G) * s * x * (p₂ * (c : G)) = x * (p' : G)
    rw [this, ← he, ← hq]
    group
  have hsplit : (⟨(q : G) * s, Q.mul_mem q.2 hsQ⟩ : Q) = q * ⟨s, hsQ⟩ := rfl
  rw [hφ _ _ _ hrel, hval, hsplit, map_mul, Module.End.mul_apply, hfix ⟨s, hsQ⟩ hsU c hc]

end GlobalTheory.CompanionTheory.BZRes
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermIdentity
section
noncomputable section

namespace GlobalTheory.CompanionTheory.MirSides

open Matrix PositivityTheory.RgEis PositivityTheory.RgEis.MG
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GodementSection
open GlobalTheory.CompanionTheory.CMMirror
open scoped NumberField.AdeleRing
open NumberField

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem tInv_dgl (d : ι → IdeleGroup k) : tInv (dgl d) = dgl fun i => (d i)⁻¹ := by
  ext r c
  rw [tInv_coe]
  show (Matrix.diagonal fun i => (((d i)⁻¹ : IdeleGroup k) : 𝔸[k]))ᵀ r c =
    Matrix.diagonal (fun i => (((d i)⁻¹ : IdeleGroup k) : 𝔸[k])) r c
  rw [Matrix.diagonal_transpose]

theorem tInv_mem_ratGL {E R : Type} [Field E] [CommRing R] (A : Ad E R) (g : GL ι R) (h : g ∈ A.ratGL ι) :
    tInv g ∈ A.ratGL ι := by
  obtain ⟨x, rfl⟩ := h
  exact ⟨tInv x, (tInv_map _ x).symm⟩

variable {G : Type} [Group G]

theorem kap_tInv (π : G →* GL ι 𝔸[k]) (d : ι → IdeleGroup k) (g : G) :
    kap (tInv.comp π) (fun i => (d i)⁻¹) g = tInv (kap π d g) := by
  unfold kap
  rw [MonoidHom.comp_apply, ← tInv_dgl, map_mul, map_mul, map_inv]

theorem kap_mem [TopologicalSpace G] {π : G →* GL ι 𝔸[k]} {Γ K : Subgroup G} {i₀ i₁ : ι} {ω : HeckeCharacter k}
    {d : ι → IdeleGroup k} {c : G → ℂ} {η η' l : G → ℝ} (h : MirData π Γ K i₀ i₁ ω d c η η' l) (κ : G) (hκ : κ ∈ K) :
    kap π d κ ∈ (adStd k).kGL ι := by
  obtain ⟨κ', hκ', e⟩ := h.piK κ hκ
  have e' : π κ * dgl d = dgl d * κ' := Units.ext e
  have : kap π d κ = κ' := by
    unfold kap
    rw [mul_assoc, e', inv_mul_cancel_left]
  rw [this]
  exact hκ'

theorem bdet_tInv_of_mem {R : Type} [CommRing R] {i : ι}
    (hmul : ∀ p ∈ stab R ({i} : Set ι), ∀ q ∈ stab R ({i} : Set ι),
      bdet ({i} : Set ι) (p * q) = bdet {i} p * bdet {i} q)
    (p : GL ι R) (hp : p ∈ stab R ({i}ᶜ : Set ι)) : bdet ({i} : Set ι) (tInv p) = (bdet {i} p)⁻¹ := by
  have h1 : tInv p ∈ stab R ({i} : Set ι) := (tInv_mem_stab p {i}).2 hp
  have h2 : tInv p⁻¹ ∈ stab R ({i} : Set ι) := (tInv_mem_stab p⁻¹ {i}).2 (inv_mem hp)
  have e := hmul _ h1 _ h2
  have b1 : bdet ({i} : Set ι) (1 : GL ι R) = 1 := by
    have := hmul 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at this
    exact left_eq_mul.1 this
  rw [← map_mul, mul_inv_cancel, map_one, b1, bdet_tInv {i} p⁻¹, inv_inv] at e
  exact eq_inv_of_mul_eq_one_left e.symm

theorem lg_inv {A : Ad k 𝔸[k]} (h : A.GoodL) (b : (𝔸[k])ˣ) : A.lg b⁻¹ = - A.lg b := by
  have h1 := h.lgmul 1 1
  have h2 := h.lgmul b b⁻¹
  rw [mul_one] at h1
  rw [mul_inv_cancel] at h2
  linarith

theorem toIdele_inv {ω : HeckeCharacter k} (h : ω * ω = 1) (b : IdeleGroup k) :
    ω.toIdele b⁻¹ = ω.toIdele b := by
  have e : ω.toIdele b * ω.toIdele b = 1 := by
    rw [HeckeCharacter.toIdele_apply]
    exact DFunLike.congr_fun h (IdeleClassGroup.mk k b)
  rw [map_inv]
  exact inv_eq_of_mul_eq_one_right e

theorem modPow_one_eq (x : IdeleGroup k) :
    modPow x 1 = Complex.exp ((adStd k).lg x : ℝ) := by
  have hp : 0 < (IdeleGroup.ideleModule k x : ℝ) := (IdeleGroup.ideleModule k x).2
  show _ = Complex.exp ((Real.log (IdeleGroup.ideleModule k x : ℝ) : ℝ) : ℂ)
  rw [← Complex.ofReal_exp, Real.exp_log hp, modPow, Complex.cpow_one]

theorem sideOf : StdGood → BdetLaw → SideOf := by
  intro hS hB G _ _ _ _ K _ k _ _ ι _ _ π Γ i₀ i₁ ω d c η η' l h
  have hG := hS k
  have hmul := (hB k 𝔸[k] (adStd k) hG ι {i₁}).2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      { two := h.two
        sq := h.sq
        cont := h.cont
        piK := kap_mem h
        piΓ := h.piΓ
        trans := h.trans _ (Or.inl rfl)
        mem := fun _ => Iff.rfl
        par := h.par
        ht := h.ht
        val := fun p hp => h.val p hp }
  · refine
      { two := h.two
        sq := h.sq
        cont := cont_tInv.comp h.cont
        piK := fun κ hκ => ?_
        piΓ := fun γ hγ => tInv_mem_ratGL _ _ (h.piΓ γ hγ)
        trans := fun g hg => ?_
        mem := fun g => (tInv_mem_stab (π g) {i₁}).symm
        par := h.par'
        ht := h.ht'
        val := fun p hp => ?_ }
    · rw [kap_tInv]
      exact tInv_mem_kGL _ _ (kap_mem h κ hκ)
    · obtain ⟨γ, hγ, e⟩ := h.trans {i₁}ᶜ (Or.inr rfl) (tInv g) (tInv_mem_ratGL _ _ hg)
      refine ⟨γ, hγ, ?_⟩
      have e' := (tInv_mem_stab _ {i₁}).2 e
      rw [map_mul, tInv_tInv, map_inv] at e'
      exact e'
    · have hp' : π p ∈ stab 𝔸[k] ({i₁}ᶜ : Set ι) := hp
      have hb := bdet_tInv_of_mem hmul (π p) hp'
      obtain ⟨v1, v2⟩ := h.val' p hp'
      refine ⟨?_, ?_⟩
      · show c p = ω.toIdele (bdet {i₁} (tInv (π p)))
        rw [hb, toIdele_inv h.sq]
        exact v1
      · show η' p = (adStd k).lg (bdet {i₁} (tInv (π p)))
        rw [hb, lg_inv hG]
        exact v2
  · intro g
    rw [map_mul, tInv_dgl]
    rfl
  · intro g
    rw [map_mul, modPow_mul, modPow_one_eq (Matrix.GeneralLinearGroup.det (π g)), ← h.vall g]

end GlobalTheory.CompanionTheory.MirSides
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothParabolicInductionProduct
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CompanionTheory.BZRes

theorem isSmooth_sQ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {r t N : ℕ} (h : r + t = N)
    (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W)
    (h₁ : IsSmooth π₁) (h₂ : IsSmooth π₂) : IsSmooth (sQ h π₁ π₂) := by
  unfold GlobalTheory.CompanionTheory.BZRes.sQ
  refine GlobalTheory.SmGL.isSmooth_comp ?_ _
    (GlobalTheory.SmGL.ProdIrr.continuous_leviProj _)
  refine GlobalTheory.SmGL.isSmooth_twist ?_
    (GlobalTheory.SmGL.isSmoothChar_deltaHalf k)
  refine GlobalTheory.SmGL.isSmooth_piTensor ?_
  intro x
  cases x
  · exact h₁
  · exact h₂

end GlobalTheory.CompanionTheory.BZRes
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedCharacterBlockValueStatement
section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_character_block_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (c : ℂˣ) (i j : ℕ) (m : GLw a w × GLw b w), ordL m.1.val.det = (i : ℤ) → ordL m.2.val.det = (j : ℤ) → (GlobalTheory.SmGL.unrChar (w.adicCompletion E) c ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) : ℂ) = (c : ℂ) ^ (i * b + j * a) := by
  first | exact @GlobalTheory.CompanionTheory.CtS.NuVal.unrChar_twist | exact GlobalTheory.CompanionTheory.CtS.NuVal.unrChar_twist | (intros; apply GlobalTheory.CompanionTheory.CtS.NuVal.unrChar_twist <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionFourStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_quadratic_condition_four : PositivityTheory.SiegelWeilFormula.Gunr.Q4 := by
  first | exact @GlobalTheory.CompanionTheory.DiscriminantUnit.q4 | exact GlobalTheory.CompanionTheory.DiscriminantUnit.q4 | (intros; apply GlobalTheory.CompanionTheory.DiscriminantUnit.q4 <;> assumption)
end

