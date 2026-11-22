import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0035
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0237
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0176
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalisedInductionProductParabolicPiTensor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0058
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0362
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.UpperRightUnipotentInvariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0534
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0536
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Unfold2
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.ContraProd

section Family

variable {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)]
  [∀ a, TopologicalSpace (Γ a)] [∀ a, IsTopologicalGroup (Γ a)]
  [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]

theorem exists_pi_subset
    (hG : ∀ a, ∀ U ∈ nhds (1 : Γ a), ∃ K : Subgroup (Γ a), IsOpen (K : Set (Γ a)) ∧
      IsCompact (K : Set (Γ a)) ∧ (K : Set (Γ a)) ⊆ U)
    (U : Set (∀ a, Γ a)) (hU : U ∈ nhds (1 : ∀ a, Γ a)) :
    ∃ H : ∀ a, Subgroup (Γ a), (∀ a, IsOpen (H a : Set (Γ a))) ∧ (∀ a, IsCompact (H a : Set (Γ a))) ∧
      ((Subgroup.pi Set.univ H : Subgroup (∀ a, Γ a)) : Set (∀ a, Γ a)) ⊆ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, -, t, ht, hsub⟩ := hU
  choose H hHo hHc hHs using fun a => hG a (t a) (ht a)
  refine ⟨H, hHo, hHc, fun x hx => hsub fun a _ => hHs a ?_⟩
  exact (Subgroup.mem_pi Set.univ).mp hx a (Set.mem_univ a)

theorem pi_compactOpen_basis
    (hG : ∀ a, ∀ U ∈ nhds (1 : Γ a), ∃ K : Subgroup (Γ a), IsOpen (K : Set (Γ a)) ∧
      IsCompact (K : Set (Γ a)) ∧ (K : Set (Γ a)) ⊆ U) :
    ∀ U ∈ nhds (1 : ∀ a, Γ a), ∃ K : Subgroup (∀ a, Γ a), IsOpen (K : Set (∀ a, Γ a)) ∧
      IsCompact (K : Set (∀ a, Γ a)) ∧ (K : Set (∀ a, Γ a)) ⊆ U := by
  intro U hU
  obtain ⟨H, hHo, hHc, hsub⟩ := exists_pi_subset hG U hU
  refine ⟨Subgroup.pi Set.univ H, ?_, ?_, hsub⟩
  · show IsOpen (Set.pi Set.univ fun a => (H a : Set (Γ a)))
    exact isOpen_set_pi Set.finite_univ fun a _ => hHo a
  · show IsCompact (Set.pi Set.univ fun a => (H a : Set (Γ a)))
    exact isCompact_univ_pi fun a => hHc a

theorem isAdmissible_piTensor [∀ a, T2Space (Γ a)]
    (hG : ∀ a, ∀ U ∈ nhds (1 : Γ a), ∃ K : Subgroup (Γ a), IsOpen (K : Set (Γ a)) ∧
      IsCompact (K : Set (Γ a)) ∧ (K : Set (Γ a)) ⊆ U)
    {ρ : ∀ a, Representation ℂ (Γ a) (X a)} (hρ : ∀ a, IsAdmissible (ρ a)) :
    IsAdmissible (piTensor ρ) := by
  refine ⟨isSmooth_piTensor fun a => (hρ a).1, fun K ho hc => ?_⟩
  obtain ⟨H, h1, h2, h3⟩ := exists_pi_subset hG _ (ho.mem_nhds (one_mem K))
  haveI : ∀ a, FiniteDimensional ℂ (fixed (ρ a) (H a)) := fun a => (hρ a).2 _ (h1 a) (h2 a)
  let M : (⨂[ℂ] a, fixed (ρ a) (H a)) →ₗ[ℂ] ⨂[ℂ] a, X a :=
    PiTensorProduct.map fun a => (fixed (ρ a) (H a)).subtype
  have hle : fixed (piTensor ρ) K ≤ LinearMap.range M := by
    intro w hw
    have hs := GlobalTheory.SmGL.IndTensor.mem_span_of_fixed (fun a => (hρ a).1) h2 w fun h hh =>
      GlobalTheory.ContraRefl.mem_fix.1 hw h (h3 hh)
    refine Submodule.span_le.2 ?_ hs
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨PiTensorProduct.tprod ℂ fun a => ⟨v a, hv a⟩, by simp [M]⟩
  exact Submodule.finiteDimensional_of_le hle

def pairForm (ρ : ∀ a, Representation ℂ (Γ a) (X a)) :
    (⨂[ℂ] a, X a) →ₗ[ℂ] (⨂[ℂ] a, smoothPart (ρ a).dual) →ₗ[ℂ] ℂ :=
  ((PiTensorProduct.dualDistrib (R := ℂ) (M := X)) ∘ₗ
    PiTensorProduct.map fun a => (smoothPart (ρ a).dual).subtype).flip

theorem pairForm_tprod (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (v : ∀ a, X a)
    (l : ∀ a, smoothPart (ρ a).dual) :
    pairForm ρ (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ l) =
      ∏ a, (l a : Module.Dual ℂ (X a)) (v a) := by
  simp only [pairForm, LinearMap.flip_apply, LinearMap.comp_apply, PiTensorProduct.map_tprod,
    PiTensorProduct.dualDistrib_apply, Submodule.subtype_apply]

theorem pairForm_invariant (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (g : ∀ a, Γ a)
    (s : ⨂[ℂ] a, X a) (t : ⨂[ℂ] a, smoothPart (ρ a).dual) :
    pairForm ρ (piTensor ρ g s) (piTensor (fun a => contra (ρ a)) g t) = pairForm ρ s t := by
  have hpt : ∀ v : ∀ a, X a, piTensor ρ g (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.tprod ℂ (fun a => ρ a (g a) (v a)) := by
    intro v
    show PiTensorProduct.mapMonoidHom ((MonoidHom.pi fun a => (ρ a).comp (Pi.evalMonoidHom Γ a)) g)
      (PiTensorProduct.tprod ℂ v) = _
    rw [PiTensorProduct.mapMonoidHom_apply, PiTensorProduct.map_tprod]
    rfl
  have hpt' : ∀ l : ∀ a, smoothPart (ρ a).dual, piTensor (fun a => contra (ρ a)) g (PiTensorProduct.tprod ℂ l) =
      PiTensorProduct.tprod ℂ (fun a => contra (ρ a) (g a) (l a)) := by
    intro l
    show PiTensorProduct.mapMonoidHom ((MonoidHom.pi fun a => (contra (ρ a)).comp (Pi.evalMonoidHom Γ a)) g)
      (PiTensorProduct.tprod ℂ l) = _
    rw [PiTensorProduct.mapMonoidHom_apply, PiTensorProduct.map_tprod]
    rfl
  refine PiTensorProduct.induction_on s (fun r v => ?_) (fun x y hx hy => ?_)
  · refine PiTensorProduct.induction_on t (fun r' l => ?_) (fun x y hx hy => ?_)
    · simp only [map_smul, LinearMap.smul_apply]
      rw [hpt, hpt', pairForm_tprod, pairForm_tprod]
      congr 2
      refine Finset.prod_congr rfl fun a _ => ?_
      show (l a : Module.Dual ℂ (X a)) (ρ a (g a)⁻¹ (ρ a (g a) (v a))) = (l a : Module.Dual ℂ (X a)) (v a)
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    · simp only [map_add, hx, hy]
  · simp only [map_add, LinearMap.add_apply, hx, hy]

theorem nonempty_equiv_piTensor_contra [∀ a, T2Space (Γ a)]
    (hG : ∀ a, ∀ U ∈ nhds (1 : Γ a), ∃ K : Subgroup (Γ a), IsOpen (K : Set (Γ a)) ∧
      IsCompact (K : Set (Γ a)) ∧ (K : Set (Γ a)) ⊆ U)
    {ρ : ∀ a, Representation ℂ (Γ a) (X a)} (hρ : ∀ a, IsAdmissible (ρ a))
    (hi : ∀ a, (ρ a).IsIrreducible) :
    Nonempty ((piTensor fun a => contra (ρ a)).Equiv (contra (piTensor ρ))) := by
  have hK : ∀ a, ∃ K : Subgroup (Γ a), IsOpen (K : Set (Γ a)) ∧ IsCompact (K : Set (Γ a)) := fun a => by
    obtain ⟨K, h1, h2, -⟩ := hG a Set.univ Filter.univ_mem
    exact ⟨K, h1, h2⟩
  choose K0 hK1 hK2 using hK
  have hschur : ∀ a, ∀ φ : X a →ₗ[ℂ] X a, (∀ g x, φ (ρ a g x) = ρ a g (φ x)) →
      ∃ c : ℂ, φ = c • LinearMap.id := fun a =>
    GlobalTheory.SchurAdm.schur_admissible (Γ a) (K0 a) (hK1 a) (hK2 a) (X a) (ρ a) (hi a) (hρ a)
  have hci : ∀ a, (contra (ρ a)).IsIrreducible := fun a =>
    GlobalTheory.ContraRefl.contra_isIrreducible (hG a) (hρ a) (hi a)
  have hca : ∀ a, IsAdmissible (contra (ρ a)) := fun a =>
    GlobalTheory.SmGL.ContraTrace.isAdmissible_contra (hρ a)
  have hcschur : ∀ a, ∀ φ : smoothPart (ρ a).dual →ₗ[ℂ] smoothPart (ρ a).dual,
      (∀ g x, φ (contra (ρ a) g x) = contra (ρ a) g (φ x)) → ∃ c : ℂ, φ = c • LinearMap.id := fun a =>
    GlobalTheory.SchurAdm.schur_admissible (Γ a) (K0 a) (hK1 a) (hK2 a) _ (contra (ρ a)) (hci a) (hca a)
  have hI : (piTensor ρ).IsIrreducible :=
    GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur ρ hi hschur
  have hI' : (piTensor fun a => contra (ρ a)).IsIrreducible :=
    GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ hci hcschur
  have hCI : (contra (piTensor ρ)).IsIrreducible :=
    GlobalTheory.ContraRefl.contra_isIrreducible (pi_compactOpen_basis hG) (isAdmissible_piTensor hG hρ) hI
  have hB0 : pairForm ρ ≠ 0 := by
    have hne : ∀ a, ∃ v : X a, v ≠ 0 := fun a => by
      by_contra h
      push_neg at h
      apply (bot_ne_top : (⊥ : Subrepresentation (ρ a)) ≠ ⊤)
      apply Subrepresentation.ext
      ext x
      rw [h x]
      exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
    choose v hv using hne
    choose l hl using fun a => GlobalTheory.ContraRefl.exists_smooth_form_ne (hρ a).1 (hG a) (hv a)
    intro h0
    have h1 := pairForm_tprod ρ v l
    rw [h0] at h1
    exact Finset.prod_ne_zero_iff.2 (fun a _ => hl a) (by simpa using h1.symm)
  exact ⟨(GlobalTheory.InvPairing.pairMap (piTensor ρ) (isSmooth_piTensor fun a => isSmooth_contra (ρ a))
    (pairForm ρ) (pairForm_invariant ρ)).ofBijective (GlobalTheory.InvPairing.pairMap_bijective _ _ _ _ hB0 hI' hCI)⟩

end Family

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem contra_rep_isIrreducible (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL k) :
    (contra x.rep).IsIrreducible :=
  GlobalTheory.ContraRefl.contra_isIrreducible (GlobalTheory.SqIntUnit.compactOpen_basis k x.1)
    (hA k x.1 _ x.rep x.2.rep.smooth x.2.rep.irr) x.2.rep.irr

theorem contra_piTensor_rep (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h : ℕ} (x : Fin h → IrrGL k) :
    Nonempty ((piTensor fun a => contra (x a).rep).Equiv (contra (piTensor fun a => (x a).rep))) := by
  haveI : ∀ a, T2Space (GL (Fin (x a).1) k) := fun a => GlobalTheory.SplitFlip.t2Space_general_linear_group
  exact nonempty_equiv_piTensor_contra (Γ := fun a => GL (Fin (x a).1) k)
    (fun a => GlobalTheory.SqIntUnit.compactOpen_basis k (x a).1)
    (fun a => hA k (x a).1 _ (x a).rep (x a).2.rep.smooth (x a).2.rep.irr)
    fun a => (x a).2.rep.irr

theorem parInd_equiv_contra {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (e : (Σ a, m a) ≃ n) {σ : Representation ℂ (Levi k m) V} {ρ : Representation ℂ (Levi k m) W}
    (hρ : IsSmooth ρ) (φ : Nonempty (σ.Equiv (contra ρ))) :
    Nonempty ((parInd e σ).Equiv (contra (parInd e ρ))) := by
  obtain ⟨φ⟩ := φ
  obtain ⟨ψ⟩ := InductionContragredient.nonempty_equiv (GlobalTheory.CompanionTheory.Glob.inductionContragredient k) e hρ
  exact ⟨(parIndEquiv e φ).trans ψ⟩

theorem contra_prodIrr_multiProd (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ}
    (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) :
    Nonempty ((multiProd (stdBlocks (fun a => (x a).1) hd) fun a => contra (x a).rep).Equiv
      (contra (prodIrr x hd))) :=
  parInd_equiv_contra (stdBlocks (fun a => (x a).1) hd)
    (isSmooth_piTensor fun a => (x a).2.rep.smooth) (contra_piTensor_rep hA x)

theorem contra_prodIrr : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ}
    (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), ∃ hd' : ∑ a, (dualCl (x a)).1 = N,
      Nonempty ((contra (prodIrr x hd)).Equiv (prodIrr (fun a => dualCl (x a)) hd')) := by
  intro k _ _ _ _ hA h N x hd
  have hci := fun a => contra_rep_isIrreducible hA (x a)
  have hy : (fun a => dualCl (x a)) =
      fun a => IrrGL.of (contra (x a).rep) (isSmooth_smoothRep _) (hci a) :=
    funext fun a => dif_pos (hci a)
  have key : ∀ y : Fin h → IrrGL k,
      y = (fun a => IrrGL.of (contra (x a).rep) (isSmooth_smoothRep _) (hci a)) →
      ∃ hd' : ∑ a, (y a).1 = N, Nonempty ((contra (prodIrr x hd)).Equiv (prodIrr y hd')) := by
    rintro _ rfl
    exact ⟨hd, (contra_prodIrr_multiProd hA x hd).map fun ψ => ψ.symm.trans
      (prodIrrEquiv hd (fun a => contra (x a).rep) (fun a => isSmooth_smoothRep _) hci)⟩
  exact key _ hy

end GlobalTheory.CompanionTheory.ContraProd

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConverseTheoremCuspidality
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.GA
open GroundTheory.Automorphic.FourierWhittaker (vecDomain vecMeasure)
open scoped NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.CompanionTheory.CuspGA

def pos2 : Fin 2 → UPos 3 2 := ![⟨(0, 2), by decide⟩, ⟨(1, 2), by decide⟩]

def pos1 : Fin 2 → UPos 3 1 := ![⟨(0, 1), by decide⟩, ⟨(0, 2), by decide⟩]

theorem second_position_bijective : Function.Bijective pos2 := by
  constructor
  · intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [pos2]
  · rintro ⟨⟨i, j⟩, h⟩
    fin_cases i <;> fin_cases j <;> simp at h
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

theorem first_position_bijective : Function.Bijective pos1 := by
  constructor
  · intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [pos1]
  · rintro ⟨⟨i, j⟩, h⟩
    fin_cases i <;> fin_cases j <;> simp at h
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

theorem setIntegral_block {r : ℕ} (e : Fin 2 ≃ UPos 3 r) (F : (UPos 3 r → 𝔸[ℚ]) → ℂ) :
    ∫ X in unipFundamentalDomain ℚ 3 r, F X ∂unipMeasure ℚ 3 r =
      ∫ y in vecDomain ℚ (Fin 2), F (fun p => y (e.symm p)) ∂vecMeasure ℚ (Fin 2) := by
  have hmp := measurePreserving_piCongrLeft (fun _ : UPos 3 r => GroundTheory.Global.adeleMeasure ℚ) e
  have h := hmp.setIntegral_preimage_emb
    (MeasurableEquiv.measurableEmbedding _) F (unipFundamentalDomain ℚ 3 r)
  have happ : ∀ y : Fin 2 → 𝔸[ℚ],
      MeasurableEquiv.piCongrLeft (fun _ : UPos 3 r => 𝔸[ℚ]) e y = fun p => y (e.symm p) := by
    intro y
    funext p
    obtain ⟨i, rfl⟩ := e.surjective p
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  have hpre : (MeasurableEquiv.piCongrLeft (fun _ : UPos 3 r => 𝔸[ℚ]) e) ⁻¹'
      unipFundamentalDomain ℚ 3 r = vecDomain ℚ (Fin 2) := by
    ext y
    simp only [Set.mem_preimage, happ, unipFundamentalDomain, vecDomain, Set.mem_univ_pi]
    exact ⟨fun hy i => by simpa using hy (e i), fun hy p => hy _⟩
  rw [← h, hpre]
  simp only [happ]

theorem unip2 (y : Fin 2 → 𝔸[ℚ]) :
    (unipGL (fun p => y ((Equiv.ofBijective pos2 second_position_bijective).symm p)) : G3) = uni 0 (y 0) (y 1) := by
  have h0 : (Equiv.ofBijective pos2 second_position_bijective).symm ⟨(0, 2), by decide⟩ = 0 :=
    (Equiv.ofBijective pos2 second_position_bijective).symm_apply_apply 0
  have h1 : (Equiv.ofBijective pos2 second_position_bijective).symm ⟨(1, 2), by decide⟩ = 1 :=
    (Equiv.ofBijective pos2 second_position_bijective).symm_apply_apply 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uni, unipMatrix, blockEntry_apply, h0, h1, Matrix.one_apply]

theorem unip1 (y : Fin 2 → 𝔸[ℚ]) :
    (unipGL (fun p => y ((Equiv.ofBijective pos1 first_position_bijective).symm p)) : G3) = uni (y 0) (y 1) 0 := by
  have h0 : (Equiv.ofBijective pos1 first_position_bijective).symm ⟨(0, 1), by decide⟩ = 0 :=
    (Equiv.ofBijective pos1 first_position_bijective).symm_apply_apply 0
  have h1 : (Equiv.ofBijective pos1 first_position_bijective).symm ⟨(0, 2), by decide⟩ = 1 :=
    (Equiv.ofBijective pos1 first_position_bijective).symm_apply_apply 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uni, unipMatrix, blockEntry_apply, h0, h1, Matrix.one_apply]

theorem dia_sw_sq : dia sw * dia sw = 1 := by
  rw [dia, ← map_mul]
  have : sw * sw = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sw, Matrix.mul_apply, Fin.sum_univ_three]
  rw [this, map_one]

theorem conj_sw (x y : 𝔸[ℚ]) : dia sw * uni x y 0 * dia sw = lowM x * uni 0 0 y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sw, uni, lowM, AdelicGLn.diagonal_apply, Matrix.mul_apply, Fin.sum_univ_three]

theorem cusp : Ad3.GA.Cusp := by
  intro f _ hinv hY hY' r hr0 hr3 g
  have hr : r = 1 ∨ r = 2 := by omega
  rcases hr with rfl | rfl
  · have h1 : constantTerm 1 f g = ctY' f (dia sw * g) := by
      rw [constantTerm, setIntegral_block (Equiv.ofBijective pos1 first_position_bijective), ctY']
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      change f (unipGL (fun p => y ((Equiv.ofBijective pos1 first_position_bijective).symm p)) * g) =
        f (lowM (y 0) * uni 0 0 (y 1) * (dia sw * g))
      rw [unip1, ← conj_sw, ← hinv sw (uni (y 0) (y 1) 0 * g)]
      congr 1
      calc dia sw * (uni (y 0) (y 1) 0 * g)
          = dia sw * uni (y 0) (y 1) 0 * 1 * g := by simp only [mul_one, mul_assoc]
        _ = dia sw * uni (y 0) (y 1) 0 * dia sw * (dia sw * g) := by
            rw [← dia_sw_sq]; simp only [mul_assoc]
    rw [h1, hY']
  · have h2 : constantTerm 2 f g = ctY f g := by
      rw [constantTerm, setIntegral_block (Equiv.ofBijective pos2 second_position_bijective), ctY]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      change f (unipGL (fun p => y ((Equiv.ofBijective pos2 second_position_bijective).symm p)) * g) =
        f (uni 0 (y 0) (y 1) * g)
      rw [unip2]
    rw [h2, hY]

end GlobalTheory.CompanionTheory.CuspGA
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CovolumeOneColumnJoinProduct
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold.ProdCovol

open scoped Pointwise

theorem isAddFundamentalDomain_prod {A B : Type*} [AddGroup A] [AddGroup B] [MeasurableSpace A]
    [MeasurableSpace B] {Γ : AddSubgroup A} {Δ : AddSubgroup B} {μ : Measure A} {ν : Measure B} [SFinite μ]
    [SFinite ν] {s : Set A} {t : Set B} (hs : IsAddFundamentalDomain Γ s μ) (ht : IsAddFundamentalDomain Δ t ν) :
    IsAddFundamentalDomain (Γ.prod Δ) (s ×ˢ t) (μ.prod ν) where
  nullMeasurableSet := hs.nullMeasurableSet.prod ht.nullMeasurableSet
  ae_covers := by
    have h1 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hs.ae_covers
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae ht.ae_covers
    filter_upwards [h1, h2] with p hp hq
    obtain ⟨g, hg⟩ := hp
    obtain ⟨h, hh⟩ := hq
    exact ⟨⟨((g : A), (h : B)), AddSubgroup.mem_prod.2 ⟨g.2, h.2⟩⟩, hg, hh⟩
  aedisjoint := by
    intro g h hgh
    change μ.prod ν ((g +ᵥ s ×ˢ t) ∩ (h +ᵥ s ×ˢ t)) = 0
    let g1 : Γ := ⟨(g : A × B).1, (AddSubgroup.mem_prod.1 g.2).1⟩
    let h1 : Γ := ⟨(h : A × B).1, (AddSubgroup.mem_prod.1 h.2).1⟩
    let g2 : Δ := ⟨(g : A × B).2, (AddSubgroup.mem_prod.1 g.2).2⟩
    let h2 : Δ := ⟨(h : A × B).2, (AddSubgroup.mem_prod.1 h.2).2⟩
    by_cases e1 : g1 = h1
    · have e2 : g2 ≠ h2 := fun e2 => hgh (Subtype.ext (Prod.ext (congrArg Subtype.val e1) (congrArg Subtype.val e2)))
      have h0 : ν ((g2 +ᵥ t) ∩ (h2 +ᵥ t)) = 0 := ht.aedisjoint e2
      refine measure_mono_null (t := Set.univ ×ˢ ((g2 +ᵥ t) ∩ (h2 +ᵥ t))) ?_ ?_
      · rintro p ⟨hp1, hp2⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hp1 hp2
        refine ⟨Set.mem_univ _, ?_, ?_⟩
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp1.2
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp2.2
      · rw [Measure.prod_prod, h0, mul_zero]
    · have h0 : μ ((g1 +ᵥ s) ∩ (h1 +ᵥ s)) = 0 := hs.aedisjoint e1
      refine measure_mono_null (t := ((g1 +ᵥ s) ∩ (h1 +ᵥ s)) ×ˢ Set.univ) ?_ ?_
      · rintro p ⟨hp1, hp2⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hp1 hp2
        refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp1.1
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp2.1
      · rw [Measure.prod_prod, h0, zero_mul]

variable {D : D7} {m r s : ℕ}

def joinAdd (D : D7) (m r s : ℕ) : Mx D m r × Mx D m s ≃+ Mx D m (r + s) :=
  { joinEquiv with map_add' := fun a b => colJoin_add a.1 b.1 a.2 b.2 }

theorem joinAdd_apply (z : Mx D m r × Mx D m s) : joinAdd D m r s z = colJoin z.1 z.2 := rfl

theorem continuous_joinAdd : Continuous (joinAdd D m r s) := by
  refine continuous_matrix fun i k => ?_
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · have : (fun z : Mx D m r × Mx D m s => joinAdd D m r s z i (Fin.castAdd s j)) = fun z => z.1 i j :=
      funext fun z => colJoin_castAdd z.1 z.2 i j
    rw [this]
    exact (continuous_apply_apply i j).comp continuous_fst
  · have : (fun z : Mx D m r × Mx D m s => joinAdd D m r s z i (Fin.natAdd r j)) = fun z => z.2 i j :=
      funext fun z => colJoin_natAdd z.1 z.2 i j
    rw [this]
    exact (continuous_apply_apply i j).comp continuous_snd

theorem continuous_joinAdd_symm : Continuous (joinAdd D m r s).symm := by
  refine Continuous.prodMk ?_ ?_
  · exact continuous_matrix fun i j => continuous_apply_apply i (Fin.castAdd s j)
  · exact continuous_matrix fun i j => continuous_apply_apply i (Fin.natAdd r j)

theorem joinAdd_mem_iff (z : Mx D m r × Mx D m s) :
    joinAdd D m r s z ∈ ratMx D m (r + s) ↔ z ∈ (ratMx D m r).prod (ratMx D m s) := by
  rw [AddSubgroup.mem_prod]
  constructor
  · rintro h
    obtain ⟨γ, hγ⟩ := mem_ratMx.1 h
    refine ⟨mem_ratMx.2 ⟨colL γ, ?_⟩, mem_ratMx.2 ⟨colR γ, ?_⟩⟩
    · ext i j
      have := congrFun (congrFun hγ i) (Fin.castAdd s j)
      rw [joinAdd_apply, colJoin_castAdd] at this
      exact this
    · ext i j
      have := congrFun (congrFun hγ i) (Fin.natAdd r j)
      rw [joinAdd_apply, colJoin_natAdd] at this
      exact this
  · rintro ⟨h1, h2⟩
    obtain ⟨p, hp⟩ := mem_ratMx.1 h1
    obtain ⟨q, hq⟩ := mem_ratMx.1 h2
    exact mem_ratMx.2 ⟨colJoin p q, by rw [rat_colJoin, hp, hq, joinAdd_apply]⟩

theorem isCovolOne_colJoin : ∀ (D : D7) (m r s : ℕ) (μr : Measure (Mx D m r)) (𝓕r : Set (Mx D m r))
    (μs : Measure (Mx D m s)) (𝓕s : Set (Mx D m s)), IsCovolOne (ratMx D m r) μr 𝓕r → IsCovolOne (ratMx D m s) μs 𝓕s →
    IsCovolOne (ratMx D m (r + s)) ((μr.prod μs).map fun z => colJoin z.1 z.2)
      ((fun z : Mx D m r × Mx D m s => colJoin z.1 z.2) '' (𝓕r ×ˢ 𝓕s)) := by
  intro D m r s μr 𝓕r μs 𝓕s hr hs
  obtain ⟨a1, a2, a3, a4, a5, -⟩ := lattice_Mx D m r
  obtain ⟨b1, b2, b3, b4, b5, -⟩ := lattice_Mx D m s
  obtain ⟨c1, c2, c3, c4, c5, -⟩ := lattice_Mx D m (r + s)
  haveI : BorelSpace (Mx D m r) := ⟨rfl⟩
  haveI : BorelSpace (Mx D m s) := ⟨rfl⟩
  haveI : BorelSpace (Mx D m (r + s)) := ⟨rfl⟩
  obtain ⟨hHr, hFr, h1r⟩ := hr
  obtain ⟨hHs, hFs, h1s⟩ := hs
  haveI := hHr
  haveI := hHs
  let e := joinAdd D m r s
  have he : Continuous e := continuous_joinAdd
  have he' : Continuous e.symm := continuous_joinAdd_symm
  let f : (Mx D m r × Mx D m s) ≃ₜ Mx D m (r + s) :=
    { e.toEquiv with continuous_toFun := he, continuous_invFun := he' }
  have hemb : MeasurableEmbedding e := f.measurableEmbedding
  have hfun : (fun z : Mx D m r × Mx D m s => colJoin z.1 z.2) = e := rfl
  rw [hfun]
  refine ⟨e.isAddHaarMeasure_map _ he he', ?_, ?_⟩
  · let g : ratMx D m (r + s) ≃ (ratMx D m r).prod (ratMx D m s) :=
      { toFun := fun γ => ⟨e.symm γ, (joinAdd_mem_iff _).1 (by
          change e (e.symm γ) ∈ _
          rw [e.apply_symm_apply]; exact γ.2)⟩
        invFun := fun γ => ⟨e γ, (joinAdd_mem_iff _).2 γ.2⟩
        left_inv := fun γ => Subtype.ext (e.apply_symm_apply _)
        right_inv := fun γ => Subtype.ext (e.symm_apply_apply _) }
    refine (isAddFundamentalDomain_prod hFr hFs).image_of_equiv e.toEquiv ?_ g fun γ x => ?_
    · refine ⟨he'.measurable, ?_⟩
      have : ((μr.prod μs).map e).map e.symm = μr.prod μs := by
        rw [Measure.map_map he'.measurable he.measurable]
        have : (e.symm ∘ e : Mx D m r × Mx D m s → Mx D m r × Mx D m s) = id := funext e.symm_apply_apply
        rw [this, Measure.map_id]
      exact this.absolutelyContinuous
    · change e (e.symm γ + x) = γ + e x
      rw [map_add, e.apply_symm_apply]
  · rw [hemb.map_apply, Set.preimage_image_eq _ e.injective, Measure.prod_prod, h1r, h1s, one_mul]

end GlobalTheory.CompanionTheory.EisUnfold.ProdCovol

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinCellsDecompositionStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_cells_decomposition : PositivityTheory.GramSchwartzFunctions.EC.Bruhat → PositivityTheory.GramSchwartzFunctions.EC.RatPts → PositivityTheory.GramSchwartzFunctions.EC.PInv → PositivityTheory.GramSchwartzFunctions.EC.Term2 → PositivityTheory.GramSchwartzFunctions.EisCells := by
  first | exact @GlobalTheory.CompanionTheory.EisCellsAsm.eisCells_of | exact GlobalTheory.CompanionTheory.EisCellsAsm.eisCells_of | (intros; apply GlobalTheory.CompanionTheory.EisCellsAsm.eisCells_of <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinSecondTermFromPartsStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_second_term_from_parts : PositivityTheory.GramSchwartzFunctions.EC.HeisSch → PositivityTheory.GramSchwartzFunctions.EC.Covar → PositivityTheory.GramSchwartzFunctions.EC.Zero → PositivityTheory.GramSchwartzFunctions.EC.Unfold2 → PositivityTheory.GramSchwartzFunctions.EC.ThetaInv → PositivityTheory.GramSchwartzFunctions.EC.Term2 := by
  first | exact @GlobalTheory.CompanionTheory.EisCells.term_of_covariance | exact GlobalTheory.CompanionTheory.EisCells.term_of_covariance | (intros; apply GlobalTheory.CompanionTheory.EisCells.term_of_covariance <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerProductMeasureEventuallyStandardStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.euler_product_measure_eventually_standard : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (M n d : ℕ) (b : Module.Basis (Fin d) F E) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (c : NNReal) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), GlobalTheory.CompanionTheory.SW.IsEulerProd b I c minf m → ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S → ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, Measurable φ → Integrable φ minf → ∀ A : (∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, MeasurableSet (A v)) → (∀ v, m v (A v) ≠ ⊤) → (∀ v, v ∉ S → A v = latV b v) → Integrable (pureN φ A) I ∧ ∫ X, pureN φ A X ∂I = (c : ℂ) * (∫ X, φ X ∂minf) * (∏ v ∈ S, ((m v (A v)).toReal : ℂ)) * ((∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal : ℝ) : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.Euler.integrable_integral_pureN | exact GlobalTheory.CompanionTheory.SiegelND.Coef.Euler.integrable_integral_pureN | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.Euler.integrable_integral_pureN <;> assumption)
end

