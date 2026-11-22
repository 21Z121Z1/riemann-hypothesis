import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactInductionTwistedKernel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0033
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0024
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0426
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0363
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0434
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.RightHolRightHolEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0405
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0397
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0430
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0105
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0425
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0410
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle0002
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbol
import GroundTheory.ProfiniteCohomology.GaloisCohomology.IsZeroGroupCohomologyQuotientToInvariantsGalAdd
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
import GroundTheory.GlobalFields.LocalFieldAtPlace
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.TransportA
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0433

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactInductionTwistEquiv
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.TwCInd

section SlopeTestRemainingChoices

variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup W] [Module ℂ W]

theorem cIndSpace_ext {H : Subgroup G} {τ : Representation ℂ H W} {a b : cIndSpace H τ}
    (h : ∀ g, a.1.1.1 g = b.1.1.1 g) : a = b :=
  Subtype.ext (Subtype.ext (Subtype.ext (funext h)))

theorem mul_mem_indSpace {H : Subgroup G} {τ τ' : Representation ℂ H W} {ψ : G →* ℂˣ}
    (hτ : ∀ (h : H) (w : W), τ' h w = ((ψ h : ℂˣ) : ℂ) • τ h w) (f : cIndSpace H τ) :
    (fun g => ((ψ g : ℂˣ) : ℂ) • f.1.1.1 g) ∈ indSpace H τ' := by
  intro h g
  have e : f.1.1.1 ((h : G) * g) = τ h (f.1.1.1 g) := f.1.1.2 h g
  beta_reduce
  rw [e, map_smul, hτ, map_mul, Units.val_mul, mul_smul, smul_comm]

theorem mul_mem_smoothPart {H : Subgroup G} {τ τ' : Representation ℂ H W} {ψ : G →* ℂˣ}
    {K : Subgroup G} (hK : IsOpen (K : Set G)) (hψ : ∀ x ∈ K, ψ x = 1)
    (hτ : ∀ (h : H) (w : W), τ' h w = ((ψ h : ℂˣ) : ℂ) • τ h w) (f : cIndSpace H τ) :
    (⟨_, mul_mem_indSpace hτ f⟩ : indSpace H τ') ∈ smoothPart (ind H τ') := by
  obtain ⟨L, hL, hLi⟩ := cInd_right_inv H τ f
  refine GlobalTheory.CompanionTheory.BZMirOnto.isOpen_fixed_of_subgroup (ind H τ') (K ⊓ L) (hK.inter hL) _
    fun x hx => ?_
  apply Subtype.ext
  funext g
  show ((ψ (g * x) : ℂˣ) : ℂ) • f.1.1.1 (g * x) = ((ψ g : ℂˣ) : ℂ) • f.1.1.1 g
  rw [hLi g x hx.2, map_mul, hψ x hx.1, mul_one]

def mulC {H : Subgroup G} {τ τ' : Representation ℂ H W} {ψ : G →* ℂˣ}
    {K : Subgroup G} (hK : IsOpen (K : Set G)) (hψ : ∀ x ∈ K, ψ x = 1)
    (hτ : ∀ (h : H) (w : W), τ' h w = ((ψ h : ℂˣ) : ℂ) • τ h w) (f : cIndSpace H τ) :
    cIndSpace H τ' :=
  ⟨⟨⟨_, mul_mem_indSpace hτ f⟩, mul_mem_smoothPart hK hψ hτ f⟩, by
    obtain ⟨C, hC, hf⟩ := f.2
    refine ⟨C, hC, fun g hg => hf g fun h0 => hg ?_⟩
    show ((ψ g : ℂˣ) : ℂ) • f.1.1.1 g = 0
    rw [show f.1.1.1 g = 0 from h0, smul_zero]⟩

theorem mulC_apply {H : Subgroup G} {τ τ' : Representation ℂ H W} {ψ : G →* ℂˣ}
    {K : Subgroup G} (hK : IsOpen (K : Set G)) (hψ : ∀ x ∈ K, ψ x = 1)
    (hτ : ∀ (h : H) (w : W), τ' h w = ((ψ h : ℂˣ) : ℂ) • τ h w) (f : cIndSpace H τ) (g : G) :
    (mulC hK hψ hτ f).1.1.1 g = ((ψ g : ℂˣ) : ℂ) • f.1.1.1 g := rfl

end SlopeTestRemainingChoices

theorem nonempty_twist_cInd_equiv : ∀ {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) (σ : Representation ℂ H W) (χ : G →* ℂˣ), IsOpen (χ.ker : Set G) →
    Nonempty ((twist (cInd H σ) χ).Equiv (cInd H (twist σ (χ.comp H.subtype)))) := by
  intro G W _ _ _ _ _ H σ χ hχ
  have h1 : ∀ x ∈ χ.ker, χ x = 1 := fun x hx => hx
  have h2 : ∀ x ∈ χ.ker, χ⁻¹ x = 1 := fun x hx => by
    rw [MonoidHom.inv_apply, show χ x = 1 from hx, inv_one]
  have t1 : ∀ (h : H) (w : W), twist σ (χ.comp H.subtype) h w = ((χ h : ℂˣ) : ℂ) • σ h w :=
    fun _ _ => rfl
  have t2 : ∀ (h : H) (w : W), σ h w =
      (((χ⁻¹) h : ℂˣ) : ℂ) • twist σ (χ.comp H.subtype) h w := fun h w => by
    rw [t1, smul_smul, ← Units.val_mul, MonoidHom.inv_apply, inv_mul_cancel, Units.val_one,
      one_smul]
  have cancel : ∀ g, (((χ⁻¹) g : ℂˣ) : ℂ) * ((χ g : ℂˣ) : ℂ) = 1 := fun g => by
    rw [← Units.val_mul, MonoidHom.inv_apply, inv_mul_cancel, Units.val_one]
  have cancel' : ∀ g, ((χ g : ℂˣ) : ℂ) * (((χ⁻¹) g : ℂˣ) : ℂ) = 1 := fun g => by
    rw [mul_comm, cancel]
  let e : cIndSpace H σ ≃ₗ[ℂ] cIndSpace H (twist σ (χ.comp H.subtype)) :=
    { toFun := mulC hχ h1 t1
      map_add' := fun a b => cIndSpace_ext fun g => smul_add _ (a.1.1.1 g) (b.1.1.1 g)
      map_smul' := fun c a => cIndSpace_ext fun g => smul_comm _ c (a.1.1.1 g)
      invFun := mulC hχ h2 t2
      left_inv := fun a => cIndSpace_ext fun g => by
        rw [mulC_apply, mulC_apply, smul_smul, cancel, one_smul]
      right_inv := fun a => cIndSpace_ext fun g => by
        rw [mulC_apply, mulC_apply, smul_smul, cancel', one_smul] }
  refine ⟨Representation.Equiv.mk e fun y => LinearMap.ext fun f => cIndSpace_ext fun g => ?_⟩
  show ((χ g : ℂˣ) : ℂ) • (((χ y : ℂˣ) : ℂ) • f.1.1.1 (g * y)) =
    ((χ (g * y) : ℂˣ) : ℂ) • f.1.1.1 (g * y)
  rw [smul_smul, map_mul, Units.val_mul]

end GlobalTheory.CompanionTheory.TwCInd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactInductionTwistedKernelStatement
section
open GlobalTheory.PRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_induction_twisted_kernel : ∀ {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W] (H U : Subgroup G) [U.Normal], U ≤ H → (∀ O : Set G, O ∈ nhds (1 : G) → ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O) → ∀ (σ : Representation ℂ H W), IsSmooth σ → ∀ f : cIndSpace H σ, (∀ g, f.1.1.1 g ∈ twKer σ (U.subgroupOf H) 1) → f ∈ twKer (cInd H σ) U 1 := by
  first | exact @GlobalTheory.CompanionTheory.PRep.CIndKer.mem_twKer_cInd | exact GlobalTheory.CompanionTheory.PRep.CIndKer.mem_twKer_cInd | (intros; apply GlobalTheory.CompanionTheory.PRep.CIndKer.mem_twKer_cInd <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstTermEqZeroOfFrame
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ConstTermConj

open GlobalTheory.Cusp GlobalTheory.AutomorphicL2Unitary GlobalTheory.MixModel

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] {Γ N₁ N₂ : Subgroup G}
  [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [DiscreteTopology Γ]
  [LocallyCompactSpace N₁] [LocallyCompactSpace N₂]

theorem constTermOn_eq_of_conj {φ : G → ℂ} (hφ : LeftInv Γ φ) {γ : G} (hγ : γ ∈ Γ)
    (hN : ∀ n, n ∈ N₁ ↔ γ * n * γ⁻¹ ∈ N₂) (x : G) :
    constTermOn Γ N₂ φ x = constTermOn Γ N₁ φ (γ⁻¹ * x) := by
  let e : N₁ ≃ₜ* N₂ :=
    { toFun := fun n => ⟨γ * n * γ⁻¹, (hN _).1 n.2⟩
      invFun := fun n => ⟨γ⁻¹ * n * γ, (hN _).2 (by simp [mul_assoc])⟩
      left_inv := fun n => by simp [mul_assoc]
      right_inv := fun n => by simp [mul_assoc]
      map_mul' := fun a b => by simp [mul_assoc]
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let m := e.toHomeomorph.toMeasurableEquiv
  have h := isFundamentalDomain_stdDom (Γ.subgroupOf N₂) (Measure.haar.map e)
  have hp : MeasurePreserving m Measure.haar (Measure.haar.map e) := ⟨m.measurable, rfl⟩
  have h' : IsFundamentalDomain (Γ.subgroupOf N₁) (m ⁻¹' stdDom (Γ.subgroupOf N₂)) Measure.haar :=
    h.preimage_of_equiv hp.quasiMeasurePreserving
      (e := fun δ => ⟨e.symm δ, mul_mem (mul_mem (inv_mem hγ) δ.2) hγ⟩)
      ⟨fun a b hab => Subtype.ext (e.symm.injective (congrArg Subtype.val hab)),
        fun δ => ⟨⟨e δ, mul_mem (mul_mem hγ δ.2) (inv_mem hγ)⟩, Subtype.ext (e.symm_apply_apply _)⟩⟩
      fun δ n => (map_mul e _ _).trans (congrArg (· * e n) (e.apply_symm_apply _))
  rw [constTermOn_eq h hφ, constTermOn_eq h' hφ, ← hp.setIntegral_preimage_emb m.measurableEmbedding,
    measureReal_def, measureReal_def, hp.measure_preimage h.nullMeasurableSet]
  refine congrArg _ (integral_congr_ae (.of_forall fun n => ?_))
  change φ (γ * n * γ⁻¹ * x) = φ (n * (γ⁻¹ * x))
  rw [mul_assoc, mul_assoc, hφ γ hγ]

end Abstract

variable {D : D7} {V : HSp D} {r : ℕ}

theorem rat_mulVec_inc {n m : ℕ} (A : Matrix (Fin n) (Fin m) D.host.E) (x : Fin m → D.host.E) :
    (rat A).mulVec (fun i => incA D (x i)) = fun i => incA D ((A.mulVec x) i) := by
  funext i
  simp [Matrix.mulVec, dotProduct, rat, map_sum]

theorem conj_conditions {C₁ C₂ : Matrix (Fin V.rank) (Fin r) D.host.E}
    (g₀ gi : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (h1 : g₀ * gi = 1)
    (hC : g₀ * C₁ = C₂) (hC' : gi * C₂ = C₁) (hH : C₂ᴴ * V.gram * g₀ = C₁ᴴ * V.gram)
    (m : Mx D V.rank V.rank) (a1 : m ⬝ rat C₁ = 0) (a2 : rat (C₁ᴴ * V.gram) ⬝ m = 0)
    (a3 : ∀ x : Fin V.rank → D.host.E, (C₁ᴴ * V.gram).mulVec x = 0 →
      ∃ a : Fin r → AE D, m.mulVec (fun i => incA D (x i)) = (rat C₁).mulVec a) :
    (rat g₀ ⬝ m ⬝ rat gi) ⬝ rat C₂ = 0 ∧ rat (C₂ᴴ * V.gram) ⬝ (rat g₀ ⬝ m ⬝ rat gi) = 0 ∧
      ∀ x : Fin V.rank → D.host.E, (C₂ᴴ * V.gram).mulVec x = 0 →
        ∃ a : Fin r → AE D, (rat g₀ ⬝ m ⬝ rat gi).mulVec (fun i => incA D (x i)) = (rat C₂).mulVec a := by
  refine ⟨?_, ?_, fun x hx => ?_⟩
  · rw [Matrix.mul_assoc, ← rat_mul, hC', Matrix.mul_assoc, a1, Matrix.mul_zero]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← rat_mul, hH, a2, Matrix.zero_mul]
  · have hy : (C₁ᴴ * V.gram).mulVec (gi.mulVec x) = 0 := by
      rw [← hH, Matrix.mulVec_mulVec, Matrix.mul_assoc (C₂ᴴ * V.gram) g₀ gi, h1, Matrix.mul_one, hx]
    obtain ⟨a, ha⟩ := a3 _ hy
    refine ⟨a, ?_⟩
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, rat_mulVec_inc, ha, Matrix.mulVec_mulVec, ← rat_mul, hC]

theorem conj_mem_NI {C₁ C₂ : Matrix (Fin V.rank) (Fin r) D.host.E} (γ : GA D V)
    (g₀ gi : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (h1 : g₀ * gi = 1) (h2 : gi * g₀ = 1)
    (hu : g₀ᴴ * V.gram * g₀ = V.gram) (hm : mt V γ = rat g₀) (hmi : mt V γ⁻¹ = rat gi)
    (hC : g₀ * C₁ = C₂) {n : GA D V} (hn : n ∈ NI V C₁) : γ * n * γ⁻¹ ∈ NI V C₂ := by
  have hC' : gi * C₂ = C₁ := by rw [← hC, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hH : C₂ᴴ * V.gram * g₀ = C₁ᴴ * V.gram := by
    rw [← hC, Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc g₀ᴴ, hu]
  have ii' : rat g₀ ⬝ rat gi = (1 : Mx D V.rank V.rank) := by rw [← rat_mul, h1, rat_one]
  have hle : NI V C₁ ≤ (NI V C₂).comap (MulAut.conj γ).toMonoidHom := by
    refine (Subgroup.closure_le _).2 fun g hg => Subgroup.subset_closure ?_
    obtain ⟨a1, a2, a3⟩ := hg
    have em : (matHom V ((MulAut.conj γ).toMonoidHom g)).1 - 1 = rat g₀ ⬝ ((matHom V g).1 - 1) ⬝ rat gi := by
      have e : (matHom V ((MulAut.conj γ).toMonoidHom g)).1 = mt V γ ⬝ mt V g ⬝ mt V γ⁻¹ := rfl
      rw [e, hm, hmi, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ii']
      rfl
    have := conj_conditions g₀ gi h1 hC hC' hH _ a1 a2 a3
    rw [← em] at this
    exact this
  exact hle hn

theorem rank_eq_of_isIsoFrame {C : Matrix (Fin V.rank) (Fin r) D.host.E} (h : IsIsoFrame V C) : C.rank = r := by
  have := LinearIndependent.rank_matrix (M := Cᵀ) h.2.1
  simpa [Matrix.rank_transpose] using this

theorem constTerm_eq_zero_of_frame : ∀ (D : D7) (V : HSp D) (r : ℕ) (C₁ C₂ : Matrix (Fin V.rank) (Fin r) D.host.E)
    (h₁ : IsIsoFrame V C₁) (h₂ : IsIsoFrame V C₂) (φ : GA D V → ℂ), (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) →
    GlobalTheory.Cusp.constTerm (GlobalTheory.Cusp.frameFlag h₁) φ = 0 → GlobalTheory.Cusp.constTerm (GlobalTheory.Cusp.frameFlag h₂) φ = 0 := by
  intro D V r C₁ C₂ h₁ h₂ φ hφ h0
  have hθ : (1 / 2 : D.host.E) + star (1 / 2 : D.host.E) = 1 := by
    have e : star (1 / 2 : D.host.E) = 1 / 2 := by simp [star_div₀]
    rw [e, add_halves]
  have e₁ : C₁ᴴ * V.gram * C₁ = 0 := h₁.2.2
  have e₂ : C₂ᴴ * V.gram * C₂ = 0 := h₂.2.2
  obtain ⟨g₀, hu, hC⟩ := GlobalTheory.WittTrace.exists_isometry_mul_eq D.host.E (1 / 2) hθ V.rank r V.gram C₁ C₂
    (gram_conjTranspose V) (gram_isUnit_det V) (rank_eq_of_isIsoFrame h₁) (rank_eq_of_isIsoFrame h₂) (e₁.trans e₂.symm)
  obtain ⟨gi, hgi⟩ : ∃ gi, gi = V.gram⁻¹ * (g₀ᴴ * V.gram) := ⟨_, rfl⟩
  have h2 : gi * g₀ = 1 := by
    rw [hgi, Matrix.mul_assoc, hu, Matrix.nonsing_inv_mul _ (gram_isUnit_det V)]
  have h1 : g₀ * gi = 1 := mul_eq_one_comm.1 h2
  have hC' : gi * C₂ = C₁ := by rw [← hC, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hu' : giᴴ * V.gram * gi = V.gram := by
    calc giᴴ * V.gram * gi = giᴴ * (g₀ᴴ * V.gram * g₀) * gi := by rw [hu]
      _ = (g₀ * gi)ᴴ * V.gram * (g₀ * gi) := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = V.gram := by rw [h1]; simp
  have hh : adj (rat g₀) * (gA V * rat g₀) = gA V := by
    rw [← rat_conjTranspose, gA, ← rat_mul, ← rat_mul, ← Matrix.mul_assoc, hu]
  obtain ⟨γ, hm⟩ : ∃ γ : GA D V, mt V γ = rat g₀ := ⟨ofMat V (rat g₀) hh, mt_ofMat V _ hh⟩
  have hmi : mt V γ⁻¹ = rat gi := by
    have e := mt_mul_inv V γ
    rw [hm] at e
    calc mt V γ⁻¹ = (rat gi * rat g₀) * mt V γ⁻¹ := by rw [← rat_mul, h2, rat_one, Matrix.one_mul]
      _ = rat gi := by rw [Matrix.mul_assoc, e, Matrix.mul_one]
  have hγ : γ ∈ GQ V := (mem_GQ_iff V γ).2 (hm ▸ rat_mem g₀)
  have hN : ∀ n, n ∈ NA (frameFlag h₁) ↔ γ * n * γ⁻¹ ∈ NA (frameFlag h₂) := fun n => by
    rw [NA_frameFlag, NA_frameFlag]
    refine ⟨conj_mem_NI γ g₀ gi h1 h2 hu hm hmi hC, fun h => ?_⟩
    have := conj_mem_NI γ⁻¹ gi g₀ h2 h1 hu' hmi (by simpa using hm) hC' h
    simpa [mul_assoc] using this
  funext x
  exact (constTermOn_eq_of_conj hφ hγ hN x).trans (congrFun h0 _)

end GlobalTheory.CompanionTheory.ConstTermConj

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAutomorphicCriterionStatement
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_automorphic_criterion : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ), ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → (∀ φ F : Sm E a, (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} → (∀ g, F.1 g = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) → ∀ (X : Lie E a) (g : GA E a), (lie E a X F).1 g = ∫ x in 𝓕, (lie E a X φ).1 (unip x * g) ∂μ) → ∀ φ F : Sm E a, (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} → (∀ g, F.1 g = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) → ∀ z ∈ Zalg E a, ∀ g, (z F).1 g = ∫ x in 𝓕, (z φ).1 (unip x * g) ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.Central.ct_Zalg | exact GlobalTheory.CompanionTheory.CTFin.Central.ct_Zalg | (intros; apply GlobalTheory.CompanionTheory.CTFin.Central.ct_Zalg <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContDiffOnInvReal
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ENNReal
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveCp GlobalTheory.CompanionTheory.WaveCp.Rep
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveCp.Rep.Frame

variable {n : ℕ}

theorem contDiffOn_inv_real : ContDiffOn ℝ ∞ (fun x : Mat n => x⁻¹) (GLs n) :=
  ReciprocityTheory.ChartRestriction.DS.Lap.LemK.contDiffOn_inv_det_ne_zero.restrict_scalars ℝ

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

end GlobalTheory.CompanionTheory.WaveCp.Rep.Frame

namespace GlobalTheory.CompanionTheory.WaveCp.Rep

end GlobalTheory.CompanionTheory.WaveCp.Rep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousLeviUnipotentProj
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.Cont

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_colMat_entry (n : ℕ) (a b : Fin (n + 1)) :
    Continuous fun y : Fin n → k => colMat k n y a b := by
  unfold colMat
  split_ifs
  · induction a using Fin.lastCases with
    | last => simp only [Fin.lastCases_last]; exact continuous_const
    | cast i => simp only [Fin.lastCases_castSucc]; exact continuous_apply i
  · exact continuous_const

theorem continuous_uM_val (n : ℕ) : Continuous fun y : Fin n → k =>
    (((uM k n y : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
  have h : (fun y : Fin n → k =>
      (((uM k n y : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) =
      fun y => 1 + colMat k n y := by
    funext y
    rfl
  rw [h]
  refine continuous_const.add (continuous_matrix fun a b => ?_)
  exact continuous_colMat_entry k n a b

theorem uM_inv (n : ℕ) (y : Fin n → k) : (uM k n y)⁻¹ = uM k n (-y) := by
  have h : uM k n (-y) * uM k n y = 1 := by
    rw [← uM_add, neg_add_cancel, uM_zero]
  exact (eq_inv_of_mul_eq_one_left h).symm

theorem continuous_uM (n : ℕ) : Continuous (uM k n) := by
  apply continuous_induced_rng.2
  refine Units.continuous_iff.2 ⟨continuous_uM_val k n, ?_⟩
  have h : ∀ y : Fin n → k, ((uM k n y : GL (Fin (n + 1)) k))⁻¹ =
      (uM k n (-y) : GL (Fin (n + 1)) k) := by
    intro y
    rw [← uM_inv k n y, Subgroup.coe_inv]
  simp only [Function.comp_apply, h]
  exact (continuous_uM_val k n).comp continuous_neg

end GlobalTheory.CompanionTheory.BZPsiPG.Cont

namespace GlobalTheory.CompanionTheory.BZPsiPG

theorem continuous_levi_uM_mirProj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), Continuous (levi k n) ∧ Continuous (uM k n) ∧ Continuous (mirabolicProjection k n) := by
  intro k _ _ _ _ n
  exact ⟨GlobalTheory.CompanionTheory.BZMirFun.continuous_levi k n, Cont.continuous_uM k n,
    GlobalTheory.CompanionTheory.BZMirFun.continuous_mirProj k n⟩

end GlobalTheory.CompanionTheory.BZPsiPG
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMirabolicEmbedding
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi

theorem continuous_glEmbMat_comp {k X : Type} [Field k] [TopologicalSpace k] [TopologicalSpace X] (m : ℕ)
    {f : X → Matrix (Fin m) (Fin m) k} (hf : Continuous f) :
    Continuous fun x => glEmbMat k m (f x) := by
  refine continuous_matrix fun i j => ?_
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_last, Fin.lastCases_castSucc] <;>
    first
    | exact continuous_const
    | exact hf.matrix_elem _ _

theorem continuous_iotaM : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), Continuous (embedding₂ k n) := by
  intro k _ _ _ _ n
  have hemb : Continuous (GlobalTheory.BZMir.glEmb k (n + 1)) :=
    Continuous.units_map _ (GlobalTheory.CompanionTheory.LeibPhi.continuous_glEmbMat_comp (n + 1) continuous_id)
  exact continuous_induced_rng.2 (hemb.comp continuous_subtype_val)

end GlobalTheory.CompanionTheory.LeibPhi

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousParabolicProj
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibPhi

theorem continuous_gpProj_phi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m j : ℕ), Continuous (gpProj k m j) :=
  GlobalTheory.CompanionTheory.BZMir.continuous_gpProj

end GlobalTheory.CompanionTheory.LeibPhi
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousRowM
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir

namespace GlobalTheory.CompanionTheory.BZOnto

variable {k : Type} [Field k]

def rowM {n : ℕ} (g : Mir k (n + 1)) : Fin (n + 1) → k :=
  ((mirabolicProjection k (n + 1) g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n)

def perp (ψ : AddChar k Circle) {m : ℕ} (Λ : AddSubgroup (Fin m → k)) : AddSubgroup (Fin m → k) where
  carrier := {b | ∀ l ∈ Λ, ψ (b ⬝ᵥ l) = 1}
  add_mem' {a b} ha hb l hl := by rw [add_dotProduct, AddChar.map_add_eq_mul, ha l hl, hb l hl, one_mul]
  zero_mem' l _ := by simp
  neg_mem' {a} ha l hl := by rw [neg_dotProduct, AddChar.map_neg_eq_inv, ha l hl, inv_one]

open GlobalTheory.BZMir.Fun GlobalTheory.CompanionTheory.BZBeta
open scoped Topology

section Row

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Row

end GlobalTheory.CompanionTheory.BZOnto

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSupportRealisedByProduct
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenSupp

theorem hasSupport_std : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (s : Multiset (IrrGL k)), HasSupport π s → ∃ (h : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), Finset.univ.val.map x = s ∧ (∀ a, (x a).IsCusp) ∧ IsSubquotient π (prodIrr x hd) := by
  intro k _ _ _ _ N V _ _ π s hπ
  obtain ⟨h, x, hs, -, hc, e, hsq⟩ := hπ
  have hd : ∑ a, (x a).1 = N := by
    have := Fintype.card_congr e
    simpa [Fintype.card_sigma] using this
  obtain ⟨φ⟩ := GlobalTheory.T.multiProd_equiv_standard_blocks k (fun a => (x a).1) hd e _ (fun a => (x a).rep)
  exact ⟨h, x, hd, hs, fun a => ⟨(hc a).1, (hc a).2.2⟩, hsq.trans (GlobalTheory.JacStages.isSubquotient_of_equiv φ)⟩

end GlobalTheory.CompanionTheory.GenSupp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DecompositionGroupLocalGaloisStatement
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decomposition_group_local_galois : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) [IsSepClosure (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F))], IsPlaceOver A v → ∀ (ι : Ω →ₐ[F] AlgebraicClosure (v.adicCompletion F)) (σ : G F Ω) (g : Gal(AlgebraicClosure (v.adicCompletion F)/v.adicCompletion F)), σ ∈ Dec (F := F) A → (∀ x, ι (σ x) = g (ι x)) → unramifiedDegree (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F)) g = Multiplicative.ofAdd 1 → IsFrob (F := F) A (normV v) σ := by
  first | exact @GlobalTheory.CompanionTheory.Dict.isFrob_of_unramifiedDegree_eq_one | exact GlobalTheory.CompanionTheory.Dict.isFrob_of_unramifiedDegree_eq_one | (intros; apply GlobalTheory.CompanionTheory.Dict.isFrob_of_unramifiedDegree_eq_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativePreservesSubquotient
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

namespace GlobalTheory.CompanionTheory.BZMirSub

section Tw

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

end Tw

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSmooth_resM {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (n + 1)) k) V) (h : IsSmooth π) : IsSmooth (resM k π).ρ := fun v =>
  (h v).preimage continuous_subtype_val

end GlobalTheory.CompanionTheory.BZMirSub
end

