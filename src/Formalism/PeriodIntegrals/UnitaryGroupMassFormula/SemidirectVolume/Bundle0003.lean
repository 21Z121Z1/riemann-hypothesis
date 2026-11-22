import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ClosedStep
import Formalism.PeriodIntegrals.Bundle0025

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.SemiDefs
section
noncomputable section

namespace PI.VolSemiDirect.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

def NormStep : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (r : ℕ) (P : Frame E M r) (T : F), 2 * r + 3 ≤ M → P.IsStd σ J T →
    ∀ h ∈ Hsub (AF F) σ J P, ∀ n ∈ FrameUnipotentSubgroup (AF F) σ J P, h * n * h⁻¹ ∈ FrameUnipotentSubgroup (AF F) σ J P

def ProjStep : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (r : ℕ) (P : Frame E M r) (T : F), 2 * r + 3 ≤ M → P.IsStd σ J T →
    ∃ π : S0 (AF F) σ J P →* Hsub (AF F) σ J P, Continuous π ∧
      (∀ s : S0 (AF F) σ J P, (s : HA (AF F) σ J) ∈ Hsub (AF F) σ J P →
        ((π s : Hsub (AF F) σ J P) : HA (AF F) σ J) = s) ∧
      (∀ s : S0 (AF F) σ J P, (s : HA (AF F) σ J) ∈ FrameUnipotentSubgroup (AF F) σ J P → π s = 1) ∧
      (∀ s : S0 (AF F) σ J P, (s : HA (AF F) σ J) *
        ((π s : Hsub (AF F) σ J P) : HA (AF F) σ J)⁻¹ ∈ FrameUnipotentSubgroup (AF F) σ J P) ∧
      (∀ s : S0 (AF F) σ J P, (s : HA (AF F) σ J) ∈ HFinIn (AF F) σ J →
        ((π s : Hsub (AF F) σ J P) : HA (AF F) σ J) ∈ HFinIn (AF F) σ J)

theorem heisenberg_le_stabilizer {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {r : ℕ}
    (P : Frame E M r) : Hsub R σ J P ≤ S0 R σ J P := by
  intro g hg
  rw [Hsub, mem_stabT] at hg
  rw [S0, mem_stabT]
  intro b
  have := hg (Fin.castAdd r b)
  simpa [tupH, Fin.append_left] using this

theorem semiStep_of (hL : LcscHA) (hN : NormStep) (hP : ProjStep) : SemiStep := by
  intro F E _ _ _ _ _ σ hCM M J hJ r P T hr hS
  obtain ⟨_, _, _, _⟩ := hL F E σ hCM M J hJ
  obtain ⟨π, hπc, hπH, hπN, hπS, hπR⟩ := hP F E σ hCM M J hJ r P T hr hS
  have hHS := heisenberg_le_stabilizer (AF F) σ J P
  have hNS : FrameUnipotentSubgroup (AF F) σ J P ≤ S0 (AF F) σ J P := inf_le_right
  have hπh : ∀ h : Hsub (AF F) σ J P, π ⟨h, hHS h.2⟩ = h := fun h => Subtype.ext (hπH _ h.2)
  have hπn : ∀ n : FrameUnipotentSubgroup (AF F) σ J P, π ⟨n, hNS n.2⟩ = 1 := fun n => hπN _ n.2
  have hπnh : ∀ (n : FrameUnipotentSubgroup (AF F) σ J P) (h : Hsub (AF F) σ J P),
      π ⟨(n : HA (AF F) σ J) * h, (S0 (AF F) σ J P).mul_mem (hNS n.2) (hHS h.2)⟩ = h := by
    intro n h
    have : (⟨(n : HA (AF F) σ J) * h, (S0 (AF F) σ J P).mul_mem (hNS n.2) (hHS h.2)⟩ :
        S0 (AF F) σ J P) = ⟨n, hNS n.2⟩ * ⟨h, hHS h.2⟩ := rfl
    rw [this, map_mul, hπn, hπh, one_mul]
  refine ⟨⟨fun h hh n hn => hN F E σ hCM M J hJ r P T hr hS h hh n hn, ?_⟩, ?_⟩
  · refine ⟨{
      toFun := fun p => ⟨(p.1 : HA (AF F) σ J) * p.2,
        (S0 (AF F) σ J P).mul_mem (hNS p.1.2) (hHS p.2.2)⟩
      invFun := fun s => (⟨(s : HA (AF F) σ J) * ((π s : Hsub (AF F) σ J P) : HA (AF F) σ J)⁻¹,
        hπS s⟩, π s)
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }, fun p => rfl⟩
    · rintro ⟨n, h⟩
      simp only [hπnh]
      refine Prod.ext (Subtype.ext ?_) rfl
      show (n : HA (AF F) σ J) * h * (h : HA (AF F) σ J)⁻¹ = n
      group
    · intro s
      apply Subtype.ext
      show (s : HA (AF F) σ J) * ((π s : Hsub (AF F) σ J P) : HA (AF F) σ J)⁻¹ *
        ((π s : Hsub (AF F) σ J P) : HA (AF F) σ J) = s
      group
    · exact ((continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd)).subtype_mk _
    · exact ((continuous_subtype_val.mul
        (continuous_subtype_val.comp hπc).inv).subtype_mk _).prodMk hπc
  · intro n hn h hh hmem
    have hs : (n : HA (AF F) σ J) * h ∈ S0 (AF F) σ J P :=
      (S0 (AF F) σ J P).mul_mem (hNS hn) (hHS hh)
    have := hπR ⟨n * h, hs⟩ hmem
    have e : π ⟨n * h, hs⟩ = ⟨h, hh⟩ := hπnh ⟨n, hn⟩ ⟨h, hh⟩
    rw [e] at this
    exact this

end PI.VolSemiDirect.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.TensTopOf
section
noncomputable section

namespace PI.VolSemiDirect.W.Lc

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

def AFTop : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    LocallyCompactSpace (AF F) ∧ SecondCountableTopology (AF F) ∧ T2Space (AF F)

theorem finite_nf (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] : Module.Finite F E :=
  Module.Finite.of_restrictScalars_finite ℚ F E

def sigL {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) : R ⊗[F] E →ₗ[R] R ⊗[F] E where
  toFun := sigR R σ
  map_add' := fun x y => map_add _ x y
  map_smul' := by
    intro r x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [sigR, TensorProduct.smul_tmul']
    | add x y hx hy => simp_all [smul_add]

theorem tensTop_of (h : AFTop) : TensTop := by
  intro F E _ _ _ _ _
  obtain ⟨hlc, hsc, ht2⟩ := h F
  have := finite_nf F E
  let R := AF F
  have : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  let b := Module.finBasis F E
  let bR := Algebra.TensorProduct.basis R b
  let e : (R ⊗[F] E) ≃ₗ[R] (Fin (Module.finrank F E) → R) := bR.equivFun
  have htr : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R (R ⊗[F] E)
  have c1 : Continuous e.toLinearMap := IsModuleTopology.continuous_of_linearMap (R := R) _
  have c2 : Continuous e.symm.toLinearMap := IsModuleTopology.continuous_of_linearMap (R := R) _
  let hm : (R ⊗[F] E) ≃ₜ (Fin (Module.finrank F E) → R) :=
    { toEquiv := e.toEquiv, continuous_toFun := by simpa using c1, continuous_invFun := by simpa using c2 }
  refine ⟨htr, ?_, ?_, ?_⟩
  · exact hm.isEmbedding.t2Space
  · exact hm.isClosedEmbedding.locallyCompactSpace
  · exact hm.isEmbedding.secondCountableTopology

end PI.VolSemiDirect.W.Lc
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.VolumeUnipotentOfSteps
section
noncomputable section

namespace PI.VolSemiDirect.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory

theorem volume_unipotent_of_steps (hSub : SubLCSC) (hFD : FDExG) (hPr : ProdHaarG) (hV : VolG)
    (hLC : LcscHA) (hD : DiscHA) (hCl : ClosedStep) (hSe : SemiStep) (hCo : ConjStep) :
    PI.VolSemiDirect.VolumeUnipotentAllCM := by
  intro F E _ _ _ _ _ σ hCM M J hJ hJ' r P T hr hP μN hμN μH hμH
  have : BorelSpace (HA (AF F) σ J) := ⟨rfl⟩
  have hX := hLC F E σ hCM M J hJ
  obtain ⟨hcnt, hdisc⟩ := hD F E σ hCM M J hJ
  obtain ⟨cS, cN, cH⟩ := hCl F E σ hCM M J hJ r P T hr hP
  obtain ⟨hsemi, hrat⟩ := hSe F E σ hCM M J hJ r P T hr hP
  have hconj := hCo F E σ hCM M J hJ r P T hr hP
  obtain ⟨lS, dS⟩ := hSub (HA (AF F) σ J) (HFinIn (AF F) σ J) _ hX cS hcnt hdisc
  obtain ⟨lN, dN⟩ := hSub (HA (AF F) σ J) (HFinIn (AF F) σ J) _ hX cN hcnt hdisc
  obtain ⟨lH, dH⟩ := hSub (HA (AF F) σ J) (HFinIn (AF F) σ J) _ hX cH hcnt hdisc
  obtain ⟨μ0, hμ0, hp0⟩ := hPr (HA (AF F) σ J) _ _ _ hsemi lS lN lH hconj μN hμN μH hμH
  obtain ⟨𝓕0, -, h𝓕0⟩ := hFD (HA (AF F) σ J) (HFinIn (AF F) σ J) _ lS dS
  obtain ⟨𝓕N0, -, h𝓕N0⟩ := hFD (HA (AF F) σ J) (HFinIn (AF F) σ J) _ lN dN
  obtain ⟨𝓕H0, -, h𝓕H0⟩ := hFD (HA (AF F) σ J) (HFinIn (AF F) σ J) _ lH dH
  unfold AllSome
  refine ⟨⟨μ0, hμ0, hp0⟩, ?_⟩
  rintro μS ⟨hμS, hpS⟩
  refine ⟨⟨𝓕0, h𝓕0 μS⟩, fun 𝓕 h𝓕 => ⟨⟨𝓕N0, h𝓕N0 μN⟩, fun 𝓕N h𝓕N =>
    ⟨⟨𝓕H0, h𝓕H0 μH⟩, fun 𝓕H h𝓕H => ?_⟩⟩⟩
  exact hV (HA (AF F) σ J) _ _ _ _ hsemi hrat lS lN lH dS dN dH μS μN μH hμS hμN hμH hpS 𝓕 𝓕N 𝓕H h𝓕 h𝓕N h𝓕H

end PI.VolSemiDirect.W
end
end

