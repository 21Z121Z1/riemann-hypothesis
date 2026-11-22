import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXLocSB
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0004
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXSplSPf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.Bundle0007

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXIntWittSt
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcX.IntWittPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain Filter Matrix
open scoped TensorProduct

def AlgWitt : Prop :=
  ∀ (S : Type) [CommRing S] (s : S →+* S) (O : Subring S), (∀ z, s (s z) = z) → (∀ z ∈ O, s z ∈ O) →
    ∀ (n : ℕ) (J J' : Matrix (Fin n) (Fin n) S), Formalism.UG.IsHerm s J → J' * J = 1 →
    (∀ i j, J i j ∈ O) → (∀ i j, J' i j ∈ O) →
    ∀ (a : ℕ) (β β' : Fin a → S), (∀ i, β i ∈ O) → (∀ i, β' i ∈ O) → (∀ i, β i * β' i = 1) →
    (∀ i, ∀ t ∈ O, ∃ lam ∈ O, lam * s lam = 1 ∧ ∃ c' ∈ O, (β i - s lam * t) * c' = 1) →
    ∀ (x y : Fin a → Fin n → S), (∀ i k, x i k ∈ O) → (∀ i k, y i k ∈ O) →
    (∀ i j, Formalism.UG.hform s J (x i) (x j) = if i = j then β i else 0) →
    (∀ i j, Formalism.UG.hform s J (y i) (y j) = if i = j then β i else 0) →
    ∃ g : GL (Fin n) S, g ∈ Formalism.UG.UJ s J ∧ (∀ i j, (g : Matrix (Fin n) (Fin n) S) i j ∈ O) ∧
      (∀ i j, ((g⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) i j ∈ O) ∧
      ∀ i, (g : Matrix (Fin n) (Fin n) S) *ᵥ y i = x i

def HermDiag : Prop :=
  ∀ (K : Type) [Field K] (σ : K →+* K), (∀ z, σ (σ z) = z) → (2 : K) ≠ 0 →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) K), Formalism.UG.IsHerm σ J →
    ∀ (a : ℕ) (X0 : Fin a → Fin n → K),
    (Matrix.of fun i j => Formalism.UG.hform σ J (X0 i) (X0 j)).det ≠ 0 →
    ∃ P Q : Matrix (Fin a) (Fin a) K, Q * P = 1 ∧
      (∀ i j, i ≠ j → Formalism.UG.hform σ J (∑ l, P i l • X0 l) (∑ l, P j l • X0 l) = 0) ∧
      ∀ i, Formalism.UG.hform σ J (∑ l, P i l • X0 l) (∑ l, P i l • X0 l) ≠ 0

def LamAE : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ δ : E, σ δ = δ → δ ≠ 0 →
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ t ∈ OEv (E := E) v,
      ∃ lam ∈ OEv (E := E) v, lam * sigR (Fv F v) σ lam = 1 ∧
        ∃ c' ∈ OEv (E := E) v, (inclR (Fv F v) δ - sigR (Fv F v) σ lam * t) * c' = 1

end Formalism.L2.SG.Pf.NcX.IntWittPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXWittLoc
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcX.WittLocPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain
open scoped TensorProduct

theorem local_witt_theorem : Formalism.L2.SG.Pf.NcX.LocSBPf.WittLocT := by
  intro F E _ _ _ _ _ σ n J a X0 hCM hJ hdet v X hX
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  set Y := ratTup (F := F) (Fv F v) X0 with hYdef
  have hYG : gramR (Fv F v) σ J Y = (gramE σ J X0).map (inclR (F := F) (Fv F v)) :=
    PI.VolStabW.LocPosW.gramR_ratTup (Fv F v) σ J X0
  have hunit : IsUnit ((gramE σ J X0).map (inclR (F := F) (Fv F v))).det := by
    have e : ((gramE σ J X0).map (inclR (F := F) (Fv F v))).det = inclR (F := F) (Fv F v) (gramE σ J X0).det :=
      (RingHom.map_det (inclR (F := F) (Fv F v)) (gramE σ J X0)).symm
    rw [e]
    exact (Ne.isUnit hdet).map (inclR (F := F) (Fv F v))
  have hYind : LinearIndependent (Fv F v ⊗[F] E) Y :=
    PI.VolStabW.linIndep_of_isUnit_det (Fv F v) σ J Y (hYG ▸ hunit)
  have hXind : LinearIndependent (Fv F v ⊗[F] E) X :=
    PI.VolStabW.linIndep_of_isUnit_det (Fv F v) σ J X (hX ▸ hunit)
  by_cases hK : IsField (Fv F v ⊗[F] E)
  · letI : Field (Fv F v ⊗[F] E) := hK.toField
    have hσ : ∀ x, σ (σ x) = x := PI.VolStabW.sigma_invol_cm σ hCM
    have hinv : ∀ x, sigR (Fv F v) σ (sigR (Fv F v) σ x) = x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul r t => simp [sigR, hσ]
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    letI : StarRing (Fv F v ⊗[F] E) := PI.VolStabW.starOfInv (sigR (Fv F v) σ) hinv
    haveI : CharZero (Fv F v ⊗[F] E) :=
      charZero_of_injective_algebraMap (algebraMap F (Fv F v ⊗[F] E)).injective
    have hs : starRingEnd (Fv F v ⊗[F] E) = sigR (Fv F v) σ := RingHom.ext fun _ => rfl
    have hJ' : ∀ i j, starRingEnd (Fv F v ⊗[F] E) (JR (F := F) (Fv F v) J j i) = JR (F := F) (Fv F v) J i j := by
      intro i j
      rw [hs]
      simp only [JR, Matrix.map_apply]
      rw [(fun x => by simp [sigR, inclR] : ∀ x : E, sigR (Fv F v) σ (inclR (F := F) (Fv F v) x) =
        inclR (F := F) (Fv F v) (σ x)), hJ.1 i j]
    have hdetJ : (JR (F := F) (Fv F v) J).det ≠ 0 := by
      have e : (JR (F := F) (Fv F v) J).det = inclR (F := F) (Fv F v) J.det := by
        rw [RingHom.map_det]
        rfl
      rw [e]
      intro h
      apply hJ.2
      exact (inclR (F := F) (Fv F v)).injective (h.trans (map_zero _).symm)
    have hGg : ∀ i j, Formalism.UG.hform (starRingEnd (Fv F v ⊗[F] E)) (JR (F := F) (Fv F v) J) (X i) (X j) =
        Formalism.UG.hform (starRingEnd (Fv F v ⊗[F] E)) (JR (F := F) (Fv F v) J) (Y i) (Y j) := by
      intro i j
      rw [hs]
      exact congrFun (congrFun (hX.trans hYG.symm) i) j
    obtain ⟨g, hg, hgX⟩ := PI.VolStabW.witt_tuple (JR (F := F) (Fv F v) J) hJ' hdetJ Y X hYind hXind hGg
    rw [hs] at hg
    exact ⟨⟨g, hg⟩, funext fun i => hgX i⟩
  · obtain ⟨π₁, π₂, h1, h2, -, h4, h5⟩ := Formalism.L2.SG.Pf.NcX.LT.splitStr σ v hCM hK
    exact Formalism.L2.SG.Pf.NcX.LT.WSp.witt_split σ J hJ v π₁ π₂ h1 h2 h4 h5 Y X hYind hXind (hYG.trans hX.symm)

end Formalism.L2.SG.Pf.NcX.WittLocPf
end
end

