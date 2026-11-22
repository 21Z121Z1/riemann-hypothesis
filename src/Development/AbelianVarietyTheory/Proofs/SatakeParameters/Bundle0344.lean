import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0031
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0002
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
import Mathlib
import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.PosBridge
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0007
import Formalism.LocalToGlobal.HermitianForms.Bundle0002
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.CardFilterValLt
import Formalism.SharpRestriction.GrowthBounds.LatticeSystems
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelMoveDegree
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0341
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsOrthCoToLEOfCTMulSelf
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV

open Matrix

theorem isOrthCo_toLE_of_cT_mul_self {E : Type} [Field E] [NumberField E] {N : ℕ} (σ : E →+* E)
    (J : Matrix (Fin N) (Fin N) E) (co : GL (Fin N) E) (h : cT σ co.1 * co.1 = J) :
    IsOrthCo σ J (toLE co) := by
  intro x y
  subst h
  simp only [toLE_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply,
    map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, j]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

end GlobalTheory.TwV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSDLatLatK
section
noncomputable section

namespace GlobalTheory.SDCompan

section Gen

open Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.L2.GlobalTheoryTheory.Comp Formalism.L2.KerInert
open scoped TensorProduct

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {N : ℕ}

theorem latAd_eq (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E)) :
    Formalism.L2.PairingIndexBounds.F.latAd y Lb = Formalism.UG.CS.globLat y Lb :=
  Submodule.span_eq (Formalism.UG.CS.globLat y Lb)

theorem compan_eq (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (Λ : Submodule (𝓞 E) (Fin N → E)) :
    Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a Λ = Λ ⊔ Ideal.span {a} • dl sp.cm.sig J Λ := rfl

theorem compan_zero (J : Matrix (Fin N) (Fin N) E) (Λ : Submodule (𝓞 E) (Fin N → E)) :
    Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J 0 Λ = Λ := by
  rw [compan_eq, Ideal.span_singleton_eq_bot.2 rfl, Submodule.bot_smul, sup_bot_eq]

theorem mem_toStd (J : Matrix (Fin N) (Fin N) E) (M : Submodule (𝓞 E) (Fin N → E)) (y : Fin N → E) :
    y ∈ Formalism.L2.PairingIndexBounds.F.toStd (sp.cm.sig : E →+* E) J M ↔
      (Formalism.L2.PairingIndexBounds.F.stdCo (sp.cm.sig : E →+* E) J).symm y ∈ M := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    have : (Formalism.L2.PairingIndexBounds.F.stdCo (sp.cm.sig : E →+* E) J).symm (Formalism.L2.PairingIndexBounds.F.stdCo (sp.cm.sig : E →+* E) J x) = x :=
      LinearEquiv.symm_apply_apply _ x
    simpa using (this ▸ hx)
  · intro h
    exact ⟨_, h, by simp⟩

theorem isSD_toStd (J : Matrix (Fin N) (Fin N) E)
    (hco : ∃ co, Formalism.L2.PairingIndexBounds.F.IsOrthCo (sp.cm.sig : E →+* E) J co)
    {M : Submodule (𝓞 E) (Fin N → E)} (hM : IsLat M) (hsd : dl sp.cm.sig J M = M) :
    IsSDLat E N (Formalism.L2.PairingIndexBounds.F.toStd (sp.cm.sig : E →+* E) J M) := by
  have hc : Formalism.L2.PairingIndexBounds.F.IsOrthCo (sp.cm.sig : E →+* E) J (Formalism.L2.PairingIndexBounds.F.stdCo (sp.cm.sig : E →+* E) J) :=
    Classical.epsilon_spec hco
  set co := Formalism.L2.PairingIndexBounds.F.stdCo (sp.cm.sig : E →+* E) J with hco_def
  have key : ∀ x y, stdH E N (co x) (co y) = hform (sp.cm.sig : E →+* E) J x y := fun x y => hc x y
  refine ⟨(Module.Finite.iff_fg.1 hM.1).map _, ?_, fun y => ?_⟩
  · rw [Formalism.L2.PairingIndexBounds.F.toStd, Submodule.map_coe, LinearMap.coe_restrictScalars, ← hco_def, eq_top_iff]
    rintro v -
    have hv : co.symm v ∈ Submodule.span E (M : Set (Fin N → E)) := by rw [hM.2]; trivial
    have h1 := Submodule.apply_mem_span_image_of_mem_span (co : (Fin N → E) →ₗ[E] (Fin N → E)) hv
    simpa using h1
  · rw [mem_toStd (sp := sp), ← hco_def]
    constructor
    · intro hy x hx
      rw [mem_toStd (sp := sp), ← hco_def] at hx
      have h1 := (mem_dl sp.cm.sig J M (co.symm y)).1 (hsd.symm ▸ hy) (co.symm x) hx
      rw [← key, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
      exact h1
    · intro h
      rw [← hsd, mem_dl]
      intro x hx
      have h1 := h (co x) ((mem_toStd (sp := sp) J M (co x)).2 (by rw [← hco_def, LinearEquiv.symm_apply_apply]; exact hx))
      rw [← LinearEquiv.apply_symm_apply co y, key] at h1
      exact h1

theorem isSD_core (J : Matrix (Fin N) (Fin N) E)
    (hJ : ∀ M : Submodule (𝓞 E) (Fin N → E), IsLat M → IsLat (dl sp.cm.sig J M))
    (hco : ∃ co, Formalism.L2.PairingIndexBounds.F.IsOrthCo (sp.cm.sig : E →+* E) J co)
    (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hy : y ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F))
    {Lb M0 : Submodule (𝓞 E) (Fin N → E)} (hLb : IsLat Lb) (a : 𝓞 E)
    (hA : Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a Lb = M0) (hM0 : IsLat M0) (hsd : dl sp.cm.sig J M0 = M0) :
    IsSDLat E N (Formalism.L2.PairingIndexBounds.F.toStd (sp.cm.sig : E →+* E) J
      (Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a (Formalism.L2.PairingIndexBounds.F.latAd y Lb))) := by
  have hG : Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a (Formalism.L2.PairingIndexBounds.F.latAd y Lb) = Formalism.UG.CS.globLat y M0 := by
    rw [latAd_eq, ← hA]
    by_cases ha : a = 0
    · subst ha
      rw [compan_zero, compan_zero]
    · rw [compan_eq, compan_eq]
      exact (glob_companion sp.cm.sig J hJ hLb ha y hy).symm
  rw [hG]
  exact isSD_toStd (sp := sp) J hco (isLat_glob hM0 y) (glob_selfdual sp.cm.sig J hJ hM0 hsd y hy)

end Gen

section Main

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isSDLat_latK : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E), (∀ M : Submodule (𝓞 E) (Fin N → E), Formalism.L2.GlobalTheoryTheory.Comp.IsLat M → Formalism.L2.GlobalTheoryTheory.Comp.IsLat (Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J M)) → (∃ co, IsOrthCo (sp.cm.sig : E →+* E) J co) → ∀ y ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F), ∀ (Lb : Submodule (𝓞 E) (Fin N → E)) (a : 𝓞 E), Formalism.L2.GlobalTheoryTheory.Comp.IsLat Lb → Formalism.L2.GlobalTheoryTheory.Comp.IsLat (compan (sp := sp) J a Lb) → Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J (compan (sp := sp) J a Lb) = compan (sp := sp) J a Lb → IsSDLat E N (latK sp J a y Lb) := by
  intro R F E _ _ _ _ _ _ sp N J hJ hco y hy Lb a hLb hM hsd
  exact isSD_core (sp := sp) J hJ hco y hy hLb a rfl hM hsd

end Main

end GlobalTheory.SDCompan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitDetFrameMatrixOfCharts
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem isUnit_det_frameMatrix_ofCharts : ∀ {p : ℕ} [Fact p.Prime] {X : Sys p} {D : D7} (cp : ChartPts X D) (a : 𝓞 D.host.E) (bad : Finset (HeightOneSpectrum (𝓞 D.host.F))) (j : ℕ) (La : X.Lt j) (v : X.Pl), IsUnit ((fdOfCharts cp a bad).frM j La v).det := by
  intro p _ X D cp a bad j La v
  simp only [Formalism.L2.PairingIndexBounds.F.fdOfCharts]
  rw [Matrix.det_submatrix_equiv_self]
  erw [← RingHom.map_det]
  refine IsUnit.map _ ?_
  rw [Matrix.det_mul]
  refine IsUnit.mul ?_ ?_
  · rw [LinearMap.det_toMatrix']
    exact LinearEquiv.isUnit_det' _
  · exact Matrix.isUnits_det_units (cp.B j La)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitNatCastOfCoprimeLocal
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem isUnit_natCast_of_coprime_local {R : Type*} [CommRing R] [IsLocalRing R] {p s : ℕ} (hp : ¬ IsUnit (p : R))
    (hs : Nat.Coprime s p) : IsUnit (s : R) := by
  have hc : IsCoprime (s : R) (p : R) := Nat.Coprime.cast hs
  obtain ⟨a, b, hab⟩ := hc
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (a := a * (s : R)) (b := b * (p : R)) (by rw [hab]; exact isUnit_one) with h | h
  · exact isUnit_of_mul_isUnit_right h
  · exact absurd (isUnit_of_mul_isUnit_right h) hp

theorem natCast_isUnit_localRing : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (v : X.Pl) (s : ℕ), Nat.Coprime s p → IsUnit (s : X.G.P.W v) :=
  fun X v _ hs => isUnit_natCast_of_coprime_local (X.G.P.setting v).p_unif.not_isUnit hs

end GlobalTheory.TwV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LamPosGOfLamPos
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU

theorem lamPosG_of_lamPos : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), LamPos X E.toCEmb pos lam ρ → RepFrame.LamPosG X E D pos lam ρ := by
  intro p _ X _ E D pos lam ρ h v s x
  rw [h v s x]
  rfl

end GlobalTheory.TwU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LamPosOfPosEmb
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwU.PlaceAbove

theorem involution_conj (D : D7) (x : D.host.E) : sigD D (D.host.conj x) = x := by
  have h3 : ∀ y : D.host.E, sigD D y = D.host.conj y := fun y => bridge_star_holds D.R D.host y
  rw [h3, ← Formalism.L2.Herm.star_conj, ← Formalism.L2.Herm.star_conj, star_star]

theorem posArg_eq_self (D : D7) {n : ℕ} (s : Fin n) (x : D.host.E) :
    (if Even s.val then (if IsOddPos s then D.host.conj x else x)
      else sigD D (if IsOddPos s then D.host.conj x else x)) = x := by
  by_cases hs : s.val % 2 = 1
  · have hodd : IsOddPos s := hs
    have hne : ¬ Even s.val := by rw [Nat.not_even_iff_odd, Nat.odd_iff]; exact hs
    rw [if_neg hne, if_pos hodd, involution_conj]
  · have hodd : ¬ IsOddPos s := hs
    have hev : Even s.val := by rw [Nat.even_iff]; omega
    rw [if_pos hev, if_neg hodd]

end GlobalTheory.TwU.PlaceAbove

open GlobalTheory.TwU.PlaceAbove in

theorem GlobalTheory.TwU.lamPos_of_posEmb : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (E : CEmb X.G) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v) (e : D.what₂.LL →+* X.G.Kf), (∀ (z : D.what₂.LL) (hz : D.what₂.embLL z ∈ algebraicClosure ℚ ℂ), E.iK (e z) = lam ⟨D.what₂.embLL z, hz⟩) → (∀ (v : X.Pl) (s : Fin (X.G.P.n' v)) (x : D.host.E), e (tEL D (pos ⟨v, s⟩) (if Even s.val then x else sigD D x)) = X.G.P.ι v ((X.G.P.σ v ^ s.val) (ρ v x))) → LamPos X E pos lam ρ := by
  intro p _ X E D pos lam ρ e hK hpos
  intro v s x
  have h1 := hpos v s (if IsOddPos s then D.host.conj x else x)
  rw [posArg_eq_self D s x] at h1
  have hz := embLL_mem_alg D (tEL D (pos ⟨v, s⟩) x)
  have h2 := hK (tEL D (pos ⟨v, s⟩) x) hz
  have he : Formalism.MainNotions.TaylorLogMetric.embT D (pos ⟨v, s⟩) x = D.what₂.embLL (tEL D (pos ⟨v, s⟩) x) := (tEL_emb D (pos ⟨v, s⟩) x).symm
  have hL : Formalism.MainNotions.TaylorLogMetric.lamC lam (Formalism.MainNotions.TaylorLogMetric.embT D (pos ⟨v, s⟩) x) = lam ⟨D.what₂.embLL (tEL D (pos ⟨v, s⟩) x), hz⟩ := by
    unfold Formalism.MainNotions.TaylorLogMetric.lamC
    rw [dif_pos (he ▸ hz)]
    congr 1
    exact Subtype.ext he
  show Formalism.MainNotions.TaylorLogMetric.lamC lam (Formalism.MainNotions.TaylorLogMetric.embT D (pos ⟨v, s⟩) x) = _
  rw [hL, ← h2, h1]
  rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocBasisMaps
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.YYMaps

section Glob

variable (D : D7) {p : ℕ} {N N' : ℕ}

theorem natsmul_mem {V : Type*} [AddCommGroup V] [Module D.host.E V] [Module (𝓞 D.host.E) V]
    (L : Submodule (𝓞 D.host.E) V) (s : ℕ) {y : V} (hy : y ∈ L) : (s : D.host.E) • y ∈ L := by
  rw [Nat.cast_smul_eq_nsmul]
  exact nsmul_mem hy s

theorem homL_maps {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    {A : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ TaylorLogMetric.homL D L L') : ∀ x ∈ L, A *ᵥ x ∈ L' := by
  induction hA using Submodule.span_induction with
  | mem A hA => exact hA
  | zero => intro x _; simp
  | add A B _ _ hA hB => intro x hx; rw [Matrix.add_mulVec]; exact L'.add_mem (hA x hx) (hB x hx)
  | smul c A _ hA => intro x hx; rw [Matrix.smul_mulVec]; exact L'.smul_mem c (hA x hx)

theorem yy_maps
    (hA0 : ∀ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∃ s : ℕ, Nat.Coprime s p ∧
      (s : D.host.E) * a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range)
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {B : Matrix (Fin N') (Fin N) D.host.E}
    (hB : B ∈ TaylorLogMetric.YYl D L L') :
    ∃ s : ℕ, Nat.Coprime s p ∧ ∀ x ∈ L, (s : D.host.E) • (B *ᵥ x) ∈ L' := by
  induction hB using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨a, ha, A, hA, rfl⟩ := hB
    obtain ⟨s, hs, t, ht⟩ := hA0 a ha
    refine ⟨s, hs, fun x hx => ?_⟩
    have e : (s : D.host.E) • ((a • A) *ᵥ x) = t • (A *ᵥ x) := by
      rw [Matrix.smul_mulVec, smul_smul, ← ht, algebraMap_smul]
    rw [e]
    exact L'.smul_mem t (homL_maps D hA x hx)
  | zero => exact ⟨1, Nat.coprime_one_left p, fun x _ => by simp⟩
  | add B C _ _ hB hC =>
    obtain ⟨s, hs, hB⟩ := hB
    obtain ⟨t, ht, hC⟩ := hC
    refine ⟨s * t, Nat.Coprime.mul_left hs ht, fun x hx => ?_⟩
    have e : ((s * t : ℕ) : D.host.E) • ((B + C) *ᵥ x) =
        (t : D.host.E) • ((s : D.host.E) • (B *ᵥ x)) + (s : D.host.E) • ((t : D.host.E) • (C *ᵥ x)) := by
      rw [Matrix.add_mulVec, smul_add, smul_smul, smul_smul, Nat.cast_mul, mul_comm (t : D.host.E) (s : D.host.E)]
    rw [e]
    exact L'.add_mem (natsmul_mem D L' t (hB x hx)) (natsmul_mem D L' s (hC x hx))
  | smul c B _ hB =>
    obtain ⟨s, hs, hB⟩ := hB
    refine ⟨s, hs, fun x hx => ?_⟩
    rw [Matrix.smul_mulVec, smul_comm]
    exact L'.smul_mem c (hB x hx)

end Glob

theorem locBasis_maps : ∀ (D : D7) (p : ℕ), (∀ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.E) * a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) → ∀ {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) {r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), TaylorLogMetric.LocBasis D p (TaylorLogMetric.YYl D L L') b → ∀ i, ∃ s : ℕ, Nat.Coprime s p ∧ ∀ x ∈ L, (s : D.host.E) • (b i *ᵥ x) ∈ L' := by
  intro D p hA0 N N' L L' r b hb i
  obtain ⟨s, hs, hsb⟩ := hb.2.1 i
  obtain ⟨t, ht, h⟩ := yy_maps D hA0 hsb
  refine ⟨t * s, Nat.Coprime.mul_left ht hs, fun x hx => ?_⟩
  have := h x hx
  rwa [Matrix.smul_mulVec, smul_smul, ← Nat.cast_mul] at this

end GlobalTheory.TwV.YYMaps
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocSpCompanEq
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.CompSp

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
theorem _root_.GlobalTheory.TwV.CompSp.locSp_compan_eq : ∀ {R : _root_.Formalism.BasicNotions.Ranks} {F E : Type} [Field F]
    [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : _root_.Formalism.BasicNotions.Spaces R F E)
    (W K : Type) [CommRing W] [Field K] [Algebra W K] (ρ : E →+* K) {N : ℕ}
    (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (T : ℕ) (Λ : Submodule (𝓞 E) (Fin N → E)),
    IsUnit (T : W) → (∀ z ∈ _root_.Formalism.BasicNotions.dualSet (sp.cm.sig : E →+* E) J Λ, (T : E) • z ∈ Λ) →
      _root_.GlobalTheory.TwV.locSp W ρ (_root_.Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a Λ) =
        _root_.GlobalTheory.TwV.locSp W ρ Λ := by
  intro R F E _ _ _ _ _ _ sp W K _ _ _ ρ N J a T Λ hT hdual
  have hsub : Λ ≤ _root_.Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a Λ := by
    simp only [_root_.Formalism.L2.PairingIndexBounds.F.compan]
    exact le_sup_left
  have key : ∀ x ∈ _root_.Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a Λ, T • x ∈ Λ := by
    intro x hx
    let S : Submodule (𝓞 E) (Fin N → E) :=
      Λ.comap (T • LinearMap.id : (Fin N → E) →ₗ[𝓞 E] (Fin N → E))
    have hΛS : Λ ≤ S := fun y hy => by
      simp only [S, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]
      exact nsmul_mem hy T
    have hDS : Submodule.span (𝓞 E) (_root_.Formalism.BasicNotions.dualSet (sp.cm.sig : E →+* E) J Λ) ≤ S := by
      rw [Submodule.span_le]
      intro z hz
      simp only [S, SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply,
        LinearMap.id_apply]
      simpa [Nat.cast_smul_eq_nsmul] using hdual z hz
    have hle : _root_.Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a Λ ≤ S := by
      simp only [_root_.Formalism.L2.PairingIndexBounds.F.compan]
      exact sup_le hΛS (Submodule.smul_le_right.trans hDS)
    have := hle hx
    simpa [S] using this
  simp only [_root_.GlobalTheory.TwV.locSp]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨u, hu⟩ := hT
    have h1 : (fun k => ρ ((T • x) k)) ∈
        Submodule.span W ((fun x k ↦ ρ (x k)) '' (Λ : Set (Fin N → E))) :=
      Submodule.subset_span ⟨_, key x hx, rfl⟩
    have h2 : (fun k => ρ ((T • x) k)) = (u : W) • (fun k => ρ (x k)) := by
      funext k
      simp [hu, map_nsmul, Nat.cast_smul_eq_nsmul]
    have h3 := Submodule.smul_mem _ ((u⁻¹ : Wˣ) : W) h1
    rwa [h2, smul_smul, Units.inv_mul, one_smul] at h3
  · exact Submodule.span_mono (Set.image_mono hsub)

end GlobalTheory.TwV.CompSp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModelPartitionSizeExtensionFirstLastRows
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem sum_Icc_one_eq_sum_fin (f : ℕ → ℤ) : ∀ n : ℕ, ∑ i ∈ Finset.Icc 1 n, f i = ∑ r : Fin n, f (r.val + 1)
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_Icc_succ_top (by omega), sum_Icc_one_eq_sum_fin f n, Fin.sum_univ_castSucc]
    simp

theorem size_first_last_rows : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → NuIs X D pos j (extNu (D.R.N (j + 1)) ν) ∧ (∀ τ, szT X D pos j τ = ∑ r, (ν τ r : ℤ)) ∧ (∀ τ, szT X D pos j τ = ∑ r, (extNu (D.R.N (j + 1)) ν τ r : ℤ)) ∧ (∀ τ r, (extNu (D.R.N (j + 1)) ν τ r : ℤ) ≤ cT1 X D pos j τ) ∧ ∀ τ, 0 ≤ X.nuv (pos.symm τ).1 (j + 1) (pos.symm τ).2 (NN X.G.P.m X.t j) := by
  intro p _ X D pos j hN ν hν
  have hle : D.R.N j ≤ D.R.N (j + 1) := rk_le X D hN
  have hz : ∀ τ (i : ℕ), D.R.N j < i → X.nuv (pos.symm τ).1 (j + 1) (pos.symm τ).2 i = 0 := fun τ i hi =>
    nuv_zero X _ j _ i (hN.1 ▸ hi)
  have hext : NuIs X D pos j (extNu (D.R.N (j + 1)) ν) := by
    intro τ i
    unfold extNu
    split_ifs with h
    · exact hν τ ⟨i.val, h⟩
    · rw [hz τ _ (by omega)]; simp
  have hsz : ∀ τ, szT X D pos j τ = ∑ i ∈ Finset.Icc 1 (D.R.N (j + 1)), X.nuv (pos.symm τ).1 (j + 1) (pos.symm τ).2 i := by
    intro τ
    unfold szT szMu
    rw [hN.2]
  refine ⟨hext, ?_, ?_, ?_, ?_⟩
  · intro τ
    rw [hsz τ, ← Finset.sum_subset (Finset.Icc_subset_Icc_right hle) (fun i hi hni => by
      simp only [Finset.mem_Icc] at hi hni
      exact hz τ i (by omega)), sum_Icc_one_eq_sum_fin]
    exact Finset.sum_congr rfl fun r _ => hν τ r
  · intro τ
    rw [hsz τ, sum_Icc_one_eq_sum_fin]
    exact Finset.sum_congr rfl fun r _ => hext τ r
  · intro τ r
    rw [← hext τ r]
    exact nuv_le_first X _ j _ _
  · intro τ
    exact nuv_nonneg X _ j _ _

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NaturalActionInverseFrameUndoesMove
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem natAct_glInv_gmOf : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (j : ℕ) (La : X.Lt j) (G : (X.Pj j).Xsp), (X.Pj j).natAct (glInv X j (BOf fd j La)) (gmOf fd j La G) = G := by
  intro p _ X D pos fd j La G
  show (X.Pj j).natAct _ ((X.Pj j).natAct (fun v => (glInv X j (BOf fd j La) v)⁻¹) G) = G
  rw [← LinearMap.comp_apply, ← Formalism.MainNotions.G.LatticeSystems.jd_natAct_mul (X.Pj j)]
  simp only [mul_inv_cancel]
  rw [Formalism.MainNotions.G.LatticeSystems.jd_natAct_one (X.Pj j)]
  rfl

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolDYExpDeg
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem polDY_exp_deg : ∀ (D : D7) {N N' : ℕ} (s : D.what₂.Tau → ℂ) (ν : D.what₂.Tau → Fin N → ℕ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ), Q ∈ WtPol ℂ ν → ∀ α ∈ (polDY D s Q (N' := N')).support, ∀ τ, ∑ b, ∑ a, α (τ, b, a) = ∑ r, ν τ r := by
  intro D N N' s ν Q hQ α hα τ
  exact Formalism.L2.KerInert.SecondKernelMoveDegree.difference_polynomial_degree D N N' s ν Q hQ α hα τ

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftFormsInternalDirectSumIsotypicStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_forms_internal_direct_sum_isotypic : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → Formalism.BasicNotions.Rows.IsotRank D.what₂ → Formalism.MainNotions.SumRepresentations.adm8 D := by
  first | exact @GlobalTheory.IsotSum.isotInternal_of_read | exact GlobalTheory.IsotSum.isotInternal_of_read | (intros; apply GlobalTheory.IsotSum.isotInternal_of_read <;> assumption)
end

