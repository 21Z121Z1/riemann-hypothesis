import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchingLatticesMatchesSphericalOps
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0122
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0112
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0113
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0107
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0019
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0386
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0715
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1113
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0896
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1059
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceHyperspecialStableLatticeEqMultiple
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

namespace GlobalTheory.SplitLatMatch

open GlobalTheory.SplitHecke

variable {D : D7}

set_option maxHeartbeats 1000000 in

theorem half (V : HSp D) (e : Formalism.L2.Theta.AE D) (he : IsSplitIdem D e)
    (M : AddSubgroup (Fin V.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)))
    (hM : ∀ a ∈ intAE D, ∀ z ∈ M, a • z ∈ M)
    (hf : ∀ z ∈ M, finPart D (e + cA D e) • z = z)
    (hb : ∃ N : ℕ, 0 < N ∧ (∀ y ∈ Formalism.L2.NTheta.LamHat V, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • (finPart D (e + cA D e) • y) ∈ M) ∧ ∀ z ∈ M, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • z ∈ Formalism.L2.NTheta.LamHat V)
    (hK : ∀ g : GA D V, g ∈ KsphC V ∅ → SuppF V (e + cA D e) g → ∀ z ∈ M, (finMat D.sp.cm.sig V.gram g).mulVec z ∈ M) :
    ∃ a a' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E, finPart D e * a * a' = finPart D e ∧
      ∀ z, (finPart D e • z ∈ M ↔ (finPart D e * a) • z ∈ Formalism.L2.NTheta.LamHat V) := by
  obtain ⟨v, π, hπ⟩ := GlobalTheory.SplitChart.exists_chart e he
  obtain ⟨β, hβ⟩ := GlobalTheory.SplitFrame.exists_frame e v π he hπ V
  obtain ⟨φ, hφ⟩ := GlobalTheory.SplitFrame.exists_factor hπ
  have hπe : π e = 1 := GlobalTheory.SplitHomLattice.pi_idem he hπ
  have hpe : φ (finPart D e) = 1 := by rw [hφ]; exact hπe
  have hpp : finPart D e * finPart D e = finPart D e := by rw [← map_mul, he.1]
  have hpO : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ hpp
  have hpq : finPart D e * finPart D (cA D e) = 0 := by rw [← map_mul, he.2.1, map_zero]
  have hφs : Function.Surjective φ := fun t => by
    obtain ⟨a, rfl⟩ := hπ.1 t
    exact ⟨finPart D a, hφ a⟩
  have hker : ∀ x, φ x = 0 → finPart D e * x = 0 := by
    intro x hx
    obtain ⟨a, rfl⟩ := GlobalTheory.SplitHecke.Stab.finPart_surj x
    rw [hφ] at hx
    rw [← map_mul, (hπ.2.1 a).1 hx, map_zero]
  let T : (Fin V.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) →+ (Fin V.rank → Fv D.host.F v) :=
    { toFun := fun z => (β⁻¹).1 *ᵥ fun k => φ (z k)
      map_zero' := by
        have : (fun k : Fin V.rank => φ ((0 : Fin V.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) k)) = 0 :=
          funext fun k => by rw [Pi.zero_apply, map_zero, Pi.zero_apply]
        simp only [this, Matrix.mulVec_zero]
      map_add' := by
        intro x y
        have : (fun k => φ ((x + y) k)) = (fun k => φ (x k)) + fun k => φ (y k) :=
          funext fun k => by rw [Pi.add_apply, map_add, Pi.add_apply]
        simp only [this, Matrix.mulVec_add] }
  have hT : ∀ z, T z = (β⁻¹).1 *ᵥ fun k => φ (z k) := fun z => rfl
  have hTs : ∀ (x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) z, T (x • z) = φ x • T z := by
    intro x z
    rw [hT, hT, ← Matrix.mulVec_smul]
    congr 1
    funext k
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul]
  have hTp : ∀ z, T (finPart D e • z) = T z := by
    intro z; rw [hTs, hpe, one_smul]
  have hmem : ∀ z, finPart D e • z ∈ Formalism.L2.NTheta.LamHat V ↔ ∀ i, T z i ∈ v.adicCompletionIntegers D.host.F := by
    intro z
    choose y hy using fun k => GlobalTheory.SplitHecke.Stab.finPart_surj (z k)
    have e1 : finPart D e • z = fun i => finPart D (e * y i) := funext fun i => by
      rw [Pi.smul_apply, smul_eq_mul, map_mul, hy]
    have e2 : (fun k => φ (z k)) = fun k => π (y k) := funext fun k => by rw [← hy, hφ]
    rw [e1, hβ y, hT, e2]
    exact forall_congr' fun i => isInt_Ov
  have hinj : ∀ z m, T z = T m → finPart D e • z = finPart D e • m := by
    intro z m h
    have h1 : (fun k => φ (z k)) = fun k => φ (m k) := by
      have := congrArg (fun u => β.1 *ᵥ u) h
      simpa only [hT, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec] using this
    funext k
    have h2 := hker (z k - m k) (by rw [map_sub, sub_eq_zero]; exact congrFun h1 k)
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    rw [mul_sub, sub_eq_zero] at h2
    exact h2
  let S : AddSubgroup (Fin V.rank → Fv D.host.F v) := M.map T
  have hS : ∀ z, T z ∈ S ↔ finPart D e • z ∈ M := by
    intro z
    constructor
    · rintro ⟨m, hm, h⟩
      rw [hinj z m h.symm]
      exact hM _ hpO m hm
    · intro h
      exact ⟨_, h, hTp z⟩
  obtain ⟨N, hN, hlo, hup⟩ := hb
  have : CharZero (Fv D.host.F v) := charZero_of_injective_algebraMap (algebraMap D.host.F (Fv D.host.F v)).injective
  have hN' : ((N : ℕ) : Fv D.host.F v) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hφN : φ ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) = (N : Fv D.host.F v) := map_natCast φ N
  have hf' : finPart D (e + cA D e) * finPart D e = finPart D e := by
    rw [(finPart D).map_add, add_mul, hpp, mul_comm (finPart D (cA D e)), hpq, add_zero]
  obtain ⟨t, ht, hSt⟩ := GlobalTheory.LatticeBetweenMultiples.eq_multiple_of_standard_lattice v S (by
      intro o ho w hw
      obtain ⟨m, hm, rfl⟩ := hw
      obtain ⟨a, ha⟩ := hπ.1 o
      refine ⟨finPart D (e * a) • m, hM _ ((hπ.2.2.2 a).2 (isInt_Ov.2 (ha ▸ ho))) m hm, ?_⟩
      rw [hTs, hφ, map_mul, hπe, one_mul, ha])
    (by
      refine ⟨N, hN', fun w hw => ?_⟩
      choose z hz using fun k => hφs ((β.1 *ᵥ w) k)
      have hTz : T z = w := by
        rw [hT, (funext hz : (fun k => φ (z k)) = β.1 *ᵥ w), Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
          Units.val_one, Matrix.one_mulVec]
      have hzL : finPart D e • z ∈ Formalism.L2.NTheta.LamHat V := (hmem z).2 (by rw [hTz]; exact hw)
      have h1 := hlo _ hzL
      rw [smul_smul (finPart D (e + cA D e)), hf'] at h1
      exact ⟨_, h1, by rw [hTs, hTp, hφN, hTz]⟩)
    (by
      refine ⟨N, hN', fun w hw i => ?_⟩
      obtain ⟨m, hm, rfl⟩ := hw
      have h2 : finPart D e • (((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • m) ∈ Formalism.L2.NTheta.LamHat V :=
        GlobalTheory.LatDual.smul_mem_lamHat V _ hpO _ (hup m hm)
      have h3 := (hmem _).1 h2 i
      rwa [hTs, hφN, Pi.smul_apply, smul_eq_mul] at h3)
    (by
      intro x hx1 hx2 w hw
      obtain ⟨m, hm, rfl⟩ := hw
      obtain ⟨g, hg, hgx⟩ := GlobalTheory.SplitOnto.exists_suppAt_rho_eq e v π he hπ V β x
      have hgK : g ∈ KsphC V ∅ := (GlobalTheory.SplitHecke.Stab.mem_KsphC_iff_gInt e v π he hπ V β hβ g hg).2 (by
        rw [hgx]
        exact ⟨fun i j => isInt_Ov.2 (hx1 i j), fun i j => isInt_Ov.2 (hx2 i j)⟩)
      refine ⟨_, hK g hgK hg m hm, ?_⟩
      have e1 : (fun k => φ ((finMat D.sp.cm.sig V.gram g *ᵥ m) k)) = (mt V g).map π *ᵥ fun k => φ (m k) := by
        funext k
        rw [RingHom.map_mulVec, GlobalTheory.SplitHecke.Stab.finMat_eq, Matrix.map_map]
        congr 2
        funext y
        exact hφ y
      rw [hT, hT, e1, ← hgx, rho_val, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_assoc _ β.1, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one])
  obtain ⟨a, ha⟩ := hφs t
  obtain ⟨a', ha'⟩ := hφs t⁻¹
  refine ⟨a, a', ?_, fun z => ?_⟩
  · have := hker (a * a' - 1) (by rw [map_sub, map_mul, ha, ha', mul_inv_cancel₀ ht, map_one, sub_self])
    linear_combination this
  · rw [← hS, hSt, mul_smul, hmem, hTs, ha]
    simp only [Pi.smul_apply, smul_eq_mul]

end GlobalTheory.SplitLatMatch

namespace GlobalTheory.SplitLatMatch

variable {D : D7}

set_option maxHeartbeats 1000000 in

theorem lat_split : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E) (e : Formalism.L2.Theta.AE D), Formalism.L2.NTheta.IsIdemAt e P → ∀ (M : AddSubgroup (Fin V.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))), (∀ a ∈ intAE D, ∀ z ∈ M, a • z ∈ M) → (∀ z ∈ M, finPart D (e + cA D e) • z = z) → (∃ N : ℕ, 0 < N ∧ (∀ y ∈ Formalism.L2.NTheta.LamHat V, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • (finPart D (e + cA D e) • y) ∈ M) ∧ ∀ z ∈ M, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • z ∈ Formalism.L2.NTheta.LamHat V) → (∀ g : GA D V, g ∈ KsphC V ∅ → SuppF V (e + cA D e) g → ∀ z ∈ M, (finMat D.sp.cm.sig V.gram g).mulVec z ∈ M) → ∃ c : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), IsUnit c ∧ ∀ z, z ∈ M ↔ (finPart D (e + cA D e) • z = z ∧ c • z ∈ Formalism.L2.NTheta.LamHat V) := by
  intro D V P e hP M hMs hf hb hK
  have he : IsSplitIdem D e := hP.1
  have he' := GlobalTheory.SplitScalar.isSplitIdem_conj he
  obtain ⟨a, a', ha, hA⟩ := half V e he M hMs hf hb hK
  have hsum : cA D e + cA D (cA D e) = e + cA D e := by rw [cA_cA, add_comm]
  obtain ⟨b, b', hb', hB⟩ := half V (cA D e) he' M hMs (by rw [hsum]; exact hf) (by rw [hsum]; exact hb)
    (by rw [hsum]; exact hK)
  have hpp : finPart D e * finPart D e = finPart D e := by rw [← map_mul, he.1]
  have hqq : finPart D (cA D e) * finPart D (cA D e) = finPart D (cA D e) := by rw [← map_mul, he'.1]
  have hpq : finPart D e * finPart D (cA D e) = 0 := by rw [← map_mul, he.2.1, map_zero]
  have hpO : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ hpp
  have hqO : finPart D (cA D e) ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ hqq
  have hfe : finPart D (e + cA D e) = finPart D e + finPart D (cA D e) := map_add _ _ _
  rw [hfe] at hf
  rw [hfe]
  refine ⟨finPart D e * a + finPart D (cA D e) * b + (1 - (finPart D e + finPart D (cA D e))),
    isUnit_iff_exists_inv.2 ⟨finPart D e * a' + finPart D (cA D e) * b' + (1 - (finPart D e + finPart D (cA D e))),
      by linear_combination (a * a' - a - a' + 1) * hpp + (b * b' - b - b' + 1) * hqq +
        (a * b' + b * a' - a - a' - b - b' + 2) * hpq + ha + hb'⟩, fun z => ⟨fun hz => ⟨hf z hz, ?_⟩, fun ⟨hz, hc⟩ => ?_⟩⟩
  · have h1 := (hA z).1 (hMs _ hpO z hz)
    have h2 := (hB z).1 (hMs _ hqO z hz)
    have h3 := hf z hz
    have e1 : (finPart D e * a + finPart D (cA D e) * b + (1 - (finPart D e + finPart D (cA D e)))) • z =
        (finPart D e * a) • z + (finPart D (cA D e) * b) • z + (z - (finPart D e + finPart D (cA D e)) • z) := by
      funext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e1, h3, sub_self, add_zero]
    exact add_mem h1 h2
  · have e2 : ∀ (p c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), p * (finPart D e * a + finPart D (cA D e) * b + (1 - (finPart D e + finPart D (cA D e)))) = p * c →
        p • ((finPart D e * a + finPart D (cA D e) * b + (1 - (finPart D e + finPart D (cA D e)))) • z) = (p * c) • z := by
      intro p c h
      rw [smul_smul, h]
    have h1 : finPart D e • z ∈ M := (hA z).2 (by
      rw [← e2 (finPart D e) a (by linear_combination (a - 1) * hpp + (b - 1) * hpq)]
      exact GlobalTheory.LatDual.smul_mem_lamHat V _ hpO _ hc)
    have h2 : finPart D (cA D e) • z ∈ M := (hB z).2 (by
      rw [← e2 (finPart D (cA D e)) b (by linear_combination (b - 1) * hqq + (a - 1) * hpq)]
      exact GlobalTheory.LatDual.smul_mem_lamHat V _ hqO _ hc)
    rw [← hz, add_smul]
    exact add_mem h1 h2

end GlobalTheory.SplitLatMatch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonEtaleCohomologyGenericFibreHenselian
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.GenFibreLine

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap]
  rw [← Functor.map_comp, ← Spec.map_comp]
  rfl

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp only [spMap]
  rw [show CommRingCat.ofHom (RingHom.id A) = 𝟙 (CommRingCat.of A) from rfl, Spec.map_id,
    CategoryTheory.Functor.map_id]

theorem pull_bijective_of_ringEquiv {R : Type} [CommRing R] {A B : Type} [CommRing A] [CommRing B]
    (e : A ≃+* B) (F : Shv R) (n : ℤ) : Function.Bijective (pull R (spMap (e : A →+* B)) F n) := by
  have h1 : spMap (e.symm : B →+* A) ≫ spMap (e : A →+* B) = 𝟙 _ := by
    rw [← spMap_comp', ← spMap_id']
    congr 1
    ext x
    simp
  have h2 : spMap (e : A →+* B) ≫ spMap (e.symm : B →+* A) = 𝟙 _ := by
    rw [← spMap_comp', ← spMap_id']
    congr 1
    ext x
    simp
  refine Function.bijective_iff_has_inverse.2 ⟨pull R (spMap (e.symm : B →+* A)) F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, h1, pull_id]
  · rw [← pull_comp, h2, pull_id]

theorem genericFibre_subsingleton : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (A : Type) [CommRing A] [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A], SH A → GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap (Polynomial T) A) → ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp (TensorProduct T (FractionRing T) A)) n i) := by
  intro q _ T _ _ _ hA hq A _ _ _ _ _ hind n i hn
  haveI : IsAlgClosed (FractionRing T) := GlobalTheory.isAlgClosed_fractionRing_of_AIC T hA
  have hqK : IsUnit (q : FractionRing T) := by simpa using hq.map (algebraMap T (FractionRing T))
  have h2 := GlobalTheory.isIndEtale_tensorProduct_left (Polynomial T) A
    (TensorProduct T (Polynomial T) (FractionRing T)) hind
  let eX : TensorProduct (Polynomial T) (TensorProduct T (Polynomial T) (FractionRing T)) A ≃+*
      TensorProduct T (FractionRing T) A :=
    (Algebra.TensorProduct.comm (Polynomial T) _ A).toRingEquiv.trans
      ((Algebra.TensorProduct.cancelBaseChange T (Polynomial T) (Polynomial T) A (FractionRing T)).toRingEquiv.trans
        (Algebra.TensorProduct.comm T A (FractionRing T)).toRingEquiv)
  let eK : Polynomial (FractionRing T) ≃+* TensorProduct T (Polynomial T) (FractionRing T) :=
    (polyEquivTensor T (FractionRing T)).toRingEquiv.trans
      (Algebra.TensorProduct.comm T (FractionRing T) (Polynomial T)).toRingEquiv
  obtain ⟨J, _, _, D, t, s, hs, hst⟩ := h2
  let c : Cocone D := ⟨CommRingCat.of (TensorProduct T (FractionRing T) A),
    s ≫ (Functor.const J).map (CommRingCat.ofHom (eX : _ →+* _))⟩
  have hc : IsColimit c := hs.ofIsoColimit (Cocones.ext eX.toCommRingCatIso (fun j => rfl))
  have hqA : IsUnit (q : c.pt) := by
    simpa using hq.map (algebraMap T (TensorProduct T (FractionRing T) A))
  suffices h0 : ∀ x : Ht q (sp (TensorProduct T (FractionRing T) A)) n i, x = 0 from
    ⟨fun x y => by rw [h0 x, h0 y]⟩
  intro x
  obtain ⟨j, z, hz⟩ := (GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity q D c hc n i).1 x hqA
  let g : TensorProduct T (Polynomial T) (FractionRing T) →+* D.obj j := (t.app j).hom
  letI : Algebra (Polynomial (FractionRing T)) (D.obj j) := (g.comp eK.toRingHom).toAlgebra
  haveI : Algebra.Etale (Polynomial (FractionRing T)) (D.obj j) := by
    rw [← RingHom.etale_algebraMap]
    exact RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective eK.bijective) (hst j).1
  haveI := GlobalTheory.T.tateTwistCohomology_subsingleton_etale_over_polynomial_algClosed q (FractionRing T) (D.obj j) hqK n i hn
  rw [← hz, Subsingleton.elim z 0, map_zero]

end GlobalTheory.EtC.GenFibreLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummablePartialFourierAdelicSchwartzRationalPair
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix

noncomputable section
namespace GlobalTheory.PartialFourierSum

open GroundTheory.Global NumberField.mixedEmbedding
open scoped Classical nonZeroDivisors

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem adelicFourierPi_mul (f : (κ → mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (y : κ → AdeleRing (𝓞 F) F) :
    adelicFourierPi F (fun x => f (infPartPi x) * g (finPartPi x)) y =
      mixedFourierPi F f (infPartPi y) * finiteFourierPi F g (finPartPi y) := by
  have h := integral_prod_mul (μ := mixedMeasurePi F) (ν := finiteMeasurePi F)
    (fun u ↦ 𝐞 (-mixedPairingPi F u (infPartPi y)) • f u)
    (fun v ↦ g v * (finiteAdelicChar F (∑ i, v i * finPartPi y i) : ℂ))
  have e := measurePreserving_splitEquivPi.integral_comp' (μ := adeleMeasurePi F)
    (f := splitEquivPi F κ) (fun p : (κ → mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) ↦
      (𝐞 (-mixedPairingPi F p.1 (infPartPi y)) • f p.1) *
        (g p.2 * (finiteAdelicChar F (∑ i, p.2 i * finPartPi y i) : ℂ)))
  rw [mixedFourierPi, finiteFourierPi, ← h, ← e, adelicFourierPi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [splitEquivPi_apply, adelicChar_sum_mul_eq_pi, Circle.smul_def, smul_eq_mul]
  ring

theorem exists_summable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (L : (κ → mixedSpace F) ≃L[ℝ] E)
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ finiteSchwartzBruhatPi F) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → Summable fun ξ : κ → F => ((1 + ‖L (embPi F ξ)‖) ^ k)⁻¹ *
      ‖g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i))‖ := by
  obtain ⟨k₀, M, hM, hb⟩ := GlobalTheory.SchwartzMajorant.exists_majorant_pureA F (g := g) hg 0
  refine ⟨k₀, fun k hk => ?_⟩
  set c : ℝ := ‖(L.symm : E →L[ℝ] (κ → mixedSpace F))‖ with hc
  have hn : ∀ v, ‖((((1 + ‖L v‖) ^ k)⁻¹ : ℝ) : ℂ)‖ = ((1 + ‖L v‖) ^ k)⁻¹ := fun v => by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hb' := hb 1 (c ^ k₀) (fun v => ((((1 + ‖L v‖) ^ k)⁻¹ : ℝ) : ℂ))
    (fun v => by
      rw [hn]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [norm_nonneg (L v)])))
    (fun v => by
      rw [hn, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
      have h1 : ‖v‖ ≤ c * ‖L v‖ := by
        simpa using (L.symm : E →L[ℝ] (κ → mixedSpace F)).le_opNorm (L v)
      have hc0 : 0 ≤ c := norm_nonneg _
      calc ‖v‖ ^ k₀ ≤ (c * (1 + ‖L v‖)) ^ k₀ :=
            pow_le_pow_left₀ (norm_nonneg _) (h1.trans (by nlinarith [norm_nonneg (L v)])) _
        _ = c ^ k₀ * (1 + ‖L v‖) ^ k₀ := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ (by linarith [norm_nonneg (L v)]) hk) (by positivity))
  refine Summable.of_nonneg_of_le (fun ξ => by positivity) (fun ξ => ?_) (hM.mul_left (1 + c ^ k₀))
  have h := hb' ξ
  rw [GlobalTheory.SchwartzMajorant.pureA_add_algebraMap, norm_mul, hn] at h
  have e1 : ((fun j => mixedEmbedding F (ξ j)) + fun j => InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((0 : κ → AdeleRing (𝓞 F) F) j).1) = embPi F ξ := by
    funext j
    simp only [Pi.add_apply, Pi.zero_apply, embPi]
    rw [show (0 : AdeleRing (𝓞 F) F).1 = 0 from rfl, map_zero, add_zero]
  have e2 : ((fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ j)) + fun j =>
      ((0 : κ → AdeleRing (𝓞 F) F) j).2) = fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ j) := by
    funext j
    simp only [Pi.add_apply, Pi.zero_apply]
    rw [show (0 : AdeleRing (𝓞 F) F).2 = 0 from rfl, add_zero]
  rw [e1, e2] at h
  exact h

def shear : ((κ → mixedSpace F) × EuclidPi F κ) ≃L[ℝ] (κ ⊕ κ → mixedSpace F) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p => Sum.elim ((toEuclidPi F).symm p.2 + p.1) ((toEuclidPi F).symm p.2)
      map_add' := fun p q => by
        funext i
        rcases i with i | i
        · simp only [Prod.fst_add, Prod.snd_add, map_add, Sum.elim_inl, Pi.add_apply]; abel
        · simp only [Prod.snd_add, map_add, Sum.elim_inr, Pi.add_apply]
      map_smul' := fun a p => by
        funext i
        rcases i with i | i
        · simp only [Prod.smul_fst, Prod.smul_snd, map_smul, Sum.elim_inl, Pi.add_apply, Pi.smul_apply,
            RingHom.id_apply, smul_add]
        · simp only [Prod.smul_snd, map_smul, Sum.elim_inr, Pi.smul_apply, RingHom.id_apply]
      invFun := fun x => (fun i => x (Sum.inl i) - x (Sum.inr i), toEuclidPi F fun i => x (Sum.inr i))
      left_inv := fun p => by
        refine Prod.ext (funext fun i => ?_) ?_
        · simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply]; abel
        · simp only [Sum.elim_inr]
          exact (toEuclidPi F).apply_symm_apply p.2
      right_inv := fun x => by
        funext i
        rcases i with i | i
        · simp only [ContinuousLinearEquiv.symm_apply_apply, Sum.elim_inl, Pi.add_apply]; abel
        · simp only [ContinuousLinearEquiv.symm_apply_apply, Sum.elim_inr] }

theorem arch_bound (f : SchwartzMap (κ ⊕ κ → mixedSpace F) ℂ) (k : ℕ) :
    ∃ C : ℝ, ∀ u v : κ → mixedSpace F, ‖mixedFourierPi F (fun t => f (Sum.elim (t + u) t)) v‖ ≤
      C * (((1 + ‖u‖) ^ k)⁻¹ * ((1 + ‖toEuclidPiConj F v‖) ^ k)⁻¹) := by
  obtain ⟨C, hC⟩ := GlobalTheory.T.schwartz_fourier_secondVariable_rapid_decay (κ → mixedSpace F) (EuclidPi F κ)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (shear (F := F) (κ := κ)) f) k
  refine ⟨C, fun u v => ?_⟩
  have h := hC u (toEuclidPiConj F v)
  rw [mixedFourierPi_eq, ← mul_inv, ← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
  exact h

theorem finiteTensor_shift (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (b : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F)
    (u t : κ → FiniteAdeleRing (𝓞 F) F) :
    finiteTensor (fun i => cosetIndicator J (b i)) (Sum.elim (t + u) t) =
      finiteTensor (fun i => cosetIndicator J (b (Sum.inl i) - b (Sum.inr i))) u *
        finiteTensor (fun i => cosetIndicator J (b (Sum.inr i))) t := by
  simp only [finiteTensor, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.add_apply,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [cosetIndicator_apply]
  by_cases h : t i - b (Sum.inr i) ∈ idealFiniteAdeles J
  · have : t i + u i - b (Sum.inl i) ∈ idealFiniteAdeles J ↔
        u i - (b (Sum.inl i) - b (Sum.inr i)) ∈ idealFiniteAdeles J := by
      rw [show t i + u i - b (Sum.inl i) = (t i - b (Sum.inr i)) + (u i - (b (Sum.inl i) - b (Sum.inr i))) by ring]
      exact AddSubgroup.add_mem_cancel_left _ h
    simp only [this]
  · simp only [if_neg h, mul_zero]

theorem summable_gen (f : SchwartzMap (κ ⊕ κ → mixedSpace F) ℂ) (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (b : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) :
    Summable fun uv : (κ → F) × (κ → F) => ‖adelicFourierPi F (fun t : κ → AF F =>
      schwartzBruhatTensorPi f (finiteTensor fun i => cosetIndicator J (b i))
        (Sum.elim (t + fun i => algebraMap F (AF F) (uv.1 i)) t)) (fun i => algebraMap F (AF F) (uv.2 i))‖ := by
  set g₁ := finiteTensor (fun i => cosetIndicator J (b (Sum.inl i) - b (Sum.inr i))) with hg₁
  set g₂ := finiteTensor (fun i => cosetIndicator J (b (Sum.inr i))) with hg₂
  have m₁ : g₁ ∈ finiteSchwartzBruhatPi F :=
    finiteTensor_mem fun i => cosetIndicator_mem_finiteSchwartzBruhat J _
  have m₂ : finiteFourierPi F g₂ ∈ finiteSchwartzBruhatPi F :=
    finiteFourierPi_mem (finiteTensor_mem fun i => cosetIndicator_mem_finiteSchwartzBruhat J _)
  obtain ⟨k₁, h₁⟩ := exists_summable (ContinuousLinearEquiv.refl ℝ (κ → mixedSpace F)) m₁
  obtain ⟨k₂, h₂⟩ := exists_summable (toEuclidPiConj F) m₂
  obtain ⟨C, hC⟩ := arch_bound f (max k₁ k₂)
  have hs := ((h₁ _ (le_max_left k₁ k₂)).mul_of_nonneg (h₂ _ (le_max_right k₁ k₂))
    (fun _ => by positivity) (fun _ => by positivity)).mul_left C
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun uv => ?_) hs
  have key : (fun t : κ → AF F => schwartzBruhatTensorPi f (finiteTensor fun i => cosetIndicator J (b i))
        (Sum.elim (t + fun i => algebraMap F (AF F) (uv.1 i)) t)) =
      fun t => (fun s => f (Sum.elim (s + embPi F uv.1) s)) (infPartPi t) *
        (g₁ (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (uv.1 i)) • g₂) (finPartPi t) := by
    funext t
    have e1 : infPartPi (Sum.elim (t + fun i => algebraMap F (AF F) (uv.1 i)) t) =
        Sum.elim (infPartPi t + embPi F uv.1) (infPartPi t) := by
      rw [← infPartPi_algebraMap]
      funext i
      rcases i with i | i
      · simp only [infPartPi, Sum.elim_inl, Pi.add_apply, homeomorphMixedSpace_apply]
        exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) _ _
      · rfl
    have e2 : finPartPi (Sum.elim (t + fun i => algebraMap F (AF F) (uv.1 i)) t) =
        Sum.elim (finPartPi t + fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (uv.1 i)) (finPartPi t) := by
      rw [← finPartPi_algebraMap]
      funext i
      rcases i with i | i <;> rfl
    rw [schwartzBruhatTensorPi, e1, e2, finiteTensor_shift]
    rfl
  rw [key, adelicFourierPi_mul (fun s => f (Sum.elim (s + embPi F uv.1) s)), finiteFourierPi_smul, infPartPi_algebraMap, finPartPi_algebraMap, norm_mul,
    Pi.smul_apply, smul_eq_mul, norm_mul]
  refine (mul_le_mul_of_nonneg_right (hC _ _) (by positivity)).trans (le_of_eq ?_)
  simp only [ContinuousLinearEquiv.refl_apply]
  ring

theorem summable_partial_fourier : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (φ : (κ ⊕ κ → AF F) → ℂ), φ ∈ schA F (κ ⊕ κ) → Summable fun uv : (κ → F) × (κ → F) => ‖adelicFourierPi F (fun t : κ → AF F => φ (Sum.elim (t + fun i => algebraMap F (AF F) (uv.1 i)) t)) (fun i => algebraMap F (AF F) (uv.2 i))‖ := by
  intro F _ _ κ _ φ hφ
  have hS : schA F (κ ⊕ κ) = cosetSpanPi F (κ ⊕ κ) := by
    rw [← schwartzBruhatPi_eq_cosetSpanPi]
    refine congrArg (Submodule.span ℂ) (Set.ext fun Φ => ?_)
    exact ⟨fun ⟨f, g, hg, h⟩ => ⟨f, g, hg, h⟩, fun ⟨f, g, hg, h⟩ => ⟨f, g, hg, h⟩⟩
  have hI : ∀ ψ ∈ cosetSpanPi F (κ ⊕ κ), ∀ u : κ → AF F,
      Integrable (fun t : κ → AF F => ψ (Sum.elim (t + u) t)) (adeleMeasurePi F) := fun ψ hψ u =>
    integrable_of_mem_schwartzBruhatPi (GlobalTheory.DiagShift.shift_mem_schwartzBruhatPi F κ ψ (hS ▸ hψ) u)
  rw [hS] at hφ
  induction hφ using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨f, J, b, rfl⟩ := hG
    exact summable_gen f J b
  | zero =>
    simp only [Pi.zero_apply, adelicFourierPi, zero_mul, integral_zero, norm_zero]
    exact summable_zero
  | add G H hG hH ihG ihH =>
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun uv => ?_) (ihG.add ihH)
    have h := congrFun (adelicFourierPi_add (hI G hG fun i => algebraMap F (AF F) (uv.1 i))
      (hI H hH fun i => algebraMap F (AF F) (uv.1 i))) (fun i => algebraMap F (AF F) (uv.2 i))
    exact (congrArg norm h).le.trans (norm_add_le _ _)
  | smul c G _ ih =>
    refine (ih.mul_left ‖c‖).congr fun uv => ?_
    have h := congrFun (adelicFourierPi_smul c (fun t : κ → AF F =>
      G (Sum.elim (t + fun i => algebraMap F (AF F) (uv.1 i)) t))) (fun i => algebraMap F (AF F) (uv.2 i))
    rw [← _root_.norm_smul]
    exact (congrArg norm h).symm

end GlobalTheory.PartialFourierSum
end
end

