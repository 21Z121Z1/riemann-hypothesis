import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0031
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingEquivTranscendental
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0081
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.ExistsMemIdealInvariants
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.SlopeBoundSingleLiftOfDefinitions
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DedekindZetaEqSumRealEisenstein
import ReciprocityTheory.ClassFieldTheory.GlobalClassField.Bundle0001
import ReciprocityTheory.Chebotarev.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedEmbeddingValues
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0002
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0144
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0004
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.GramLevelZeroEqReindex
import Formalism.LocalToGlobal.HermitianForms.Bundle0007
import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0003
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0341
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0027
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvalBasisCoordsAgainstBlockAction
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelA

open Formalism.BasicNotions NumberField Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG
open Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Act

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

theorem substR_substR (R : Type) [CommRing R] (G G' : ∀ v, Fin (P.n' v) → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) R)
    (Q : XR P R) : substR P R G (substR P R G' Q) = substR P R (fun v s => G' v s * G v s) Q := by
  have hc : (substR P R G).comp (substR P R G') = substR P R (fun v s => G' v s * G v s) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨v, s, a, t⟩
    simp only [AlgHom.comp_apply, substR, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.aeval_C,
      MvPolynomial.algebraMap_eq, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← mul_assoc, ← MvPolynomial.C_mul]
  exact congrArg (fun φ : XR P R →ₐ[R] XR P R => φ Q) hc

theorem natActR_natActR (R : Type) [Field R] (g g' : ∀ v, Fin (P.n' v) → GL (Fin (P.m + 1)) R) (Q : XR P R) :
    natActR P R g (natActR P R g' Q) = natActR P R (fun v s => g v s * g' v s) Q := by
  unfold natActR
  simp only [LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_smul, smul_smul, substR_substR]
  congr 1
  · rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [Units.val_mul, Matrix.det_mul, mul_zpow, mul_comm]

theorem natActR_one (R : Type) [Field R] (Q : XR P R) : natActR P R (fun _ _ => 1) Q = Q := by
  have hs : substR P R (fun _ _ => 1) = AlgHom.id R (XR P R) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨v, s, a, t⟩
    simp only [substR, MvPolynomial.aeval_X, AlgHom.coe_id, id_eq, Matrix.one_apply]
    simp [ite_mul, Finset.sum_ite_eq]
  unfold natActR
  simp only [inv_one, Units.val_one, Matrix.det_one, one_zpow, Finset.prod_const_one, one_smul,
    LinearMap.smul_apply, AlgHom.toLinearMap_apply]
  rw [hs]
  rfl

end Act

theorem invT_mul {k : Type} [Fintype k] [DecidableEq k] (A B : GL k ℂ) : invT (A * B) = invT A * invT B := by
  ext : 1
  simp only [invT, Units.val_mk, Units.val_mul, mul_inv_rev, Matrix.transpose_mul]

theorem invT_one {k : Type} [Fintype k] [DecidableEq k] : invT (1 : GL k ℂ) = 1 := by
  ext : 1
  simp [invT]

variable {p : ℕ} [Fact p.Prime]

theorem evC_crdB_actC (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ}
    (h : (X.Pj i).m + 1 = n) (Gr : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (B M : GL (Fin n) D.host.E)
    (V : XR (X.Pj i) ℂ) (z : Frames Gr) (f : Fr1 D n)
    (hf : ∀ τ, f.1 τ = (atR D (M * B⁻¹) τ : Matrix (Fin n) (Fin n) ℂ) * z.1 τ) :
    evC (X.Pj i) h (posJ X D pos i) Gr (crdB (embT D) B) V z = ev1 X D pos i h (actC X D pos i h M V) f ∧
      actC X D pos i h M (actC X D pos i h M⁻¹ V) = V := by
  have hcr : ∀ τ, crdB (embT D) B τ = (atR D B⁻¹ τ : Matrix (Fin n) (Fin n) ℂ) := fun τ => rfl
  let y : Fr1 D n := ⟨fun τ => crdB (embT D) B τ * z.1 τ, fun τ => by
    rw [Matrix.det_mul, hcr]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (atR D B⁻¹ τ).isUnit).mul (z.2 τ)⟩
  refine ⟨?_, ?_⟩
  · have hz : ∀ v s, zAt (X.Pj i) h (posJ X D pos i) (crdB (embT D) B) z.1 v s =
        zAt (X.Pj i) h (posJ X D pos i) (fun _ => 1) y.1 v s := by
      intro v s
      simp only [zAt, y, one_mul]
    have h1 : evC (X.Pj i) h (posJ X D pos i) Gr (crdB (embT D) B) V z = ev1 X D pos i h V y := by
      show (∏ v, ∏ s : Fin ((X.Pj i).n' v), (_ : ℂ)) * (_ : ℂ) = (∏ v, ∏ s : Fin ((X.Pj i).n' v), (_ : ℂ)) * (_ : ℂ)
      simp only [hz]
    have hy : IsTr (fun τ => (atR D M τ : Matrix (Fin n) (Fin n) ℂ)) y f := by
      intro τ
      rw [hf τ]
      show _ = (atR D M τ : Matrix (Fin n) (Fin n) ℂ) * (crdB (embT D) B τ * z.1 τ)
      rw [hcr, ← Matrix.mul_assoc, ← Units.val_mul]
      unfold atR
      rw [map_mul]
    have h2 := evC_natAct (X.Pj i) h (posJ X D pos i) (fun _ => 1) (fun _ => 1) (atR D M) y f hy V
    rw [h1]
    exact h2.symm
  · unfold actC
    rw [natActR_natActR]
    have he : (fun v s => hAt (X.Pj i) h (posJ X D pos i) (fun _ => 1) (atR D M) v s *
        hAt (X.Pj i) h (posJ X D pos i) (fun _ => 1) (atR D M⁻¹) v s) = fun _ _ => 1 := by
      funext v s
      have hm : ∀ τ, ((1 : GL (Fin n) ℂ) * atR D M τ * (1 : GL (Fin n) ℂ)⁻¹) * ((1 : GL (Fin n) ℂ) * atR D M⁻¹ τ * (1 : GL (Fin n) ℂ)⁻¹) = (1 : GL (Fin n) ℂ) := by
        intro τ
        simp only [one_mul, inv_one, mul_one, atR, ← map_mul, mul_inv_cancel, map_one]
      unfold hAt
      split_ifs
      · rw [← map_mul, hm, map_one]
      · rw [← invT_mul, ← map_mul, hm, map_one, invT_one]
    rw [he, natActR_one]

end GlobalTheory.TwV.DelA

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGenusOneFormalIsoOfUnramifiedGoodReduction
section
namespace GlobalTheory.TwV.Lt

theorem curveEx_of_cm (h2 : Formalism.L2.Th1.CM.CM2) (h3 : Formalism.L2.Th1.CM.CM3) : CurveEx := by
  intro D cc δ B χ hc hd hχ p _ hcop h5 hIn lam
  obtain ⟨g, hgl, hAt, hM, hLT⟩ :=
    GlobalTheory.InertGenusOne.datum_exists_coprime h2 h3 D cc δ hc hd p hcop h5 hIn lam
  exact ⟨g, hLT, h5, hAt, hIn, hM, hc, hd, hχ, hgl.symm, hAt.2.2.2.1⟩

theorem exists_genusOne_formal_iso_of_unramified_good_reduction (h : Formalism.L2.Th1.CM.CM2) : CurveEx :=
  curveEx_of_cm h GlobalTheory.HondaCM3.cm3

end GlobalTheory.TwV.Lt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnitaryPt
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU

theorem exists_unitary_pt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p} {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {A : LocAt F E n G}, LocGood σ J A → ∀ (i : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)), ∃ x, A.IsPt i g x ∧ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := by
  intro F E _ _ _ _ _ n p G σ J A H i g
  exact ⟨_, H.isPt_sec i g, Subgroup.mul_mem _ (H.yG_mem i) (H.sec _).2⟩

end GlobalTheory.TwU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FacQIsPt
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.FacQPt

set_option maxHeartbeats 400000 in

theorem facQ_isPt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p} (A : LocAt F E n G) (i : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (y : GL (Fin n) (E ⊗[F] (FiniteAdeleRing (𝓞 F) F))) : A.IsPt i g y → ∀ v, facQ A v y = bc (A.iw v) A.B * castGL A.rk (G.P.Qq v) (g v) * (bc (A.iw v) A.B)⁻¹ := by
  intro h v

  have hv := h.2 v
  have hB : bc ((A.eQ v).symm : (A.pl v).1.adicCompletion F →+* G.P.Qq v) (bc (A.phE v) A.B) = bc (A.iw v) A.B := by
    ext a b
    rfl
  have hg : bc ((A.eQ v).symm : (A.pl v).1.adicCompletion F →+* G.P.Qq v)
      (bc ((A.eQ v : G.P.Qq v →+* (A.pl v).1.adicCompletion F)) (castGL A.rk (G.P.Qq v) (g v))) =
      castGL A.rk (G.P.Qq v) (g v) := by
    apply Units.ext
    ext a b
    simp [Formalism.UG.bc]
  unfold facQ
  rw [hv, map_mul, map_mul, map_inv, hB, hg]

end GlobalTheory.TwV.FacQPt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GidxFacts
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.XdInert

theorem gidx_facts : ∀ (D : D7) (T p : ℕ), GIdx D.host T p →
    5 ≤ p ∧ GL3Theta.InertK D p ∧ Nat.Coprime T p ∧ ∀ i, p ≠ D.host.g i := by
  intro D T p h
  obtain ⟨hp, h5, hc, hn, hl, hT⟩ := h
  refine ⟨h5, ?_, ?_, ?_⟩
  · exact (GlobalTheory.TwU.Served.served_facts D p hp hc hn).2.1
  · exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hT).symm
  · intro i hi
    exact hl (hi ▸ D.host.g_level i)

end GlobalTheory.TwU.XdInert
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HServTwoSidesJoint0
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.hServTwoSidesJoint0 : ∀ {D : D7} (Gt : GatTies D) (c : LatCmp D) (g : GroupCompatibilityAll D Gt c) (C : ColsTiedSym D) (full : ColsFullS C), g.herm = full.1.to0 → (g.forms = fun u => (C.forms u).to0) → ∀ u, Joint0 g.herm.lev0 u (g.forms u) := by
  intro D Gt c g C full hh hf u
  rw [hh, hf]
  have e : full.1.to0.lev0 = C.herm.base.lev0 :=
    congrArg (fun X : Formalism.L2.Herm.ColsHermS D => X.base.lev0) full.2
  rw [e]
  exact C.joint0 u
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsFractionRingGat
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ggeo.FracLocal

theorem isFractionRing_gat : ∀ {D : D7} (Gl : G.LatInst D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf :=
  fun {_} Gl u w hg => GlobalTheory.TwV.Lt.fracAt Gl u w hg

end GlobalTheory.Ggeo.FracLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLatAndDlEqOfIsSDLatMvL
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.OrthSelfDual

theorem toLE_mem_mvL {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ} (co : GL (Fin N) E)
    (M : Submodule (𝓞 E) (Fin N → E)) (y : Fin N → E) :
    toLE co y ∈ mvL co M ↔ y ∈ M := by
  constructor
  · rintro ⟨x, hx, hxy⟩
    have hxy' : x = y := (toLE co).injective hxy
    rw [hxy'] at hx
    exact hx
  · intro hy
    exact Submodule.mem_map.mpr ⟨y, hy, rfl⟩

theorem isLat_and_dl_eq_of_isSDLat_mvL : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (co : GL (Fin N) E) (M : Submodule (𝓞 E) (Fin N → E)), IsOrthCo (sp.cm.sig : E →+* E) J (toLE co) → IsSDLat E N (mvL co M) → Formalism.L2.GlobalTheoryTheory.Comp.IsLat M ∧ Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J M = M := by
  intro R F E _ _ _ _ _ _ sp N J co M hco hsd
  obtain ⟨hfg, hspan, hdual⟩ := hsd

  have hkey : ∀ x z : Fin N → E, Formalism.BasicNotions.stdH E N (toLE co x) (toLE co z) =
      ∑ a, ∑ b, (sp.cm.sig : E →+* E) (x a) * J a b * z b := fun x z => hco x z
  have hinj : Function.Injective
      (((toLE co : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)).restrictScalars (𝓞 E)) :=
    (toLE co).injective
  refine ⟨⟨?_, ?_⟩, ?_⟩
  ·
    have hfin : Module.Finite (𝓞 E)
        (M.map ((((toLE co : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E))).restrictScalars (𝓞 E))) :=
      Module.Finite.iff_fg.mpr hfg
    exact Module.Finite.equiv (Submodule.equivMapOfInjective _ hinj M).symm
  ·
    rw [eq_top_iff]
    intro v _
    have hv : toLE co v ∈ Submodule.span E ((mvL co M : Submodule (𝓞 E) (Fin N → E)) : Set (Fin N → E)) := by
      rw [hspan]
      exact Submodule.mem_top
    have hset : ((mvL co M : Submodule (𝓞 E) (Fin N → E)) : Set (Fin N → E)) =
        ((toLE co : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)) '' (M : Set (Fin N → E)) := by
      unfold mvL
      rw [Submodule.map_coe]
      rfl
    rw [hset, Submodule.span_image] at hv
    obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.mp hv
    have hwv' : w = v := (toLE co).injective hwv
    rw [hwv'] at hw
    exact hw
  ·
    ext y
    rw [Formalism.L2.GlobalTheoryTheory.Comp.mem_dl, ← toLE_mem_mvL co M y, hdual (toLE co y)]
    constructor
    · intro h x' hx'
      obtain ⟨x, hx, hxx'⟩ := Submodule.mem_map.mp hx'
      have hx'' : x' = toLE co x := hxx'.symm
      rw [hx'', hkey]
      exact h x hx
    · intro h x hx
      have h1 := h (toLE co x) ((toLE_mem_mvL co M x).mpr hx)
      rw [hkey] at h1
      exact h1

end GlobalTheory.OrthSelfDual

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLatDlOfIsOrthCo
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.OrthDual

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

theorem int_mem_range {t : E} (h : IsIntegral ℤ t) : t ∈ (algebraMap (𝓞 E) E).range :=
  ⟨⟨t, h⟩, rfl⟩

theorem ringHom_mem_range (τ : E →+* E) {t : E} (h : t ∈ (algebraMap (𝓞 E) E).range) :
    τ t ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨r, rfl⟩ := h
  exact int_mem_range (IsIntegral.map τ.toIntAlgHom r.isIntegral_coe)

theorem exists_int_smul_mem (M : Submodule (𝓞 E) (Fin N → E)) {v : Fin N → E}
    (hv : v ∈ Submodule.span E (M : Set (Fin N → E))) : ∃ n : ℤ, n ≠ 0 ∧ (n : E) • v ∈ M := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n₁, h₁, hx⟩ := hx
    obtain ⟨n₂, h₂, hy⟩ := hy
    refine ⟨n₁ * n₂, mul_ne_zero h₁ h₂, ?_⟩
    have e : ((n₁ * n₂ : ℤ) : E) • (x + y) = n₂ • ((n₁ : E) • x) + n₁ • ((n₂ : E) • y) := by
      rw [← Int.cast_smul_eq_zsmul E, ← Int.cast_smul_eq_zsmul E, smul_smul, smul_smul, smul_add]
      push_cast
      rw [mul_comm (n₂ : E)]
    rw [e]
    exact add_mem (zsmul_mem hx _) (zsmul_mem hy _)
  | smul e x _ hx =>
    obtain ⟨n, hn, hx⟩ := hx
    obtain ⟨k, hk, hki⟩ := exists_integral_multiples ℤ ℚ (L := E) {e}
    have hke := hki e (Finset.mem_singleton_self e)
    refine ⟨k * n, mul_ne_zero hk hn, ?_⟩
    have e1 : ((k * n : ℤ) : E) • (e • x) = (⟨k • e, hke⟩ : 𝓞 E) • ((n : E) • x) := by
      rw [← algebraMap_smul E (⟨k • e, hke⟩ : 𝓞 E), smul_smul, smul_smul]
      congr 1
      show ((k * n : ℤ) : E) * e = (k • e) * n
      push_cast
      rw [zsmul_eq_mul]
      ring
    rw [e1]
    exact M.smul_mem _ hx

theorem isLat_dl (σ : E →ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (co : (Fin N → E) ≃ₗ[E] (Fin N → E))
    (hc : Formalism.L2.PairingIndexBounds.F.IsOrthCo (σ : E →+* E) J co) (M : Submodule (𝓞 E) (Fin N → E))
    (hM : Formalism.L2.GlobalTheoryTheory.Comp.IsLat M) : Formalism.L2.GlobalTheoryTheory.Comp.IsLat (Formalism.L2.GlobalTheoryTheory.Comp.dl σ J M) := by
  classical
  set v : Fin N → Fin N → E := fun a => co.symm (Pi.single a 1) with hv
  have key : ∀ x y, Formalism.UG.hform (σ : E →+* E) J x y = ∑ b, (σ : E →+* E) (co x b) * co y b :=
    fun x y => (hc x y).symm
  have hsingle : ∀ (a : Fin N) (c : E), Pi.single a c = c • (Pi.single a (1 : E) : Fin N → E) := by
    intro a c; ext j; simp [Pi.single_apply]
  have hexp : ∀ z : Fin N → E, z = ∑ a, co z a • v a := by
    intro z
    conv_lhs => rw [← co.symm_apply_apply z, ← Finset.univ_sum_single (co z)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hsingle, map_smul]
  have hcv : ∀ (c : E) a b, co (c • v a) b = if b = a then c else 0 := by
    intro c a b; simp [v, Pi.single_apply]
  have hform_v : ∀ (c : E) a x, Formalism.UG.hform (σ : E →+* E) J x (c • v a) = (σ : E →+* E) (co x a) * c := by
    intro c a x; rw [key]; simp [hcv]

  have hex : ∀ a, ∃ n : ℤ, n ≠ 0 ∧ (n : E) • v a ∈ M := fun a =>
    exists_int_smul_mem M (by rw [hM.2]; trivial)
  choose n hn0 hnM using hex
  have hle : Formalism.L2.GlobalTheoryTheory.Comp.dl σ J M ≤
      Submodule.span (𝓞 E) (Set.range fun a => ((n a : E))⁻¹ • v a) := by
    intro y hy
    rw [Formalism.L2.GlobalTheoryTheory.Comp.mem_dl] at hy
    have hr : ∀ a, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = (n a : E) * co y a := by
      intro a
      obtain ⟨r, hr⟩ := hy _ (hnM a)
      refine ⟨r, ?_⟩
      rw [hr, key, Finset.sum_eq_single a]
      · rw [hcv, if_pos rfl, map_intCast]
      · intro b _ hb
        rw [hcv, if_neg hb, map_zero, zero_mul]
      · intro h; exact absurd (Finset.mem_univ a) h
    choose r hr using hr
    rw [hexp y]
    refine Submodule.sum_mem _ fun a _ => ?_
    have e3 : co y a • v a = r a • (((n a : E))⁻¹ • v a) := by
      rw [← algebraMap_smul E (r a), smul_smul, hr a, mul_comm (n a : E), mul_assoc,
        mul_inv_cancel₀ (Int.cast_ne_zero.2 (hn0 a)), mul_one]
    rw [e3]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  haveI : Module.Finite (𝓞 E) (Submodule.span (𝓞 E) (Set.range fun a => ((n a : E))⁻¹ • v a)) :=
    Module.Finite.span_of_finite _ (Set.finite_range _)
  refine ⟨Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle), ?_⟩

  obtain ⟨s, hs⟩ := Module.Finite.iff_fg.1 hM.1
  obtain ⟨m, hm0, hmi⟩ := exists_integral_multiples ℤ ℚ (L := E)
    (s.biUnion fun x => Finset.univ.image fun b => co x b)
  have hint : ∀ a, ∀ x ∈ M, (m : E) * co x a ∈ (algebraMap (𝓞 E) E).range := by
    intro a x hx
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      apply int_mem_range
      have := hmi (co x a) (Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩⟩)
      rwa [zsmul_eq_mul] at this
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, Pi.add_apply, mul_add]; exact add_mem hx hy
    | smul t x _ hx =>
      rw [← algebraMap_smul E t x, map_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm]
      exact mul_mem ⟨t, rfl⟩ hx
  have hmem : ∀ a, (m : E) • v a ∈ Formalism.L2.GlobalTheoryTheory.Comp.dl σ J M := by
    intro a
    rw [Formalism.L2.GlobalTheoryTheory.Comp.mem_dl]
    intro x hx
    rw [hform_v]
    have e4 : (σ : E →+* E) (co x a) * (m : E) = (σ : E →+* E) ((m : E) * co x a) := by
      rw [map_mul, map_intCast, mul_comm]
    rw [e4]
    exact ringHom_mem_range _ (hint a x hx)
  rw [eq_top_iff]
  intro z _
  rw [hexp z]
  refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_
  have e5 : v a = ((m : E))⁻¹ • ((m : E) • v a) := by
    rw [smul_smul, inv_mul_cancel₀ (Int.cast_ne_zero.2 hm0), one_smul]
  rw [e5]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (hmem a))

end GlobalTheory.OrthDual

theorem GlobalTheory.isLat_dl_of_isOrthCo : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E), (∃ co, IsOrthCo (sp.cm.sig : E →+* E) J co) → ∀ M : Submodule (𝓞 E) (Fin N → E), Formalism.L2.GlobalTheoryTheory.Comp.IsLat M → Formalism.L2.GlobalTheoryTheory.Comp.IsLat (Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J M) := by
  rintro R F E _ _ _ _ _ _ sp N J ⟨co, hc⟩ M hM
  exact GlobalTheory.OrthDual.isLat_dl sp.cm.sig J co hc M hM

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodValuationsTypePrimesOfJetTableSplitPrimeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.atGRows_bundlePoints_of_jetSplitAmbient : GlobalTheory.AtG.JetSplitAmb → ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd), (∀ K X f T c, Q K X f T c → (positionOf (HasPartAnd fun _ _ _ _ w Z => ∀ a, GlobalTheory.AtG.RowPin w.I w.ok w.l Z a)) K X f T c) → AllBundlePointProperties.ArithmeticConditionAtBundlePoints Q Lk := by
  first | exact @GlobalTheory.AtG.row_atG_pinned | exact GlobalTheory.AtG.row_atG_pinned | (intros; apply GlobalTheory.AtG.row_atG_pinned <;> assumption)
end

