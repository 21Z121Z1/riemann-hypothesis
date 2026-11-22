import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0907
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0915
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.Bundle0002
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0011
import Formalism.SharpRestriction.LevelLetterCocycles.JumpAndLengthOfAdmitted
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0633
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0386
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0543
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0641
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0322
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionLocalAway
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0098
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0919
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0057
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0920
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0914
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0918
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0050
import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0895
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0250
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0243
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0892
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0250
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0259
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0201
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0916

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActExtLApply
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

noncomputable section
namespace GlobalTheory.UseLoc.Cases.AdmW

open GlobalTheory.AdmLoc

section Ext
variable {G : Type} [Group G] [TopologicalSpace G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
  (L : Lattice (O := O) ρ) (X : Type) [AddCommGroup X] [Module O X] (χ₁ : G →* Oˣ) (z : G → ↥L.T ⊗[O] X)

def actExtL (g : G) : ((↥L.T ⊗[O] X) × O) →ₗ[O] ((↥L.T ⊗[O] X) × O) :=
  LinearMap.prod ((actT L g).rTensor X ∘ₗ LinearMap.fst O _ O +
      (LinearMap.id : O →ₗ[O] O).smulRight (((χ₁ g : Oˣ) : O) • z g) ∘ₗ LinearMap.snd O _ O)
    ((((χ₁ g : Oˣ) : O) • (LinearMap.id : O →ₗ[O] O)) ∘ₗ LinearMap.snd O _ O)

theorem actExtL_apply (g : G) (p : (↥L.T ⊗[O] X) × O) : actExtL L X χ₁ z g p = tableLineDegreeTwo.actExt L X χ₁ z g p := by
  simp [actExtL, tableLineDegreeTwo.actExt, mul_comm]

theorem actT_one' : actT L 1 = LinearMap.id := (latRep L).map_one

theorem actT_mul' (g h : G) : actT L (g * h) = actT L g ∘ₗ actT L h := (latRep L).map_mul g h

variable {L X χ₁ z}

theorem coc_one (hz : tableLineDegreeTwo.IsCoc L X χ₁ z) : z 1 = 0 := by
  have h := hz.2 1 1
  simp only [mul_one, tableLineDegreeTwo.actTw, map_one, inv_one, Units.val_one, one_smul, actT_one', LinearMap.rTensor_id,
    LinearMap.id_apply] at h
  simpa using h

theorem actExtL_one (hz : tableLineDegreeTwo.IsCoc L X χ₁ z) : actExtL L X χ₁ z 1 = LinearMap.id := by
  apply LinearMap.ext
  intro p
  rw [actExtL_apply]
  simp [tableLineDegreeTwo.actExt, coc_one hz, actT_one']

theorem actExtL_mul (hz : tableLineDegreeTwo.IsCoc L X χ₁ z) (g h : G) :
    actExtL L X χ₁ z (g * h) = actExtL L X χ₁ z g ∘ₗ actExtL L X χ₁ z h := by
  apply LinearMap.ext
  intro p
  rw [LinearMap.comp_apply, actExtL_apply, actExtL_apply, actExtL_apply]
  have hc := hz.2 g h
  simp only [tableLineDegreeTwo.actExt, hc, tableLineDegreeTwo.actTw, actT_mul', LinearMap.rTensor_comp, LinearMap.comp_apply, map_mul,
    Units.val_mul, map_add, map_smul, LinearMap.smul_apply]
  refine Prod.ext ?_ ?_
  · simp only [smul_add, smul_smul, add_assoc]
    congr 1
    rw [add_comm]
    congr 1
    · congr 1
      have : ((χ₁ g : Oˣ) : O) * ((χ₁ g)⁻¹ : Oˣ) = 1 := Units.mul_inv _
      calc p.2 * (((χ₁ g : Oˣ) : O) * ((χ₁ h : Oˣ) : O) * (((χ₁ g)⁻¹ : Oˣ) : O))
          = p.2 * ((χ₁ h : Oˣ) : O) * (((χ₁ g : Oˣ) : O) * ((χ₁ g)⁻¹ : Oˣ)) := by ring
        _ = p.2 * ((χ₁ h : Oˣ) : O) := by rw [this, mul_one]
    · congr 1; ring
  · simp only
    ring

variable (L X χ₁ z)

theorem actExtL_ker (lam : O) (a : ℕ) (hX : ∀ x : X, lam ^ a • x = 0) (g : G) :
    tableLineDegreeTwo.kerExt L X lam a ≤ (tableLineDegreeTwo.kerExt L X lam a).comap (actExtL L X χ₁ z g) := by
  have hT : ∀ m : ↥L.T ⊗[O] X, lam ^ a • m = 0 := by
    intro m
    induction m using TensorProduct.induction_on with
    | zero => simp
    | tmul t x => rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, hX, TensorProduct.tmul_zero]
    | add u v hu hv => rw [smul_add, hu, hv, add_zero]
  rintro ⟨m, y⟩ ⟨hm, hy⟩
  simp only [Submodule.mem_bot] at hm
  subst hm
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  rw [Submodule.mem_comap, actExtL_apply]
  refine ⟨?_, ?_⟩
  · show _ ∈ (⊥ : Submodule O (↥L.T ⊗[O] X))
    rw [Submodule.mem_bot]
    simp only [tableLineDegreeTwo.actExt, map_zero, zero_add]
    rw [mul_smul, hT, smul_zero]
  · show _ ∈ Ideal.span {lam ^ a}
    simp only [tableLineDegreeTwo.actExt]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))

theorem kerExt_kill (lam : O) (a : ℕ) (hX : ∀ x : X, lam ^ a • x = 0)
    (m : ((↥L.T ⊗[O] X) × O) ⧸ tableLineDegreeTwo.kerExt L X lam a) : lam ^ a • m = 0 := by
  have hT : ∀ m : ↥L.T ⊗[O] X, lam ^ a • m = 0 := by
    intro m
    induction m using TensorProduct.induction_on with
    | zero => simp
    | tmul t x => rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, hX, TensorProduct.tmul_zero]
    | add u v hu hv => rw [smul_add, hu, hv, add_zero]
  obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  refine ⟨?_, ?_⟩
  · show _ ∈ (⊥ : Submodule O (↥L.T ⊗[O] X))
    rw [Submodule.mem_bot]
    exact hT p.1
  · show _ ∈ Ideal.span {lam ^ a}
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

def extRep (hz : tableLineDegreeTwo.IsCoc L X χ₁ z) (lam : O) (a : ℕ) (hX : ∀ x : X, lam ^ a • x = 0) :
    Representation O G (((↥L.T ⊗[O] X) × O) ⧸ tableLineDegreeTwo.kerExt L X lam a) where
  toFun g := (tableLineDegreeTwo.kerExt L X lam a).mapQ _ (actExtL L X χ₁ z g) (actExtL_ker L X χ₁ z lam a hX g)
  map_one' := by
    apply Submodule.linearMap_qext
    ext p
    · simp [actExtL_one hz]
    · simp [actExtL_one hz]
  map_mul' g h := by
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro p
    simp [actExtL_mul hz, Module.End.mul_apply]

theorem extRep_mk (hz : tableLineDegreeTwo.IsCoc L X χ₁ z) (lam : O) (a : ℕ) (hX : ∀ x : X, lam ^ a • x = 0) (g : G)
    (p : (↥L.T ⊗[O] X) × O) :
    extRep L X χ₁ z hz lam a hX g (Submodule.Quotient.mk p) = Submodule.Quotient.mk (tableLineDegreeTwo.actExt L X χ₁ z g p) := by
  rw [← actExtL_apply]; rfl

end Ext
end GlobalTheory.UseLoc.Cases.AdmW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmH0Setup
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink.PowerSmulVanishing

theorem pow_smul_eq_zero_of_le {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (p : O) {a b : ℕ}
    (h : a ≤ b) {x : M} (hx : p ^ a • x = 0) : p ^ b • x = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, mul_comm, ← smul_smul, hx, smul_zero]

set_option maxHeartbeats 1600000 in

theorem main : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), Setup L nch HW X C₂ → ∀ i, TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.SplitK D (D.nd.l i) → ∀ π ∈ D.nd.Zgood i, EmbeddingTypes.H0ColumnLengthBound i (X.ρ i) π (X.dc i) (X.c0 i) := by
  intro hP D L P nch HW F Cm X C₂ hS i hTw hg hRA hSp π hπ
  have hJ : AdmissibleParameterJ.JumpConditions L := GlobalTheory.JumpStatement.holds_all D L (hS.facts.admJ L hS.par)
  obtain ⟨M0, h0, hl2, hJC⟩ := GlobalTheory.HubX.jointCondH0all_canon hP.font D L HW (rowC C₂) X hS.canon hJ
    hS.facts.Conclusion1.1 (GlobalTheory.FontaineAdm.fontaineProperties_all_places D) i hTw hg hRA hSp π hπ
  have hlq : D.nd.l i ≠ D.host.q := fun h => hRA.2.1 (Or.inl h)
  have hld : D.nd.l i ≠ D.host.d := fun h => hRA.2.1 (Or.inr h)
  intro _ u hu w hw hconj C hC L2 hstd
  obtain ⟨-, hall⟩ := hJC u hu w hw hconj
  have hur : (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i) := GlobalTheory.HubLoc.kw_le_Kur_all D i (fun h => hRA.1 (Or.inl h)) hlq hld w hw
  have hg1 : Good (D.nbr i w hw).Kw 1 C.LL := hC.good_one hl2 (le_trans (le_inf le_rfl hur) le_sup_left)
  have hT2c : Continuous fun g => T2O D.nd i (X.ρ i) π g :=
    GlobalTheory.HTW.RecS.Model.continuous_twistedDual_rhoO i (X.ρ i) π (hS.canon.fam.cont i π)
  have hc : ∀ v, Continuous fun g => matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (T2O D.nd i (X.ρ i) π)) g v :=
    fun v => (GlobalTheory.CrysChiOne.locC_cont' C _ hT2c).matrix_mulVec continuous_const
  obtain ⟨hcr, hwin, hnj, hc0⟩ := hall C hg1 hc L2
  have hW := GlobalTheory.T.crystallineLatticeWachModuleExists_proof D HW F Cm (D.nd.l i) (D.nbr i w hw).Kw 1 C.LL hg1 (GlobalTheory.HubX.tTwoLocalLattice D i (X.ρ i) π C hc L2) M0 h0 hcr hwin
  have hkill := GlobalTheory.T.torsion_exponent_kills_invariants_of_good hP.bk hP.tate hP.euler D HW F Cm (D.nd.l i) (D.nbr i w hw).Kw 1 C.LL hg1 M0 h0
    (GlobalTheory.HubX.tTwoLocalLattice D i (X.ρ i) π C hc L2) hW hnj
  unfold EmbeddingTypes.lenInvD
  haveI : IsDiscreteValuationRing ↥(OL C.LL) := Formalism.BasicNotions.Examples₂.LB.OL_dvr C.LL
  haveI : IsFractionRing ↥(OL C.LL) ↥C.LL.1 := Formalism.BasicNotions.Examples₂.LB.OL_frac C.LL
  refine EmbeddingTypes.len_le_of_kill (Br.PD D.loc D.nbr i w hw) L2.T hstd _ (X.c0 i u) ?_
  intro x hx
  exact pow_smul_eq_zero_of_le _ hc0 (hkill x fun g => hx g)

end GlobalTheory.NLink.PowerSmulVanishing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleParametersFamilyConst
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem mul_rpow_self_le {x c C : ℝ} (hx : 1 ≤ x) (hc : c ≤ C) (hC : 0 ≤ C) :
    c * x ^ c ≤ C * x ^ C := by
  have h0 : 0 ≤ x ^ c := Real.rpow_nonneg (by linarith) _
  calc c * x ^ c ≤ C * x ^ c := mul_le_mul_of_nonneg_right hc h0
    _ ≤ C * x ^ C := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx hc) hC

theorem admissible_parameters_design_family : ∀ {eps : ℝ} (Fm : FamP eps), ∃ C x0 : ℝ, 1 ≤ C ∧ ∀ x ≥ x0, ∀ (hx : Fm.x1 < x)
    (i : Fm.Ix x), TwistedPlaces.ParametersPolynomiallyBounded (Fm.L x i) C (Fm.params x hx i) := by
  intro eps Fm
  obtain ⟨C1, y1, h1⟩ := GlobalTheory.T.log_hostClassNumber_le_scale_pow_family Fm
  obtain ⟨C2, y2, h2⟩ := GlobalTheory.T.exists_log_card_restRows_le_pow_mul_length Fm
  set C : ℝ := max 1 (max (Fm.PK.getD 7 0) (max (Fm.PK.getD 19 0) (max (9 / 2 + 10 * eps + eps / 100)
    (max (2 + 8 * eps + eps / 100) (max (Fm.Ct + eps / 100) (max C1 C2)))))) with hCdef
  have hC1 : 1 ≤ C := le_max_left _ _
  have hC0 : 0 ≤ C := by linarith
  have hCLw : Fm.PK.getD 7 0 ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCYL : Fm.PK.getD 19 0 ≤ C :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hrest : max (9 / 2 + 10 * eps + eps / 100)
      (max (2 + 8 * eps + eps / 100) (max (Fm.Ct + eps / 100) (max C1 C2))) ≤ C :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  have hK : 9 / 2 + 10 * eps + eps / 100 ≤ C := le_trans (le_max_left _ _) hrest
  have hN : 2 + 8 * eps + eps / 100 ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hrest
  have hT : Fm.Ct + eps / 100 ≤ C :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hrest
  have hc12 : max C1 C2 ≤ C :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hrest
  have hCC1 : C1 ≤ C := le_trans (le_max_left _ _) hc12
  have hCC2 : C2 ≤ C := le_trans (le_max_right _ _) hc12
  refine ⟨C, max y1 y2, hC1, fun x hxy hx i => ?_⟩
  have hx1 : 1 ≤ x := le_of_lt (lt_trans Fm.one_lt_family_threshold hx)
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i hx
  have heps : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  have hPK := Fm.params_K x hx i
  obtain ⟨sN, -, sK, -, sT, -, -, -, -, -, -, sDe2, -⟩ := Fm.sizes x hx i
  unfold SizeN szTh at sN
  unfold SizeK szTh at sK
  unfold SizeT szTh at sT
  unfold SizeDe2 at sDe2
  rw [hsx, heps] at sN sK
  rw [hsx, heps, Fm.Ct_eq x i] at sT
  have hmono : ∀ a : ℝ, a ≤ C → x ^ a ≤ x ^ C := fun a ha => Real.rpow_le_rpow_of_exponent_le hx1 ha
  have hLg : 0 ≤ (Fm.L x i).sc.L := by
    unfold Scale.L
    exact Real.rpow_nonneg (le_trans zero_le_one (le_of_lt (Fm.L x i).sc.one_lt_alt)) _
  unfold TwistedPlaces.ParametersPolynomiallyBounded
  refine ⟨?_, ?_, ?_, ?_, ?_, sDe2, ?_, ?_⟩
  · have e : (Fm.params x hx i).CLw = Fm.PK.getD 7 0 := by rw [← hPK]; rfl
    rw [e]; exact hCLw
  · have e : (Fm.params x hx i).CYL = Fm.PK.getD 19 0 := by rw [← hPK]; rfl
    rw [e]; exact hCYL
  · rw [hsx]; exact le_trans sK.2 (hmono _ hK)
  · rw [hsx]; exact le_trans sN.2 (hmono _ hN)
  · rw [hsx]; exact le_trans sT.2 (hmono _ hT)
  · rw [hsx]
    exact le_trans (h1 x (le_trans (le_max_left _ _) hxy) hx i) (mul_rpow_self_le hx1 hCC1 hC0)
  · rw [hsx]
    refine le_trans (h2 x (le_trans (le_max_right _ _) hxy) hx i) ?_
    exact mul_le_mul_of_nonneg_right (mul_rpow_self_le hx1 hCC2 hC0) hLg

end GlobalTheory.NLink
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientSubContinuitySetup
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section
namespace GlobalTheory.NLink.AmbSub

variable {D : D7}

theorem WpO_cont (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hρ : Continuous fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) :
    Continuous fun g => WpO D.nd i ρ π g := by
  have h1 : Continuous fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i) := by
    have e : (fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i)) =
        fun g => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
      funext g
      rw [map_inv]
      rfl
    rw [e]
    exact (D.nd.chi_cont i 1).comp continuous_inv
  exact h1.smul hρ

theorem main : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), Setup L nch HW X C₂ → ∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, EmbeddingTypes.ambSub i (X.r i) π (X.dc i) ∧ EmbeddingTypes.ambCont i (X.r i) (X.ρ i) π ∧ EmbeddingTypes.ColumnH0Vanishing i (X.ρ i) π (X.dc i) := by
  intro hP D L P nch HW F Cm X C₂ hSet i hi π hπ
  have hS := GlobalTheory.T.set_point_good hP D L P nch HW F Cm X C₂ hSet i hi π hπ
  obtain ⟨_, hG2, _, _, _, _, _, _, hCont, _, _, _, _, _, hFont, _, _⟩ := hS
  have hρ : Continuous fun g => ((X.ρ i π g : GL (Fin D.R.r) (D.nd.O i)) :
      Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)) := hSet.canon.fam.cont i π
  have hcx : ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i) (v : Fin D.R.nV → ↥C.LL.1),
      Continuous fun g => (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x) g).mulVec v :=
    fun w hw C x v => locC_cont D i _ (rTwO_cont D i (X.r i) hCont x) w hw C v
  have hcr : ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i),
      IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x))) := by
    intro w hw C x
    rw [locC_rTwO]
    exact (hG2 w hw C).2 x
  refine ⟨?_, ?_, ?_⟩
  · intro _ _ w hw _ C A hA
    have hJ : ∀ x τ, JumpsInV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x))) τ
        {a | IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) π))) τ a} := by
      intro x τ
      refine jumps_of_multV_eq (O := ↥(OL C.LL)) (fun x => TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x)) (hcx w hw C)
        (hFont w hw C) x π (hcr w hw C x) (hcr w hw C π) τ (fun a => ?_)
      rw [locC_rTwO, locC_rTwO]
      exact (hG2 w hw C).1.2.1 τ x π a
    exact subsum_crys (fun x => TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x)) (hcx w hw C) (hFont w hw C)
      (hcr w hw C) hJ A hA
  · intro w hw C
    refine ⟨fun x v => hcx w hw C x v, fun _ => ⟨fun v => ?_, fun v => ?_⟩⟩
    · exact locC_cont D i _ (WpO_cont i (X.ρ i) π hρ) w hw C v
    · exact locC_cont D i _ (GlobalTheory.TwistedDualLoc.continuous_T2O D i (X.ρ i) π hρ) w hw C v
  · intro _ w hw _ C
    exact (hG2 w hw C).1.2.2.2.2.2.1

end GlobalTheory.NLink.AmbSub
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryDescentEnlargementCoefficientsStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coboundary_descent_enlargement_coefficients : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (z : Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T),
    (fun g => liftQ C.le k (z g)) ∈ BD (latC C (locOC C M)) → z ∈ BD (Br.locLat D.nbr i w hw M) := by
  first | exact @GlobalTheory.UseLoc.DescBD.main | exact GlobalTheory.UseLoc.DescBD.main | (intros; apply GlobalTheory.UseLoc.DescBD.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CurveOverOfRayIn
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TwistRat.Field

theorem curveOver_of_rayIn : GlobalTheory.Published.RayClassFieldSt → ∀ (D : D7) (Q : Par D), Q.PinHost → ∀ (N : ℕ), 3 ≤ N →
    ∀ (Fc : IntermediateField ℚ ℂ) (σ : Fc →+* ℂ), RayIn D N σ.fieldRange → GlobalTheory.CompRat.CurveOver Q.H Fc N := by
  intro _ D Q hP N hN Fc σ hray
  obtain ⟨L, _, _, _, _, hL, j, -, hjv⟩ := hray

  have hC : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (algebraMap D.host.K L) N :=
    GlobalTheory.FieldSize.RayNorm.containsRayField_of_ray N hL.1 fun I hI hc => (hL.2.2 I hI hc).1

  let S : IntermediateField ℚ ℂ := σ.toRatAlgHom.fieldRange
  let e : Fc ≃ₐ[ℚ] S := AlgEquiv.ofInjectiveField σ.toRatAlgHom
  have hS : ∀ x, j x ∈ S := fun x => by
    obtain ⟨y, hy⟩ := hjv x
    exact ⟨y, hy⟩
  let j' : L →+* S := j.codRestrict S hS
  let ψ : L →+* ℂ := (algebraMap Fc ℂ).comp (((e.symm : S ≃+* Fc) : S →+* Fc).comp j')
  have hψ : ψ.toRatAlgHom.fieldRange ≤ Fc := by
    rintro _ ⟨x, rfl⟩
    exact (e.symm (j' x)).2

  have hsq : ∃ a : D.host.K, a ^ 2 = -(Q.H.d : D.host.K) := by
    refine ⟨⟨D.host.sqrtMinusD, Formalism.L2.Pj.LPb.sqrtMinusD_mem_K D⟩, ?_⟩
    rw [hP.1]
    apply Subtype.ext
    have hb : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := D.host.sqrtMinusD_sq
    simpa using hb
  obtain ⟨hW, hrt⟩ := GlobalTheory.FieldSize.WeberTransport.weberIn_of_containsRayField D.host.E Q.H D.host.K L
    (algebraMap D.host.K L) ψ (Formalism.L2.Pj.LPb.finrank_K D) hsq N hN hC
  refine (GlobalTheory.FinalJoin.CurveField.curveOver_of_weberIn D.host.E Q.H Fc N (by omega)).1 (hψ hrt) fun Λ hΛ => ?_
  obtain ⟨h1, h2⟩ := hW Λ hΛ
  exact ⟨hψ h1, fun s hs => hψ (h2 s hs)⟩

end GlobalTheory.TwistRat.Field
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroOfLabels
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DepthZeroTame

theorem main : GlobalTheory.NRows.Hypotheses₂ → GlobalTheory.Published.DepthZeroWild → GlobalTheory.Published.DepthZeroSupport → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL)
    (D : D7) (P : Pin hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → LabAll D P.T → ChiTOk D P.cf →
    DepthZ D := by
  intro hP hW hS hL D P hrow hlab hchi
  obtain ⟨S, hT, hLaws, -⟩ := GlobalTheory.T.exists_true_reading_with_laws hP.fin hL D P hrow
  have hfix : ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k),
      TameLP D (D.naut.locV i PI (D.naut.plGw k v)) := by
    intro i PI k v
    have hw := GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v
    have htame := GlobalTheory.PendOf.isTame_mu_plGw hL D P S hT i k v hw
    have hTB := GlobalTheory.T.tame_block_type_at_split_place hL D P S hT i _ hw ⟨k, D.naut.plGw_over k v⟩ htame
    obtain ⟨x, hx0, hx⟩ := hTB.2 PI
    have hfixd : x ∈ GlobalTheory.PRep.fixed ((S i _ hw).rep PI).π
        (GlobalTheory.SplitWeil.KOne ((D.naut.plGw k v).adicCompletion D.host.E) (Fin (D.R.r + D.R.t))) := by
      intro h
      have h' : ((S i _ hw).rep PI).π h x = x := GlobalTheory.JacBlock.KOne_le_stab htame hx h.2
      simpa using h'
    have hwild := GlobalTheory.DepthZeroLoc.main hP.bz hW hS hL D _ _ ((S i _ hw).rep PI) ⟨x, hfixd, hx0⟩
    intro σ hσI hσW
    have hd : D.naut.lpDim (D.naut.locV i PI (D.naut.plGw k v)) = D.R.r + D.R.t := by
      rw [← P.T.dim, (S i _ hw).locV PI, (hLaws i _ hw).dim]
    rw [P.T.inePol _ _ σ hσI, (S i _ hw).locV PI, hT.rc i _ hw, hwild σ hσW, hd]
  intro i PI k w hw
  obtain ⟨v, rfl | hc⟩ := GlobalTheory.TypePlaceCover.place_cover D k w hw
  · exact hfix i PI k v
  · exact ((GlobalTheory.T.conj_dual_of_labels hP hL D P hlab) i PI k v w hc).2.1 (hfix i PI k v)

end GlobalTheory.DepthZeroTame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoverDictionaryAdelicElementComponentStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coverDictionary_adelic_element_component : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ k₂ : C.U₂.Comp, ∃ h : GA D (T.V j σ), (C.dict₂ h).1 = k₂ := by
  first | exact @GlobalTheory.CoverOnto.exists_dict₂_comp | exact GlobalTheory.CoverOnto.exists_dict₂_comp | (intros; apply GlobalTheory.CoverOnto.exists_dict₂_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFieldExtensionOfIntegralRetractionStatement
section
open Formalism.MainNotions.N Formalism.BasicNotions.Loc GlobalTheory.UseLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fieldExtension_of_integral_retraction : ∀ {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL)), (∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) → r 1 = 1 → ∃ p : ↥LL'.1 →ₗ[ℚ_[l]] ↥LL.1, (∀ (a : ↥LL.1) (x : ↥LL'.1), p (IntermediateField.inclusion h a * x) = a * p x) ∧ ∀ x : ↥(OL LL'), p (x : ↥LL'.1) = ((r x : ↥(OL LL)) : ↥LL.1) := by
  first | exact @GlobalTheory.UseLoc.extRet_exists | exact GlobalTheory.UseLoc.extRet_exists | (intros; apply GlobalTheory.UseLoc.extRet_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralRetractionLocalIntegersStatement
section
open Formalism.MainNotions.N Formalism.BasicNotions.Loc GlobalTheory.UseLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_retraction_localIntegers : ∀ {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1), ∃ r : ↥(OL LL') →+ ↥(OL LL), (∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) ∧ r 1 = 1 := by
  first | exact @GlobalTheory.UseLoc.exists_intRetraction | exact GlobalTheory.UseLoc.exists_intRetraction | (intros; apply GlobalTheory.UseLoc.exists_intRetraction <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelCoverUniformisationDictionaryStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelCover_uniformisation_dictionary : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ (c' : Coeff T.Q.l) (hle : T.Q.c.F ≤ c'.F) (d : DeltaDat (T.Q.Xo j) c' 0) (σ₂ : d.c₂.F →+* ℂ), d.IsLev → d.l₂.A = 1 → σ₂.comp ((d.eF : c'.F →+* d.c₂.F).comp (incF T.Q.c c' hle)) = σ → ∃ (U₂ : Unf d.Xo₂ d.c₂ σ₂ D.R.r) (dict₂ : GA D (T.V j σ) → Σ k, Frame (U₂.X k).Ψ D.R.r), ∀ cc₂, (⟨c', hle, d, σ₂, U₂, dict₂, cc₂⟩ : Cover T j σ).IsUnif := by
  first | exact @GlobalTheory.CoverUnif.exists_unf_dict | exact GlobalTheory.CoverUnif.exists_unf_dict | (intros; apply GlobalTheory.CoverUnif.exists_unf_dict <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCoverFormsMulComponentFunctionStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCover_forms_mul_componentFunction : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ N : ℕ, 0 < N → C.d.l₂.M ∣ N → (WeberIn T.Q.H C.d.c₂.F N ∨ CurveOver T.Q.H C.d.c₂.F N) → ∀ w : GA D (T.V j σ) → C.d.c₂.F, (∀ h h' : GA D (T.V j σ), finHom (T.V j σ) h = finHom (T.V j σ) h' → w h = w h') → (∀ γ ∈ GQ (T.V j σ), ∀ h, w (γ * h) = w h) → (∀ u : GA D (T.V j σ), gLat (T.V j σ) u = latHat (T.V j σ) → FinCong (T.V j σ) C.d.l₂.M u → ∀ h, w (h * u) = w h) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ φ ∈ C.ratForms a n, (fun h => C.σ₂ (w h) * φ h) ∈ C.ratForms a n) ∧ ∀ S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F)), (∀ la ∈ S, ∀ h, la.valuation C.d.c₂.F (w h) ≤ 1) → ∀ φ ∈ C.intForms a n S, (fun h => C.σ₂ (w h) * φ h) ∈ C.intForms a n S := by
  first | exact @GlobalTheory.CoverComp.forms_mul_comp | exact GlobalTheory.CoverComp.forms_mul_comp | (intros; apply GlobalTheory.CoverComp.forms_mul_comp <;> assumption)
end

