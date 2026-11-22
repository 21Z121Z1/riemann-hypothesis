import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1132
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0825
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0070
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchingLatticesMatchesSphericalOps
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignSecond
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1120
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0149
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1121

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrincipalIdealRingStalk
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB
open GlobalTheory.Twist (resM germ_resM)

namespace GlobalTheory.VB

variable {X : Scheme.{0}} [IsIntegral X] {F : X.Modules}

theorem IsTorsionFree.isTorsionFree_stalk (h : IsTorsionFree F) (x : X) :
    Module.IsTorsionFree (X.presheaf.stalk x) (F.presheaf.stalk x :) := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun a t hat => ?_
  obtain ⟨V, hV, a, rfl⟩ := X.presheaf.exists_germ_eq a
  obtain ⟨T, hT, hxT, t, rfl⟩ := Twist.exists_germ_eq_of_mem hV t
  rw [← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hT) x hxT a] at hat ⊢
  generalize X.presheaf.map (homOfLE hT).op a = b at hat ⊢
  by_cases hb : b = 0
  · exact Or.inl (by rw [hb, map_zero])
  · right
    rw [← QCoh.germ_smul, ← map_zero (ConcreteCategory.hom (F.presheaf.germ T x hxT))] at hat
    obtain ⟨W, hxW, i₁, i₂, e⟩ := F.presheaf.germ_eq x hxT hxT _ _ hat
    rw [map_zero, Scheme.Modules.map_smul] at e
    have : Nonempty W := ⟨⟨x, hxW⟩⟩
    have hb' : X.presheaf.map i₁.op b ≠ 0 := fun h0 =>
      hb (map_injective_of_isIntegral X i₁ (h0.trans (map_zero _).symm))
    have := h.eq_zero_of_smul hb' e
    rw [← TopCat.Presheaf.germ_res_apply F.presheaf i₁ x hxW t, this, map_zero]

theorem finrank_stalk_eq_genRank [F.IsQuasicoherent] (x : X) :
    Module.finrank (X.presheaf.stalk x) (F.presheaf.stalk x :) = genRank F := by
  obtain ⟨U, hU, hx⟩ := QCoh.exists_affine_mem x
  have : Nonempty U := ⟨⟨x, hx⟩⟩
  have key (y : U) : Module.finrank (X.presheaf.stalk (y : X)) (F.presheaf.stalk (y : X) :) =
      Module.finrank Γ(X, U) Γ(F, U) := by
    have := hU.isLocalization_stalk y
    have := QCoh.isLocalizedModule_germLinear F hU y
    have hp := (hU.primeIdealOf y).asIdeal.primeCompl_le_nonZeroDivisors
    rw [IsLocalization.finrank_eq _ _ hp, IsLocalizedModule.finrank_eq _ (QCoh.germLinear F y) hp]
  exact (key ⟨x, hx⟩).trans (key ⟨_, genericPoint_mem hx⟩).symm

theorem IsSmoothProjCurve.isPrincipalIdealRing_stalk {k : Type} [Field k] [Algebra k Γ(X, ⊤)]
    (hC : IsSmoothProjCurve k X) (x : X) : IsPrincipalIdealRing (X.presheaf.stalk x) := by
  have := hC.smooth
  have := hC.toIsProjCurve.isNoetherian
  have hn := (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (strHom k X) (fun y => by
    have hf : IsField ((Sp k).presheaf.stalk y) := by
      have : Ring.KrullDimLE 0 ((Sp k).presheaf.stalk y) :=
        krullDimLE_of_coheight_le (by
          have : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
          exact (Order.coheight_eq_zero.2 (fun b _ => (Subsingleton.elim b y).le)).le)
      have : IsIntegral (Sp k) := inferInstanceAs (IsIntegral (Spec (.of k)))
      exact Ring.KrullDimLE.isField_of_isDomain
    letI := hf.toField
    exact ⟨inferInstance, inferInstance⟩) x).2
  have h1 : Ring.KrullDimLE 1 (X.presheaf.stalk x) := by
    refine krullDimLE_of_coheight_le ?_
    have e : topologicalKrullDim X = Order.krullDim X :=
      Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))
    have := Order.coheight_le_krullDim x
    rw [← e, hC.dim_eq] at this
    exact_mod_cast this
  have h3 : IsIntegrallyClosed (X.presheaf.stalk x) ∧ ∀ P : Ideal (X.presheaf.stalk x),
      P ≠ ⊥ → P.IsPrime → P = IsLocalRing.maximalIdeal _ :=
    ⟨hn, fun P h0 hP => IsLocalRing.eq_maximalIdeal
      (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp h1 P h0 hP)⟩
  exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (X.presheaf.stalk x)).out 0 3).mpr h3

theorem isVB_of_isTorsionFree_and_isSubbundle_satι : ∀ (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] [IsIntegral C], IsSmoothProjCurve k C → (∀ (F : C.Modules) [GlobalTheory.QCoh.IsFiniteQC F], IsTorsionFree F → IsVB F (genRank F)) ∧ ∀ (F G : C.Modules) (i : G ⟶ F) [GlobalTheory.QCoh.IsFiniteQC F], IsSubbundle (satι i) := by
  intro k _ C _ _ hC
  have := hC.toIsProjCurve.isNoetherian
  have H : ∀ (F : C.Modules) [GlobalTheory.QCoh.IsFiniteQC F], IsTorsionFree F → IsVB F (genRank F) := by
    intro F _ hF
    refine GlobalTheory.T.vector_bundle_of_free_stalks C F _ fun x => ?_
    have := hC.isPrincipalIdealRing_stalk x
    have := hF.isTorsionFree_stalk x
    exact ⟨Module.finBasisOfFinrankEq _ _ (finrank_stalk_eq_genRank x)⟩
  exact ⟨H, fun F G i _ => ⟨inferInstance, _, H _ (isSaturated_satι i)⟩⟩

end GlobalTheory.VB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCColumnLatticeOfOrthonormalFrame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FunObj.OrthoFrame

theorem isSelfDualC_colLat_of_orthonormal : ∀ {D : D7} (S : HSp D) (B : GL (Fin S.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * S.gram * B.1 = 1 → IsSelfDualC S (colLat B) := by
  intro D S B hB
  exact GlobalTheory.FunObj.VecEx.isSelfDualC_colLat S B hB

end GlobalTheory.FunObj.OrthoFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNatCastFrameCoeffRingNotDvd
section
open GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative

namespace GlobalTheory.ExpFrame.Frame

theorem isUnit_natCast_of_not_dvd : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [DecidableEq ι] (N : ℕ) (F : Frame l ι N), F.Ok →
    ∀ n : ℕ, ¬ l ∣ n → IsUnit (n : F.O) := by
  intro l _ ι _ N F hF n hn
  obtain ⟨hinj, L, _, hrange⟩ := hF.ring
  have hnorm : ‖(n : PadicAlgCl l)‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)) n, PadicAlgCl.norm_extends,
      Padic.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).2 hn
  have hne : (n : PadicAlgCl l) ≠ 0 := by
    intro h; rw [h, norm_zero] at hnorm; exact zero_ne_one hnorm
  have hmem : (n : PadicAlgCl l)⁻¹ ∈ Set.range F.emb := by
    rw [hrange]
    refine ⟨?_, ?_⟩
    · exact L.inv_mem (L.natCast_mem n)
    · rw [norm_inv, hnorm, inv_one]
  obtain ⟨y, hy⟩ := hmem
  have h1 : (n : F.O) * y = 1 := by
    apply hinj
    rw [map_mul, map_natCast, hy, map_one, mul_inv_cancel₀ hne]
  exact IsUnit.of_mul_eq_one y h1

end GlobalTheory.ExpFrame.Frame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchingLatticesMatchesSphericalOpsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isometry_matching_lattices_matches_spherical_ops : ∀ {D : D7} (V V' : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (β' : GL (Fin V'.rank) (Lev.EAf D)) (Pg : Finset (Pl D.host.E)) (j : Matrix (Fin V'.rank) (Fin V.rank) (Lev.EAf D)) (Φ : GfC V ≃ₜ* GfC V') (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)) (N N' : ℕ), IsBaseFrame V β Λ N → IsBaseFrame V' β' Λ' N' → GlobalTheory.CuspMult.IsFinIso V V' β β' Pg j Φ → ∀ (P : Pl D.host.E), ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ((N' : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ∀ (d : List ℤ) (B : Finset (GfC V)), GlobalTheory.Hk3.SphOp V P d (B.map ⟨Subtype.val, Subtype.val_injective⟩) ↔ GlobalTheory.Hk3.SphOp V' P d ((B.map Φ.toEquiv.toEmbedding).map ⟨Subtype.val, Subtype.val_injective⟩) := by
  first | exact @GlobalTheory.SphTrans.sphOp_iff | exact GlobalTheory.SphTrans.sphOp_iff | (intros; apply GlobalTheory.SphTrans.sphOp_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JKInvOfTriv
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial

namespace GlobalTheory.ExpFrame.HeckeMod

variable {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} (F : Frame l ι N) (lam : ι → ℕ → ℕ)
  (jK : F.K →* alg F.O N lam) (W : Type) [AddCommGroup W] [Module F.O W] [Module (alg F.O N lam) W]
  [IsScalarTower F.O (alg F.O N lam) W]

theorem mem_forms {f : F.G → W} : f ∈ Forms F.O (A := alg F.O N lam) F.Γ jK W ↔
    ∀ (γ : F.Γ) (g : F.G) (κ : F.K), f ((γ : F.G) * g * κ) = jK κ⁻¹ • f g := Iff.rfl

variable {F lam jK} in

theorem jK_eq (hJ : F.IsJ lam jK) {κ κ' : F.K} (h1 : F.kap κ' = F.kap κ) (h2 : F.chi κ' = F.chi κ) : jK κ' = jK κ := by
  rw [hJ κ', hJ κ, h1, h2]

variable {F lam jK} in
theorem jK_inv_congr {κ κ' : F.K} (h : jK κ' = jK κ) : jK κ'⁻¹ = jK κ⁻¹ := by
  have e1 : jK κ'⁻¹ * jK κ' = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have e2 : jK κ * jK κ⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  calc jK κ'⁻¹ = jK κ'⁻¹ * (jK κ * jK κ⁻¹) := by rw [e2, mul_one]
    _ = (jK κ'⁻¹ * jK κ') * jK κ⁻¹ := by rw [h, mul_assoc]
    _ = jK κ⁻¹ := by rw [e1, one_mul]

theorem grpA_one : grpA F.O N lam 1 = 1 := Subtype.ext (by simp [grpA, grp])

variable {F lam jK} in

theorem jK_inv_of_triv (hJ : F.IsJ lam jK) {κ : F.K} (h1 : F.kap κ = 1) (h2 : F.chi κ = 1) : jK κ⁻¹ = 1 := by
  have : jK κ = jK 1 := by rw [hJ κ, h1, h2, map_one, grpA_one]; simp
  rw [jK_inv_congr this, inv_one, map_one]

def heckeFn (i : F.I) (f : F.G → W) : F.G → W := fun g => F.cst i • ∑ s ∈ F.tr i, f (g * s)

variable {F lam jK W}

theorem heckeFn_mem (hOk : F.Ok) (hJ : F.IsJ lam jK) (i : F.I) {f : F.G → W}
    (hf : f ∈ Forms F.O (A := alg F.O N lam) F.Γ jK W) : heckeFn F W i f ∈ Forms F.O (A := alg F.O N lam) F.Γ jK W := by
  rw [mem_forms] at hf ⊢
  intro γ g κ
  obtain ⟨σ, hσ⟩ := hOk.perm i κ
  have key : ∀ s : F.tr i, f ((γ : F.G) * g * κ * s) = jK κ⁻¹ • f (g * (σ s : F.G)) := by
    intro s
    obtain ⟨κ', h1, h2, h3⟩ := hσ s
    have e : (γ : F.G) * g * κ * s = γ * (g * σ s) * κ' := by
      rw [mul_assoc ((γ : F.G) * g) (κ : F.G) (s : F.G), h1]; simp only [mul_assoc]
    rw [e, hf γ (g * σ s) κ', jK_inv_congr (jK_eq hJ h2 h3)]
  simp only [heckeFn]
  rw [← Finset.sum_coe_sort (F.tr i), ← Finset.sum_coe_sort (F.tr i)]
  simp_rw [key]
  rw [← Finset.smul_sum, Equiv.sum_comp σ (fun s : F.tr i => f (g * (s : F.G))), smul_comm]

theorem heckeFn_comm (hOk : F.Ok) (hJ : F.IsJ lam jK) (i j : F.I) {f : F.G → W}
    (hf : f ∈ Forms F.O (A := alg F.O N lam) F.Γ jK W) :
    heckeFn F W i (heckeFn F W j f) = heckeFn F W j (heckeFn F W i f) := by
  rw [mem_forms] at hf
  funext g
  obtain ⟨σ, hσ⟩ := hOk.comm i j
  have key : ∀ x : F.tr i × F.tr j, f (g * x.1 * x.2) = f (g * (σ x).1 * (σ x).2) := by
    intro x
    obtain ⟨hK, h1, h2⟩ := hσ x
    have e : g * x.1 * x.2 = ((1 : F.Γ) : F.G) * (g * (σ x).1 * (σ x).2) * (⟨_, hK⟩ : F.K) := by
      simp only [OneMemClass.coe_one, one_mul, mul_assoc, mul_inv_cancel_left]
    rw [e, hf, jK_inv_of_triv hJ h1 h2, one_smul]
  have hsum : ∀ (a b : F.I), heckeFn F W a (heckeFn F W b f) g =
      F.cst a • F.cst b • ∑ x : F.tr a × F.tr b, f (g * x.1 * x.2) := by
    intro a b
    simp only [heckeFn, Fintype.sum_prod_type, Finset.smul_sum]
    rw [← Finset.sum_coe_sort (F.tr a)]
    refine Fintype.sum_congr _ _ fun s => ?_
    rw [← Finset.sum_coe_sort (F.tr b)]
  rw [hsum, hsum, smul_comm (F.cst i) (F.cst j)]
  congr 2
  rw [Fintype.sum_congr _ _ key, Equiv.sum_comp σ (fun y : F.tr j × F.tr i => f (g * y.1 * y.2))]

end GlobalTheory.ExpFrame.HeckeMod

namespace GlobalTheory.ExpFrame.HeckeMod

variable {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} {F : Frame l ι N} {lam : ι → ℕ → ℕ}
  {jK : F.K →* alg F.O N lam} {W : Type} [AddCommGroup W] [Module F.O W] [Module (alg F.O N lam) W]
  [IsScalarTower F.O (alg F.O N lam) W]

def op (hOk : F.Ok) (hJ : F.IsJ lam jK) (i : F.I) :
    Module.End F.O (Forms F.O (A := alg F.O N lam) F.Γ jK W) where
  toFun f := ⟨heckeFn F W i f, heckeFn_mem hOk hJ i f.2⟩
  map_add' f f' := by
    ext g
    simp [heckeFn, Finset.sum_add_distrib, smul_add]
  map_smul' c f := by
    ext g
    simp [heckeFn, Finset.smul_sum, smul_comm (F.cst i) c]

theorem op_comm (hOk : F.Ok) (hJ : F.IsJ lam jK) (i j : F.I) :
    (op (W := W) hOk hJ i) * op hOk hJ j = op hOk hJ j * op hOk hJ i := by
  ext f : 1
  exact Subtype.ext (heckeFn_comm hOk hJ i j f.2)

end GlobalTheory.ExpFrame.HeckeMod

namespace GlobalTheory.ExpFrame.HeckeMod

variable {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} {F : Frame l ι N} {lam : ι → ℕ → ℕ}
  {jK : F.K →* alg F.O N lam} {W : Type} [AddCommGroup W] [Module F.O W] [Module (alg F.O N lam) W]
  [IsScalarTower F.O (alg F.O N lam) W]

def heckeAlg (hOk : F.Ok) (hJ : F.IsJ lam jK) : F.T →ₐ[F.O] Module.End F.O (Forms F.O (A := alg F.O N lam) F.Γ jK W) :=
  letI : CommRing (Algebra.adjoin F.O (Set.range (op (W := W) hOk hJ))) := Algebra.adjoinCommRingOfComm F.O (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact op_comm hOk hJ i j)
  (Algebra.adjoin F.O (Set.range (op (W := W) hOk hJ))).val.comp
    (MvPolynomial.aeval fun i => ⟨op hOk hJ i, Algebra.subset_adjoin ⟨i, rfl⟩⟩)

theorem heckeAlg_X (hOk : F.Ok) (hJ : F.IsJ lam jK) (i : F.I) : heckeAlg (W := W) hOk hJ (X i) = op hOk hJ i := by
  simp [heckeAlg]

theorem hecke_module : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ) (jK : F.K →* alg F.O N lam), F.Ok → F.IsJ lam jK → ∀ (W : Type) [AddCommGroup W] [Module F.O W] [Module (alg F.O N lam) W] [IsScalarTower F.O (alg F.O N lam) W], ∃ (_ : Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK W)) (_ : IsScalarTower F.O F.T (Forms F.O (A := alg F.O N lam) F.Γ jK W)), F.IsHecke lam jK W := by
  intro l _ ι _ _ N F lam jK hOk hJ W _ _ _ _
  letI inst : Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK W) := Module.compHom _ (heckeAlg (W := W) hOk hJ).toRingHom
  refine ⟨inst, ⟨fun c t f => ?_⟩, fun c f => ?_, fun i f g => ?_⟩
  · change heckeAlg hOk hJ (c • t) f = c • heckeAlg hOk hJ t f
    rw [map_smul, LinearMap.smul_apply]
  · change heckeAlg hOk hJ (C c) f = c • f
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, Module.algebraMap_end_apply]
  · change ((heckeAlg hOk hJ (X i) f : Forms F.O (A := alg F.O N lam) F.Γ jK W) : F.G → W) g = _
    rw [heckeAlg_X]
    rfl

end GlobalTheory.ExpFrame.HeckeMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignSecondStatement
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_isometry_sign_second : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (i : Fin D.R.m), VStd D i → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → LatIsom (Wc D i) Dw.EF ι → ∃ δ : ℤˣ, ∀ (t : T0) (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), PhiIs R i (RingHom.id ℂ) t ι (Mfr l₂ • ⊤) φ → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → l₂.Mb ≤ PP.asIdeal ∧ ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ (bad N : ℕ) (h : GA D (Vc D i)) (k : GA D (Wc D i)) (Λ : GenLat D.host.E (Vc D i).rank) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)), (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → SplitOffBad (Vc D i) bad h → (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → Λ.TrivAt l₂.M → Λ.LevOK N l₂.M → MarkAd l₂ (Wc D i) (rank_Wc i) ι k mk → ∀ (Y : (Fin (Vc D i).rank → LevQ Dw l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E) (γ : (Fin (Vc D i).rank → LevQ Dw l₂) → Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (u : (Fin (Vc D i).rank → LevQ Dw l₂) → WO (Vc D i) (Wc D i)), IsRoots l₂ (latR (rank_Wc i) (latG (Wc D i) k)) mk N Y → (∀ q, colsR (rank_Wc i) (γ q) = (δ : ℤ) • Y q ∧ IsFinOf (Vc D i) (Wc D i) (γ q) (u q)) → R.ωP i t (h, k) (R.vP i t) = ((Nat.card (Fin (Vc D i).rank → LevQ Dw l₂) : ℂ))⁻¹ • ∑ᶠ q : Fin (Vc D i).rank → LevQ Dw l₂, hatC l₂ φ q • heisO R.ψ (Vc D i) (Wc D i) (u q) (R.ωP i t (h, k) (R.vacP i)) := by
  first | exact @GlobalTheory.AdTh.MovedDatum.moved_datum | exact GlobalTheory.AdTh.MovedDatum.moved_datum | (intros; apply GlobalTheory.AdTh.MovedDatum.moved_datum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoPullO1ToProjOfIsLB
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ProjSpace

theorem lbIso_pull_O1_toProj_of_isLB : ∀ (R : Type) [CommRing R] (N : ℕ) (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (f : X ⟶ Sp R) (s : Fin (N + 1) → L.Sec) (hs : ⨆ i, nonzeroLocus (s i) = ⊤), LBIso ((ProjSpace.O1 R N).pull (ProjSpace.toProj f s hs)) L :=
  fun _ _ _ _ _ _ f s hs => GlobalTheory.ProjSpace.lbIso_pullback_O1_toProj f s hs

end GlobalTheory.ProjSpace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMapExists
section
open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpFrame.LevelMap

variable {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ}

theorem grpA_mul (O : Type) [CommRing O] (lam : ι → ℕ → ℕ) (g h : ι → GL (Fin N) O) :
    grpA O N lam (g * h) = grpA O N lam g * grpA O N lam h := by
  apply Subtype.ext
  show grp O N lam (g * h) = grp O N lam g * grp O N lam h
  unfold grp
  exact map_mul _ g h

theorem grpA_one (O : Type) [CommRing O] (lam : ι → ℕ → ℕ) :
    grpA O N lam 1 = 1 := by
  apply Subtype.ext
  show grp O N lam 1 = 1
  unfold grp
  exact map_one _

def jK (F : Frame l ι N) (lam : ι → ℕ → ℕ) : F.K →* alg F.O N lam where
  toFun κ := (F.chi κ : F.O) • grpA F.O N lam (F.kap κ)
  map_one' := by simp [grpA_one]
  map_mul' a b := by
    rw [map_mul, map_mul, grpA_mul, Units.val_mul, smul_mul_smul_comm]

end GlobalTheory.ExpFrame.LevelMap

theorem GlobalTheory.ExpFrame.levelMap_exists : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ), ∃ (jK : F.K →* alg F.O N lam), F.IsJ lam jK := by
  intro l _ ι _ _ N F lam
  exact ⟨GlobalTheory.ExpFrame.LevelMap.jK F lam, fun κ => rfl⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelRowsEqTypeVectorsOfLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_rows_eq_type_vectors_of_level : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → (R.toCx3 F).EEl false = typeSp3 A3 (R.toCx3 F) (R.gEx F) F.P0 F.ψ0 ∧ (R.toCx3 F).EEl true = typeSp3 A3 (R.toCx3 F) (R.gEx F) F.P1 F.ψ1 := by
  first | exact @GlobalTheory.LevelRows3.eel_eq_typeSp3 | exact GlobalTheory.LevelRows3.eel_eq_typeSp3 | (intros; apply GlobalTheory.LevelRows3.eel_eq_typeSp3 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftIntSpec
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N

namespace GlobalTheory.IntDescend

theorem lift_units {Γ A B : Type} [Group Γ] [Monoid A] [Monoid B] (φ : A →* B) (hφ : Function.Injective φ)
    (f : Γ →* Bˣ) (hf : ∀ g, ((f g : Bˣ) : B) ∈ Set.range φ) : ∃ f' : Γ →* Aˣ, (Units.map φ).comp f' = f := by
  classical
  have h1 : ∀ g, φ (Function.invFun φ ((f g : Bˣ) : B)) = f g := fun g => Function.invFun_eq (hf g)
  have hu : ∀ g, Function.invFun φ ((f g : Bˣ) : B) * Function.invFun φ ((f g⁻¹ : Bˣ) : B) = 1 := by
    intro g
    apply hφ
    rw [map_mul φ, h1, h1, map_one φ, ← Units.val_mul, ← map_mul f, mul_inv_cancel, map_one f, Units.val_one]
  have hv : ∀ g, Function.invFun φ ((f g⁻¹ : Bˣ) : B) * Function.invFun φ ((f g : Bˣ) : B) = 1 := by
    intro g
    apply hφ
    rw [map_mul φ, h1, h1, map_one φ, ← Units.val_mul, ← map_mul f, inv_mul_cancel, map_one f, Units.val_one]
  refine ⟨MonoidHom.mk' (fun g => ⟨Function.invFun φ ((f g : Bˣ) : B), Function.invFun φ ((f g⁻¹ : Bˣ) : B), hu g, hv g⟩) ?_, ?_⟩
  · intro a b
    apply Units.ext
    apply hφ
    change φ (Function.invFun φ ((f (a * b) : Bˣ) : B)) = φ (Function.invFun φ ((f a : Bˣ) : B) * Function.invFun φ ((f b : Bˣ) : B))
    rw [h1, map_mul φ, h1, h1, map_mul f, Units.val_mul]
  · ext g
    exact h1 g

variable {l : ℕ} [Fact l.Prime] (LL : FinExt l)

def liftInt (x : PadicAlgCl l) (hx : x ∈ LL.1 ∧ ‖x‖ ≤ 1) : ↥(OL LL) :=
  ⟨⟨x, hx.1⟩, (GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one l LL ⟨x, hx.1⟩).2 hx.2⟩

theorem liftInt_spec (x : PadicAlgCl l) (hx : x ∈ LL.1 ∧ ‖x‖ ≤ 1) :
    ((LL.1.val.toRingHom).comp ((OL LL).val.toRingHom)) (liftInt LL x hx) = x := rfl

theorem incl_injective : Function.Injective ((LL.1.val.toRingHom).comp ((OL LL).val.toRingHom)) := by
  intro a b h
  exact Subtype.ext (Subtype.ext h)

end GlobalTheory.IntDescend

namespace GlobalTheory.IntDescend

theorem descend : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (Γ : Type) [Group Γ], (∀ (n : ℕ) (f : Γ →* GL (Fin n) (PadicAlgCl l)), (∀ g i j, (f g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ LL.1 ∧ ‖(f g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖ ≤ 1) → ∃ f' : Γ →* GL (Fin n) ↥(OL LL), (Matrix.GeneralLinearGroup.map ((LL.1.val.toRingHom).comp ((OL LL).val.toRingHom))).comp f' = f) ∧ ∀ χ : Γ →* (PadicAlgCl l)ˣ, (∀ g, ((χ g : (PadicAlgCl l)ˣ) : PadicAlgCl l) ∈ LL.1 ∧ ‖((χ g : (PadicAlgCl l)ˣ) : PadicAlgCl l)‖ = 1) → ∃ ψ : Γ →* (↥(OL LL))ˣ, (Units.map ((LL.1.val.toRingHom).comp ((OL LL).val.toRingHom)).toMonoidHom).comp ψ = χ := by
  intro l _ LL Γ _
  refine ⟨?_, ?_⟩
  · intro n f hf
    have hinj : Function.Injective
        ((((LL.1.val.toRingHom).comp ((OL LL).val.toRingHom)).mapMatrix : Matrix (Fin n) (Fin n) ↥(OL LL) →+* Matrix (Fin n) (Fin n) (PadicAlgCl l)).toMonoidHom) := by
      intro M N h
      refine Matrix.ext fun i j => ?_
      apply incl_injective LL
      have := congrArg (fun P : Matrix (Fin n) (Fin n) (PadicAlgCl l) => P i j) h
      simpa only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply] using this
    have hr : ∀ g, ((f g : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) ∈ Set.range
        ((((LL.1.val.toRingHom).comp ((OL LL).val.toRingHom)).mapMatrix : Matrix (Fin n) (Fin n) ↥(OL LL) →+* Matrix (Fin n) (Fin n) (PadicAlgCl l)).toMonoidHom) := by
      intro g
      refine ⟨Matrix.of fun i j => liftInt LL _ (hf g i j), ?_⟩
      ext i j
      simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
      exact liftInt_spec LL _ (hf g i j)
    exact lift_units _ hinj f hr
  · intro χ hχ
    refine lift_units _ (incl_injective LL) χ ?_
    intro g
    exact ⟨liftInt LL _ ⟨(hχ g).1, (hχ g).2.le⟩, liftInt_spec LL _ _⟩

end GlobalTheory.IntDescend
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftModelParameterDecreasingHalfIntegralWidthStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftModelParameter_decreasing_halfIntegral_width : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ i σ s, IsEmbOverK D σ s → ∀ ρ, StrictAnti ((R.MW i σ).lam ρ) ∧ (∀ a, ∃ z : ℤ, (R.MW i σ).lam ρ a - (((Wc D i).rank : ℝ) - 1) / 2 = (z : ℝ)) ∧ ∀ a b, |(R.MW i σ).lam ρ a - (R.MW i σ).lam ρ b| ≤ (degAt D i σ ρ : ℝ) + D.R.nV + 3 := by
  first | exact @GlobalTheory.LowRow.lam_par_width | exact GlobalTheory.LowRow.lam_par_width | (intros; apply GlobalTheory.LowRow.lam_par_width <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftRowsAntitoneSignatureRankStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftRows_antitone_signature_rank : ∀ (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau), Antitone (aPlAt D i σ ρ) ∧ Antitone (aMiAt D i σ ρ) ∧ pW D i ρ + qW D i ρ = (Wc D i).rank ∧ (Wc D i).rank ≤ (Vc D i).rank := by
  first | exact @GlobalTheory.LowRow.lift_rows_antitone | exact GlobalTheory.LowRow.lift_rows_antitone | (intros; apply GlobalTheory.LowRow.lift_rows_antitone <;> assumption)
end

